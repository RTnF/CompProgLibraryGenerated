"""Erase classes with exactly one scalar field into plain functions over that field.

A class K with a single scalar field of type T is modelled by T itself: objects of K become values of
type T, `this` becomes a reference parameter of type T, member access disappears, copy and move
construction become the identity, user constructors become value-returning functions of their
arguments, and methods and friend functions become functions whose receiver is the first argument.
The transformation is syntactic on the Clang AST and keeps ids and locations, so the downstream
lowering (and the inliner in inline_ast) sees ordinary scalar code.
"""
import copy
import re

SCALAR_FIELD_TYPES = {'unsigned int', 'int', 'long long', 'unsigned long long', 'long', 'unsigned long', 'bool',
                      'short', 'unsigned short', 'char', 'unsigned char'}

OPERATOR_NAMES = {'+=': 'add_assign', '-=': 'sub_assign', '*=': 'mul_assign', '/=': 'div_assign', '%=': 'rem_assign',
                  '++': 'increment', '--': 'decrement', '+': 'add', '-': 'sub', '*': 'mul', '/': 'div', '%': 'rem',
                  '==': 'eq', '!=': 'ne', '<': 'lt', '>': 'gt', '<=': 'le', '>=': 'ge', '!': 'not', '<<': 'shl',
                  '>>': 'shr', '&': 'and', '|': 'or', '^': 'xor', '()': 'call', '[]': 'index', '=': 'assign'}


def validate_scalar_value_record(record, fields):
    """Identity copying is valid only for plain scalar value objects.

    Rich construction/lifetime frontends have their own contracts. This guard
    applies to scalar erasure, including helper records in factory bodies.
    """
    if record.get('bases') or any(c.get('kind') == 'CXXBaseSpecifier' for c in record.get('inner', [])):
        raise ValueError('scalar value erasure does not support base classes')
    if any(field.get('isBitfield') for field in fields):
        raise ValueError('scalar value erasure does not support bitfields')
    definition = record.get('definitionData', {})
    if not definition.get('dtor', {}).get('trivial'):
        raise ValueError('scalar value erasure requires trivial destruction')
    if not definition.get('copyCtor', {}).get('trivial') or (
            definition.get('moveCtor', {}).get('exists') and
            not definition.get('moveCtor', {}).get('trivial')):
        raise ValueError('scalar value erasure requires trivial copy and move construction')


def constructor_body_may_change_state(node):
    """Keep the old pure/assert-only models; sequence all other bodies explicitly.

    The assertion verifier still checks the system failure declaration later.
    A successful call to that noreturn declaration cannot modify a live state.
    """
    kind = node.get('kind')
    if kind in ('CXXConstructExpr', 'CXXTemporaryObjectExpr') or node.get('cleanupsHaveSideEffects'):
        return True
    if kind in ('CallExpr', 'CXXMemberCallExpr', 'CXXOperatorCallExpr'):
        from scalar_assert import direct_callee
        callee = direct_callee(node)
        if callee is None or callee.get('referencedDecl', {}).get('name') != '__assert_fail':
            return True
    if kind == 'CompoundAssignOperator' or (kind == 'BinaryOperator' and node.get('opcode') == '=') or (
            kind == 'UnaryOperator' and node.get('opcode') in ('++', '--')):
        return True
    return any(constructor_body_may_change_state(c) for c in node.get('inner', []))


def constructor_uses_this(node):
    return node.get('kind') == 'CXXThisExpr' or any(
        constructor_uses_this(c) for c in node.get('inner', []))


def function_name(class_name, method_name):
    if method_name.startswith('operator'):
        symbol = method_name[len('operator'):].strip()
        if symbol not in OPERATOR_NAMES:
            raise ValueError('unsupported operator: ' + method_name)
        method_name = OPERATOR_NAMES[symbol]
    return re.sub(r'[^A-Za-z0-9_]', '_', f'{class_name}_{method_name}')


def spellings(record, qualified_name):
    """The ways Clang spells the class type in qualType strings."""
    return sorted({qualified_name, qualified_name.removeprefix('cp::')}, key=len, reverse=True)


class ErasedClass:
    def __init__(self, record, class_name, display):
        self.record = record
        self.class_name = class_name
        fields = [c for c in record.get('inner', []) if c.get('kind') == 'FieldDecl']
        if len(fields) != 1 or any(c.get('kind') in ('CXXBaseSpecifier',) for c in record.get('inner', [])):
            raise ValueError('single scalar field required')
        validate_scalar_value_record(record, fields)
        self.field = fields[0]
        self.field_type = self.field['type'].get('desugaredQualType', self.field['type']['qualType'])
        if self.field_type not in SCALAR_FIELD_TYPES:
            raise ValueError('unsupported field type: ' + self.field_type)
        self.display = display
        arguments = [c for c in record.get('inner', []) if c.get('kind') == 'TemplateArgument'] \
            if record.get('kind') == 'ClassTemplateSpecializationDecl' else []
        # Type arguments (`T = long long`) are resolved by the instantiation itself: the instance is then an
        # ordinary program with no generic Lean counterpart. Only integral arguments become Nat parameters.
        self.template_arguments = [str(c.get('value')) for c in arguments] \
            if arguments and all('value' in c for c in arguments) else []
        names = {}
        def scan(node):
            if isinstance(node, dict):
                if node.get('kind') == 'NonTypeTemplateParmDecl':
                    names[node.get('index', len(names))] = node['name']
                for value in node.values():
                    scan(value)
            elif isinstance(node, list):
                for value in node:
                    scan(value)
        scan(record.get('inner', []))
        self.parameter_names = [names[i] for i in sorted(names)]
        self.pattern = re.compile(r'(?:cp::)?' + re.escape(display))
        self.methods = {}      # method id -> function
        self.constructors = {}  # constructor signature -> function
        self.friends = {}       # function id -> function

    def template_key(self, name):
        """(generic function name, template arguments) when the class is a template specialization."""
        if not self.template_arguments:
            return None
        prefix = self.class_name
        generic_prefix = prefix[:len(prefix) - len('_'.join(re.sub(r'[^A-Za-z0-9_]', '_', a) for a in self.template_arguments)) - 1]
        return (generic_prefix + name[len(prefix):], list(self.template_arguments), list(self.parameter_names))

    def erase_text(self, text):
        return self.pattern.sub(self.field_type, text)


def erase_type_info(info, classes):
    if not isinstance(info, dict):
        return info
    result = dict(info)
    for key in ('qualType', 'desugaredQualType'):
        if key in result:
            for erased in classes:
                result[key] = erased.erase_text(result[key])
    return result


class Eraser:
    def __init__(self, classes):
        self.classes = classes
        self.by_method = {}
        self.by_function = {}
        self.by_constructor = {}
        for erased in classes:
            self.by_method.update(erased.methods)
            self.by_function.update(erased.friends)
            self.by_constructor.update({(id(erased), s): f for s, f in erased.constructors.items()})

    def mentions_class(self, text):
        return any(erased.pattern.search(text or '') for erased in self.classes)

    def class_of_type(self, info):
        text = info.get('desugaredQualType', info.get('qualType', '')) if isinstance(info, dict) else ''
        for erased in self.classes:
            if erased.pattern.search(text):
                return erased
        return None

    def field_ids(self):
        return {erased.field['id'] for erased in self.classes}

    def transform(self, node, this_parameter):
        if isinstance(node, list):
            return [self.transform(child, this_parameter) for child in node]
        if not isinstance(node, dict):
            return node
        kind = node.get('kind')
        children = node.get('inner', [])
        if kind == 'ExprWithCleanups':
            # Drop only the envelope of known trivial record materializations;
            # keep every child expression and reject destruction/cleanup effects.
            materialized = []
            known = set()
            for cls in self.classes:
                known.update((cls.display, 'cp::'+cls.display))
                requested = cls.record.get('_template_witness_origin', {}).get('requested')
                if requested:
                    known.add(requested)

            def validate_cleanup(expression):
                if expression.get('cleanupsHaveSideEffects') or expression.get('kind') == 'CXXBindTemporaryExpr':
                    raise ValueError('materialized scalar expression has unsupported cleanup effects')
                if expression.get('kind') == 'MaterializeTemporaryExpr':
                    info = expression.get('type', {})
                    text = info.get('desugaredQualType', info.get('qualType', '')).removeprefix('const ').removeprefix('::')
                    if text not in known:
                        raise ValueError('materialized scalar expression needs an exact known trivial record type')
                    materialized.append(text)
                for child in expression.get('inner', []):
                    validate_cleanup(child)

            validate_cleanup(node)
            if len(children) != 1 or not materialized:
                raise ValueError('materialized scalar expression needs one value and a known materialization')
            return self.transform(children[0], this_parameter)
        if kind == 'SubstNonTypeTemplateParmExpr':
            replacement = [c for c in children if c.get('kind') != 'NonTypeTemplateParmDecl']
            declarations = [c for c in children if c.get('kind') == 'NonTypeTemplateParmDecl']
            if len(replacement) != 1 or len(declarations) != 1 or replacement[0].get('kind') != 'IntegerLiteral':
                raise ValueError('unsupported template parameter substitution')
            literal = self.transform(replacement[0], this_parameter)
            return dict(literal, templateParameter=declarations[0]['name'])
        if kind == 'CXXThisExpr':
            raise ValueError('this may only appear as *this or as the object of a member access')
        if kind == 'UnaryOperator' and node.get('opcode') == '*' and len(children) == 1 \
                and children[0].get('kind') == 'CXXThisExpr':
            return self.reference(this_parameter, node)
        if kind == 'MemberExpr' and len(children) == 1 and children[0].get('kind') == 'CXXThisExpr' \
                and node.get('referencedMemberDecl') in self.field_ids():
            return self.reference(this_parameter, node)
        if kind == 'MemberExpr' and len(children) == 1 and children[0].get('kind') == 'CXXThisExpr' \
                and this_parameter is not None:
            # the implicit receiver of a call to another method of the class
            object_type = {'qualType': this_parameter['type']['qualType'].removesuffix(' &')}
            return dict(node, inner=[self.reference(this_parameter, dict(children[0], type=object_type))])
        if kind == 'MemberExpr' and node.get('referencedMemberDecl') in self.field_ids() and len(children) == 1:
            base = self.transform(children[0], this_parameter)
            return self.retype(base, node)
        new_children = [self.transform(child, this_parameter) for child in children]
        result = dict(node)
        if 'inner' in node:
            result['inner'] = new_children
        for key in ('type',):
            if key in result:
                result[key] = erase_type_info(result[key], self.classes)
        if 'referencedDecl' in result:
            result['referencedDecl'] = dict(result['referencedDecl'])
            if 'type' in result['referencedDecl']:
                result['referencedDecl']['type'] = erase_type_info(result['referencedDecl']['type'], self.classes)
        if kind == 'VarDecl' and result.get('inner') and self.class_of_type(node.get('type', {})) is not None:
            result['init'] = 'c'
        if kind == 'CXXConstructExpr':
            return self.construct(result, node)
        if kind in ('ImplicitCastExpr', 'CXXFunctionalCastExpr') and node.get('castKind') in ('ConstructorConversion',) \
                and len(new_children) == 1:
            return new_children[0]
        if kind in ('CXXOperatorCallExpr', 'CXXMemberCallExpr'):
            return self.call(result, node)
        if kind == 'CXXStaticCastExpr' and node.get('castKind') == 'NoOp' and len(new_children) == 1:
            return self.rvalue_alias(new_children[0], result)
        return result

    def reference(self, parameter, original):
        return {'kind': 'DeclRefExpr', 'type': erase_type_info(original['type'], self.classes),
                'valueCategory': 'lvalue',
                'referencedDecl': {'id': parameter['id'], 'kind': 'ParmVarDecl', 'name': parameter['name'],
                                   'type': parameter['type']}}

    def retype(self, base, original):
        return dict(base, type=erase_type_info(original['type'], self.classes),
                    valueCategory=original.get('valueCategory', base.get('valueCategory')))

    def rvalue_alias(self, child, node):
        return dict(child, type=node['type'], valueCategory=node.get('valueCategory', child.get('valueCategory')))

    def construct(self, result, original):
        signature = original.get('ctorType', {}).get('qualType', '')
        erased = self.class_of_type(original.get('type', {}))
        if erased is None:
            return result
        children = result.get('inner', [])
        parameter = re.sub(r'^void \(', '', signature).rstrip(')')
        parameter = parameter.replace(' noexcept', '')
        parameter = erased.erase_text(parameter)
        copy_like = signature.replace(' noexcept', '') in (f'void (const {erased.display} &)', f'void ({erased.display} &&)',
                                                          f'void (const cp::{erased.display} &)', f'void (cp::{erased.display} &&)')
        if copy_like and len(children) == 1:
            return children[0]
        key = (id(erased), signature.replace(' noexcept', ''))
        function = self.by_constructor.get(key)
        if function is None:
            raise ValueError('constructor without a user-provided definition: ' + signature)
        callee = {'kind': 'DeclRefExpr', 'type': function['type'], 'valueCategory': 'lvalue',
                  'referencedDecl': {'id': function['id'], 'kind': 'FunctionDecl', 'name': function['name'],
                                     'type': function['type']}}
        return {'kind': 'CallExpr', 'type': erase_type_info(original['type'], self.classes),
                'valueCategory': 'prvalue', 'range': original.get('range', {}), 'loc': original.get('loc', {}),
                'inner': [callee] + [c for c in children]}

    def call(self, result, original):
        children = result.get('inner', [])
        if original['kind'] == 'CXXMemberCallExpr':
            head = children[0]
            if head.get('kind') != 'MemberExpr':
                raise ValueError('unsupported member call')
            function = self.by_method.get(head.get('referencedMemberDecl'))
            if function is None:
                return result
            receiver = head['inner'][0]
            arguments = [receiver] + children[1:]
        else:
            callee = children[0]
            while callee.get('kind') == 'ImplicitCastExpr' and len(callee.get('inner', [])) == 1:
                callee = callee['inner'][0]
            declaration = callee.get('referencedDecl', {})
            function = self.by_method.get(declaration.get('id')) or self.by_function.get(declaration.get('id'))
            if function is None:
                return result
            arguments = children[1:]
        callee = {'kind': 'DeclRefExpr', 'type': function['type'], 'valueCategory': 'lvalue',
                  'referencedDecl': {'id': function['id'], 'kind': 'FunctionDecl', 'name': function['name'],
                                     'type': function['type']}}
        return {'kind': 'CallExpr', 'type': result['type'], 'valueCategory': result.get('valueCategory', 'prvalue'),
                'range': original.get('range', {}), 'loc': original.get('loc', {}), 'inner': [callee] + arguments}


def build_functions(erased, source, friends):
    """Create the functions of an erased class (methods, constructors and friends)."""
    record = erased.record
    functions = []
    this_parameters = {}
    name = erased.class_name
    for member in record.get('inner', []):
        kind = member.get('kind')
        if member.get('isImplicit'):
            continue
        bodies = [c for c in member.get('inner', []) if c.get('kind') == 'CompoundStmt']
        if kind == 'CXXMethodDecl' and len(bodies) == 1:
            signature = member['type']['qualType']
            constant = signature.endswith(' const')
            static = member.get('storageClass') == 'static'
            reference = ('const ' if constant else '') + erased.field_type + ' &'
            parameter = {'kind': 'ParmVarDecl', 'id': f'this:{member["id"]}', 'name': erased.field['name'],
                         'isUsed': True, 'field': True, 'type': {'qualType': reference}}
            if 'loc' in erased.field:
                parameter['loc'] = erased.field['loc']
            function = {key: value for key, value in member.items() if key != 'inner'}
            function['kind'] = 'FunctionDecl'
            function['name'] = function_name(name, member['name'])
            if member['name'] in ('operator-', 'operator+') and not any(
                    c.get('kind') == 'ParmVarDecl' for c in member.get('inner', [])):
                function['name'] += '_unary'
            function['type'] = {'qualType': erased.erase_text(signature[:-len(' const')] if constant else signature)}
            # A static member function has no receiver: it is a function of its arguments alone.
            function.pop('storageClass', None)
            function['inner'] = ([] if static else [parameter]) + list(member.get('inner', []))
            function['loc'].setdefault('file', str(source))
            function['_this'] = None if static else parameter
            function['_inline'] = True
            function['_template'] = erased.template_key(function['name'])
            erased.methods[member['id']] = function
            functions.append(function)
        elif kind == 'CXXConstructorDecl' and len(bodies) == 1:
            initializers = [c for c in member.get('inner', []) if c.get('kind') == 'CXXCtorInitializer']
            if len(initializers) != 1:
                raise ValueError('constructors must initialize exactly the field or delegate')
            initializer = initializers[0]
            direct = initializer.get('anyInit', {}).get('id') == erased.field['id']
            delegated = initializer.get('delegatingInit')
            if not direct:
                if not isinstance(delegated, dict) or not erased.pattern.fullmatch(
                        delegated.get('desugaredQualType', delegated.get('qualType', ''))):
                    raise ValueError('constructor delegation must name the same scalar class')
                # A delegated initializer is evaluated before this body. The scalar
                # erasure returns the initializer last, so a nonempty body needs
                # a separate sequencing model; reject it here.
                if bodies[0].get('inner'):
                    raise ValueError('delegating constructor body must be empty')
            if len(initializer.get('inner', [])) != 1:
                raise ValueError('exactly one constructor initializer expression required')
            expression = initializer['inner'][0]
            if not direct:
                def check_cleanup(node):
                    if node.get('kind') == 'CXXBindTemporaryExpr' or node.get('cleanupsHaveSideEffects'):
                        raise ValueError('delegated temporary has unsupported cleanup effects')
                    for child in node.get('inner', []):
                        check_cleanup(child)
                check_cleanup(expression)
                if expression.get('kind') == 'ExprWithCleanups':
                    if len(expression.get('inner', [])) != 1:
                        raise ValueError('one delegated initializer expression required')
                    expression = expression['inner'][0]
            parameters = [c for c in member.get('inner', []) if c.get('kind') == 'ParmVarDecl']
            return_statement = {'kind': 'ReturnStmt', 'range': member.get('range', {}), 'inner': [expression]}
            body_statements = list(bodies[0].get('inner', []))
            field_local = None
            if direct and (constructor_uses_this(bodies[0]) or
                    constructor_body_may_change_state(bodies[0]) or (
                    body_statements and constructor_body_may_change_state(expression))):
                # Field initialization precedes the body, including writes to
                # constructor parameters and to this field. Store that value
                # once, then use the local as this for the body and result.
                field_local = dict(kind='VarDecl', id='constructor-field:'+member['id'],
                                   name='constructor_field', type={'qualType':erased.field_type},
                                   init='c', inner=[expression])
                reference = dict(kind='DeclRefExpr', type=field_local['type'], valueCategory='lvalue',
                                 referencedDecl={k:field_local[k] for k in ('id','kind','name','type')})
                return_statement = dict(return_statement, inner=[reference])
                body_statements.insert(0, dict(kind='DeclStmt', inner=[field_local]))
            body = {'kind': 'CompoundStmt', 'range': bodies[0].get('range', {}),
                    'inner': body_statements + [return_statement]}
            signature = member['type']['qualType']
            function = {key: value for key, value in member.items() if key != 'inner'}
            function['kind'] = 'FunctionDecl'
            function['name'] = re.sub(r'[^A-Za-z0-9_]', '_', f'{name}_new{len(erased.constructors)}')
            function['type'] = {'qualType': erased.field_type + signature[len('void'):]}
            function['inner'] = parameters + [body]
            function['loc'].setdefault('file', str(source))
            function['_inline'] = True
            if field_local is not None:
                function['_this'] = field_local
            function['_template'] = erased.template_key(function['name'])
            erased.constructors[signature.replace(' noexcept', '')] = function
            functions.append(function)
    for friend in friends:
        declaration = friend.get('inner', [None])[0]
        if not declaration or declaration.get('kind') != 'FunctionDecl':
            continue
        bodies = [c for c in declaration.get('inner', []) if c.get('kind') == 'CompoundStmt']
        if len(bodies) != 1:
            continue
        if any(c.get('kind') == 'TemplateArgument' for c in declaration.get('inner', [])):
            continue  # a friend that is a function template instance is lowered with the template's instances
        function = dict(declaration)
        function['name'] = function_name(name, declaration['name'])
        function['loc'] = dict(declaration.get('loc', {}))
        function['loc'].setdefault('file', str(source))
        function['_inline'] = True
        erased.friends[declaration['id']] = function
        functions.append(function)
    return functions


def erase_functions(erased_classes, functions):
    """Apply the erasure to the functions built by build_functions (and to free functions)."""
    eraser = Eraser(erased_classes)
    result = []
    for function in functions:
        if function.get('kind') != 'FunctionDecl':
            result.append(function)  # a template declaration without instances is not lowered
            continue
        this_parameter = function.get('_this')
        rewritten = dict(function)
        rewritten['inner'] = [eraser.transform(c, this_parameter) if c.get('kind') != 'ParmVarDecl'
                              else dict(c, type=erase_type_info(c['type'], erased_classes))
                              for c in function['inner']]
        rewritten['type'] = erase_type_info(function['type'], erased_classes)
        # A reference result is modelled by the returned value (the final `return *this` yields the new value).
        qual = rewritten['type']['qualType']
        match = re.match(r'^([^(]*?)\s*&\s*(\(.*)$', qual)
        if match:
            rewritten['type'] = {'qualType': match.group(1) + ' ' + match.group(2)}
        result.append(rewritten)
    return result
