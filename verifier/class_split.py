"""Split classes with several scalar fields into per-field scalar functions.

A class K with scalar fields f1..fk is never materialised. Every function that mentions K is rewritten:

* a parameter of type K (by value, by reference or `this`) becomes one parameter per field, with the same constness;
* `x.fi` over such a parameter becomes a reference to the parameter of that field;
* a function returning K must return a constructor call; it becomes k functions `name_fi`, the i-th returning the
  expression that initialises the field `fi` (the constructor's initialisers with its parameters replaced by the
  arguments);
* a function returning a scalar is rewritten once.

The result is a list of ordinary scalar function declarations, so the rest of the pipeline sees no class. Anything
outside these shapes (locals of type K, copies, calls that pass or return K) is rejected, not guessed.
"""
import copy
import re

from class_lowering import (SCALAR_FIELD_TYPES, function_name, validate_scalar_value_record,
                            constructor_body_may_change_state, nested_type_pattern)

SKIP_WRAPPERS = ('ExprWithCleanups', 'ImplicitCastExpr', 'CXXFunctionalCastExpr', 'MaterializeTemporaryExpr',
                 'CXXBindTemporaryExpr', 'ParenExpr')


def field_type(field):
    return field['type'].get('desugaredQualType', field['type']['qualType'])


def is_split_candidate(record):
    fields = [c for c in record.get('inner', []) if c.get('kind') == 'FieldDecl']
    return (len(fields) >= 2 and all(field_type(f) in SCALAR_FIELD_TYPES for f in fields)
            and not any(c.get('kind') == 'CXXBaseSpecifier' for c in record.get('inner', [])))


class SplitClass:
    def __init__(self, record, class_name, display):
        self.record = record
        self.class_name = class_name
        self.display = display
        self.fields = [c for c in record.get('inner', []) if c.get('kind') == 'FieldDecl']
        validate_scalar_value_record(record, self.fields)
        self.pattern = nested_type_pattern(record, display) or re.compile(
            r'(?<![A-Za-z0-9_])(?:cp::)?' + re.escape(display) + r'(?![A-Za-z0-9_<])')
        self.constructors = {}
        self.raw_constructors = {}
        self.constructor_nodes = {}
        self.delegating = set()
        self.value_types = {display}
        origin = record.get('_template_witness_origin', {})
        if origin.get('nested_members'):
            self.value_types.update((origin['requested'], '::'+origin['requested']))
        self.factories = {n['id']:n for n in record.get('inner',[]) if n.get('kind') == 'CXXMethodDecl'
                          and n.get('storageClass') == 'static'
                          and any(c.get('kind') == 'CompoundStmt' for c in n.get('inner',[]))}
        for member in record.get('inner', []):
            if member.get('kind') != 'CXXConstructorDecl' or member.get('isImplicit'):
                continue
            body = [c for c in member.get('inner', []) if c.get('kind') == 'CompoundStmt']
            if len(body) != 1:
                raise ValueError('a constructor needs a body')
            parameters = [c for c in member.get('inner', []) if c.get('kind') == 'ParmVarDecl']
            initializers = [n for n in member.get('inner',[]) if n.get('kind') == 'CXXCtorInitializer']
            delegated = [n for n in initializers if 'delegatingInit' in n]
            signature = member['type']['qualType'].replace(' noexcept','')
            if delegated:
                if len(initializers) != 1 or len(delegated[0].get('inner',[])) != 1 or not self.is_class_type(delegated[0]['delegatingInit']):
                    raise ValueError('split delegation needs exactly one same-class initializer')
                if body[0].get('inner'):
                    raise ValueError('split delegating constructor body must be empty')
                inits = [delegated[0]['inner'][0]]
                # Clang's delegating initializer belongs to this record and
                # constructs this same class. Preserve its canonical qualified
                # spelling instead of guessing a namespace from a source name.
                for info in (delegated[0]['delegatingInit'],inits[0].get('type',{})):
                    self.value_types.update(info[key] for key in ('qualType','desugaredQualType') if key in info)
                self.delegating.add(signature)
            else:
                inits = {n.get('anyInit',{}).get('id'):n['inner'][0] for n in initializers
                         if len(n.get('inner',[])) == 1}
                if set(inits) != {f['id'] for f in self.fields}:
                    raise ValueError('a constructor must initialise every field')
            self.raw_constructors[signature] = (parameters,inits,body[0].get('inner',[]))
            self.constructor_nodes[signature] = member
        for signature,(parameters,inits,body) in self.raw_constructors.items():
            if signature in self.delegating:
                inits = self.delegation_fields(inits[0],(('constructor',signature),))
            self.constructors[signature] = (parameters,inits,body)

    def delegation_fields(self, expression, active=()):
        """Resolve a literal-only, same-class factory used by a delegating ctor.

        This projection path never discards effects or failing arithmetic in
        another field: all expanded field values must be integer literals.
        """
        if self.record.get('bases'):
            raise ValueError('split delegation does not support base classes')
        def same_class(info):
            text = info.get('desugaredQualType',info.get('qualType','')).strip()
            text = text.removeprefix('const ').removesuffix(' &&').removesuffix(' &')
            return text in self.value_types
        definition = self.record.get('definitionData', {})
        if not definition.get('dtor', {}).get('trivial') or not definition.get('copyCtor', {}).get('trivial') or (
                definition.get('moveCtor', {}).get('exists') and not definition.get('moveCtor', {}).get('trivial')):
            raise ValueError('split delegation requires trivial copy, move and destruction')
        def unwrap(node):
            while node.get('kind') in ('ExprWithCleanups','MaterializeTemporaryExpr','CXXFunctionalCastExpr',
                                       'ImplicitCastExpr','ParenExpr'):
                if node.get('cleanupsHaveSideEffects') or node.get('castKind') not in (None,'NoOp','ConstructorConversion'):
                    raise ValueError('split delegation has unsupported cleanup or cast')
                if len(node.get('inner',[])) != 1:
                    raise ValueError('split delegation wrapper must have one expression')
                node = node['inner'][0]
            return node
        value = unwrap(expression)
        if value.get('kind') == 'CallExpr':
            children = value.get('inner',[])
            if len(children) != 1:
                raise ValueError('split delegation factory must have no arguments')
            callee = children[0]
            while callee.get('kind') == 'ImplicitCastExpr' and callee.get('castKind') == 'FunctionToPointerDecay':
                if len(callee.get('inner',[])) != 1:
                    raise ValueError('split delegation factory needs a direct callee')
                callee = callee['inner'][0]
            if callee.get('kind') != 'DeclRefExpr':
                raise ValueError('split delegation factory needs a direct callee')
            identity = callee.get('referencedDecl',{}).get('id')
            factory = self.factories.get(identity)
            if factory is None or identity in active:
                raise ValueError('split delegation factory must be a defined nonrecursive static member')
            allowed = {'CompoundStmt'}
            if any(n.get('kind') not in allowed for n in factory.get('inner',[])) or factory.get('variadic'):
                raise ValueError('split delegation factory parameters and attributes are unsupported')
            body = factory['inner'][0]
            statements = body.get('inner',[])
            if len(statements) != 1 or statements[0].get('kind') != 'ReturnStmt' or len(statements[0].get('inner',[])) != 1:
                raise ValueError('split delegation factory needs one return and no side effects')
            return self.delegation_fields(statements[0]['inner'][0],(*active,identity))
        if value.get('kind') not in ('CXXConstructExpr','CXXTemporaryObjectExpr') or not same_class(value.get('type',{})):
            raise ValueError('split delegation needs same-class construction')
        signature = value.get('ctorType',{}).get('qualType','').replace(' noexcept','')
        arguments = value.get('inner',[])
        if signature not in self.raw_constructors:
            # Implicit trivial copy/move: the single argument has the same class.
            copies = {f'void ({prefix}{name}{suffix})' for name in self.value_types
                      for prefix in ('','const ') for suffix in (' &',' &&')}
            if signature not in copies or len(arguments) != 1 or not same_class(arguments[0].get('type',{})):
                raise ValueError('split delegation constructor is unsupported')
            return self.delegation_fields(arguments[0],active)
        identity = ('constructor',signature)
        if identity in active:
            raise ValueError('recursive split delegation is unsupported')
        parameters,inits,body = self.raw_constructors[signature]
        if body or len(parameters) != len(arguments):
            raise ValueError('split delegation target needs an empty body and explicit arguments')
        def literal_argument(node):
            if node.get('kind') == 'IntegerLiteral':
                return not node.get('inner') and re.fullmatch(r'[0-9]+',node.get('value','')) is not None
            return (node.get('kind') == 'ImplicitCastExpr' and
                    node.get('castKind') in ('IntegralCast','NoOp','LValueToRValue') and
                    len(node.get('inner',[])) == 1 and literal_argument(node['inner'][0]))
        if not all(literal_argument(argument) for argument in arguments):
            raise ValueError('split delegation requires literal-only constructor arguments, including unused arguments')
        mapping = {p['id']:argument for p,argument in zip(parameters,arguments)}
        if isinstance(inits,list):
            if len(inits) != 1:
                raise ValueError('split delegation needs exactly one initializer')
            return self.delegation_fields(substitute(inits[0],mapping),(*active,identity))
        result = {field:substitute(initializer,mapping) for field,initializer in inits.items()}
        def literal(node):
            if node.get('kind') == 'IntegerLiteral':
                return not node.get('inner') and re.fullmatch(r'[0-9]+',node.get('value','')) is not None
            return (node.get('kind') == 'ImplicitCastExpr' and
                    node.get('castKind') in ('IntegralCast','NoOp','LValueToRValue') and
                    len(node.get('inner',[])) == 1 and literal(node['inner'][0]))
        if not all(literal(initializer) for initializer in result.values()):
            raise ValueError('split delegation currently requires literal-only field initializers')
        return result

    def constructor_functions(self):
        """Expose each constructor's fields when delegation is present."""
        if not self.delegating:
            return []
        results = []
        for number,(signature,member) in enumerate(self.constructor_nodes.items()):
            parameters = [n for n in member.get('inner',[]) if n.get('kind') == 'ParmVarDecl']
            arguments = [dict(kind='DeclRefExpr',type=p['type'],valueCategory='lvalue',
                              referencedDecl={k:p[k] for k in ('id','kind','name','type')}) for p in parameters]
            construct = dict(kind='CXXConstructExpr',type={'qualType':self.display},valueCategory='prvalue',
                             ctorType={'qualType':signature},inner=arguments)
            original_body = next(n for n in member['inner'] if n.get('kind') == 'CompoundStmt')
            body = dict(kind='CompoundStmt',range=original_body['range'],
                        inner=[dict(kind='ReturnStmt',range=member.get('range',{}),inner=[construct])])
            function = {k:v for k,v in member.items() if k not in ('inner','storageClass')}
            function.update(kind='CXXMethodDecl',id='split-constructor:'+member['id'],name='new'+str(number),
                            storageClass='static',type={'qualType':self.display+signature[len('void'):]},
                            inner=parameters+[body])
            results.append(function)
        return results


    def mentions(self, text):
        return bool(self.pattern.search(text or ''))

    def is_class_type(self, info):
        text = info.get('desugaredQualType', info.get('qualType', '')) if isinstance(info, dict) else ''
        return self.mentions(text)


def strip(node):
    while isinstance(node, dict) and node.get('kind') in SKIP_WRAPPERS and len(node.get('inner', [])) == 1 \
            and node.get('castKind') in (None, 'NoOp', 'ConstructorConversion', 'LValueToRValue'):
        node = node['inner'][0]
    return node


def qual(const, text, reference):
    return ('const ' if const else '') + text + (' &' if reference else '')


def parameter_for(field, owner_name, owner_id, const, reference, loc):
    parameter = {'kind': 'ParmVarDecl', 'id': f"split:{owner_id}:{field['id']}", 'name': f"{owner_name}_{field['name']}",
                 'isUsed': True, 'field': True, 'type': {'qualType': qual(const, field_type(field), reference)}}
    if loc:
        parameter['loc'] = loc
    return parameter


def substitute(node, mapping):
    """Replace references to parameters (by id) with copies of the given expressions."""
    if isinstance(node, list):
        return [substitute(c, mapping) for c in node]
    if not isinstance(node, dict):
        return node
    if node.get('kind') == 'DeclRefExpr' and node.get('referencedDecl', {}).get('id') in mapping:
        return copy.deepcopy(mapping[node['referencedDecl']['id']])
    result = dict(node)
    if 'inner' in node:
        result['inner'] = [substitute(c, mapping) for c in node['inner']]
    return result


class Splitter:
    def __init__(self, classes):
        self.classes = classes
        self.return_hook = None
        self.by_field = {f['id']: (c, f) for c in classes for f in c.fields}

    def class_of(self, info):
        for c in self.classes:
            if c.is_class_type(info):
                return c
        return None

    def rewrite(self, node, params):
        """params: id of a class parameter -> {field id: field parameter}."""
        if isinstance(node, list):
            return [self.rewrite(c, params) for c in node]
        if not isinstance(node, dict):
            return node
        kind = node.get('kind')
        children = node.get('inner', [])
        if kind == 'ReturnStmt' and self.return_hook is not None:
            return self.return_hook(node, params)
        if kind == 'MemberExpr' and node.get('referencedMemberDecl') in self.by_field and len(children) == 1:
            base = strip(children[0])
            owner = None
            if base.get('kind') == 'CXXThisExpr':
                owner = params.get('this')
            elif base.get('kind') == 'DeclRefExpr':
                owner = params.get(base.get('referencedDecl', {}).get('id'))
            if owner is None:
                raise ValueError('a field is read from an unsupported object')
            parameter = owner[node['referencedMemberDecl']]
            return {'kind': 'DeclRefExpr', 'type': node['type'], 'valueCategory': 'lvalue',
                    'referencedDecl': {'id': parameter['id'], 'kind': 'ParmVarDecl', 'name': parameter['name'],
                                       'type': parameter['type']}}
        if kind == 'CXXThisExpr':
            raise ValueError('this may only appear as the object of a field access')
        if kind == 'DeclRefExpr' and node.get('referencedDecl', {}).get('id') in params:
            raise ValueError('a class value may only be used through its fields')
        if self.class_of(node.get('type', {})) is not None and kind not in ('ReturnStmt',):
            raise ValueError(f'unsupported use of a class value ({kind})')
        result = dict(node)
        if 'inner' in node:
            rewritten = [self.rewrite(c, params) for c in children]
            if kind == 'CompoundStmt':
                # A returned constructor with a body becomes several statements of the enclosing block.
                flat = []
                for c in rewritten:
                    flat.extend(c['inner'] if isinstance(c, dict) and c.get('_splice') else [c])
                rewritten = flat
            result['inner'] = rewritten
        return result


def split_functions(split_classes, source, friends_by_class, roots=()):
    """Return the scalar functions replacing the members, friends and class-typed free functions."""
    splitter = Splitter(split_classes)
    declarations = []
    for c in split_classes:
        for member in [*c.record.get('inner', []),*c.constructor_functions()]:
            if member.get('isImplicit'):
                continue
            body = [x for x in member.get('inner', []) if x.get('kind') == 'CompoundStmt']
            if member.get('kind') == 'CXXMethodDecl' and len(body) == 1:
                declarations.append((c, member, member.get('storageClass') != 'static'))
        for friend in friends_by_class.get(id(c), []):
            declaration = friend.get('inner', [None])[0]
            if declaration and declaration.get('kind') == 'FunctionDecl' and \
                    any(x.get('kind') == 'CompoundStmt' for x in declaration.get('inner', [])) and \
                    not any(x.get('kind') == 'TemplateArgument' for x in declaration.get('inner', [])):
                # (a friend that is a function template instance is lowered with the template's instances)
                declarations.append((c, dict(declaration, _source_friend=True), False))
    functions = []
    namespace_bases = set()
    for declaration in roots:
        classes = [splitter.class_of(p.get('type', {})) for p in declaration.get('inner', [])
                   if p.get('kind') == 'ParmVarDecl']
        first = next((c for c in classes if c is not None), None)
        if first is not None:
            namespace_bases.add(function_name(first.class_name, declaration['name']))
    used_bases = namespace_bases | {function_name(c.class_name, d['name']) for c, d, _ in declarations}
    for owner, declaration, has_this in declarations:
        if declaration.get('_source_friend') and function_name(owner.class_name, declaration['name']) in namespace_bases:
            name = declaration['name']+'_friend'
            while function_name(owner.class_name, name) in used_bases:
                name += '_'
            used_bases.add(function_name(owner.class_name, name))
            declaration = dict(declaration, name=name)
        functions.extend(split_one(splitter, owner, declaration, has_this, source))
    for declaration in roots:
        if declaration.get('kind') == 'FunctionDecl' and any(splitter.class_of(p.get('type', {})) or False
                                                              for p in declaration.get('inner', [])
                                                              if p.get('kind') == 'ParmVarDecl'):
            functions.extend(split_one(splitter, splitter.class_of(next(p['type'] for p in declaration['inner']
                if p.get('kind') == 'ParmVarDecl' and splitter.class_of(p.get('type', {})))), declaration, False, source))
    return functions


def split_one(splitter, owner, declaration, has_this, source):
    signature = declaration['type']['qualType']
    constant = signature.endswith(' const')
    params = {}
    new_parameters = []
    if has_this:
        mapping = {}
        for field in owner.fields:
            parameter = parameter_for(field, 'this', declaration['id'], constant, True, field.get('loc'))
            mapping[field['id']] = parameter
            new_parameters.append(parameter)
        params['this'] = mapping
    other = []
    for child in declaration.get('inner', []):
        if child.get('kind') != 'ParmVarDecl':
            other.append(child)
            continue
        cls = splitter.class_of(child.get('type', {}))
        if cls is None:
            new_parameters.append(child)
            continue
        text = child['type']['qualType']
        const = text.startswith('const ')
        reference = text.rstrip().endswith('&')
        mapping = {}
        for field in cls.fields:
            parameter = parameter_for(field, child['name'], child['id'], const, reference, child.get('loc'))
            mapping[field['id']] = parameter
            new_parameters.append(parameter)
        params[child['id']] = mapping
    bodies = [c for c in other if c.get('kind') == 'CompoundStmt']
    base_name = function_name(owner.class_name, declaration['name'])
    if declaration['name'] in ('operator-', 'operator+') and not any(
            c.get('kind') == 'ParmVarDecl' for c in declaration.get('inner', [])):
        base_name += '_unary'
    return_text = re.sub(r'\s*\(.*$', '', signature.removesuffix(' const')).strip()
    result_class = splitter.class_of({'qualType': return_text})
    results = []
    if result_class is None:
        body = splitter.rewrite(bodies[0], params)
        function = {k: v for k, v in declaration.items() if k not in ('inner', 'storageClass')}
        function['kind'] = 'FunctionDecl'
        function['name'] = base_name
        types = ', '.join(p['type']['qualType'] for p in new_parameters)
        function['type'] = {'qualType': f"{return_text} ({types})"}
        function['inner'] = new_parameters + [body]
        function['loc'].setdefault('file', str(source))
        function['_inline'] = True
        return [function]
    # A function returning the class: every `return` returns a constructor call; the function becomes one function
    # per field whose returns give that field's initialiser (after the constructor body's statements).
    for field in result_class.fields:
        def hook(node, params_, field=field):
            if not node.get('inner'):
                raise ValueError('a function returning a split class must return a value')
            value = strip(node['inner'][0])
            if value.get('kind') not in ('CXXTemporaryObjectExpr', 'CXXConstructExpr'):
                raise ValueError('a function returning a split class must return a constructor call')
            signature_key = value.get('ctorType', {}).get('qualType', '').replace(' noexcept', '')
            if signature_key not in result_class.constructors:
                raise ValueError('unknown constructor: ' + signature_key)
            constructor_parameters, inits, ctor_body = result_class.constructors[signature_key]
            # Projection must not erase or duplicate argument/initializer effects,
            # even when a parameter or another field is unused by this result.
            # Such constructors need the object-state sequencing frontend.
            if any(constructor_body_may_change_state(a) for a in value.get('inner', [])):
                raise ValueError('split constructor arguments must be free of runtime effects')
            if any(constructor_body_may_change_state(a) for a in inits.values()):
                raise ValueError('split field initializers must be free of runtime effects')
            if any(constructor_body_may_change_state(statement) for statement in ctor_body):
                raise ValueError('split constructor body needs object-state sequencing')
            arguments = [splitter.rewrite(a_, params_) for a_ in value.get('inner', [])]
            if len(arguments) != len(constructor_parameters):
                raise ValueError('default arguments of constructors are not supported')
            def references(node):
                result = {node.get('referencedDecl', {}).get('id')} if node.get('kind') == 'DeclRefExpr' else set()
                for child in node.get('inner', []):
                    result.update(references(child))
                return result
            used = set()
            for expression in [*inits.values(), *ctor_body]:
                used.update(references(expression))
            prefix = []
            for index, (parameter, argument) in enumerate(zip(constructor_parameters, arguments)):
                if parameter['id'] not in used:
                    # C++ evaluates every argument even if the constructor does
                    # not use it. Preserve failures (e.g. division by zero) and
                    # conversions before returning any projected field.
                    temporary = dict(kind='VarDecl', id='split-unused:'+node.get('id','')+':'+parameter['id'],
                                     name='split_unused_'+str(index), type=parameter['type'], init='c', inner=[argument])
                    prefix.append(dict(kind='DeclStmt', inner=[temporary]))
            mapping = {p['id']: a_ for p, a_ in zip(constructor_parameters, arguments)}
            expression = substitute(inits[field['id']], mapping)
            returned = {'kind': 'ReturnStmt', 'range': node.get('range', {}), 'inner': [expression]}
            if not ctor_body and not prefix:
                return returned
            return {'kind': 'CompoundStmt', 'range': node.get('range', {}), '_splice': True,
                    'inner': prefix + [substitute(c, mapping) for c in ctor_body] + [returned]}
        splitter.return_hook = hook
        try:
            body = splitter.rewrite(bodies[0], params)
        finally:
            splitter.return_hook = None
        function = {k: v for k, v in declaration.items() if k not in ('inner', 'storageClass')}
        function['kind'] = 'FunctionDecl'
        function['name'] = f"{base_name}_{field['name']}"
        types = ', '.join(p['type']['qualType'] for p in new_parameters)
        function['type'] = {'qualType': f"{field_type(field)} ({types})"}
        function['inner'] = new_parameters + [body]
        function['loc'] = dict(declaration.get('loc', {}))
        function['loc'].setdefault('file', str(source))
        function['_inline'] = True
        results.append(function)
    return results
