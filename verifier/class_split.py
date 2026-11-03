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

from class_lowering import SCALAR_FIELD_TYPES, function_name

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
        self.pattern = re.compile(r'(?<![A-Za-z0-9_])(?:cp::)?' + re.escape(display) + r'(?![A-Za-z0-9_<])')
        self.constructors = {}  # ctorType qualType -> (parameters, {field id: init expression})
        for member in record.get('inner', []):
            if member.get('kind') == 'CXXConstructorDecl' and not member.get('isImplicit'):
                body = [c for c in member.get('inner', []) if c.get('kind') == 'CompoundStmt']
                if len(body) != 1:
                    raise ValueError('a constructor needs a body')
                parameters = [c for c in member.get('inner', []) if c.get('kind') == 'ParmVarDecl']
                inits = {}
                for initializer in member.get('inner', []):
                    if initializer.get('kind') == 'CXXCtorInitializer':
                        inits[initializer['anyInit']['id']] = initializer['inner'][0]
                if set(inits) != {f['id'] for f in self.fields}:
                    raise ValueError('a constructor must initialise every field')
                signature = member['type']['qualType'].replace(' noexcept', '')
                # The statements of the constructor body run before the object exists, so they may only use the
                # constructor's parameters (checked when the body is substituted into a returning function).
                self.constructors[signature] = (parameters, inits, body[0].get('inner', []))

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
        for member in c.record.get('inner', []):
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
                declarations.append((c, declaration, False))
    functions = []
    for owner, declaration, has_this in declarations:
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
            arguments = [splitter.rewrite(a_, params_) for a_ in value.get('inner', [])]
            if len(arguments) != len(constructor_parameters):
                raise ValueError('default arguments of constructors are not supported')
            mapping = {p['id']: a_ for p, a_ in zip(constructor_parameters, arguments)}
            expression = substitute(inits[field['id']], mapping)
            returned = {'kind': 'ReturnStmt', 'range': node.get('range', {}), 'inner': [expression]}
            if not ctor_body:
                return returned
            return {'kind': 'CompoundStmt', 'range': node.get('range', {}), '_splice': True,
                    'inner': [substitute(c, mapping) for c in ctor_body] + [returned]}
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
