"""Read direct-input function roots from one Clang JSON translation unit.

Whole standard-library subtrees remain JSON text, never Python AST dictionaries.
Declaration IDs come from one compiler process and are preserved verbatim.
"""

import json
from pathlib import Path
import re

from class_lowering import ErasedClass, SCALAR_FIELD_TYPES, build_functions, erase_functions
from class_split import SplitClass, is_split_candidate, split_functions

# Consume text and complete strings in the regex engine: Python visits only
# braces and unfinished strings. Possessive string runs avoid backtracking
# through long escaped strings. The outer skip repetition stays greedy:
# CPython 3.11 can lose the following unfinished-string capture when that
# repetition is possessive. At chunk boundaries retain the closing-quote
# and trailing-backslash state, while leaving the original root bytes intact.
STRING_END = rb'[^"\\]*+(?:\\[\s\S][^"\\]*+)*+(?:(?P<closed>")|(?P<escape>\\)?\Z)'
SKIP = rb'(?:[^"{}]++|"[^"\\]*+(?:\\[\s\S][^"\\]*+)*+")*'
TOKENS = re.compile(SKIP + rb'(?:(?P<brace>[{}])|(?P<string>"' + STRING_END + rb')|\Z)')
STRING_CONTINUATION = re.compile(STRING_END)
INNER = re.compile(rb'"inner"\s*:\s*\[')


def root_objects(stream, chunk_size=1 << 20):
    prefix = b''
    while not (match := INNER.search(prefix)):
        chunk = stream.read(chunk_size)
        if not chunk:
            raise ValueError('Clang translation unit has no inner array')
        prefix += chunk
    header = json.loads(prefix[:match.start()] + b'"inner": []}')
    if header.get('kind') != 'TranslationUnitDecl':
        raise ValueError('a complete Clang translation unit is required')
    buffer = prefix[match.end():]
    if not buffer:
        buffer = stream.read(chunk_size)
    parts = []
    outside = b''
    depth = 0
    quoted = escaped = False
    while buffer:
        start = 0 if depth else None
        previous = 0
        if quoted:
            # An unpaired backslash in the previous chunk escapes this byte,
            # even when it is a quote or another backslash.
            token = STRING_CONTINUATION.match(buffer, int(escaped))
            quoted = token['closed'] is None
            escaped = token['escape'] is not None
            previous = token.end()
        for token in TOKENS.finditer(buffer, previous):
            char = token['brace']
            if char is None and token['string'] is None:
                # Keep skipped trailing text for the root delimiter check.
                break
            pos = token.end() - 1
            if token['string'] is not None:
                quoted = token['closed'] is None
                escaped = token['escape'] is not None
            elif char == b'{':
                if depth == 0:
                    # Whitespace and commas are the only delimiters of roots.
                    if (outside+buffer[previous:pos]).strip(b' \r\n\t,'):
                        raise ValueError('unexpected translation-unit delimiter')
                    outside = b''
                    start = pos
                depth += 1
            elif char == b'}':
                depth -= 1
                if depth == 0:
                    parts.append(buffer[start:pos+1])
                    yield b''.join(parts)
                    parts = []
                    start = None
                elif depth < 0:
                    # The closing inner array and root object must terminate
                    # the stream; no second environment may be concatenated.
                    tail = outside+buffer[previous:]
                    tail += stream.read()
                    if tail.strip() != b']\n}' and not re.fullmatch(rb'\s*]\s*}\s*',tail):
                        raise ValueError('invalid translation-unit trailer')
                    return
            previous = token.end()
        if start is not None:
            parts.append(buffer[start:])
        else:
            outside += buffer[previous:]
        buffer = stream.read(chunk_size)
    raise ValueError('truncated Clang translation unit')


def node_header(raw):
    match = INNER.search(raw)
    return json.loads(raw if match is None else raw[:match.start()] + b'"inner": []}')


def direct_location(node, source):
    loc = node.get('loc', {})
    # An included declaration always records includedFrom in Clang's JSON.
    # Macro-defined declarations have multiple source locations; refuse them.
    return ('offset' in loc and 'includedFrom' not in loc
            and 'spellingLoc' not in loc and 'expansionLoc' not in loc
            and ('file' not in loc or Path(loc['file']).resolve() == source))


def forced_class_records(stream, source, qualified):
    """Records owned by the sole forced include of a controlled copy witness.

    Clang marks these declarations as included from <built-in>. Declarations
    from headers included by the source have a different immediate includer.
    The ordinary direct-input policy remains unchanged.
    """
    source = Path(source).resolve(strict=True)
    selected = []

    def collect(node, scopes):
        kind = node.get('kind')
        if kind == 'NamespaceDecl':
            name = node.get('name')
            if not name:
                return
            for child in node.get('inner', []):
                collect(child, scopes + [name])
        elif kind == 'CXXRecordDecl' and node.get('completeDefinition'):
            name = node.get('name')
            if '::'.join(scopes + [name or '']) == qualified:
                loc = node.get('loc', {})
                if (loc.get('includedFrom', {}).get('file') != '<built-in>' or
                        'offset' not in loc or 'spellingLoc' in loc or 'expansionLoc' in loc or
                        ('file' in loc and Path(loc['file']).resolve() != source)):
                    raise ValueError('copy class must be defined in the original forced source')
                selected.append(node)
            for child in node.get('inner', []):
                collect(child, scopes + [name or ''])

    for raw in root_objects(stream):
        header = node_header(raw)
        if (header.get('kind') in ('NamespaceDecl', 'CXXRecordDecl') and
                header.get('name') == qualified.split('::')[0]):
            collect(json.loads(raw), [])
    return selected


def forced_source_functions(stream, source):
    """Unexpanded free function definitions from the original forced source.

    Keep declaration identities shared with forced_class_records. Included
    headers and the synthetic witness are excluded using the immediate
    includer, rather than a function's spelling or namespace.
    """
    source = Path(source).resolve(strict=True)
    selected = []

    def collect(node, scopes):
        kind = node.get('kind')
        if kind == 'NamespaceDecl':
            name = node.get('name')
            if name:
                for child in node.get('inner', []):
                    collect(child, scopes + [name])
        elif kind == 'FunctionDecl' and any(c.get('kind') == 'CompoundStmt'
                                          for c in node.get('inner', [])):
            loc = node.get('loc', {})
            if (loc.get('includedFrom', {}).get('file') == '<built-in>' and
                    'offset' in loc and 'spellingLoc' not in loc and 'expansionLoc' not in loc and
                    ('file' not in loc or Path(loc['file']).resolve() == source)):
                function = dict(node)
                function['_qualified_name'] = '::'.join([*scopes, node['name']])
                function['loc'] = dict(loc, file=str(source))
                selected.append(function)

    for raw in root_objects(stream):
        if node_header(raw).get('kind') in ('NamespaceDecl', 'FunctionDecl'):
            collect(json.loads(raw), [])
    return selected


def _field_reference_parameters(record):
    fields = [c for c in record.get('inner', []) if c.get('kind') == 'FieldDecl']
    return fields


def _strip_noop(node):
    """Look through the qualification conversions (`T *` to `const T *`) around `this`."""
    while node.get('kind') == 'ImplicitCastExpr' and node.get('castKind') == 'NoOp' and len(node.get('inner', [])) == 1:
        node = node['inner'][0]
    return node


def _replace_this_members(node, fields, parameters):
    """Rewrite `this->field` (explicit or implicit) into the reference parameter of that field."""
    if isinstance(node, list):
        return [_replace_this_members(child, fields, parameters) for child in node]
    if not isinstance(node, dict):
        return node
    kind = node.get('kind')
    if kind == 'CXXThisExpr':
        raise ValueError('use of this other than a direct field access is unsupported')
    if kind == 'CXXMemberCallExpr' and node.get('inner'):
        head, rest = node['inner'][0], node['inner'][1:]
        if (head.get('kind') == 'MemberExpr' and len(head.get('inner', [])) == 1
                and _strip_noop(head['inner'][0]).get('kind') == 'CXXThisExpr'
                and head.get('referencedMemberDecl') not in parameters):
            # A method of this class: the callee member expression keeps its implicit `this`; the inliner resolves it.
            return dict(node, inner=[dict(head, inner=[_strip_noop(head['inner'][0])])]
                        + _replace_this_members(rest, fields, parameters))
    if kind == 'MemberExpr':
        children = node.get('inner', [])
        if len(children) == 1 and children[0].get('kind') == 'CXXThisExpr':
            identifier = node.get('referencedMemberDecl')
            if identifier not in parameters:
                raise ValueError('member access must name a scalar field of the class')
            parameter = parameters[identifier]
            return {'kind': 'DeclRefExpr', 'type': node['type'], 'valueCategory': 'lvalue',
                    'referencedDecl': {'id': parameter['id'], 'kind': 'ParmVarDecl', 'name': parameter['name'],
                                       'type': parameter['type']}}
    return {key: (_replace_this_members(value, fields, parameters) if key == 'inner' else value)
            for key, value in node.items()}


ASSIGNMENT_OPERATORS = {'=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>='}


def _read_only_fields(record, methods):
    """Ids of the scalar fields that no method of the class modifies (directly or through another method).

    A field that is only ever read can be passed by value: the lowered function then sees the same value
    through the whole call, which is what the reference would give it.
    """
    field_ids = {c['id'] for c in record.get('inner', []) if c.get('kind') == 'FieldDecl'}
    # A mutable argument can alias a field even if no method assigns that
    # field directly. Capturing its old value would then hide the write.
    for method in methods:
        for parameter in method.get('inner', []):
            if parameter.get('kind') != 'ParmVarDecl':
                continue
            ty = parameter.get('type', {})
            spelling = ty.get('desugaredQualType', ty.get('qualType', ''))
            if spelling.endswith('&') and spelling[:-1].strip() in SCALAR_FIELD_TYPES:
                return set()
    method_ids = {m['id'] for m in methods}
    written = {m['id']: set() for m in methods}
    calls = {m['id']: set() for m in methods}

    def scan(node, method, parent, grandparent):
        if isinstance(node, list):
            for child in node:
                scan(child, method, parent, grandparent)
            return
        if not isinstance(node, dict):
            return
        kind = node.get('kind')
        if kind == 'MemberExpr':
            target = node.get('referencedMemberDecl')
            if target in field_ids:
                plain_read = (parent is not None and parent.get('kind') == 'ImplicitCastExpr'
                              and parent.get('castKind') == 'LValueToRValue')
                if not plain_read:
                    written[method['id']].add(target)
            elif target in method_ids:
                calls[method['id']].add(target)
        for child in node.get('inner', []):
            scan(child, method, node, parent)

    for method in methods:
        scan([c for c in method.get('inner', []) if c.get('kind') == 'CompoundStmt'], method, None, None)
    changed = True
    while changed:
        changed = False
        for method in methods:
            for callee in calls[method['id']]:
                extra = written[callee] - written[method['id']]
                if extra:
                    written[method['id']] |= extra
                    changed = True
    modified = set().union(*written.values()) if written else set()
    return field_ids - modified


def _method_names(name, methods):
    """Function names of the methods; overloads get the number of their parameters as a suffix."""
    counts = {}
    for method in methods:
        counts[method['name']] = counts.get(method['name'], 0) + 1
    names = {}
    used = set()
    for method in methods:
        base = f"{name}_{method['name']}"
        if counts[method['name']] > 1:
            base += '_' + str(len([c for c in method.get('inner', []) if c.get('kind') == 'ParmVarDecl']))
        candidate, index = base, 1
        while candidate in used:
            index += 1
            candidate = f"{base}_{index}"
        used.add(candidate)
        names[method['id']] = candidate
    return names


def _field_parameter(name, field, constant, by_value):
    spelling = field['type'].get('desugaredQualType', field['type']['qualType'])
    add_const = constant and not field.get('mutable') and not spelling.startswith('const ')
    reference = spelling if by_value else ('const ' if add_const else '') + spelling + ' &'
    parameter = {'kind': 'ParmVarDecl', 'id': f"field:{name}:{field['name']}", 'name': field['name'],
                 'isUsed': True, 'field': True, 'type': {'qualType': reference}}
    if 'loc' in field:
        parameter['loc'] = field['loc']
    return parameter


def _constructs(expression):
    while expression and expression.get('kind') in ('ExprWithCleanups', 'MaterializeTemporaryExpr', 'ImplicitCastExpr') \
            and len(expression.get('inner', [])) == 1:
        expression = expression['inner'][0]
    return bool(expression) and expression.get('kind') == 'CXXConstructExpr'


def class_method_functions(record, source):
    """Lower the inline methods and constructors of a class to ordinary functions.

    Every field becomes a leading parameter named after the field, and every `this->field` access becomes a
    use of that parameter. A scalar field that no method modifies is passed by value; every other field is a
    reference (respecting declared constness and mutable fields in const methods). Only direct field accesses are
    supported; the objects of the class are
    therefore fully described by their fields. A constructor becomes a function that initialises the reference
    parameters: scalar fields from the initialiser list, vector fields by statements of the body (a vector
    field must be default-initialised, e.g. `tree.assign(n + 1, 0)`).
    """
    name = _function_class_name(record)
    fields = _field_reference_parameters(record)
    scalar_types = {f['id'] for f in fields
                    if f['type'].get('desugaredQualType', f['type']['qualType']).removeprefix('const ') in SCALAR_FIELD_TYPES}
    candidates = []
    static_methods = []
    for method in record.get('inner', []):
        if method.get('kind') != 'CXXMethodDecl' or method.get('isImplicit'):
            continue
        bodies = [c for c in method.get('inner', []) if c.get('kind') == 'CompoundStmt']
        if len(bodies) != 1:
            continue
        if method.get('storageClass') == 'static':
            static_methods.append(method)
            continue
        candidates.append(method)
    by_value = _read_only_fields(record, candidates) & scalar_types
    names = _method_names(name, candidates)
    functions = []
    for method in candidates:
        signature = method['type']['qualType']
        constant = signature.endswith(' const')
        parameters = {}
        synthetic = []
        for field in fields:
            parameter = _field_parameter(name, field, constant, field['id'] in by_value)
            parameters[field['id']] = parameter
            synthetic.append(parameter)
        function = {key: value for key, value in method.items() if key != 'inner'}
        function['kind'] = 'FunctionDecl'
        function['name'] = names[method['id']]
        function['type'] = {'qualType': signature[:-len(' const')] if constant else signature}
        function['inner'] = synthetic + [
            _replace_this_members(c, fields, parameters) if c.get('kind') == 'CompoundStmt' else c
            for c in method.get('inner', [])]
        function['loc'].setdefault('file', str(source))
        function['_fields'] = synthetic
        functions.append(function)
    # A static member function has no receiver and no fields: it is an ordinary function of its arguments that is
    # inlined into its callers (for instance the `e()` and `apply(a, b)` of a monoid used by a segment tree).
    static_names = _method_names(name + '_static', static_methods)
    for method in static_methods:
        function = {key: value for key, value in method.items() if key != 'storageClass'}
        function['kind'] = 'FunctionDecl'
        function['name'] = static_names[method['id']]
        function['loc'].setdefault('file', str(source))
        function['_inline'] = True
        functions.append(function)
    constructors = [c for c in record.get('inner', []) if c.get('kind') == 'CXXConstructorDecl' and not c.get('isImplicit')
                    and any(x.get('kind') == 'CompoundStmt' for x in c.get('inner', []))]
    for number, constructor in enumerate(constructors):
        body = [c for c in constructor.get('inner', []) if c.get('kind') == 'CompoundStmt'][0]
        if not body.get('inner'):
            # Only the mem-initialisers run. A scalar field is a plain value of the arguments and a vector field is
            # built by the standard constructor, so there is nothing for a function to model.
            for initializer in constructor.get('inner', []):
                if initializer.get('kind') == 'CXXCtorInitializer' and initializer.get('anyInit', {}).get('id') in {
                        f['id'] for f in fields} - scalar_types and not _constructs(initializer.get('inner', [None])[0]):
                    raise ValueError('a vector field must be initialised by a standard vector constructor')
            continue
        initializers = {i.get('anyInit', {}).get('id'): i for i in constructor.get('inner', [])
                        if i.get('kind') == 'CXXCtorInitializer'}
        parameters = {}
        synthetic = []
        prologue = []
        # The object does not exist before its constructor runs: a scalar field is a local that holds the value of its
        # mem-initialiser (in declaration order), a vector field is a reference parameter holding the vector that the
        # standard constructor of its mem-initialiser built (an audited standard library contract).
        for field in fields:
            initializer = initializers.get(field['id'])
            if initializer is None or not initializer.get('inner'):
                raise ValueError('every field of a class with a constructor body needs a mem-initialiser')
            if field['id'] in scalar_types:
                spelling = field['type'].get('desugaredQualType', field['type']['qualType'])
                local = {'kind': 'VarDecl', 'id': f"ctorfield:{name}:{number}:{field['name']}", 'name': field['name'],
                         'type': {'qualType': spelling}, 'init': 'c', 'isUsed': True, 'inner': [initializer['inner'][0]],
                         'loc': field.get('loc', {}), 'range': initializer.get('range', {})}
                prologue.append({'kind': 'DeclStmt', 'range': initializer.get('range', {}), 'inner': [local]})
                parameters[field['id']] = {'kind': 'VarDecl', 'id': local['id'], 'name': field['name'], 'type': local['type']}
            else:
                if not _constructs(initializer['inner'][0]):
                    raise ValueError('a vector field must be initialised by a standard vector constructor')
                parameter = _field_parameter(name, field, False, False)
                parameters[field['id']] = parameter
                synthetic.append(parameter)
        new_body = dict(body, inner=prologue + list(body.get('inner', [])))
        function = {key: value for key, value in constructor.items() if key != 'inner'}
        function['kind'] = 'FunctionDecl'
        function['name'] = f"{name}_new{number}"
        signature = constructor['type']['qualType']
        function['type'] = {'qualType': 'void' + signature[len('void'):]} if signature.startswith('void') else {'qualType': signature}
        function['inner'] = synthetic + [c for c in constructor.get('inner', []) if c.get('kind') == 'ParmVarDecl'] \
            + [_replace_this_members(new_body, fields, parameters)]
        function['loc'].setdefault('file', str(source))
        function['_fields'] = synthetic
        # every field in declaration order (the local that holds a scalar field, the reference parameter of a vector
        # field): the arguments of a call of a method of the class from inside the constructor body
        function['_all_fields'] = [parameters[f['id']] for f in fields]
        functions.append(function)
    return functions


def class_construction_stages(record, source):
    """Constructor initializers and body, before object export/scope retirement.

    All fields are locals, in declaration order. The returned unit NProgram is
    a stage to run with runFuel, not a complete constructor callFuel contract.
    """
    name = _function_class_name(record)
    fields = _field_reference_parameters(record)
    if not fields or record.get('bases') or any(c.get('kind') == 'CXXBaseSpecifier' for c in record.get('inner', [])):
        raise ValueError('construction stages require fields and no base classes')
    functions = []
    constructors = [c for c in record.get('inner', []) if c.get('kind') == 'CXXConstructorDecl'
                    and not c.get('isImplicit')]
    for number, ctor in enumerate(constructors):
        if any(c.get('kind') not in ('ParmVarDecl', 'CXXCtorInitializer', 'CompoundStmt')
               for c in ctor.get('inner', [])):
            raise ValueError('constructor attributes and extra declarations are unsupported')
        bodies = [c for c in ctor.get('inner', []) if c.get('kind') == 'CompoundStmt']
        if len(bodies) != 1:
            raise ValueError('construction stages require a defined constructor body')
        body = bodies[0]
        inits = {i.get('anyInit', {}).get('id'): i for i in ctor.get('inner', [])
                 if i.get('kind') == 'CXXCtorInitializer'}
        if set(inits) != {f['id'] for f in fields}:
            raise ValueError('construction stages require every field initializer and no delegation')
        parameters, prologue, layout = {}, [], []
        for field in fields:
            init = inits[field['id']]
            if len(init.get('inner', [])) != 1:
                raise ValueError('a field requires exactly one initializer expression')
            local = {'kind': 'VarDecl', 'id': f"construct:{name}:{number}:{field['id']}",
                     'name': field['name'], 'type': field['type'], 'init': 'c',
                     'loc': field.get('loc', {}), 'range': body.get('range', {}),
                     'inner': [_replace_this_members(init['inner'][0], fields, parameters)]}
            spelling = field['type'].get('desugaredQualType', field['type']['qualType'])
            base_spelling = spelling.removeprefix('const ')
            if base_spelling not in SCALAR_FIELD_TYPES:
                if not base_spelling.startswith('std::vector<') or not _constructs(local['inner'][0]):
                    raise ValueError('construction field must be scalar or standard vector')
                local['_construction_field'] = True
            prologue.append({'kind': 'DeclStmt', 'range': body.get('range', {}), 'inner': [local]})
            parameters[field['id']] = local
            layout.append({'name': field['name'], 'id': local['id'],
                           'field_id': field['id'], 'declared_type': spelling,
                           'mutable': bool(field.get('mutable'))})
        rewritten = _replace_this_members(dict(body, inner=prologue+body.get('inner', [])), fields, parameters)
        function = {k: v for k, v in ctor.items() if k not in ('inner', 'storageClass')}
        function.update(kind='FunctionDecl', name=f'{name}_construct{number}',
                        type={'qualType': ctor['type']['qualType']},
                        inner=[c for c in ctor.get('inner', []) if c.get('kind') == 'ParmVarDecl']+[rewritten],
                        _construction_fields=layout,
                        _all_fields=[parameters[f['id']] for f in fields])
        function['loc'].setdefault('file', str(source))
        functions.append(function)
    return functions


def _display_name(record):
    """The spelling Clang uses for the class type, e.g. `ModInt<998244353U>` (found in member types)."""
    name = record.get('name')
    pattern = re.compile(r'\b' + re.escape(name) + r'(?:<[^<>]*>)?')
    def strings(node):
        if isinstance(node, dict):
            for key, value in node.items():
                if key in ('qualType', 'desugaredQualType'):
                    yield value
                else:
                    yield from strings(value)
        elif isinstance(node, list):
            for value in node:
                yield from strings(value)
    if record.get('kind') == 'ClassTemplateSpecializationDecl':
        for text in strings(record.get('inner', [])):
            match = re.search(r'\b' + re.escape(name) + r'<[^<>]*>', text)
            if match:
                return match.group(0)
        raise ValueError('cannot determine the spelling of the class specialization')
    return name


def _function_class_name(record):
    name = record['name']
    if record.get('kind') == 'ClassTemplateSpecializationDecl':
        arguments = [str(c.get('value', c.get('type', {}).get('qualType', ''))) for c in record.get('inner', [])
                     if c.get('kind') == 'TemplateArgument']
        name = re.sub(r'[^A-Za-z0-9_]', '_', name + '_' + '_'.join(arguments))
    return name


def _template_instances(template):
    """The instantiated definitions of a function template, named after the first parameter type (so that overloaded
    templates keep distinct, stable names) or, without parameters, the template arguments."""
    instances = []
    for child in template.get('inner', []):
        if child.get('kind') != 'FunctionDecl':
            continue
        arguments = [c for c in child.get('inner', []) if c.get('kind') == 'TemplateArgument']
        if not arguments or not any(c.get('kind') == 'CompoundStmt' for c in child.get('inner', [])):
            continue
        spellings = [str(a.get('type', {}).get('qualType', a.get('value', ''))) for a in arguments]
        parameters = [c for c in child.get('inner', []) if c.get('kind') == 'ParmVarDecl']
        first = re.sub(r'\bconst\b|&|\*', '', parameters[0]['type']['qualType']) if parameters else ''
        suffix = re.sub(r'[^A-Za-z0-9_]+', '_', first if first else '_'.join(spellings)).strip('_')
        instance = dict(child)
        template_name = template['name']
        if template_name.startswith('operator'):
            # Operator templates (a free `operator+` over a class template) are named like the member operators.
            from class_lowering import OPERATOR_NAMES
            symbol = template_name[len('operator'):].strip()
            if symbol not in OPERATOR_NAMES:
                raise ValueError('unsupported operator template: ' + template_name)
            template_name = 'operator_' + OPERATOR_NAMES[symbol]
        instance['name'] = f"{template_name}_{suffix}"
        instance['_template_name'] = template_name
        instance['inner'] = [c for c in child.get('inner', []) if c.get('kind') != 'TemplateArgument']
        instances.append(instance)
    return instances


def direct_functions(stream, source, *, construction_stages=False):
    source = Path(source).resolve(strict=True)
    roots = []
    erased_classes = []
    split_classes = []
    library = []
    def collect_library(node):
        # Included definitions of the library namespace: only callable (inlined) by the functions of this file.
        if node.get('kind') == 'FunctionDecl':
            if any(c.get('kind') == 'CompoundStmt' for c in node.get('inner', [])):
                library.append(node)
        elif node.get('kind') == 'NamespaceDecl':
            for child in node.get('inner', []):
                collect_library(child)
    def collect(node):
        if not direct_location(node, source):
            return
        kind = node.get('kind')
        if kind == 'FunctionTemplateDecl':
            # The explicit instantiations of a function template are ordinary functions of concrete types; the
            # template itself (and a declaration without instances) is not lowered.
            for instance in _template_instances(node):
                instance['loc'].setdefault('file',str(source))
                roots.append(instance)
        elif kind == 'FunctionDecl':
            # Clang omits repeated file names. The main-file location above
            # establishes the origin needed by the scalar std::swap verifier.
            node['loc'].setdefault('file',str(source))
            roots.append(node)
        elif (kind in ('CXXRecordDecl', 'ClassTemplateSpecializationDecl') and node.get('completeDefinition')
              and node.get('tagUsed') in ('class', 'struct')):
            if construction_stages:
                roots.extend(class_construction_stages(node, source))
                # Calls on this use the field locals just allocated by the
                # construction stage. Keep helpers out of the output roots;
                # the common inliner expands only the methods actually called.
                for function in class_method_functions(node, source):
                    if '_all_fields' not in function:
                        function['_construction_helper'] = True
                        library.append(function)
                return
            fields = [c for c in node.get('inner', []) if c.get('kind') == 'FieldDecl']
            if len(fields) == 1 and fields[0]['type'].get('desugaredQualType', fields[0]['type']['qualType']) in SCALAR_FIELD_TYPES:
                erased = ErasedClass(node, _function_class_name(node), _display_name(node))
                friends = [c for c in node.get('inner', []) if c.get('kind') == 'FriendDecl']
                erased_classes.append((erased, friends))
            elif is_split_candidate(node) and any(
                    (c.get('kind') == 'CXXConstructorDecl' and not c.get('isImplicit')) or c.get('kind') == 'FriendDecl'
                    for c in node.get('inner', [])):
                split = SplitClass(node, _function_class_name(node), _display_name(node))
                friends = [c for c in node.get('inner', []) if c.get('kind') == 'FriendDecl']
                split_classes.append((split, friends))
            else:
                roots.extend(class_method_functions(node, source))
        elif kind == 'NamespaceDecl':
            for child in node.get('inner', []):
                collect(child)
    for raw in root_objects(stream):
        header = node_header(raw)
        if header.get('kind') == 'NamespaceDecl' and header.get('name') == 'cp' and not direct_location(header, source):
            collect_library(json.loads(raw))
            continue
        if header.get('kind') in ('FunctionDecl','FunctionTemplateDecl','NamespaceDecl','CXXRecordDecl',
                                  'ClassTemplateSpecializationDecl') and direct_location(header,source):
            collect(json.loads(raw))
    def compile_only_type(node):
        if not isinstance(node, dict):
            return True
        kind = node.get('kind', '')
        if kind in ('VariableArrayType', 'DependentSizedArrayType') or 'typeof' in kind.lower():
            return False
        info = node.get('type', {})
        if any('[' in text or 'typeof' in text.lower() for text in info.values() if isinstance(text, str)):
            return False
        return all(compile_only_type(child) for child in node.get('inner', []))

    def compile_only_declaration(node):
        kind = node.get('kind')
        children = node.get('inner', [])
        if kind == 'StaticAssertDecl':
            return True
        if kind in ('TypeAliasDecl', 'TypedefDecl'):
            return compile_only_type(node) and not any(c.get('kind', '').endswith('Attr') for c in children)
        return (kind == 'FunctionDecl' and compile_only_type(node) and node.get('storageClass') in (None, 'extern')
                and all(c.get('kind') == 'ParmVarDecl' for c in children))

    def empty_constexpr_if(node):
        if (node.get('kind') != 'IfStmt' or not node.get('isConstexpr')
                or node.get('hasInit') or node.get('hasVar')):
            return False
        children = node.get('inner', [])
        expected = 3 if node.get('hasElse') else 2
        return (len(children) == expected and children[0].get('kind') not in ('VarDecl', 'DeclStmt')
                and all(c.get('kind') == 'CompoundStmt' and not c.get('inner') for c in children[1:]))

    def strip_compile_only(node):
        if not isinstance(node, dict):
            return
        children = node.get('inner', [])
        for child in children:
            strip_compile_only(child)
        if node.get('kind') == 'CompoundStmt':
            retained = []
            for child in children:
                if child.get('kind') == 'StaticAssertDecl' or empty_constexpr_if(child):
                    continue
                if child.get('kind') == 'DeclStmt' and child.get('inner') and all(
                        compile_only_declaration(c) for c in child['inner']):
                    continue
                retained.append(child)
            node['inner'] = retained

    # Clang has checked compile-time declarations and resolved all references.
    # Empty constexpr branches have no init/condition variable or runtime body.
    # Runtime variables, attributed functions and all executable statements stay.
    for node in [*roots, *(c.record for c, _ in [*erased_classes, *split_classes])]:
        strip_compile_only(node)
    from inline_ast import inline_functions
    if split_classes:
        from class_split import Splitter
        classes = [c for c, _ in split_classes]
        splitter = Splitter(classes)
        # Free functions (instances of function templates) that take a split class are rewritten like the friends.
        convertible = [r for r in roots if r.get('kind') == 'FunctionDecl' and any(
            splitter.class_of(p.get('type', {})) for p in r.get('inner', []) if p.get('kind') == 'ParmVarDecl')]
        roots = [r for r in roots if not any(r is c for c in convertible)]
        convertible = [dict(r, name=r.get('_template_name', r['name'])) for r in convertible]
        roots.extend(split_functions(classes, source, {id(c): f for c, f in split_classes}, tuple(convertible)))
    if erased_classes:
        built = []
        for erased, friends in erased_classes:
            built.extend(build_functions(erased, source, friends))
        classes = [erased for erased, _ in erased_classes]
        roots = erase_functions(classes, roots + built)
    return inline_functions(roots, library)
