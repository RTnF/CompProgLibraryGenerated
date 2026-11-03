"""Nested vector bodies lowered from audited Clang AST to the nested interpreter.

Containers are local vectors or `container[index]` rows of a vector of vectors.
Supported statements: count-only construction of a vector of integer vectors,
reserve / emplace_back / push_back / subscript write / begin-end assign on any
container of integers, empty-row emplace_back on vectors of integer vectors,
vector return of a local by NRVO or move, and scalar
calls. Scalar callees come from the same AST dump and are lowered by the
shared scalar generator. Everything else fails closed.
"""
import re
import json
import copy
from pathlib import Path
from scalar_ir import expression, scalar_type, lean_type, lean_expression, TYPES, apply_conversion_policy
from state_ir import ValueCalls, lean_statement
from vector_bindings import bindings_from_audit, verify_type_probes
from vector_ir import Body, unwrap_lvalue
from vector_stl import audit_vector_operations

UINT64 = dict(width=64, signed=False, boolean=False)
BOOL = dict(width=1, signed=False, boolean=True)


def terminal_return_kinds(statements):
    """Return kinds guaranteed by a terminal statement on every path."""
    if not statements:
        return set()
    last = statements[-1]
    if last['kind'] in ('return', 'return_vector', 'return_unit'):
        return {last['kind']}
    if last['kind'] == 'scope':
        return terminal_return_kinds(last['body'])
    if last['kind'] == 'branch':
        yes = terminal_return_kinds(last['yes'])
        no = terminal_return_kinds(last['no'])
        return yes | no if yes and no else set()
    return set()


# LP64 libstdc++ fixed-width aliases; the type-identity probes still compare the written spelling.
ALIASES = {'std::uint64_t': 'unsigned long', 'uint64_t': 'unsigned long', 'std::size_t': 'unsigned long',
           'std::int64_t': 'long', 'int64_t': 'long', 'std::int32_t': 'int', 'int32_t': 'int',
           'std::uint32_t': 'unsigned int', 'uint32_t': 'unsigned int'}


def parse_element(spelling):
    spelling = ALIASES.get(spelling.strip(), spelling.strip())
    if spelling in TYPES and spelling != 'bool':
        width, signed, boolean = TYPES[spelling]
        return dict(width=width, signed=signed, boolean=boolean)
    match = re.fullmatch(r'std::vector<(.+)>', spelling)
    if match:
        return dict(vector=parse_element(match.group(1)))
    raise ValueError('unsupported vector element type: ' + spelling)


def lean_element(element):
    if 'vector' in element:
        return f"(.vector {lean_element(element['vector'])})"
    return f"(.integer {lean_type(element)})"


def global_spelling(spelling):
    return re.sub(r'(?<![:\w])std::', '::std::', spelling)


def render_container(container):
    if container['kind'] == 'local':
        return f"(.local {container['slot']})"
    return (f"(.row {render_container(container['parent'])} {lean_element(container['element'])} "
            f"{render_expression(container['index'])})")


def render_expression(expr):
    def extension(value):
        if value['kind'] == 'logical':
            return (f"(.logical {str(value['conjunction']).lower()} "
                    f"{render_expression(value['left'])} {render_expression(value['right'])})")
        if value['kind'] == 'vector_size':
            return f"(.size {lean_element(value['element'])} {render_container(value['container'])})"
        if value['kind'] == 'vector_read':
            return (f"(.read {lean_type(value['element'])} {render_container(value['container'])} "
                    f"{render_expression(value['index'])})")
        return None
    return lean_expression(expr, extension)


class NestedBody(Body):
    def __init__(self, node, schema, calls, source):
        super().__init__(node, schema)
        self.calls = calls
        self.source = Path(source).resolve(strict=True)
        self.text = self.source.read_bytes()
        self.allow_calls = False
        self.callees = {}
        self.prelude = []
        self.result = None
        bodies = [child for child in node.get('inner', []) if child['kind'] == 'CompoundStmt']
        self.body_end = bodies[0]['range']['end']['offset'] if len(bodies) == 1 else None

    # --- helpers -----------------------------------------------------
    def expr(self, node):
        return expression(node, self.slots, call_lowerer=self.call, node_lowerer=self.extension)

    def scalar_slots(self):
        result = {}
        for identity, slot in self.slots.items():
            if self.bindings[slot]['kind'] == 'scalar':
                result[identity] = sum(1 for b in self.bindings[:slot] if b['kind'] == 'scalar')
        return result

    def spelled(self, node):
        begin, end = node['range']['begin'], node['range']['end']
        begin, end = begin.get('spellingLoc', begin), end.get('spellingLoc', end)
        if 'offset' not in begin or 'offset' not in end:
            raise ValueError('source spelling required')
        return self.text[begin['offset']:end['offset'] + end['tokLen']].decode()

    def container(self, node):
        node = unwrap_lvalue(node)
        children = node.get('inner', [])
        if node['kind'] == 'DeclRefExpr':
            referenced = node.get('referencedDecl', {}).get('id')
            peek = self.bindings[self.slots[referenced]] if referenced in self.slots else None
            if peek is not None and peek['kind'] == 'nested':
                # A nested vector parameter: the container's element is a vector of the scalar type.
                slot, binding = self.binding(node, 'nested')
                return dict(kind='local', slot=slot, element=dict(vector=binding['element']),
                            writable=binding['writable'])
            slot, binding = self.binding(node, 'vector')
            return dict(kind='local', slot=slot, element=binding['element'], writable=binding['writable'])
        if (node['kind'] == 'CXXOperatorCallExpr' and node.get('verifiedVectorOperation') == 'operator[]'
                and len(children) == 3):
            parent = self.container(children[1])
            element = parse_element(node['verifiedVectorElement'])
            if parent['element'] != element or 'vector' not in element:
                raise ValueError('row access requires a vector of vectors')
            index = self.expr(children[2])
            if index['type'] != UINT64:
                raise ValueError('vector subscript requires size_type')
            return dict(kind='row', parent=parent, element=element['vector'], index=index,
                        writable=parent['writable'])
        raise ValueError('unsupported container expression')

    def operation(self, node):
        operation = node.get('verifiedVectorOperation')
        children = node.get('inner', [])
        if node['kind'] == 'CXXOperatorCallExpr' and operation == 'operator[]' and len(children) == 3:
            owner, args = children[1], children[2:]
        elif (node['kind'] == 'CXXMemberCallExpr' and children and
              children[0]['kind'] == 'MemberExpr' and len(children[0].get('inner', [])) == 1):
            owner, args = children[0]['inner'][0], children[1:]
        else:
            raise ValueError('unsupported vector operation AST shape')
        return operation, self.container(owner), args

    def scalar_container(self, container):
        if 'vector' in container['element']:
            raise ValueError('integer vector operation requires a container of integers')
        return container['element']

    # --- expressions -------------------------------------------------
    def extension(self, node, slots):
        if node.get('verifiedVectorOperation'):
            operation, container, args = self.operation(node)
            element = container['element']
            if operation == 'size' and not args:
                result = dict(kind='vector_size', type=UINT64, element=element, container=container)
            elif operation == 'operator[]' and len(args) == 1 and 'vector' not in element:
                result = dict(kind='vector_read', type=element, element=element,
                              container=self.container(node['inner'][1]), index=self.expr(args[0]))
                if result['index']['type'] != UINT64:
                    raise ValueError('vector subscript requires size_type')
            else:
                raise ValueError('effectful or row-valued vector operations cannot be scalar expressions')
            if scalar_type(node) != result['type']:
                raise ValueError('vector operation result type mismatch')
            return result
        return super().extension(node, slots)

    def call(self, node, slots, ty):
        children = node.get('inner', [])
        callee = children[0] if children else None
        while callee is not None and callee['kind'] == 'ImplicitCastExpr' and len(callee.get('inner', [])) == 1:
            callee = callee['inner'][0]
        if callee is None or callee['kind'] != 'DeclRefExpr':
            raise ValueError('only direct calls are supported')
        reference = callee['referencedDecl']
        if reference.get('kind') == 'CXXMethodDecl' and reference.get('name') in ('max', 'min', 'lowest') \
                and len(children) == 1:
            return self.numeric_maximum(node, callee, ty)
        if not self.allow_calls:
            raise ValueError('scalar calls are supported only in scalar declaration initializers')
        if reference.get('kind') != 'FunctionDecl':
            raise ValueError('only direct ordinary function calls are supported')
        function = self.calls.resolve(reference['id'])
        parameters = function['parameters']
        if ty != function['result_type'] or len(children) - 1 != len(parameters):
            raise ValueError('call return type or argument count mismatch')
        arguments = []
        scalar_map = self.scalar_slots()
        for child, parameter in zip(children[1:], parameters):
            if parameter['reference']:
                raise ValueError('reference parameters are unsupported in nested calls')
            value = expression(child, scalar_map)
            if value['type'] != parameter['type']:
                raise ValueError('call argument type mismatch')
            arguments.append(value)
        self.callees[function['name']] = function
        self.prelude.append(dict(kind='invoke', name=function['name'], result_type=ty, arguments=arguments))
        slot = len(self.bindings)
        self.bindings.append(dict(kind='scalar', element=ty, reference=False, writable=False))
        return dict(kind='variable', type=ty, slot=slot)

    def numeric_maximum(self, node, callee, ty):
        """`std::numeric_limits<T>::max()`, `min()` and `lowest()` of an integer type (the same value for min and lowest)."""
        spelling = node['type'].get('desugaredQualType', node['type']['qualType'])
        if spelling not in TYPES or TYPES[spelling] != (ty['width'], ty['signed'], ty['boolean']) or ty['boolean']:
            raise ValueError('numeric_limits<T> member requires an integer type')
        member = callee['referencedDecl']['name']
        if member == 'max':
            value = (1 << (ty['width'] - 1)) - 1 if ty['signed'] else (1 << ty['width']) - 1
            literal = f'{value}ull'
        else:
            value = -(1 << (ty['width'] - 1)) if ty['signed'] else 0
            literal = f'(-{(1 << (ty["width"] - 1)) - 1}ll - 1)' if ty['signed'] else '0ull'
        user = self.spelled(callee)
        probe = ('\n#if defined(std) || defined(numeric_limits) || defined(max) || defined(min) || defined(lowest)\n'
                 '#error numeric_limits identity names must not be macros\n#endif\n'
                 f'static_assert(&::std::numeric_limits<{spelling}>::{member} == &{user},'
                 '"called member must be the standard numeric_limits member");\n'
                 f'static_assert(::std::numeric_limits<{spelling}>::{member}() == {literal},'
                 f'"unexpected numeric_limits {member}");\n')
        if self.body_end is None:
            raise ValueError('function body required')
        self.probes.append((self.body_end, probe))
        return dict(kind='literal', type=ty, value=value)

    # --- statements --------------------------------------------------
    def vector_spelling(self, declaration):
        type_info = declaration.get('type', {})
        return type_info.get('desugaredQualType', type_info.get('qualType', ''))

    def declaration(self, declaration, node):
        spelling = self.vector_spelling(declaration)
        if re.fullmatch(r'(const )?std::vector<.+>', spelling):
            return self.vector_declaration(declaration, node, spelling)
        if (declaration['kind'] != 'VarDecl' or declaration.get('storageClass') or
                declaration.get('init') != 'c' or len(declaration.get('inner', [])) != 1):
            raise ValueError('only initialized scalar automatic locals are supported')
        ty = scalar_type(declaration)
        self.prelude = []
        self.allow_calls = True
        try:
            value = self.expr(declaration['inner'][0])
        finally:
            self.allow_calls = False
        prelude, self.prelude = self.prelude, []
        if ty != value['type']:
            raise ValueError('initializer type mismatch')
        writable = 'const' not in spelling.split()
        self.slots[declaration['id']] = len(self.bindings)
        self.bindings.append(dict(kind='scalar', element=ty, reference=False, writable=writable))
        return [*prelude, dict(kind='declare', type=ty, writable=writable, value=value)]

    def vector_declaration(self, declaration, node, spelling):
        if declaration.get('storageClass') or len(declaration.get('inner', [])) != 1:
            raise ValueError('automatic vector declaration required')
        constructor = declaration['inner'][0]
        if constructor['kind'] == 'ExprWithCleanups' and len(constructor.get('inner', [])) == 1:
            constructor = constructor['inner'][0]
        kind = constructor.get('verifiedVectorConstructor')
        flat = kind == 'default'
        fill = kind == 'fill'
        copy = kind == 'copy'
        if kind != 'count' and not flat and not fill and not copy:
            raise ValueError('audited standard fill, count, copy or default constructor required')
        arguments = [] if flat else constructor.get('inner', [])
        element_spelling = constructor['verifiedVectorElement']
        element = parse_element(element_spelling)
        if copy:
            if 'vector' in element or len(arguments) != 1:
                raise ValueError('copy construction requires one flat scalar vector source')
            copy_source = self.container(arguments[0])
            if copy_source['element'] != element:
                raise ValueError('copy source element mismatch')
        elif fill:
            if 'vector' in element:
                raise ValueError('fill construction supports vectors of integers')
            if len(arguments) != 3 or arguments[2]['kind'] != 'CXXDefaultArgExpr':
                raise ValueError('fill constructor requires the standard default allocator')
            allocator = arguments[2].get('type', {}).get('desugaredQualType', '')
            if allocator != f'const std::allocator<{element_spelling}>':
                raise ValueError('canonical default allocator required')
            count = self.expr(arguments[0])
            if count['type'] != UINT64:
                raise ValueError('constructor count type mismatch')
            fill_value = arguments[1]
            while fill_value['kind'] == 'MaterializeTemporaryExpr' and len(fill_value.get('inner', [])) == 1:
                fill_value = fill_value['inner'][0]
            fill_value = self.expr(fill_value)
            if fill_value['type'] != element:
                raise ValueError('fill value type mismatch')
        elif flat:
            if 'vector' in element:
                raise ValueError('default construction supports vectors of integers')
        else:
            if len(arguments) != 2 or arguments[1]['kind'] != 'CXXDefaultArgExpr':
                raise ValueError('count constructor requires the standard default allocator')
            allocator = arguments[1].get('type', {}).get('desugaredQualType', '')
            if allocator != f'const std::allocator<{element_spelling}>':
                raise ValueError('canonical default allocator required')
            if 'vector' not in element or 'vector' in element['vector']:
                raise ValueError('count construction supports vectors of integer vectors')
            count = self.expr(arguments[0])
            if count['type'] != UINT64:
                raise ValueError('constructor count type mismatch')
        name = declaration.get('name', '')
        field = declaration.get('_construction_field', False)
        location = node.get('range', {}).get('begin' if field else 'end', {})
        if (not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name) or
                'offset' not in location or 'spellingLoc' in location or 'expansionLoc' in location):
            raise ValueError('named nonmacro local vector declaration required')
        readonly = spelling.startswith('const ')
        canonical = ('const ' if readonly else '') + global_spelling(f'std::vector<{element_spelling}>')
        probe = ('\n#if defined(__is_same) || defined(decltype) || defined(static_assert) || defined(std) || '
                 'defined(vector) || defined(int) || defined(long) || defined(unsigned) || '
                 'defined(signed) || defined(const)\n'
                 '#error vector identity keywords must not be macros\n#endif\n'
                 f'static_assert(__is_same(decltype({"this->" if field else ""}{name}),{canonical}),"canonical local vector required");\n')
        self.probes.append((location['offset'] + location['tokLen'], probe))
        self.slots[declaration['id']] = len(self.bindings)
        self.bindings.append(dict(kind='vector', element=element, writable=not readonly))
        if copy:
            return [dict(kind='copy_vector', element=element, writable=not readonly, source=copy_source)]
        if fill:
            return [dict(kind='fill_vector', element=element, writable=not readonly, count=count, value=fill_value)]
        if flat:
            return [dict(kind='declare_vector', element=element, writable=not readonly)]
        return [dict(kind='construct_rows', element=element['vector'], writable=not readonly, count=count)]

    def statement(self, node):
        children = node.get('inner', [])
        kind = node['kind']
        if kind == 'DeclStmt':
            result = []
            for declaration in children:
                result.extend(self.declaration(declaration, node))
            return result
        if kind == 'ReturnStmt' and not children and 'unit' in (self.result or {}):
            return [dict(kind='return_unit')]
        if kind == 'ReturnStmt' and len(children) == 1 and 'vector' in (self.result or {}):
            return [self.vector_return(children[0])]
        if kind == 'BinaryOperator' and node.get('opcode') == '=' and len(children) == 2:
            left = unwrap_lvalue(children[0])
            if left.get('verifiedVectorOperation'):
                operation, container, args = self.operation(left)
                element = self.scalar_container(container)
                if operation != 'operator[]' or len(args) != 1 or not container['writable']:
                    raise ValueError('writable vector subscript required')
                value, index = self.expr(children[1]), self.expr(args[0])
                if value['type'] != element or index['type'] != UINT64:
                    raise ValueError('element assignment type mismatch')
                return [dict(kind='write', container=self.container(left['inner'][1]), element=element,
                             index=index, value=value)]
        if (kind == 'ExprWithCleanups' and len(children) == 1 and children[0]['kind'] == 'CXXMemberCallExpr'
                and children[0].get('verifiedVectorOperation') in ('push_back', 'emplace_back')):
            return self.vector_update(children[0])
        if (kind == 'ExprWithCleanups' and len(children) == 1 and children[0]['kind'] == 'CXXMemberCallExpr'
                and children[0].get('verifiedVectorOperation') == 'erase'):
            return self.dedup_vector(children[0])
        if node.get('verifiedVectorOperation') and kind == 'CXXMemberCallExpr':
            return self.vector_update(node)
        if kind == 'CallExpr' and node.get('verifiedStdSort'):
            return self.sort_vector(node)
        return super().statement(node)

    def vector_update(self, node):
        operation, container, args = self.operation(node)
        if not container['writable']:
            raise ValueError('vector update requires a writable container')
        if operation == 'emplace_back' and not args and 'vector' in container['element']:
            element = container['element']['vector']
            if 'vector' in element:
                raise ValueError('empty row append requires a vector of integers')
            return [dict(kind='append_row', container=container, element=element)]
        element = self.scalar_container(container)
        if operation == 'assign' and len(args) == 2:
            endpoints = []
            for argument in args:
                endpoint, source, values = self.operation(unwrap_lvalue(argument))
                if (endpoint not in ('begin', 'end') or values or source['kind'] != 'local'
                        or source['element'] != element):
                    raise ValueError('assign requires pure begin/end of local vectors of matching element type')
                endpoints.append((source['slot'], endpoint == 'end'))
            return [dict(kind='assign_range', container=container, element=element,
                         first=endpoints[0][0], last=endpoints[1][0],
                         first_end=endpoints[0][1], last_end=endpoints[1][1])]
        if len(args) != 1:
            raise ValueError('single-argument vector update required')
        value = self.expr(args[0])
        if operation == 'reserve' and value['type'] == UINT64:
            return [dict(kind='reserve', container=container, element=element, value=value)]
        if operation in ('push_back', 'emplace_back') and value['type'] == element:
            return [dict(kind='append_reserved', container=container, element=element, value=value)]
        raise ValueError('unsupported vector update or argument type')

    def sort_vector(self, node):
        # `std::sort(v.begin(), v.end())` with the default `<` on a writable local vector of integers.
        args = node['inner'][1:]
        if len(args) != 2:
            raise ValueError('only std::sort(first, last) without a comparator is supported')
        endpoints = []
        for argument, expected in zip(args, ('begin', 'end'), strict=True):
            operation, container, values = self.operation(unwrap_lvalue(argument))
            if operation != expected or values or container['kind'] != 'local':
                raise ValueError('std::sort requires v.begin() and v.end() of a local vector')
            endpoints.append(container)
        if endpoints[0] != endpoints[1]:
            raise ValueError('std::sort endpoints must belong to the same vector')
        container = endpoints[0]
        element = self.scalar_container(container)
        if not container['writable'] or element['width'] > 64:
            raise ValueError('std::sort requires a writable vector of integers')
        return [dict(kind='sort_vector', container=container, element=element)]

    @staticmethod
    def iterator_value(node):
        # Look through the implicit conversions to const_iterator and the temporary around an iterator value.
        while node['kind'] in ('ImplicitCastExpr', 'CXXConstructExpr', 'MaterializeTemporaryExpr', 'ExprWithCleanups'):
            if len(node.get('inner', [])) != 1:
                raise ValueError('unsupported iterator conversion')
            node = node['inner'][0]
        return node

    def endpoint(self, node, expected):
        operation, container, values = self.operation(unwrap_lvalue(self.iterator_value(node)))
        if operation != expected or values or container['kind'] != 'local':
            raise ValueError(f'expected {expected}() of a local vector')
        return container

    def dedup_vector(self, node):
        # `v.erase(std::unique(v.begin(), v.end()), v.end())` on a writable local vector of integers.
        operation, container, args = self.operation(node)
        if operation != 'erase' or len(args) != 2 or container['kind'] != 'local':
            raise ValueError('only v.erase(std::unique(v.begin(), v.end()), v.end()) is supported')
        unique = self.iterator_value(args[0])
        if unique['kind'] != 'CallExpr' or not unique.get('verifiedStdUnique') or len(unique['inner']) != 3:
            raise ValueError('erase requires std::unique(first, last) as its first argument')
        endpoints = [self.endpoint(unique['inner'][1], 'begin'), self.endpoint(unique['inner'][2], 'end'),
                     self.endpoint(args[1], 'end')]
        if any(e != container for e in endpoints):
            raise ValueError('erase and unique must use the same vector')
        element = self.scalar_container(container)
        if not container['writable'] or element['width'] > 64:
            raise ValueError('std::unique requires a writable vector of integers')
        return [dict(kind='dedup_vector', container=container, element=element)]

    def vector_return(self, node):
        if node['kind'] == 'ExprWithCleanups' and len(node.get('inner', [])) == 1:
            node = node['inner'][0]
        if node['kind'] != 'CXXConstructExpr' or node.get('verifiedVectorConstructor') != 'move':
            raise ValueError('returning a vector requires the audited standard move constructor')
        operand = unwrap_lvalue(node['inner'][0]) if len(node.get('inner', [])) == 1 else None
        if operand is None or operand['kind'] != 'DeclRefExpr':
            raise ValueError('only a local vector variable can be returned')
        slot, binding = self.binding(operand, 'vector')
        if not binding['writable'] or binding['element'] != self.result['vector']:
            raise ValueError('returned local vector type mismatch')
        if slot < len(self.parameters):
            raise ValueError('a parameter vector cannot be returned')
        return dict(kind='return_vector', slot=slot, element=binding['element'])

    def lower(self):
        if self.node.get('variadic') or self.node.get('storageClass'):
            raise ValueError('only ordinary nonvariadic function definitions are supported')
        bodies = [child for child in self.node.get('inner', []) if child['kind'] == 'CompoundStmt']
        if len(bodies) != 1 or any(child['kind'] not in ('ParmVarDecl', 'CompoundStmt', 'AlwaysInlineAttr')
                                   for child in self.node.get('inner', [])):
            raise ValueError('function body required; attributes and templates are unsupported')
        spelling = self.node['type']['qualType'].split(' (')[0]
        scalar = TYPES.get(spelling)
        if scalar is not None and spelling != 'bool':
            self.result = dict(width=scalar[0], signed=scalar[1], boolean=scalar[2])
        elif spelling == 'void':
            self.result = dict(unit=True)
        elif spelling.startswith('std::vector<'):
            self.result = parse_element(spelling) if False else dict(vector=parse_element(
                spelling[len('std::vector<'):-1]))
        else:
            self.result = scalar_type({'type': {'qualType': spelling}})
        statements = []
        for child in bodies[0].get('inner', []):
            if statements and statements[-1]['kind'] in ('return', 'return_vector', 'return_unit'):
                raise ValueError('statements after return are unsupported')
            statements.extend(self.statement(child))
        if 'unit' in self.result:
            if any(s['kind'] in ('return', 'return_vector') for s in statements):
                raise ValueError('a void function cannot return a value')
        else:
            returns = terminal_return_kinds(statements)
            if not returns:
                raise ValueError('a final return on every supported path is required')
            expected_return = 'return_vector' if 'vector' in self.result else 'return'
            if returns != {expected_return}:
                raise ValueError('return kind differs from the function result type')
        result = dict(name=self.node['name'], parameters=self.parameters, result=self.result, body=statements)
        if '_construction_fields' in self.node:
            result['construction_fields'] = [dict(name=f['name'], slot=self.slots[f['id']])
                                             for f in self.node['_construction_fields']]
            result['construction_layout'] = []
            for field in self.node['_construction_fields']:
                slot = self.slots[field['id']]
                binding = self.bindings[slot]
                if binding['kind'] not in ('vector', 'scalar'):
                    raise ValueError('unsupported constructor field binding')
                result['construction_layout'].append(dict(
                    name=field['name'], slot=slot, kind=binding['kind'],
                    element=copy.deepcopy(binding['element']), writable=binding['writable'],
                    mutable=field['mutable']))
        return result


def lower_source(source, include_dirs=(), signed_conversion="checked", *, construction_stages=False):
    callees = []
    audited = audit_vector_operations(source, include_dirs, callees, construction_stages=construction_stages)
    schemas = bindings_from_audit(source, audited, include_dirs)['functions']
    apply_conversion_policy([*audited['functions'], *callees], signed_conversion)
    calls = ValueCalls(callees)
    functions, probes, callees = [], [], {}
    for node, schema in zip(audited['functions'], schemas, strict=True):
        body = NestedBody(node, schema, calls, source)
        function = body.lower()
        if node.get('_template') is not None:
            function['template'] = node.get('_template')
        probes.extend(body.probes)
        callees.update(body.callees)
        function['parameters'] = schema['parameters']
        functions.append(function)
    verify_type_probes(source, probes, include_dirs)
    ir = dict(coverage='nested_control_flow',
              callees=[callees[name] for name in sorted(callees)], functions=functions)
    if signed_conversion != 'checked':
        ir['signed_conversion'] = signed_conversion
    return ir


def render_statement(statement):
    kind = statement['kind']
    if kind == 'check':
        return f"(.check {render_expression(statement['condition'])})"
    if kind == 'declare':
        return (f"(.declare {lean_type(statement['type'])} {str(statement['writable']).lower()} "
                f"{render_expression(statement['value'])})")
    if kind == 'construct_rows':
        return (f"(.constructRows {lean_type(statement['element'])} {str(statement['writable']).lower()} "
                f"{render_expression(statement['count'])})")
    if kind == 'fill_vector':
        return (f"(.fillVector {lean_type(statement['element'])} {str(statement['writable']).lower()} "
                f"{render_expression(statement['count'])} {render_expression(statement['value'])})")
    if kind == 'copy_vector':
        return (f"(.copyVector {render_container(statement['source'])} {lean_type(statement['element'])} "
                f"{str(statement['writable']).lower()})")
    if kind == 'declare_vector':
        return f"(.declareVector {lean_type(statement['element'])} {str(statement['writable']).lower()})"
    if kind == 'assign':
        return (f"(.assign {statement['slot']} {lean_type(statement['type'])} "
                f"{render_expression(statement['value'])})")
    if kind == 'write':
        return (f"(.write {render_container(statement['container'])} {lean_type(statement['element'])} "
                f"{render_expression(statement['index'])} {render_expression(statement['value'])})")
    if kind == 'reserve':
        return (f"(.reserve {render_container(statement['container'])} {lean_type(statement['element'])} "
                f"{render_expression(statement['value'])})")
    if kind == 'append_row':
        return f"(.appendRow {render_container(statement['container'])} {lean_type(statement['element'])})"
    if kind == 'append_reserved':
        return (f"(.append {render_container(statement['container'])} {lean_type(statement['element'])} "
                f"{render_expression(statement['value'])})")
    if kind == 'dedup_vector':
        return f"(.dedupVec {render_container(statement['container'])} {lean_type(statement['element'])})"
    if kind == 'sort_vector':
        return f"(.sortVec {render_container(statement['container'])} {lean_type(statement['element'])})"
    if kind == 'assign_range':
        return (f"(.assignRange {render_container(statement['container'])} {statement['first']} "
                f"{statement['last']} {lean_type(statement['element'])} "
                f"{str(statement['first_end']).lower()} {str(statement['last_end']).lower()})")
    if kind == 'return':
        return f"(.ret {render_expression(statement['value'])})"
    if kind == 'return_unit':
        return '.retUnit'
    if kind == 'return_vector':
        return f"(.retVector {statement['slot']})"
    raise ValueError('unsupported statement kind: ' + kind)


def render_commands(statements, *, share=None):
    body = '(.primitive .skip)'
    for ordinal, statement in enumerate(reversed(statements),1):
        kind = statement['kind']
        if kind == 'scope':
            command = f"(.scope {render_commands(statement['body'],share=share)})"
        elif kind == 'while':
            command = (f"(.whileLoop {render_expression(statement['condition'])} "
                       f"{render_commands(statement['body'],share=share)})")
        elif kind == 'branch':
            command = (f"(.branch {render_expression(statement['condition'])} "
                       f"{render_commands(statement['yes'],share=share)} {render_commands(statement['no'],share=share)})")
        elif kind == 'break':
            command = '.breakLoop'
        elif kind == 'invoke':
            arguments = ', '.join(lean_expression(a) for a in statement['arguments'])
            command = f"(.invokeScalar «{statement['name']}» [{arguments}])"
        else:
            command = f'(.primitive {render_statement(statement)})'
        body = f'(.sequence {command} {body})'
        if share is not None and ordinal % 32 == 0:
            body = share(body)
    return body


def emit_lean(ir, namespace='NestedProgramInstances', *, constructor_exports=False, share_commands=False):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', namespace):
        raise ValueError('invalid Lean namespace')
    if not isinstance(constructor_exports, bool):
        raise ValueError('constructor_exports must be boolean')
    if not isinstance(share_commands, bool):
        raise ValueError('share_commands must be boolean')
    lines = ['-- Generated from audited Clang vector operations and scalar syntax.',
             'import Proofs.CppNestedCall', '', f'namespace {namespace}',
             'open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall', '']
    if 'signed_conversion' in ir:
        lines.insert(1, '-- Signed conversion contract: ' + ir['signed_conversion'])
    if constructor_exports:
        lines.insert(2, 'import Proofs.CppConstructorMultiFinish')
    for callee in ir['callees']:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', callee['name']):
            raise ValueError('unsupported callee name')
        parameters = ', '.join(f"⟨{lean_type(p['type'])}, {str(p['reference']).lower()}, "
                               f"{str(p['writable']).lower()}⟩" for p in callee['parameters'])
        lines.append(f"def «{callee['name']}» : Proofs.CppLoop.LoopProgram :=\n"
                     f"  ⟨[{parameters}], {lean_type(callee['result_type'])},\n"
                     f"   {lean_statement(callee['body'])}⟩")
        lines.append('')
    generic = {}
    for function in ir['functions']:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', function['name']):
            raise ValueError('unsupported function name')
        template = function.get('template')
        if template is None:
            if 'construction_fields' in function:
                lines.append('-- Initializer/body stage: runFuel retains fields; callFuel retires them.')
            body_text = None
            if share_commands:
                parts = []
                def share(body):
                    name = f'«{function["name"]}».commandPart{len(parts)}'
                    parts.append(f'private def {name} : Command := {body}')
                    return name
                body_text = render_commands(function['body'],share=share)
                lines.extend(parts)
            lines.append(render_function(function['name'], function,body_text=body_text))
            if 'construction_fields' in function:
                fields = ', '.join(f'({json.dumps(f["name"])},{f["slot"]})' for f in function['construction_fields'])
                lines.append(f'def «{function["name"]}_fields» : List (String × Nat) := [{fields}]')
                if constructor_exports:
                    layout = function.get('construction_layout')
                    if not isinstance(layout, list) or len(layout) != len(function['construction_fields']):
                        raise ValueError('typed constructor field layout required')
                    slots = set()
                    for field, original in zip(layout, function['construction_fields'], strict=True):
                        if (field.get('name') != original['name'] or field.get('slot') != original['slot'] or
                                type(field.get('slot')) is not int or field['slot'] < 0 or field['slot'] in slots or
                                field.get('kind') not in ('vector', 'scalar') or
                                not isinstance(field.get('writable'), bool) or not isinstance(field.get('mutable'), bool)):
                            raise ValueError('constructor field layout identity, order or permission differs')
                        slots.add(field['slot'])
                    vectors = ', '.join(f"⟨{f['slot']},{lean_element(f['element'])}⟩"
                                        for f in layout if f['kind'] == 'vector')
                    scalars = ', '.join(f"⟨{f['slot']},{lean_type(f['element'])}⟩"
                                        for f in layout if f['kind'] == 'scalar')
                    name = function['name']
                    lines += [f'def «{name}».vectorFields : List Proofs.CppConstructorMultiFinish.VectorField := [{vectors}]',
                              f'def «{name}».scalarFields : List Proofs.CppConstructorFinish.ScalarField := [{scalars}]',
                              f'def «{name}».exportMembersFuel (fuel : Nat) (caller : NState) (args : List NArgument) :',
                              '    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=',
                              f'  «{name}».constructMembersFuel fuel caller args «{name}».vectorFields «{name}».scalarFields']
            continue
        if constructor_exports and 'construction_fields' in function:
            raise ValueError('template constructor export layout requires a separate generic model')
        if share_commands:
            raise ValueError('template command sharing requires a separate generic model')
        generic_name, arguments, parameter_names = template
        if len(arguments) != len(parameter_names):
            raise ValueError('template parameter names are unknown')
        import scalar_ir
        scalar_ir.PARAMETRIC = True
        try:
            parametric = render_function(generic_name, function, parameter_names)
        finally:
            scalar_ir.PARAMETRIC = False
        if generic_name not in generic:
            generic[generic_name] = parametric
            lines.append(parametric)
        elif generic[generic_name] != parametric:
            raise ValueError('specializations of one template differ beyond their template arguments')
        # The instance must be the generic program applied to the arguments: re-render with literals and compare.
        literal = render_function(function['name'], function)
        substituted = parametric
        for parameter, argument in zip(parameter_names, arguments):
            substituted = re.sub(r'\(' + re.escape(parameter) + r'\)', f'({argument})', substituted)
        substituted = substituted.replace(f'def «{generic_name}» ' + ''.join(f'({p} : Nat) ' for p in parameter_names),
                                          f'def «{function["name"]}» ')
        if substituted != literal:
            raise ValueError('template instance differs from its generic program')
        lines.append(f'def «{function["name"]}» : NProgram := «{generic_name}» ' + ' '.join(arguments))
    if not share_commands and sum(len(line) for line in lines) > 200000:
        # Elaborating a very large generated program needs a deeper recursion limit.
        lines.insert(lines.index(f'namespace {namespace}'), 'set_option maxRecDepth 100000')
    return '\n'.join([*lines, '', f'end {namespace}', ''])


def render_function(name, function, parameter_names=(), *, body_text=None):
    parameters = []
    for p in function['parameters']:
        ty = lean_type(p['element'])
        writable = str(p['writable']).lower()
        if p['kind'] == 'vector':
            parameters.append(f'.vector {ty} {writable}')
        elif p['kind'] == 'nested':
            parameters.append(f'.nested {ty} {writable}')
        else:
            parameters.append(f'.scalar {ty} {str(p["reference"]).lower()} {writable}')
    result = function['result']
    kind = (".unit" if 'unit' in result else f".vector {lean_element(result['vector'])}" if 'vector' in result
            else f".scalar {lean_type(result)}")
    binder = ''.join(f'({p} : Nat) ' for p in parameter_names)
    return (f'def «{name}» {binder}: NProgram := ⟨[{", ".join(parameters)}],{kind},'
            f'{render_commands(function["body"]) if body_text is None else body_text}⟩')
