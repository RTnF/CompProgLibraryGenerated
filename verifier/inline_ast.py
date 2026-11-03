"""Inline calls between the functions of one translation unit at the Clang AST level.

The result is again a set of ordinary function definitions in the shape the common generator accepts:
every call to a function defined in the same file (or to a method of the same scalar-field class, already
lowered to a function whose fields are leading reference parameters) becomes the callee's statements,
spliced before the statement that contained the call. Value parameters become fresh locals, reference
parameters are replaced by the (side-effect free) lvalue argument, and the callee's single final `return`
becomes a fresh local holding the call's value. Recursion, early returns, and calls whose position makes
hoisting change the evaluation order (loop conditions, short-circuit operands, conditional operands)
are rejected.
"""
import copy


class Inliner:
    def __init__(self, functions, library=()):
        self.by_id = {f['id']: f for f in functions
                      if 'id' in f and ('_fields' in f or f.get('_inline') or takes_vector(f) or marked_inline(f))}
        for f in library:
            if 'id' in f and (takes_vector(f) or f.get('_construction_helper')):
                self.by_id.setdefault(f['id'], f)
        self.counter = 0
        self.active = []

    def fresh(self, base):
        self.counter += 1
        return f'inline:{self.counter}:{base}'

    # --- call recognition ---------------------------------------------------------------
    def callee_of(self, node, caller):
        kind = node.get('kind')
        children = node.get('inner', [])
        if kind == 'CallExpr' and children:
            callee = children[0]
            while callee.get('kind') == 'ImplicitCastExpr' and len(callee.get('inner', [])) == 1:
                callee = callee['inner'][0]
            if callee.get('kind') == 'DeclRefExpr':
                function = self.by_id.get(callee['referencedDecl'].get('id'))
                if function is not None:
                    return function, children[1:], []
        if kind == 'CXXMemberCallExpr' and children and children[0].get('kind') == 'MemberExpr':
            member = children[0]
            function = self.by_id.get(member.get('referencedMemberDecl'))
            if function is not None:
                base = member.get('inner', [])
                if len(base) != 1 or base[0].get('kind') != 'CXXThisExpr':
                    raise ValueError('methods can only be called on this')
                fields = caller.get('_all_fields', caller.get('_fields'))
                if fields is None or len(fields) != len(function.get('_fields', [])):
                    raise ValueError('method call requires a method of the same class')
                refs = [self.field_reference(p) for p in fields]
                return function, children[1:], refs
        return None

    @staticmethod
    def field_reference(parameter):
        return {'kind': 'DeclRefExpr', 'type': {'qualType': parameter['type']['qualType'].removesuffix(' &')},
                'valueCategory': 'lvalue',
                'referencedDecl': {'id': parameter['id'], 'kind': parameter.get('kind', 'ParmVarDecl'), 'name': parameter['name'],
                                   'type': parameter['type']}}

    def contains_call(self, node, caller):
        if isinstance(node, list):
            return any(self.contains_call(child, caller) for child in node)
        if not isinstance(node, dict):
            return False
        if self.callee_of(node, caller) is not None:
            return True
        return self.contains_call(node.get('inner', []), caller)

    # --- expansion ----------------------------------------------------------------------
    def expand_call(self, node, caller, arguments_done, discard=False):
        function, arguments, field_refs = self.callee_of(node, caller)
        if function['id'] in self.active or function is caller:
            raise ValueError('recursive calls cannot be inlined')
        all_arguments = field_refs + arguments
        parameters = [c for c in function['inner'] if c.get('kind') == 'ParmVarDecl']
        if len(parameters) != len(all_arguments):
            raise ValueError('call argument count mismatch')
        body = [c for c in function['inner'] if c.get('kind') == 'CompoundStmt'][0]
        statements = []
        subst = {}
        rename = {}
        for parameter, argument in zip(parameters, all_arguments):
            spelling = parameter['type'].get('desugaredQualType', parameter['type']['qualType'])
            reference = spelling.endswith(' &')
            argument = strip_temporary(argument)
            if reference and not is_plain_lvalue(argument):
                if spelling.startswith('const ') and argument.get('valueCategory') != 'lvalue':
                    reference = False
                elif not is_plain_lvalue(argument):
                    raise ValueError('reference arguments must be plain variables')
            if reference:
                subst[parameter['id']] = ('lvalue', argument)
            else:
                identity = self.fresh(parameter.get('name', 'arg'))
                value_type = spelling[:-2] if spelling.endswith(' &') else spelling
                declaration = {'kind': 'VarDecl', 'id': identity, 'name': parameter.get('name', 'arg'),
                               'type': {'qualType': value_type}, 'init': 'c', 'isUsed': True,
                               'inner': [copy.deepcopy(argument)], 'loc': node.get('loc', {}),
                               'range': node.get('range', {})}
                statements.append({'kind': 'DeclStmt', 'inner': [declaration], 'range': node.get('range', {})})
                subst[parameter['id']] = ('value', identity, value_type, parameter.get('name', 'arg'))
        inner = body.get('inner', [])
        if not inner or inner[-1].get('kind') != 'ReturnStmt' and not function['type']['qualType'].startswith('void'):
            raise ValueError('inlined functions need one final return')
        self.active.append(function['id'])
        try:
            if inner and inner[-1].get('kind') == 'ReturnStmt':
                leading, returned = inner[:-1], inner[-1]
            else:
                leading, returned = inner, None
            for statement in leading:
                if contains_return(statement):
                    raise ValueError('early returns cannot be inlined')
            cloned = [self.clone(s, subst, rename) for s in leading]
            statements.extend(self.expand_statements(cloned, function))
            result = None
            if returned is not None and discard and _is_pure(returned) and not self.contains_call(returned, function):
                returned = None  # the value is unused and computing it has no effect
            if returned is not None:
                value = returned.get('inner', [None])[0]
                if value is None:
                    raise ValueError('inlined return needs a value')
                value = self.clone(value, subst, rename)
                value, pre = self.hoist(value, function)
                statements.extend(pre)
                identity = self.fresh('ret')
                spelling = node['type'].get('desugaredQualType', node['type']['qualType'])
                declaration = {'kind': 'VarDecl', 'id': identity, 'name': 'ret', 'type': {'qualType': spelling},
                               'init': 'c', 'isUsed': True, 'inner': [value], 'loc': node.get('loc', {}),
                               'range': node.get('range', {})}
                statements.append({'kind': 'DeclStmt', 'inner': [declaration], 'range': node.get('range', {})})
                result = {'kind': 'ImplicitCastExpr', 'type': {'qualType': spelling}, 'valueCategory': 'prvalue',
                          'castKind': 'LValueToRValue', 'range': node.get('range', {}),
                          'inner': [{'kind': 'DeclRefExpr', 'type': {'qualType': spelling}, 'valueCategory': 'lvalue',
                                     'range': node.get('range', {}),
                                     'referencedDecl': {'id': identity, 'kind': 'VarDecl', 'name': 'ret',
                                                        'type': {'qualType': spelling}}}]}
        finally:
            self.active.pop()
        return statements, result

    def clone(self, node, subst, rename):
        if isinstance(node, list):
            return [self.clone(child, subst, rename) for child in node]
        if not isinstance(node, dict):
            return node
        kind = node.get('kind')
        if kind == 'DeclRefExpr':
            identity = node['referencedDecl'].get('id')
            if identity in subst:
                entry = subst[identity]
                if entry[0] == 'lvalue':
                    return copy.deepcopy(entry[1])
                _, new_id, value_type, name = entry
                reference = dict(node['referencedDecl'], id=new_id, kind='VarDecl', name=name,
                                 type={'qualType': value_type})
                return dict(node, referencedDecl=reference, type={'qualType': value_type})
            if identity in rename:
                return dict(node, referencedDecl=dict(node['referencedDecl'], id=rename[identity]))
        result = {}
        for key, value in node.items():
            if key == 'inner':
                continue
            result[key] = copy.deepcopy(value)
        if kind == 'VarDecl' and 'id' in node:
            rename[node['id']] = self.fresh(node.get('name', 'local'))
            result['id'] = rename[node['id']]
        if 'inner' in node:
            result['inner'] = [self.clone(child, subst, rename) for child in node['inner']]
        return result

    # --- hoisting -----------------------------------------------------------------------
    def hoist(self, node, caller, discard=False):
        """Return (expression without known calls, statements to run before it)."""
        if not isinstance(node, dict):
            return node, []
        if self.callee_of(node, caller) is not None:
            pre = []
            function, arguments, refs = self.callee_of(node, caller)
            arguments = list(arguments)
            new_arguments = []
            for argument in arguments:
                argument, extra = self.hoist(argument, caller)
                pre.extend(extra)
                new_arguments.append(argument)
            rebuilt = dict(node)
            children = list(node['inner'])
            rebuilt['inner'] = children[:1] + new_arguments
            statements, result = self.expand_call(rebuilt, caller, True, discard)
            pre.extend(statements)
            if result is None:
                return {'kind': 'NullStmt'}, pre
            return result, pre
        kind = node.get('kind')
        children = node.get('inner', [])
        if kind in ('ConditionalOperator',) or (kind == 'BinaryOperator' and node.get('opcode') in ('&&', '||')):
            for index, child in enumerate(children):
                if (kind == 'ConditionalOperator' or index > 0) and self.contains_call(child, caller):
                    raise ValueError('calls in conditionally evaluated operands cannot be inlined')
        pre = []
        new_children = []
        for child in children:
            child, extra = self.hoist(child, caller)
            pre.extend(extra)
            new_children.append(child)
        if not children:
            return node, []
        return dict(node, inner=new_children), pre

    # --- statements ---------------------------------------------------------------------
    def expand_statements(self, statements, caller):
        result = []
        for statement in statements:
            result.extend(self.expand_statement(statement, caller))
        return result

    def block(self, statements):
        return statements[0] if len(statements) == 1 else {'kind': 'CompoundStmt', 'inner': statements}

    def expand_statement(self, node, caller):
        kind = node.get('kind')
        children = node.get('inner', [])
        if not self.contains_call(node, caller):
            return [node]
        while kind in ('ExprWithCleanups', 'ParenExpr') and len(children) == 1:
            node = children[0]
            kind = node.get('kind')
            children = node.get('inner', [])
        if kind == 'CompoundStmt':
            return [dict(node, inner=self.expand_statements(children, caller))]
        if kind == 'DeclStmt':
            result = []
            for declaration in children:
                if declaration.get('kind') == 'VarDecl' and declaration.get('inner'):
                    value, pre = self.hoist(declaration['inner'][0], caller)
                    result.extend(pre)
                    result.append(dict(node, inner=[dict(declaration, inner=[value])]))
                else:
                    result.append(dict(node, inner=[declaration]))
            return result
        if kind == 'IfStmt':
            condition, pre = self.hoist(children[0], caller)
            yes = self.block(self.expand_statement(children[1], caller))
            rest = [yes]
            if len(children) == 3:
                rest.append(self.block(self.expand_statement(children[2], caller)))
            return pre + [dict(node, inner=[condition] + rest)]
        if kind in ('WhileStmt', 'ForStmt', 'DoStmt', 'CXXForRangeStmt'):
            if kind == 'WhileStmt':
                guards, bodies = children[:1], children[1:]
            elif kind == 'ForStmt':
                guards, bodies = children[:4], children[4:]
            else:
                raise ValueError('calls in this loop kind cannot be inlined')
            if kind == 'ForStmt':
                # init, (condition variable), condition, increment, body
                body = children[4]
                guards = children[:4]
                if any(self.contains_call(g, caller) for g in guards):
                    raise ValueError('calls in loop headers cannot be inlined')
                return [dict(node, inner=guards + [self.block(self.expand_statement(body, caller))])]
            if any(self.contains_call(g, caller) for g in guards):
                raise ValueError('calls in loop conditions cannot be inlined')
            return [dict(node, inner=guards + [self.block(self.expand_statement(bodies[0], caller))])]
        if kind in ('ReturnStmt', 'ExprWithCleanups', 'BinaryOperator', 'CompoundAssignOperator', 'CallExpr',
                    'CXXMemberCallExpr', 'ParenExpr', 'UnaryOperator'):
            if self.callee_of(node, caller) is not None:
                expression, pre = self.hoist(node, caller, discard=True)
                return pre
            expression, pre = self.hoist(node, caller)
            return pre + ([] if expression.get('kind') == 'NullStmt' else [expression])
        raise ValueError('unsupported statement containing an inlined call: ' + str(kind))

    def run(self, function):
        body = [c for c in function['inner'] if c.get('kind') == 'CompoundStmt']
        if len(body) != 1:
            return function
        self.active = [function['id']] if 'id' in function else []
        expanded = self.expand_statement(body[0], function)
        new_inner = [expanded[0] if c is body[0] else c for c in function['inner']]
        return dict(function, inner=new_inner)


def strip_temporary(node):
    while node.get('kind') in ('MaterializeTemporaryExpr', 'ParenExpr') and len(node.get('inner', [])) == 1:
        node = node['inner'][0]
    return node


def is_plain_lvalue(node):
    if node.get('kind') == 'ImplicitCastExpr' and node.get('castKind') in ('NoOp',) and len(node.get('inner', [])) == 1:
        return is_plain_lvalue(node['inner'][0])
    return node.get('kind') == 'DeclRefExpr' and node.get('valueCategory') == 'lvalue'


def contains_return(node):
    if isinstance(node, list):
        return any(contains_return(c) for c in node)
    return isinstance(node, dict) and (node.get('kind') == 'ReturnStmt' or contains_return(node.get('inner', [])))


def marked_inline(function):
    """A function declared `[[gnu::always_inline]]`: calls to it are inlined (also when it takes only scalars)."""
    return (any(c.get('kind') == 'AlwaysInlineAttr' for c in function.get('inner', []))
            and any(c.get('kind') == 'CompoundStmt' for c in function.get('inner', [])))


def takes_vector(function):
    """A function with a vector parameter: calls to it are inlined (the call model has scalar parameters only)."""
    return any('vector<' in _spelling(c['type']) for c in function.get('inner', [])
               if c.get('kind') == 'ParmVarDecl') and any(c.get('kind') == 'CompoundStmt' for c in function.get('inner', []))


def inline_functions(functions, library=()):
    functions = [desugar_compound(f) if f.get('kind') == 'FunctionDecl' else f for f in functions]
    library = [desugar_compound(f) for f in library]
    inliner = Inliner(functions, library)
    return [inliner.run(f) for f in functions]


def _is_pure(node):
    """No assignments, increments or calls: duplicating the expression cannot change behavior."""
    if isinstance(node, list):
        return all(_is_pure(c) for c in node)
    if not isinstance(node, dict):
        return True
    kind = node.get('kind')
    if kind in ('CompoundAssignOperator', 'CallExpr', 'CXXMemberCallExpr'):
        return False
    if kind == 'BinaryOperator' and node.get('opcode') in ('=',):
        return False
    if kind == 'UnaryOperator' and node.get('opcode') in ('++', '--'):
        return False
    return _is_pure(node.get('inner', []))


def _spelling(info):
    return info.get('desugaredQualType', info['qualType'])


def desugar_compound(node):
    """Rewrite `lhs op= rhs` into `lhs = (T)((C)lhs op rhs)` for a pure lhs."""
    if isinstance(node, list):
        return [desugar_compound(c) for c in node]
    if not isinstance(node, dict):
        return node
    children = [desugar_compound(c) for c in node.get('inner', [])] if 'inner' in node else None
    result = dict(node) if children is None else dict(node, inner=children)
    if node.get('kind') != 'CompoundAssignOperator':
        return result
    opcode = node.get('opcode', '')
    if not opcode.endswith('=') or opcode in ('==', '!=', '<=', '>=') or len(children) != 2:
        raise ValueError('unsupported compound assignment')
    lhs, rhs = children
    if not _is_pure(lhs):
        raise ValueError('compound assignment needs a side-effect free left operand')
    lhs_type = lhs['type']
    read = {'kind': 'ImplicitCastExpr', 'type': lhs_type, 'valueCategory': 'prvalue', 'castKind': 'LValueToRValue',
            'range': node.get('range', {}), 'inner': [copy.deepcopy(lhs)]}
    compute_lhs = node.get('computeLHSType', lhs_type)
    if _spelling(compute_lhs) != _spelling(lhs_type):
        read = {'kind': 'ImplicitCastExpr', 'type': compute_lhs, 'valueCategory': 'prvalue',
                'castKind': 'IntegralCast', 'range': node.get('range', {}), 'inner': [read]}
    compute_result = node.get('computeResultType', lhs_type)
    value = {'kind': 'BinaryOperator', 'type': compute_result, 'valueCategory': 'prvalue',
             'opcode': opcode[:-1], 'range': node.get('range', {}), 'inner': [read, rhs]}
    if _spelling(compute_result) != _spelling(lhs_type):
        value = {'kind': 'ImplicitCastExpr', 'type': lhs_type, 'valueCategory': 'prvalue',
                 'castKind': 'IntegralCast', 'range': node.get('range', {}), 'inner': [value]}
    return {'kind': 'BinaryOperator', 'type': lhs_type, 'valueCategory': 'lvalue', 'opcode': '=',
            'range': node.get('range', {}), 'loc': node.get('loc', {}), 'inner': [lhs, value]}
