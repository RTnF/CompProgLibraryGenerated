"""Pinned two-argument std::min/max when their reference result is copied.

Only plain scalar lvalues of identical 32/64-bit integer type are supported.
The value wrapper preserves the selected standard comparison and uses the
existing inliner, including its conditional-evaluation and loop restrictions.
"""
import copy
from functools import lru_cache
from pathlib import Path
import tempfile

from clang_ast import gcc_include_dirs, normalized
from scalar_ir import TYPES, scalar_type, source_ast
from inline_ast import inline_functions


def _stable(node):
    if isinstance(node, list):
        return [_stable(c) for c in node]
    if isinstance(node, dict):
        return normalized({k: _stable(v) for k, v in node.items()
                           if k not in {'isUsed', 'isReferenced'}})
    return node


def _templates(roots):
    headers = {(Path(p)/'bits/stl_algobase.h').resolve() for p in gcc_include_dirs()}
    for root in roots:
        nodes = root.get('inner', []) if root.get('kind') == 'NamespaceDecl' else [root]
        for node in nodes:
            if node.get('kind') != 'FunctionTemplateDecl' or node.get('name') not in {'min', 'max'}:
                continue
            loc = node.get('loc', {})
            origin = loc.get('file', root.get('loc', {}).get('file', ''))
            if (not origin or Path(origin).resolve() not in headers or
                    'spellingLoc' in loc or 'expansionLoc' in loc or 'offset' not in loc):
                continue
            primary = [f for f in node.get('inner', []) if f.get('kind') == 'FunctionDecl'
                       and not any(c.get('kind') == 'TemplateArgument' for c in f.get('inner', []))
                       and len([c for c in f.get('inner', []) if c.get('kind') == 'ParmVarDecl']) == 2
                       and any(c.get('kind') == 'CompoundStmt' for c in f.get('inner', []))]
            if len(primary) == 1:
                yield node, primary[0]


def _plain(node):
    while (node.get('kind') == 'ParenExpr' or
           node.get('kind') == 'ImplicitCastExpr' and node.get('castKind') == 'NoOp'):
        children = node.get('inner', [])
        if len(children) != 1:
            raise ValueError('invalid scalar choice lvalue wrapper')
        node = children[0]
    if (node.get('kind') != 'DeclRefExpr' or node.get('valueCategory') != 'lvalue' or
            node.get('referencedDecl', {}).get('kind') not in {'ParmVarDecl', 'VarDecl'}):
        raise ValueError('std::min/max value copying requires plain scalar lvalue arguments')
    scalar_type(node)  # Reject volatile and nonprimitive objects.
    return node


@lru_cache(maxsize=32)
def _pristine(operation, spelling):
    with tempfile.TemporaryDirectory(prefix='scalar-choice-standard-') as directory:
        source = Path(directory)/'standard.cpp'
        source.write_text('#include <algorithm>\n'+spelling+' probe(const '+spelling+
                          '& a,const '+spelling+'& b){return std::'+operation+'(a,b);}\n')
        roots = source_ast(source, 'std::'+operation)
        matches = []
        for template, primary in _templates(roots):
            if template['name'] != operation:
                continue
            for instance in template.get('inner', []):
                if instance.get('TemplateInstantiationPattern') != primary['id']:
                    continue
                arguments = [c.get('type', {}).get('qualType') for c in instance.get('inner', [])
                             if c.get('kind') == 'TemplateArgument']
                if arguments == [spelling]:
                    matches.append((_stable(primary), _stable(_body(instance))))
        if len(matches) != 1:
            raise ValueError('one pristine scalar std::min/max instance required')
        return matches[0]


def _body(function):
    bodies = [c for c in function.get('inner', []) if c.get('kind') == 'CompoundStmt']
    if len(bodies) != 1:
        raise ValueError('std::min/max instance body required')
    return bodies[0]


def _value_wrapper(function, operation, spelling):
    """Copy the actual comparison from the audited standard body."""
    parameters = [copy.deepcopy(c) for c in function['inner'] if c.get('kind') == 'ParmVarDecl']
    statements = _body(function).get('inner', [])
    if (len(parameters) != 2 or len(statements) != 2 or statements[0].get('kind') != 'IfStmt'
            or statements[1].get('kind') != 'ReturnStmt'):
        raise ValueError('unsupported pinned scalar choice body shape')
    branch = statements[0].get('inner', [])
    if len(branch) != 2 or branch[1].get('kind') != 'ReturnStmt':
        raise ValueError('unsupported pinned scalar choice return shape')
    condition = branch[0]
    operands = condition.get('inner', [])
    def loaded_parameter(node):
        if node.get('kind') != 'ImplicitCastExpr' or node.get('castKind') != 'LValueToRValue':
            raise ValueError('scalar choice comparison must load primitive parameters')
        children = node.get('inner', [])
        if len(children) != 1:
            raise ValueError('invalid scalar choice comparison load')
        return _plain(children[0])['referencedDecl']['id']
    order = [p['id'] for p in parameters]
    expected = order if operation == 'max' else list(reversed(order))
    if (condition.get('kind') != 'BinaryOperator' or condition.get('opcode') != '<' or
            len(operands) != 2 or [loaded_parameter(c) for c in operands] != expected):
        raise ValueError('scalar choice comparison differs from standard selection')
    for returned, selected in ((branch[1], order[1]), (statements[1], order[0])):
        values = returned.get('inner', [])
        if len(values) != 1 or _plain(values[0])['referencedDecl']['id'] != selected:
            raise ValueError('scalar choice reference selection differs from standard')
    identity = 'std-value:'+function['id']
    def ref(identifier, name, ty=spelling):
        return dict(kind='DeclRefExpr', type={'qualType': ty}, valueCategory='lvalue',
                    referencedDecl=dict(kind='VarDecl', id=identifier, name=name, type={'qualType': ty}))
    def load(node):
        return dict(kind='ImplicitCastExpr', castKind='LValueToRValue',
                    type={'qualType': spelling}, valueCategory='prvalue', inner=[node])
    first = copy.deepcopy(statements[1]['inner'][0])
    second = copy.deepcopy(branch[1]['inner'][0])
    local = identity+':selected'
    declaration = dict(kind='VarDecl', id=local, name='selected', type={'qualType': spelling},
                       init='c', inner=[load(first)])
    assignment = dict(kind='BinaryOperator', opcode='=', type={'qualType': spelling},
                      valueCategory='lvalue', inner=[ref(local, 'selected'), load(second)])
    body = dict(kind='CompoundStmt', inner=[dict(kind='DeclStmt', inner=[declaration]),
                dict(kind='IfStmt', inner=[copy.deepcopy(condition), assignment]),
                dict(kind='ReturnStmt', inner=[load(ref(local, 'selected'))])])
    return dict(kind='FunctionDecl', id=identity, name='std_value_'+operation,
                type={'qualType': spelling+'(const '+spelling+' &, const '+spelling+' &)'},
                _inline=True, inner=[*parameters, body])


def lower_scalar_choices(functions, roots):
    """Return rewritten functions and a declaration-identity audit ledger."""
    calls = []
    def collect(node, parent=None):
        if node.get('kind') == 'CallExpr' and len(node.get('inner', [])) == 3:
            callee = node['inner'][0]
            while callee.get('kind') == 'ImplicitCastExpr' and len(callee.get('inner', [])) == 1:
                callee = callee['inner'][0]
            declaration = callee.get('referencedDecl', {})
            if declaration.get('kind') == 'FunctionDecl' and declaration.get('name') in {'min', 'max'}:
                calls.append((node, parent, callee))
        for child in node.get('inner', []):
            collect(child, node)
    for function in functions:
        collect(function)
    if not calls:
        return functions, []
    instances = {}
    declared_standard = set()
    for template, primary in _templates(roots):
        for instance in template.get('inner', []):
            if instance.get('kind') == 'FunctionDecl':
                declared_standard.add(instance.get('id'))
            if instance.get('TemplateInstantiationPattern') != primary['id']:
                continue
            arguments = [c.get('type', {}).get('qualType') for c in instance.get('inner', [])
                         if c.get('kind') == 'TemplateArgument']
            spelling = arguments[0] if len(arguments) == 1 else None
            if spelling not in TYPES or TYPES[spelling][0] not in (32, 64) or TYPES[spelling][2]:
                continue
            instances[instance['id']] = template['name'], spelling, primary, instance
    wrappers, ledger = {}, []
    for call, parent, callee in calls:
        selected = instances.get(callee['referencedDecl']['id'])
        if selected is None:
            if callee['referencedDecl']['id'] in declared_standard:
                raise ValueError('unsupported or unowned scalar std::min/max instance')
            continue  # An ordinary user function stays an ordinary call.
        operation, spelling, primary, instance = selected
        clean_primary, clean_body = _pristine(operation, spelling)
        if _stable(primary) != clean_primary or _stable(_body(instance)) != clean_body:
            raise ValueError('std::min/max differs from the pristine pinned implementation')
        signature = 'const '+spelling+' &(const '+spelling+' &, const '+spelling+' &)'
        if instance.get('type', {}).get('qualType') != signature:
            raise ValueError('std::min/max scalar signature mismatch')
        if (parent is None or parent.get('kind') != 'ImplicitCastExpr' or
                parent.get('castKind') != 'LValueToRValue' or parent.get('inner') != [call] or
                parent.get('valueCategory') != 'prvalue'):
            raise ValueError('std::min/max reference result must be immediately copied to a value')
        ty = scalar_type(parent)
        if ty != dict(zip(('width', 'signed', 'boolean'), TYPES[spelling])):
            raise ValueError('std::min/max copied result type mismatch')
        for argument in call['inner'][1:]:
            if scalar_type(_plain(argument)) != ty:
                raise ValueError('std::min/max argument type mismatch')
        wrapper = wrappers.setdefault(instance['id'], _value_wrapper(instance, operation, spelling))
        new_call = copy.deepcopy(call)
        new_call['type'] = {'qualType': spelling}
        new_call['valueCategory'] = 'prvalue'
        reference = new_call['inner'][0]
        while reference.get('kind') == 'ImplicitCastExpr' and len(reference.get('inner', [])) == 1:
            reference = reference['inner'][0]
        reference['referencedDecl'] = dict(kind='FunctionDecl', id=wrapper['id'], name=wrapper['name'],
                                          type=wrapper['type'])
        parent.clear()
        parent.update(new_call)
        ledger.append(dict(operation='std::'+operation, element=spelling,
                           callee_id=instance['id'], pattern_id=primary['id']))
    if not wrappers:
        return functions, []
    identifiers = {f['id'] for f in functions}
    lowered = inline_functions([*functions, *wrappers.values()])
    return [f for f in lowered if f['id'] in identifiers], ledger
