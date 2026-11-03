"""Audit implicit copy assignment and emit its declaration-ordered evaluator profile.

Only same-TU declaration identities select fields, source, this and the pinned
vector copy-assignment operation. ObjectRef call-site layout remains separate.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

from class_copy import audit_class_fields, original_location, source_member, spelling
from scalar_ir import TYPES, lean_type
from scalar_stl import walk
from vector_stl import translation_unit, audit_vector_nodes, vector_declarations


def materialize_assignment(source, qualified, include_dirs=()):
    records = []
    try:
        _, roots = translation_unit(source, include_dirs, copy_class=qualified,
                                    copy_records=records, copy_assignment=True)
    except subprocess.CalledProcessError as error:
        raise ValueError('class assignment witness must compile without access overrides') from error
    if len(records) != 1:
        raise ValueError('exactly one original assignment class required')
    records[0]['_copy_qualified'] = qualified
    return records[0], roots


def this_expression(node, qualified, name):
    if (node.get('kind') != 'CXXThisExpr' or node.get('valueCategory') != 'prvalue' or
            spelling(node) not in {qualified+' *', name+' *'} or node.get('inner')):
        raise ValueError('assignment destination requires the original this pointer')


def target_member(node, field, qualified, name):
    if (node.get('kind') != 'MemberExpr' or node.get('referencedMemberDecl') != field['id'] or
            node.get('name') != field['name'] or node.get('isArrow') is not True or
            node.get('valueCategory') != 'lvalue' or spelling(node) != spelling(field) or
            len(node.get('inner', [])) != 1):
        raise ValueError('assignment destination must match its original field identity')
    this_expression(node['inner'][0], qualified, name)


def audit_assignment_record(source, qualified, record, roots, include_dirs=()):
    source = Path(source).resolve(strict=True)
    fields = audit_class_fields(source, qualified, record, roots)
    candidates = []
    for node in record.get('inner', []):
        params = [c for c in node.get('inner', []) if c.get('kind') == 'ParmVarDecl']
        if (node.get('kind') == 'CXXMethodDecl' and node.get('name') == 'operator=' and len(params) == 1 and
                spelling(params[0]) in {f'const {record["name"]} &', f'const {qualified} &'}):
            candidates.append((node, params[0]))
    if len(candidates) != 1:
        raise ValueError('exactly one const-reference copy assignment required')
    method, parameter = candidates[0]
    signatures = {f'{name} &({spelling(parameter)})'+suffix
                  for name in (record['name'], qualified)
                  for suffix in ('', ' noexcept', ' noexcept(false)', ' noexcept(true)')}
    if (not method.get('isImplicit') or not method.get('isUsed') or not method.get('id') or
            method.get('explicitlyDefaulted') != 'default' or method.get('isDeleted') or
            method.get('explicitlyDeleted') or spelling(method) not in signatures or
            not original_location(method, source) or not parameter.get('id') or not original_location(parameter, source) or
            any(n.get('kind') not in ('ParmVarDecl', 'CompoundStmt') for n in method.get('inner', []))):
        raise ValueError('assignment must be the used implicit defaulted method returning its class reference')
    bodies = [c for c in method.get('inner', []) if c.get('kind') == 'CompoundStmt']
    if len(bodies) != 1 or len(bodies[0].get('inner', [])) != len(fields)+1:
        raise ValueError('assignment requires one action per field followed by return this')
    actions = bodies[0]['inner']
    returned = actions[-1]
    if returned.get('kind') != 'ReturnStmt' or len(returned.get('inner', [])) != 1:
        raise ValueError('assignment must return its destination')
    expression = returned['inner'][0]
    if (expression.get('kind') != 'UnaryOperator' or expression.get('opcode') != '*' or
            expression.get('valueCategory') != 'lvalue' or spelling(expression) not in {record['name'], qualified} or
            len(expression.get('inner', [])) != 1):
        raise ValueError('assignment return must be the lvalue *this')
    this_expression(expression['inner'][0], qualified, record['name'])

    # Reaudit pristine primary/out-of-line definitions and used helpers in the
    # same dump. This opt-in does not enable operator= in ordinary vector lowering.
    audited = audit_vector_nodes(source, [method], roots, include_dirs, copy_assignment=True)
    _, instances = vector_declarations(roots)
    methods = {n['id']: n for instance in instances for n in walk(instance)
               if n.get('kind') == 'CXXMethodDecl' and n.get('id')}
    plan = []
    for position, (field, action) in enumerate(zip(fields, actions[:-1], strict=True)):
        ty = spelling(field)
        if ty.startswith('const '):
            raise ValueError('implicit assignment cannot write a const field')
        children = action.get('inner', [])
        if position == 0:
            if (action.get('kind') != 'CXXMemberCallExpr' or len(children) != 2 or
                    action.get('valueCategory') != 'lvalue' or children[0].get('kind') != 'MemberExpr'):
                raise ValueError('first assignment field requires the audited vector copy-assignment call')
            member = children[0]
            element = action.get('verifiedVectorElement')
            identifier = member.get('referencedMemberDecl')
            selected = methods.get(identifier)
            params = [p for p in selected.get('inner', []) if p.get('kind') == 'ParmVarDecl'] if selected else []
            if (action.get('verifiedVectorOperation') != 'operator=' or not selected or
                    member.get('name') != 'operator=' or member.get('isArrow') is not False or
                    member.get('valueCategory') != 'prvalue' or len(member.get('inner', [])) != 1 or
                    element not in TYPES or element == 'bool' or ty != f'std::vector<{element}>' or
                    spelling(action) not in {f'std::vector<{element}>', f'vector<{element}>'} or
                    len(params) != 1 or spelling(params[0]) not in {f'const std::vector<{element}> &', f'const vector<{element}> &'} or
                    not any(op['callee_id'] == identifier and op['operation'] == 'operator=' for op in audited['operations'])):
                raise ValueError('vector copy assignment must use the pinned const-reference declaration identity')
            target_member(member['inner'][0], field, qualified, record['name'])
            source_member(children[1], field, parameter)
            plan.append(dict(kind='vector_assign', element=element, callee_id=identifier))
        else:
            if (ty not in TYPES or action.get('kind') != 'BinaryOperator' or action.get('opcode') != '=' or
                    spelling(action) != ty or action.get('valueCategory') != 'lvalue' or len(children) != 2):
                raise ValueError('remaining fields require declaration-ordered scalar assignments')
            target_member(children[0], field, qualified, record['name'])
            rhs = children[1]
            if (rhs.get('kind') != 'ImplicitCastExpr' or rhs.get('castKind') != 'LValueToRValue' or
                    spelling(rhs) != ty or rhs.get('valueCategory') != 'prvalue' or len(rhs.get('inner', [])) != 1):
                raise ValueError('scalar assignment source requires the matching source field load')
            source_member(rhs['inner'][0], field, parameter)
            plan.append(dict(kind='scalar_assign', type=ty))
        plan[-1].update(field_id=field['id'], name=field['name'], writable=True)
    return dict(coverage='member_identity_only', source=str(source), **{'class': qualified},
                class_id=record['id'], assignment_id=method['id'], source_parameter_id=parameter['id'], fields=plan)


def audit_class_assignment(source, qualified, include_dirs=()):
    record, roots = materialize_assignment(source, qualified, include_dirs)
    return audit_assignment_record(source, qualified, record, roots, include_dirs)


def emit_class_assignment(source, qualified, namespace='Proofs.Generated.ClassAssignment', include_dirs=()):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', namespace):
        raise ValueError('invalid Lean namespace')
    source = Path(source).resolve(strict=True)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    plan = audit_class_assignment(source, qualified, include_dirs)
    if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
        raise ValueError('assignment source changed during generation')
    def ty(name):
        width, signed, boolean = TYPES[name]
        return lean_type(dict(width=width, signed=signed, boolean=boolean))
    vector, *scalars = plan['fields']
    scalar_profiles = ', '.join(f'({ty(f["type"])},true)' for f in scalars)
    names = ', '.join(json.dumps(f['name']) for f in plan['fields'])
    return '\n'.join([
        '-- Generated from audited implicit assignment. ObjectRef layout remains a caller obligation.',
        'import Proofs.CppClassAssign', '', f'namespace {namespace}',
        'open Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.CppClassCopy Proofs.CppClassAssign',
        f'def sourceSHA256 : String := "{digest}"', f'def fieldNames : List String := [{names}]',
        f'def profile : Profile := ⟨{ty(vector["element"])},true,[{scalar_profiles}]⟩',
        'def assign (s : NState) (target source : ObjectRef) := assignClass s target source profile',
        'def trackedAssign (s : NState) (generation : Generations) (target source : ObjectRef) :=',
        '  trackedAssignClass s generation target source profile',
        'theorem tracked_data (s : NState) (generation : Generations) (target source : ObjectRef) :',
        '    (trackedAssign s generation target source).map Prod.fst = assign s target source :=',
        '  tracked_class_data s generation target source profile',
        f'end {namespace}', ''])
