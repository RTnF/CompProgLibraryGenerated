"""Same-TU implicit move audit and construction/assignment emission; caller layouts remain separate."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

from class_copy import audit_class_fields, original_location, spelling
from class_assign import target_member, this_expression
from scalar_ir import TYPES, lean_type
from scalar_stl import walk
from vector_stl import translation_unit, audit_vector_nodes, vector_declarations


def materialize_move(source, qualified, kind, include_dirs=()):
    if kind not in ('construct','assign'):
        raise ValueError('one move construction or assignment operation required')
    records = []
    try:
        _, roots = translation_unit(source, include_dirs, copy_class=qualified, copy_records=records, move_kind=kind)
    except subprocess.CalledProcessError as error:
        raise ValueError('move witness must compile without access overrides') from error
    if len(records) != 1:
        raise ValueError('exactly one original move class required')
    records[0]['_copy_qualified'] = qualified
    return records[0], roots


def source_member(node, field, parameter, qualified, name):
    if (node.get('kind') != 'MemberExpr' or node.get('referencedMemberDecl') != field['id'] or
            node.get('name') != field['name'] or node.get('isArrow') is not False or
            node.get('valueCategory') != 'xvalue' or spelling(node) != spelling(field) or len(node.get('inner', [])) != 1):
        raise ValueError('move source must be the original xvalue field')
    cast = node['inner'][0]
    if (cast.get('kind') != 'CXXStaticCastExpr' or cast.get('castKind') != 'NoOp' or
            cast.get('valueCategory') != 'xvalue' or spelling(cast) not in {qualified,name} or
            len(cast.get('inner', [])) != 1):
        raise ValueError('move source requires the original class rvalue cast')
    origin = cast['inner'][0]
    reference = origin.get('referencedDecl', {})
    if (origin.get('kind') != 'DeclRefExpr' or origin.get('valueCategory') != 'lvalue' or
            reference.get('kind') != 'ParmVarDecl' or reference.get('id') != parameter['id'] or
            spelling(reference) != spelling(parameter) or spelling(origin) != spelling(parameter).removesuffix(' &&') or origin.get('inner')):
        raise ValueError('move source must refer to its original rvalue-reference parameter')


def audit_move_record(source, qualified, record, roots, kind, include_dirs=()):
    if kind not in ('construct','assign'):
        raise ValueError('one move construction or assignment operation required')
    source = Path(source).resolve(strict=True)
    fields = audit_class_fields(source, qualified, record, roots)
    name = record['name']
    candidates = []
    for member in record.get('inner', []):
        params = [n for n in member.get('inner', []) if n.get('kind') == 'ParmVarDecl']
        if (member.get('kind') == ('CXXConstructorDecl' if kind == 'construct' else 'CXXMethodDecl') and
                member.get('name') == (name if kind == 'construct' else 'operator=') and len(params) == 1 and
                spelling(params[0]) in {name+' &&',qualified+' &&'}):
            candidates.append((member,params[0]))
    if len(candidates) != 1:
        raise ValueError('exactly one original rvalue-reference move member required')
    member, parameter = candidates[0]
    signatures = ({'void ('+spelling(parameter)+')'+suffix for suffix in ('',' noexcept',' noexcept(true)')} if kind == 'construct' else
                  {n+' &('+spelling(parameter)+')'+suffix for n in (name,qualified) for suffix in ('',' noexcept',' noexcept(true)')})
    if (not member.get('id') or not member.get('isImplicit') or not member.get('isUsed') or
            member.get('explicitlyDefaulted') != 'default' or member.get('isDeleted') or member.get('explicitlyDeleted') or
            spelling(member) not in signatures or not original_location(member, source) or
            not parameter.get('id') or not original_location(parameter, source) or parameter.get('inner')):
        raise ValueError('move member must be used, implicit, defaulted and return the original type')
    children = member.get('inner', [])
    allowed = {'ParmVarDecl','CompoundStmt'} | ({'CXXCtorInitializer'} if kind == 'construct' else set())
    bodies = [n for n in children if n.get('kind') == 'CompoundStmt']
    if len(bodies) != 1 or any(n.get('kind') not in allowed for n in children):
        raise ValueError('move member requires one original body and no extra declarations')
    if kind == 'construct':
        actions = [n for n in children if n.get('kind') == 'CXXCtorInitializer']
        if bodies[0].get('inner') or len(actions) != len(fields):
            raise ValueError('implicit move construction requires all ordered initializers and an empty body')
    else:
        actions = bodies[0].get('inner', [])
        if len(actions) != len(fields)+1:
            raise ValueError('implicit move assignment requires all ordered fields and return this')
        returned = actions[-1]
        if returned.get('kind') != 'ReturnStmt' or len(returned.get('inner', [])) != 1:
            raise ValueError('move assignment must return its destination')
        expr = returned['inner'][0]
        if (expr.get('kind') != 'UnaryOperator' or expr.get('opcode') != '*' or expr.get('valueCategory') != 'lvalue' or
                spelling(expr) not in {qualified,name} or len(expr.get('inner', [])) != 1):
            raise ValueError('move assignment return must be lvalue *this')
        this_expression(expr['inner'][0],qualified,name)
        actions = actions[:-1]
    audited = audit_vector_nodes(source,[member],roots,include_dirs,move_assignment=kind=='assign')
    _, instances = vector_declarations(roots)
    methods = {n['id']:n for instance in instances for n in walk(instance) if n.get('kind')=='CXXMethodDecl' and n.get('id')}
    constructors = {n['id']:n for instance in instances for n in walk(instance)
                    if n.get('kind')=='CXXConstructorDecl' and n.get('id')}
    plan = []
    for position,(field,action) in enumerate(zip(fields,actions,strict=True)):
        ty = spelling(field)
        base = ty.removeprefix('const ')
        if kind == 'construct':
            target = action.get('anyInit', {})
            if (target.get('kind') != 'FieldDecl' or target.get('id') != field['id'] or target.get('name') != field['name'] or
                    spelling(target) != ty or len(action.get('inner', [])) != 1):
                raise ValueError('move initializer must match original field identity and order')
            value = action['inner'][0]
        else:
            if ty.startswith('const '):raise ValueError('move assignment cannot write a const field')
            value = action
        if position == 0:
            if kind == 'construct':
                element = value.get('verifiedVectorElement')
                selected = constructors.get(value.get('verifiedVectorConstructorDecl'))
                if (value.get('kind') != 'CXXConstructExpr' or value.get('verifiedVectorConstructor') != 'move' or
                        value.get('constructionKind') != 'complete' or value.get('valueCategory') != 'prvalue' or
                        element not in TYPES or element == 'bool' or ty != f'std::vector<{element}>' or
                        spelling(value) != ty or len(value.get('inner', [])) != 1 or not selected or not selected.get('isUsed')):
                    raise ValueError('first move initializer requires the pinned scalar vector move constructor')
                source_member(value['inner'][0],field,parameter,qualified,name)
                callee = value['verifiedVectorConstructorDecl']
            else:
                parts = value.get('inner', [])
                if value.get('kind') != 'CXXMemberCallExpr' or value.get('valueCategory') != 'lvalue' or len(parts) != 2:
                    raise ValueError('first move field requires the pinned vector move assignment')
                access = parts[0]
                element = value.get('verifiedVectorElement')
                callee = access.get('referencedMemberDecl')
                selected = methods.get(callee)
                params = [p for p in selected.get('inner', []) if p.get('kind')=='ParmVarDecl'] if selected else []
                if (access.get('kind') != 'MemberExpr' or access.get('name') != 'operator=' or access.get('isArrow') is not False or
                        access.get('valueCategory') != 'prvalue' or len(access.get('inner', [])) != 1 or
                        value.get('verifiedVectorOperation') != 'operator=' or element not in TYPES or element == 'bool' or
                        ty != f'std::vector<{element}>' or spelling(value) not in {ty,f'vector<{element}>'} or len(params) != 1 or
                        spelling(params[0]) not in {f'std::vector<{element}> &&',f'vector<{element}> &&'} or
                        not any(op['callee_id']==callee and op['operation']=='operator=' for op in audited['operations'])):
                    raise ValueError('move assignment requires its pinned rvalue-reference vector callee')
                target_member(access['inner'][0],field,qualified,name)
                source_member(parts[1],field,parameter,qualified,name)
            plan.append(dict(kind='vector_move',element=element,callee_id=callee))
        else:
            if base not in TYPES:raise ValueError('move scalar fields require supported fixed-width types')
            if kind == 'assign':
                if (value.get('kind') != 'BinaryOperator' or value.get('opcode') != '=' or spelling(value) != ty or
                        value.get('valueCategory') != 'lvalue' or len(value.get('inner', [])) != 2):
                    raise ValueError('move scalar fields require declaration-ordered assignments')
                target_member(value['inner'][0],field,qualified,name)
                value = value['inner'][1]
            if (value.get('kind') != 'ImplicitCastExpr' or value.get('castKind') != 'LValueToRValue' or
                    spelling(value) != base or value.get('valueCategory') != 'prvalue' or len(value.get('inner', [])) != 1):
                raise ValueError('move scalar source requires a matching field load')
            source_member(value['inner'][0],field,parameter,qualified,name)
            plan.append(dict(kind='scalar_move',type=base))
        plan[-1].update(field_id=field['id'],name=field['name'],writable=not ty.startswith('const '))
    return dict(coverage='member_identity_only',source=str(source),**{'class':qualified},operation='move_'+kind,
                class_id=record['id'],member_id=member['id'],source_parameter_id=parameter['id'],fields=plan)


def audit_class_move(source, qualified, kind, include_dirs=()):
    record, roots = materialize_move(source,qualified,kind,include_dirs)
    return audit_move_record(source,qualified,record,roots,kind,include_dirs)


def emit_class_move_assignment(source, qualified, namespace='Proofs.Generated.ClassMoveAssignment', include_dirs=()):
    """Reaudit the implicit move assignment and emit its Context evaluator.

    Caller ObjectRef slots must still be connected to the original fields.
    Construction, const-rvalue copy fallback and other layouts remain separate.
    """
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', namespace):
        raise ValueError('invalid Lean namespace')
    source = Path(source).resolve(strict=True)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    plan = audit_class_move(source, qualified, 'assign', include_dirs)
    if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
        raise ValueError('move assignment source changed during generation')
    def ty(name):
        width, signed, boolean = TYPES[name]
        return lean_type(dict(width=width, signed=signed, boolean=boolean))
    vector, *scalars = plan['fields']
    scalar_profiles = ', '.join(f'({ty(field["type"])},true)' for field in scalars)
    names = ', '.join(json.dumps(field['name'], ensure_ascii=False) for field in plan['fields'])
    return '\n'.join([
        '-- Generated from audited implicit move assignment; caller field-slot layout remains an obligation.',
        'import Proofs.CppMoveClass', '', f'namespace {namespace}',
        'open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppClassCopy',
        f'def sourceSHA256 : String := "{digest}"', f'def fieldNames : List String := [{names}]',
        f'def profile : Profile := ⟨{ty(vector["element"])},true,[{scalar_profiles}]⟩',
        'def assign (s : Context) (target source : ObjectRef) :=',
        '  Proofs.CppMoveClass.assignClass s target source profile',
        'theorem result_target (s out : Context) (target source result : ObjectRef)',
        '    (run : assign s target source = some (out,result)) : result = target :=',
        '  (Proofs.CppMoveClass.assignClass_metadata s out target source result profile run).1',
        f'end {namespace}', ''])


def emit_class_move_construction(source, qualified, namespace='Proofs.Generated.ClassMoveConstruction', include_dirs=()):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', namespace):
        raise ValueError('invalid Lean namespace')
    include_dirs = tuple(include_dirs)
    source = Path(source).resolve(strict=True)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    record, roots = materialize_move(source, qualified, 'construct', include_dirs)
    plan = audit_move_record(source, qualified, record, roots, 'construct', include_dirs)
    if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
        raise ValueError('move construction source changed during generation')
    originals = {f['id']: f for f in record['inner'] if f.get('kind') == 'FieldDecl'}
    def ty(name):
        width, signed, boolean = TYPES[name]
        return lean_type(dict(width=width, signed=signed, boolean=boolean))
    def permission(field):
        declared = str(field['writable']).lower()
        mutable = str(bool(originals[field['field_id']].get('mutable'))).lower()
        return f'({declared} && (!targetConst || {mutable}))'
    vector, *scalars = plan['fields']
    scalar_profiles = ', '.join(f'({ty(field["type"])},{permission(field)})' for field in scalars)
    names = ', '.join(json.dumps(field['name'], ensure_ascii=False) for field in plan['fields'])
    return '\n'.join([
        '-- Generated from audited implicit move construction; caller field-slot layout remains an obligation.',
        'import Proofs.CppClassMoveConstruct', '', f'namespace {namespace}',
        'open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppClassCopy',
        f'def sourceSHA256 : String := "{digest}"', f'def fieldNames : List String := [{names}]',
        f'def profileFor (targetConst : Bool) : Profile := ⟨{ty(vector["element"])},{permission(vector)},[{scalar_profiles}]⟩',
        'def construct (s : Context) (source : ObjectRef) (targetConst : Bool) :=',
        '  Proofs.CppClassMoveConstruct.constructClass s source (profileFor targetConst)',
        f'end {namespace}', ''])
