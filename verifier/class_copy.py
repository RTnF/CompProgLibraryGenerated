"""Audit an instantiated implicit class copy; execution lowering remains separate.

The default execution profile is a flat scalar vector followed by scalar fields.
The member-call audit can explicitly accept multiple declaration-ordered vectors.
Field
names and class names do not choose translation rules. Declaration identities
and the pinned standard vector copy constructor are checked in one dump.
"""
from pathlib import Path
import subprocess
import hashlib
import json
import re

from scalar_ir import TYPES, lean_type
from vector_stl import translation_unit, audit_vector_nodes


def spelling(node):
    ty = node.get('type', {})
    return ty.get('desugaredQualType', ty.get('qualType', ''))


def original_location(node, source):
    loc = node.get('loc', {})
    return (loc.get('includedFrom', {}).get('file') == '<built-in>' and
            'offset' in loc and 'spellingLoc' not in loc and 'expansionLoc' not in loc and
            ('file' not in loc or Path(loc['file']).resolve() == Path(source).resolve()))


def materialize_copy(source, qualified, include_dirs=()):
    records = []
    try:
        _, roots = translation_unit(source, include_dirs, copy_class=qualified, copy_records=records)
    except subprocess.CalledProcessError as error:
        raise ValueError('class copy witness must compile without access overrides') from error
    if len(records) != 1:
        raise ValueError('exactly one original class definition required')
    records[0]['_copy_qualified'] = qualified
    return records[0], roots


def source_member(node, field, parameter):
    # A mutable vector field acquires const qualification when passed to the
    # vector copy constructor. The implicit class copy still reads that field.
    if node.get('kind') == 'ImplicitCastExpr' and node.get('castKind') == 'NoOp':
        if not field.get('mutable') or len(node.get('inner', [])) != 1:
            raise ValueError('unexpected copy source qualification cast')
        node = node['inner'][0]
    expected = spelling(field)
    if not expected.startswith('const ') and not field.get('mutable'):
        expected = 'const ' + expected
    if (node.get('kind') != 'MemberExpr' or node.get('referencedMemberDecl') != field['id'] or
            node.get('name') != field['name'] or node.get('isArrow') is not False or
            node.get('valueCategory') != 'lvalue' or spelling(node) != expected or
            len(node.get('inner', [])) != 1):
        raise ValueError('copy initializer must read the matching source member by identity')
    origin = node['inner'][0]
    reference = origin.get('referencedDecl', {})
    if (origin.get('kind') != 'DeclRefExpr' or reference.get('kind') != 'ParmVarDecl' or
            reference.get('id') != parameter['id'] or spelling(reference) != spelling(parameter) or
            origin.get('valueCategory') != 'lvalue' or
            spelling(origin) != spelling(parameter).removesuffix(' &')):
        raise ValueError('copy member must belong to the const source parameter')


def audit_class_fields(source, qualified, record, roots):
    source = Path(source).resolve(strict=True)
    dump_id = record.get('_copy_translation_unit')
    if not dump_id or not roots or any(root.get('_copy_translation_unit') != dump_id for root in roots):
        raise ValueError('class copy and standard declarations must come from the same translation unit')
    if record.get('_copy_qualified') != qualified:
        raise ValueError('copy audit qualified class identity changed')
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    if any(node.get('_copy_source') != str(source) or node.get('_copy_source_sha256') != digest
           for node in [record, *roots]):
        raise ValueError('copy audit source identity or contents changed')
    if (record.get('kind') != 'CXXRecordDecl' or not record.get('completeDefinition') or
            not record.get('id') or
            record.get('tagUsed') not in ('class', 'struct') or not original_location(record, source) or
            record.get('name') != qualified.split('::')[-1] or record.get('bases') or
            record.get('definitionData', {}).get('isPolymorphic') or
            any(n.get('virtual') or n.get('kind', '').endswith('Attr') for n in record.get('inner', []))):
        raise ValueError('copy profile requires an original nonpolymorphic class without bases or attributes')
    if any(n.get('kind') == 'CXXDestructorDecl' and not n.get('isImplicit') for n in record.get('inner', [])):
        raise ValueError('user-declared destructors require a separate lifetime model')
    fields = [n for n in record.get('inner', []) if n.get('kind') == 'FieldDecl']
    if (not fields or len({f.get('id') for f in fields}) != len(fields) or
            any(not f.get('id') or not original_location(f, source) or f.get('isBitfield') or
                'volatile' in spelling(f).split() or
                any(c.get('kind', '').endswith('Attr') for c in f.get('inner', [])) for f in fields)):
        raise ValueError('copy fields must be distinct original addressable nonvolatile declarations')
    return fields


def audit_copy_record(source, qualified, record, roots, include_dirs=(), *, vector_anywhere=False,
                      multiple_vectors=False):
    # Method receivers can normalize field parameters; legacy copy execution
    # profiles still require one vector. The multi-member path audits identities
    # here without claiming a generated class-copy execution model.
    if not isinstance(multiple_vectors, bool) or (multiple_vectors and not vector_anywhere):
        raise ValueError('multiple vector audit requires declaration-based vector classification')
    source = Path(source).resolve(strict=True)
    fields = audit_class_fields(source, qualified, record, roots)
    candidates = []
    for node in record.get('inner', []):
        parameters = [c for c in node.get('inner', []) if c.get('kind') == 'ParmVarDecl']
        if (node.get('kind') == 'CXXConstructorDecl' and len(parameters) == 1 and
                spelling(parameters[0]) in {f'const {record["name"]} &', f'const {qualified} &'}):
            candidates.append((node, parameters[0]))
    if len(candidates) != 1:
        raise ValueError('exactly one const-reference copy constructor required')
    constructor, parameter = candidates[0]
    if (not constructor.get('isImplicit') or not constructor.get('isUsed') or
            constructor.get('name') != record['name'] or not constructor.get('id') or
            constructor.get('explicitlyDefaulted') != 'default' or constructor.get('isDeleted') or
            constructor.get('explicitlyDeleted') or not original_location(constructor, source) or
            not parameter.get('id') or not original_location(parameter, source)):
        raise ValueError('copy constructor must be the used implicit defaulted declaration')
    children = constructor.get('inner', [])
    bodies = [n for n in children if n.get('kind') == 'CompoundStmt']
    initializers = [n for n in children if n.get('kind') == 'CXXCtorInitializer']
    if (len(bodies) != 1 or bodies[0].get('inner') or len(initializers) != len(fields) or
            any(n.get('kind') not in ('ParmVarDecl', 'CXXCtorInitializer', 'CompoundStmt') for n in children)):
        raise ValueError('implicit copy needs ordered member initializers and an empty body')
    # This shared audit clears constructor markers and checks standard primary,
    # allocator and used helper identities before granting the copy marker.
    audit_vector_nodes(source, [constructor], roots, include_dirs)
    plan = []
    for position, (field, initializer) in enumerate(zip(fields, initializers)):
        target = initializer.get('anyInit', {})
        expressions = initializer.get('inner', [])
        if (target.get('kind') != 'FieldDecl' or target.get('id') != field['id'] or
                target.get('name') != field['name'] or spelling(target) != spelling(field) or len(expressions) != 1):
            raise ValueError('copy member initialization must follow declaration identities and order')
        expr = expressions[0]
        ty = spelling(field).removeprefix('const ')
        if (ty.startswith('std::vector<') if vector_anywhere else position == 0):
            element = expr.get('verifiedVectorElement')
            if (expr.get('kind') != 'CXXConstructExpr' or expr.get('verifiedVectorConstructor') != 'copy' or
                    not expr.get('verifiedVectorConstructorDecl') or element not in TYPES or element == 'bool' or
                    ty != f'std::vector<{element}>' or len(expr.get('inner', [])) != 1):
                raise ValueError('first copy field requires the audited flat scalar vector copy constructor')
            source_member(expr['inner'][0], field, parameter)
            action = {'kind': 'vector_copy', 'element': element, 'constructor_id': expr['verifiedVectorConstructorDecl']}
        else:
            if (ty not in TYPES or expr.get('kind') != 'ImplicitCastExpr' or expr.get('castKind') != 'LValueToRValue' or
                    spelling(expr) != ty or len(expr.get('inner', [])) != 1):
                raise ValueError('remaining copy fields require scalar source loads')
            source_member(expr['inner'][0], field, parameter)
            action = {'kind': 'scalar_copy', 'type': ty}
        plan.append(dict(action, field_id=field['id'], name=field['name'], writable=not spelling(field).startswith('const ')))
    if not multiple_vectors and sum(f['kind'] == 'vector_copy' for f in plan) != 1:
        raise ValueError('exactly one flat vector field required')
    return {'coverage': 'member_identity_only', 'source': str(source), 'class': qualified,
            'class_id': record['id'], 'constructor_id': constructor['id'], 'source_parameter_id': parameter['id'],
            'fields': plan}


def audit_class_copy(source, qualified, include_dirs=()):
    record, roots = materialize_copy(source, qualified, include_dirs)
    return audit_copy_record(source, qualified, record, roots, include_dirs)


def emit_class_copy(source, qualified, namespace='Proofs.Generated.ClassCopy', include_dirs=()):
    """Reaudit source and emit its direct evaluator profile, not a call-site layout.

    Declaration IDs are local audit evidence and are not stable generated names.
    Field names are ordered metadata; the caller must establish ObjectRef slots.
    """
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', namespace):
        raise ValueError('invalid Lean namespace')
    source = Path(source).resolve(strict=True)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    plan = audit_class_copy(source, qualified, include_dirs)
    if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
        raise ValueError('copy source changed during generation')

    def ty(spelling):
        width, signed, boolean = TYPES[spelling]
        return lean_type(dict(width=width, signed=signed, boolean=boolean))

    def flag(field):
        return str(field['writable']).lower()

    vector, *scalars = plan['fields']
    scalar_profiles = ', '.join(f"({ty(f['type'])}, {flag(f)})" for f in scalars)
    names = ', '.join(json.dumps(f['name']) for f in plan['fields'])
    return '\n'.join([
        '-- Generated from the audited implicit member copy; call-site layout remains an obligation.',
        'import Proofs.CppClassCopy', '', f'namespace {namespace}',
        'open Proofs.CppClassCopy Proofs.CppNestedProgram Proofs.CppConstructorFinish', '',
        f'def qualifiedClass : String := {json.dumps(qualified)}',
        f'def sourceSHA256 : String := {json.dumps(digest)}',
        f'def fieldNames : List String := [{names}]',
        f'def profile : Profile := ⟨{ty(vector["element"])}, {flag(vector)}, [{scalar_profiles}]⟩',
        'def copy (state : NState) (source : ObjectRef) : Option (NState × ObjectRef) :=',
        '  copyClass state source profile', '', f'end {namespace}', ''])
