"""Audit implicit class destruction identities and reverse member lifetime order.

The plan identifies original declarations; caller/body lowering is separate.
An implicit destructor's empty CompoundStmt does not omit member destruction.
"""
from pathlib import Path
import subprocess

from class_copy import audit_class_fields, original_location, spelling
from scalar_ir import TYPES
from vector_stl import translation_unit, audit_vector_nodes, vector_declarations


def materialize_destroy(source, qualified, include_dirs=()):
    records = []
    try:
        _, roots = translation_unit(source, include_dirs, copy_class=qualified, copy_records=records,
                                    class_destruction=True)
    except subprocess.CalledProcessError as error:
        raise ValueError('destruction witness must compile without access overrides') from error
    if len(records) != 1:
        raise ValueError('exactly one original destruction class required')
    records[0]['_copy_qualified'] = qualified
    return records[0], roots


def audit_destroy_record(source, qualified, record, roots, include_dirs=()):
    source = Path(source).resolve(strict=True)
    fields = audit_class_fields(source, qualified, record, roots)
    positions = [field['loc']['offset'] for field in fields]
    if (any(type(position) is not int or position < 0 for position in positions) or
            any(left >= right for left, right in zip(positions, positions[1:]))):
        raise ValueError('destruction fields must retain their original declaration order')
    destructors = [n for n in record.get('inner', []) if n.get('kind') == 'CXXDestructorDecl']
    if len(destructors) != 1:
        raise ValueError('exactly one original implicit destructor required')
    destructor = destructors[0]
    scalar_only = all(spelling(field).removeprefix('const ') in TYPES for field in fields)
    trivial = scalar_only and record.get('definitionData', {}).get('dtor', {}).get('trivial') is True
    referenced_trivial = trivial and destructor.get('isReferenced') is True
    if (not destructor.get('id') or not destructor.get('isImplicit') or
            not (destructor.get('isUsed') or referenced_trivial) or
            destructor.get('name') != '~'+record['name'] or destructor.get('explicitlyDefaulted') != 'default' or
            destructor.get('isDeleted') or destructor.get('explicitlyDeleted') or destructor.get('virtual') or
            destructor.get('pure') or not original_location(destructor, source) or
            destructor['loc']['offset'] != record['loc']['offset'] or
            spelling(destructor) not in ('void () noexcept','void () noexcept(true)')):
        raise ValueError('destructor must be the used implicit defaulted nonthrowing declaration')
    children = destructor.get('inner', [])
    if not (trivial and not children) and (
            len(children) != 1 or children[0].get('kind') != 'CompoundStmt' or children[0].get('inner')):
        raise ValueError('implicit destructor requires an empty original body')

    # Check the pinned primary, same-TU instance patterns and used helpers.
    # STL internals remain a contract; no scan of the class body substitutes
    # for the implicit destruction of its fields.
    audit_vector_nodes(source, [], roots, include_dirs)
    primary, instances = vector_declarations(roots)
    primary_destructors = [n for n in primary.get('inner', []) if n.get('kind') == 'CXXDestructorDecl']
    if len(primary_destructors) != 1 or not primary_destructors[0].get('id'):
        raise ValueError('one pinned vector destructor pattern required')
    pattern = primary_destructors[0]['id']
    vector_types = {}
    for instance in instances:
        arguments = [n.get('type', {}).get('qualType') for n in instance.get('inner', [])
                     if n.get('kind') == 'TemplateArgument']
        if (instance.get('TemplateInstantiationPattern') == primary['id'] and len(arguments) == 2 and
                arguments[0] in TYPES and arguments[0] != 'bool' and
                arguments[1] == f'std::allocator<{arguments[0]}>'):
            vector_types.setdefault(f'std::vector<{arguments[0]}>', []).append((instance, arguments[0]))

    plan = []
    for field in reversed(fields):
        ty = spelling(field).removeprefix('const ')
        if ty in TYPES:
            action = dict(kind='scalar_lifetime_end', type=ty)
        else:
            matches = vector_types.get(ty, [])
            if len(matches) != 1:
                raise ValueError('destruction field needs a supported scalar or pinned flat scalar vector')
            instance, element = matches[0]
            selected = [n for n in instance.get('inner', []) if n.get('kind') == 'CXXDestructorDecl']
            if len(selected) != 1:
                raise ValueError('one vector destructor instance required')
            selected = selected[0]
            if (not selected.get('id') or selected.get('TemplateInstantiationPattern') != pattern or
                    not selected.get('isUsed') or selected.get('name') != '~vector' or selected.get('isDeleted') or
                    selected.get('explicitlyDeleted') or selected.get('virtual') or
                    spelling(selected) not in ('void () noexcept','void () noexcept(true)') or
                    len(selected.get('inner', [])) != 1 or selected['inner'][0].get('kind') != 'CompoundStmt'):
                raise ValueError('field requires the used pinned nonthrowing vector destructor')
            action = dict(kind='vector_destroy', element=element, callee_id=selected['id'],
                          vector_id=instance['id'])
        action.update(field_id=field['id'], name=field['name'])
        plan.append(action)
    return dict(coverage='member_identity_only', source=str(source), **{'class': qualified}, operation='destroy',
                class_id=record['id'], member_id=destructor['id'], fields=plan)


def audit_class_destroy(source, qualified, include_dirs=()):
    record, roots = materialize_destroy(source, qualified, include_dirs)
    return audit_destroy_record(source, qualified, record, roots, include_dirs)
