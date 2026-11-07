"""Finite scalar class-template instances lowered from unchanged C++ sources.

This entry does not model general object lifetime or prove generic templates.
The returned coverage describes the concrete instance and selected members.
"""
import hashlib
from pathlib import Path

from ast_stream import _display_name, _function_class_name
from class_templates import TemplateInstance, instantiate_members, require_method_bodies
from class_lowering import ErasedClass, build_functions, erase_functions, selected_type_pattern
from class_split import SplitClass, split_functions
from inline_ast import inline_functions
from nested_ir import NestedBody, ValueCalls, apply_conversion_policy
from vector_bindings import bindings_from_audit
from vector_stl import audit_vector_nodes, translation_unit
from mixed_scalar_functions import mixed_scalar_functions


def lower_template_class(source, qualified, instance, include_dirs=(), *,
                         member_instances=None, signed_conversion='checked', companion_instances=()):
    if not isinstance(instance, TemplateInstance):
        raise ValueError('a structured template instance is required')
    source = Path(source).resolve(strict=True)
    include_dirs = tuple(include_dirs)
    before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in (source, instance.witness)}
    records, callees = [], []
    _, standard = translation_unit(source, include_dirs, callees=callees,
        copy_class=qualified, copy_records=records, template_instance=instance,
        companion_instances=companion_instances)
    if len(records) != 1+len(companion_instances):
        raise ValueError('one source-owned class template instance per request required')
    record, ledger = instantiate_members(records[0], {} if member_instances is None else member_instances,
        record_arguments=records)
    require_method_bodies(record)
    fields = [node for node in record.get('inner', []) if node.get('kind') == 'FieldDecl']
    friends = [node for node in record.get('inner', []) if node.get('kind') == 'FriendDecl']
    if companion_instances:
        functions = mixed_scalar_functions([record, *records[1:]], source)
    elif len(fields) == 1:
        cls = ErasedClass(record, _function_class_name(record), _display_name(record))
        functions = erase_functions([cls], build_functions(cls, source, friends))
    elif len(fields) > 1:
        cls = SplitClass(record, _function_class_name(record), _display_name(record))
        functions = split_functions([cls], source, {id(cls): friends})
    else:
        raise ValueError('scalar template instance requires at least one field')
    functions = inline_functions(functions, callees)
    if not functions:
        raise ValueError('template instance produced no models')
    audited = audit_vector_nodes(source, functions, standard, include_dirs)
    schemas = bindings_from_audit(source, audited, include_dirs)['functions']
    apply_conversion_policy([*audited['functions'], *callees], signed_conversion)
    calls, programs, used = ValueCalls(callees), [], {}
    for node, schema in zip(audited['functions'], schemas, strict=True):
        body = NestedBody(node, schema, calls, source)
        program = body.lower()
        if body.probes:
            # A header-only probe would lose the controlled instantiation and
            # could validate a different type. Require same-context support.
            raise ValueError('template type probes require the same instantiation context')
        program['parameters'] = schema['parameters']
        programs.append(program)
        used.update(body.callees)
    for path, digest in before.items():
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError('template source or instantiation witness changed during lowering')
    ir = dict(coverage='nested_control_flow',
              callees=[used[name] for name in sorted(used)], functions=programs)
    if signed_conversion != 'checked':
        ir['signed_conversion'] = signed_conversion
    coverage = dict(kind='finite_scalar_template_instance',
        source_sha256=before[source], witness_sha256=before[instance.witness],
        qualified_class=qualified, arguments=list(instance.arguments),
        member_instances=[dict(source_name=item['source_name'], type_arguments=item['type_arguments'])
                          for item in ledger], models=[p['name'] for p in programs],
        generic_types_verified=False, full_cpp_object_lifetime_verified=False)
    origin = record.get('_template_witness_origin', {})
    if origin.get('nested_members'):
        coverage['nested_members'] = list(origin['nested_members'])
        coverage['selected_type'] = origin['requested']
    if companion_instances:
        coverage['companions'] = [dict(qualified_class=q, arguments=list(i.arguments),
            nested_members=list(i.nested_members), selected_type=i.target(q)) for q, i in companion_instances]
    return ir, coverage
