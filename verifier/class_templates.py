"""Source-owned implicit class template instances in a controlled Clang TU.

Selecting an instance proves provenance only. Callers must separately check
that all requested method bodies were instantiated and lower every such body.
"""
from dataclasses import dataclass, field
import copy
import hashlib
import json
from pathlib import Path
import re

from ast_stream import node_header, root_objects
from scalar_ir import TYPES
from nested_templates import collect_nested_template_record, source_member_patterns


@dataclass(frozen=True)
class TemplateInstance:
    arguments: tuple[str, ...]
    witness: Path
    nested_members: tuple[str, ...] = field(default=(), kw_only=True)

    def __post_init__(self):
        if (not isinstance(self.arguments, tuple) or not self.arguments or
                any(not isinstance(arg, str) or
                    not (arg in TYPES or re.fullmatch(r'0|[1-9][0-9]*', arg))
                    for arg in self.arguments)):
            raise ValueError('template arguments must be primitive types or decimal integers')
        if (not isinstance(self.nested_members, tuple) or
                any(not isinstance(n, str) or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', n)
                    for n in self.nested_members)):
            raise ValueError('nested members must be a tuple of identifiers')
        path = Path(self.witness).resolve(strict=True)
        if not path.is_file() or any(c in str(path) for c in ('"', '\n', '\r', '\\')):
            raise ValueError('template witness requires a regular file with a safe include path')
        object.__setattr__(self, 'witness', path)

    def target(self, qualified):
        if not isinstance(qualified, str) or not re.fullmatch(
                r'[A-Za-z_][A-Za-z_0-9]*(?:::[A-Za-z_][A-Za-z_0-9]*)*', qualified):
            raise ValueError('template class requires a qualified identifier')
        target = qualified + '<' + ', '.join(self.arguments) + '>'
        return target + ('::'+'::'.join(self.nested_members) if self.nested_members else '')


def collect_template_record(stream, source, requested, alias_namespace, witness):
    if '>::' in requested:
        return collect_nested_template_record(stream, source, requested, alias_namespace, witness)
    source = Path(source).resolve(strict=True)
    witness = Path(witness).resolve(strict=True)
    first = requested.split('<', 1)[0].split('::')[0]
    records, aliases, primaries = {}, [], []

    def visit(node, in_alias=False):
        if node.get('kind') == 'NamespaceDecl' and node.get('name') == alias_namespace:
            in_alias = True
        if in_alias and node.get('kind') == 'TypeAliasDecl' and node.get('name') == 'Selected':
            aliases.append(node)
        if node.get('kind') == 'ClassTemplateSpecializationDecl' and node.get('completeDefinition'):
            records[node['id']] = node
        if node.get('kind') == 'ClassTemplateDecl':
            primaries.append(node)
        for child in node.get('inner', []):
            visit(child, in_alias)

    for raw in root_objects(stream):
        if node_header(raw).get('name') in {first, alias_namespace}:
            visit(json.loads(raw))
    if len(aliases) != 1:
        raise ValueError('one controlled template alias required')
    alias = aliases[0]
    loc = alias.get('loc', {})
    if (loc.get('includedFrom') or 'spellingLoc' in loc or 'expansionLoc' in loc or
            'offset' not in loc or 'file' in loc and Path(loc['file']).resolve() != witness):
        raise ValueError('template alias must belong to controlled witness')
    refs = []

    def reference(node):
        if node.get('kind') == 'RecordType':
            refs.append(node.get('decl', {}).get('id'))
        for child in node.get('inner', []):
            reference(child)

    reference(alias)
    if len(refs) != 1 or refs[0] not in records:
        raise ValueError('template alias must identify one complete specialization')
    record = records[refs[0]]
    owners = [p for p in primaries
              if any(c.get('id') == record['id'] for c in p.get('inner', []))]
    if len(owners) != 1:
        raise ValueError('specialization must belong to one primary template')
    for node in (owners[0], record):
        loc = node.get('loc', {})
        if (loc.get('includedFrom', {}).get('file') != '<built-in>' or
                'offset' not in loc or 'spellingLoc' in loc or 'expansionLoc' in loc or
                'file' in loc and Path(loc['file']).resolve() != source):
            raise ValueError('template and implicit specialization must belong to original forced source')
    if alias.get('type', {}).get('desugaredQualType', '').removeprefix('::') != requested:
        raise ValueError('canonical requested specialization mismatch')
    generic = [n for n in owners[0].get('inner', [])
               if n.get('kind') == 'CXXRecordDecl' and n.get('completeDefinition')]
    if len(generic) != 1:
        raise ValueError('one source-owned primary template record required')
    record['_template_witness_origin'] = dict(
        source=str(source), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        requested=requested, alias_id=alias['id'], primary_id=owners[0]['id'], record_id=record['id'],
        member_template_patterns=source_member_patterns(generic[0], source))
    return [record]


@dataclass(frozen=True)
class RecordArgument:
    """An index into records selected and audited in the same Clang TU."""
    index: int

    def __post_init__(self):
        if type(self.index) is not int or self.index < 0:
            raise ValueError('record argument requires a nonnegative record index')


def instantiate_members(record, requested, *, record_arguments=()):
    """Select explicit compiler-produced instances, preserving IDs and bodies.

    Model names are separate from the original C++ names. The returned ledger
    records finite coverage; it never claims verification for arbitrary types.
    """
    if not isinstance(requested, dict):
        raise ValueError('member instance request must be a map')
    for name, instances in requested.items():
        if (not isinstance(name, str) or not isinstance(instances, (list, tuple)) or
                not instances):
            raise ValueError('at least one concrete instance per member template required')
        for args in instances:
            if (not isinstance(args, tuple) or not args or
                    any(not isinstance(arg, RecordArgument) and (not isinstance(arg, str) or arg not in TYPES) for arg in args)):
                raise ValueError('primitive concrete member type arguments required')
    def concrete(argument):
        if not isinstance(argument, RecordArgument):
            return argument, None
        if argument.index >= len(record_arguments):
            raise ValueError('record argument is outside the selected context')
        selected = record_arguments[argument.index]
        origin = selected.get('_template_witness_origin', {})
        if (not origin.get('requested') or selected.get('id') != origin.get('record_id') or
                not record.get('_copy_translation_unit') or
                selected.get('_copy_translation_unit') != record['_copy_translation_unit'] or
                not record.get('_copy_source_sha256') or
                selected.get('_copy_source_sha256') != record['_copy_source_sha256'] or
                origin.get('source_sha256') != record['_copy_source_sha256'] or
                selected.get('_copy_source') != record.get('_copy_source') or
                origin.get('source') != record.get('_copy_source')):
            raise ValueError('record argument must be selected in the same audited translation unit')
        return origin['requested'], selected['id']

    for instances in requested.values():
        for args in instances:
            for arg in args:
                concrete(arg)
    result = copy.deepcopy(record)
    seen, ledger, rewritten = set(), [], []
    names = {n.get('name') for n in record.get('inner', []) if n.get('kind') == 'CXXMethodDecl'}
    for node in result.get('inner', []):
        if node.get('kind') != 'FunctionTemplateDecl':
            rewritten.append(node)
            continue
        name = node.get('name')
        if name not in requested:
            raise ValueError('member template needs explicit requested instances')
        if name in seen:
            raise ValueError('overloaded member template requests are unsupported')
        variants = {}
        for child in node.get('inner', []):
            if child.get('kind') != 'CXXMethodDecl':
                continue
            arguments = [a for a in child.get('inner', []) if a.get('kind') == 'TemplateArgument']
            if not arguments or not any(c.get('kind') == 'CompoundStmt' for c in child.get('inner', [])):
                continue
            types = tuple(a.get('type', {}).get('desugaredQualType', a.get('type', {}).get('qualType'))
                          for a in arguments)
            if types in variants:
                raise ValueError('duplicate concrete member template body')
            variants[types] = child
        for requested_args in requested[name]:
            resolved = [concrete(arg) for arg in requested_args]
            args = tuple(ty for ty, _ in resolved)
            child = variants.get(args)
            if child is None:
                raise ValueError('requested member specialization is not instantiated')
            origin = record.get('_template_witness_origin', {})
            loc = child.get('loc', {})
            if (child.get('TemplateInstantiationPattern') not in
                    origin.get('member_template_patterns', {}).get(name, []) or
                    loc.get('includedFrom', {}).get('file') != '<built-in>' or 'offset' not in loc or
                    'spellingLoc' in loc or 'expansionLoc' in loc or
                    'file' in loc and Path(loc['file']).resolve() != Path(origin['source']).resolve()):
                raise ValueError('member specialization must derive from the original source pattern')
            actual_args = [a for a in child.get('inner', []) if a.get('kind') == 'TemplateArgument']
            for actual, (spelling, identifier) in zip(actual_args, resolved, strict=True):
                if identifier is None:
                    continue
                refs = actual.get('inner', [])
                if (len(refs) != 1 or refs[0].get('kind') != 'RecordType' or
                        refs[0].get('decl', {}).get('id') != identifier or
                        refs[0].get('type', {}).get('qualType') != spelling):
                    raise ValueError('member record type argument must match its selected declaration ID')
            method = copy.deepcopy(child)
            model_name = name + '__template_' + '_'.join(re.sub(r'[^A-Za-z0-9_]', '_', a) for a in args)
            if model_name in names:
                raise ValueError('member model name collision')
            names.add(model_name)
            method['name'] = model_name
            method['inner'] = [c for c in method['inner'] if c.get('kind') != 'TemplateArgument']
            method['_member_template_instance'] = dict(
                source_name=name, type_arguments=list(args), declaration_id=child['id'])
            rewritten.append(method)
            ledger.append(method['_member_template_instance'])
        seen.add(name)
    if seen != set(requested):
        raise ValueError('requested member template does not exist')
    result['inner'] = rewritten
    return result, ledger


def require_method_bodies(record):
    """Reject incomplete materialization before a lowering can skip methods."""
    for node in record.get('inner', []):
        if node.get('kind') == 'FunctionTemplateDecl' or any(
                c.get('kind') == 'FunctionTemplateDecl' for c in node.get('inner', [])):
            raise ValueError('member template needs explicit requested instances')
        if (node.get('kind') in {'CXXConstructorDecl', 'CXXMethodDecl', 'CXXDestructorDecl', 'CXXConversionDecl'}
                and not node.get('isImplicit')
                and not any(c.get('kind') == 'CompoundStmt' for c in node.get('inner', []))):
            raise ValueError('requested class method body is not instantiated: ' + node.get('name', ''))
