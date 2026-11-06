"""Source-owned implicit class template instances in a controlled Clang TU.

Selecting an instance proves provenance only. Callers must separately check
that all requested method bodies were instantiated and lower every such body.
"""
from dataclasses import dataclass
import copy
import hashlib
import json
from pathlib import Path
import re

from ast_stream import node_header, root_objects
from scalar_ir import TYPES


@dataclass(frozen=True)
class TemplateInstance:
    arguments: tuple[str, ...]
    witness: Path

    def __post_init__(self):
        if (not isinstance(self.arguments, tuple) or not self.arguments or
                any(not isinstance(arg, str) or
                    not (arg in TYPES or re.fullmatch(r'0|[1-9][0-9]*', arg))
                    for arg in self.arguments)):
            raise ValueError('template arguments must be primitive types or decimal integers')
        path = Path(self.witness).resolve(strict=True)
        if not path.is_file() or any(c in str(path) for c in ('"', '\n', '\r', '\\')):
            raise ValueError('template witness requires a regular file with a safe include path')
        object.__setattr__(self, 'witness', path)

    def target(self, qualified):
        if not isinstance(qualified, str) or not re.fullmatch(
                r'[A-Za-z_][A-Za-z_0-9]*(?:::[A-Za-z_][A-Za-z_0-9]*)*', qualified):
            raise ValueError('template class requires a qualified identifier')
        return qualified + '<' + ', '.join(self.arguments) + '>'


def collect_template_record(stream, source, requested, alias_namespace, witness):
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
    record['_template_witness_origin'] = dict(
        source=str(source), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        requested=requested, alias_id=alias['id'], primary_id=owners[0]['id'], record_id=record['id'])
    return [record]


def instantiate_members(record, requested):
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
                    any(not isinstance(arg, str) or arg not in TYPES for arg in args)):
                raise ValueError('primitive concrete member type arguments required')
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
        for args in requested[name]:
            child = variants.get(args)
            if child is None:
                raise ValueError('requested member specialization is not instantiated')
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
