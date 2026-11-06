"""Source-owned non-template records inside one implicit template instance.

The selected record, every nested primary, and the outer specialization are
linked by Clang declaration IDs in the same controlled translation unit.
This proves selection provenance, not generic types or full object lifetime.
"""
import hashlib
import json
from pathlib import Path
import re

from ast_stream import node_header, root_objects



def source_member_patterns(record, source):
    """IDs of generic member methods owned by the audited primary record."""
    patterns = {}
    for template in record.get('inner', []):
        if template.get('kind') != 'FunctionTemplateDecl':
            continue
        methods = [n for n in template.get('inner', []) if n.get('kind') == 'CXXMethodDecl'
                   and not any(c.get('kind') == 'TemplateArgument' for c in n.get('inner', []))]
        for method in methods:
            loc = method.get('loc', {})
            if (loc.get('includedFrom', {}).get('file') != '<built-in>' or 'offset' not in loc or
                    'spellingLoc' in loc or 'expansionLoc' in loc or
                    'file' in loc and Path(loc['file']).resolve() != Path(source).resolve()):
                raise ValueError('member template pattern must belong to original forced source')
            patterns.setdefault(template['name'], []).append(method['id'])
    return patterns


def select_nested_records(roots, source, requested, alias_namespace, witness):
    source, witness = Path(source).resolve(strict=True), Path(witness).resolve(strict=True)
    match = re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*(?:::[A-Za-z_][A-Za-z_0-9]*)*<[^<>]+>)((?:::[A-Za-z_][A-Za-z_0-9]*)+)', requested)
    if not match:
        raise ValueError('one template root and non-template nested path required')
    member_names = tuple(match[2].removeprefix('::').split('::'))
    records, parents, aliases, primaries = {}, {}, [], []

    def visit(node, parent=None, in_alias=False):
        if node.get('kind') == 'NamespaceDecl' and node.get('name') == alias_namespace:
            in_alias = True
        if in_alias and node.get('kind') == 'TypeAliasDecl' and node.get('name') == 'Selected':
            aliases.append(node)
        if (node.get('kind') in ('CXXRecordDecl','ClassTemplateSpecializationDecl')
                and node.get('completeDefinition')):
            identifier = node.get('id')
            if not identifier or identifier in records:
                raise ValueError('duplicate complete record identity')
            records[identifier], parents[identifier] = node, parent
            parent = identifier
        if node.get('kind') == 'ClassTemplateDecl':
            primaries.append(node)
        for child in node.get('inner', []):
            visit(child, parent, in_alias)

    for root in roots:
        visit(root)
    if len(aliases) != 1:
        raise ValueError('one controlled alias required')
    alias = aliases[0]
    loc = alias.get('loc', {})
    if (loc.get('includedFrom') or 'spellingLoc' in loc or 'expansionLoc' in loc or
            'offset' not in loc or 'file' in loc and Path(loc['file']).resolve() != witness):
        raise ValueError('alias must belong to controlled witness')
    references = []

    def refs(node):
        if node.get('kind') == 'RecordType':
            references.append(node)
        for child in node.get('inner', []):
            refs(child)

    refs(alias)
    if len(references) != 1:
        raise ValueError('one alias record reference required')
    reference = references[0]
    if reference.get('type', {}).get('qualType', '').removeprefix('::') != requested:
        raise ValueError('canonical nested record spelling mismatch')
    identifier = reference.get('decl', {}).get('id')
    if identifier not in records or records[identifier].get('kind') != 'CXXRecordDecl':
        raise ValueError('alias must select one complete non-template record')
    record = records[identifier]
    nested = []
    seen = set()
    while records[identifier]['kind'] != 'ClassTemplateSpecializationDecl':
        if identifier in seen:
            raise ValueError('record ownership cycle')
        seen.add(identifier)
        nested.append(records[identifier])
        identifier = parents[identifier]
        if identifier not in records:
            raise ValueError('nested record must belong to an instantiated template')
    nested.reverse()
    if tuple(n['name'] for n in nested) != member_names:
        raise ValueError('nested ownership path differs from requested members')
    outer = records[identifier]
    owners = [p for p in primaries if any(c.get('id') == identifier for c in p.get('inner', []))]
    if len(owners) != 1:
        raise ValueError('one owning primary required')
    owner = owners[0]
    expected_name = match[1].split('<',1)[0].split('::')[-1]
    if owner.get('name') != expected_name or outer.get('name') != expected_name:
        raise ValueError('outer record and owning primary must match requested root')
    generic = [n for n in owner.get('inner', []) if n.get('kind') == 'CXXRecordDecl' and n.get('completeDefinition')]
    if len(generic) != 1 or outer.get('TemplateInstantiationPattern') != generic[0]['id']:
        raise ValueError('outer instance must derive from its owning primary record')
    pattern = generic[0]
    audited = [owner, outer, pattern]
    pairs = []
    for actual in nested:
        patterns = [n for n in pattern.get('inner', [])
                    if n.get('id') == actual.get('TemplateInstantiationPattern') and
                    n.get('kind') == 'CXXRecordDecl' and n.get('completeDefinition')]
        if len(patterns) != 1 or patterns[0]['name'] != actual['name']:
            raise ValueError('nested instance must derive from the corresponding primary member')
        pattern = patterns[0]
        audited.extend([actual, pattern])
        pairs.append(dict(record_id=actual['id'], pattern_id=pattern['id']))
    for node in audited:
        loc = node.get('loc', {})
        if (loc.get('includedFrom', {}).get('file') != '<built-in>' or
                'offset' not in loc or 'spellingLoc' in loc or 'expansionLoc' in loc or
                'file' in loc and Path(loc['file']).resolve() != source):
            raise ValueError('all selected definitions must belong to original forced source')
    record['_template_witness_origin'] = dict(source=str(source),
        source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(), requested=requested,
        alias_id=alias['id'], primary_id=owner['id'], outer_record_id=outer['id'],
        record_id=record['id'], nested_members=list(member_names), nested_patterns=pairs,
        member_template_patterns=source_member_patterns(pattern, source))
    return [record]


def collect_nested_template_record(stream, source, requested, alias_namespace, witness):
    first = requested.split('<',1)[0].split('::')[0]
    roots = [json.loads(raw) for raw in root_objects(stream)
             if node_header(raw).get('name') in {first,alias_namespace}]
    return select_nested_records(roots, source, requested, alias_namespace, witness)
