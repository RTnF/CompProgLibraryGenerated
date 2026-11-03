"""Generate constructor exports and non-resizing methods from one class source.

The result records the common source digest. Copy profiles and constructor
exports retain their existing evaluator; method calls use the Context evaluator.
The opt-in member_exports path uses multi-member NState construction and calls.
Assignment, move construction, destruction and arbitrary call sites are separate.
"""
import hashlib
import json
import re
from pathlib import Path

from class_copy_layout import emit_class_layout
from context_method_ir import emit_context_methods, emit_member_methods


def emit_context_class(source, qualified, namespace='Proofs.Generated.ContextClass',
                       include_dirs=(), signed_conversion='checked', *, member_exports=False):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', namespace):
        raise ValueError('invalid Lean namespace')
    source = Path(source).resolve(strict=True)
    include_dirs = tuple(include_dirs)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    if not isinstance(member_exports, bool):
        raise ValueError('member_exports must be boolean')
    if member_exports:
        parts = [emit_class_layout(source, qualified, namespace+'.Construction', include_dirs,
                                   signed_conversion, member_exports=True),
                 emit_member_methods(source, qualified, namespace+'.Calls', include_dirs, signed_conversion)]
    else:
        parts = [
            emit_class_layout(source, qualified, namespace+'.Construction', include_dirs, signed_conversion),
            emit_context_methods(source, qualified, namespace+'.Calls', include_dirs, signed_conversion, strict_declarations=True),
        ]
    marker = f'def sourceSHA256 : String := {json.dumps(digest)}'
    if (hashlib.sha256(source.read_bytes()).hexdigest() != digest
            or any(marker not in part.splitlines() for part in parts)):
        raise ValueError('class source changed between constructor and method generation')
    imports, bodies = [], []
    for part in parts:
        for line in part.splitlines():
            if line.startswith('import '):
                if line not in imports:
                    imports.append(line)
            else:
                bodies.append(line)
    return '\n'.join([
        '-- Generated constructor layouts and all nonstatic method receivers from the audited class.',
        *imports, '', *bodies, '', f'namespace {namespace}',
        f'def qualifiedClass : String := {json.dumps(qualified)}',
        marker,
        'theorem construction_source : Construction.sourceSHA256 = sourceSHA256 := rfl',
        'theorem method_source : Calls.sourceSHA256 = sourceSHA256 := rfl',
        f'end {namespace}', '',
    ])
