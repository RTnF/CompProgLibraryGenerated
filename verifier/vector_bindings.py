"""Generate parameter binding schemas from the audited vector AST.

This emits binding metadata, not a model of the function body. Body lowering
must consume the same audited nodes and compose scalar and object state.
"""
import re
import json
from pathlib import Path
import subprocess
import tempfile
from clang_ast import clang_command,ROOT
from scalar_ir import TYPES, lean_type
from state_ir import parameter_type
from vector_stl import audit_vector_operations


def lower_bindings(source, include_dirs=()):
    return bindings_from_audit(source,audit_vector_operations(source,include_dirs),include_dirs)


def bindings_from_audit(source, audited, include_dirs=()):
    """Consume declarations and operation IDs from one audited compiler AST."""
    functions=[]
    probes=[]
    for function in audited['functions']:
        if function.get('kind')!='FunctionDecl':
            raise ValueError('vector binding schemas require concrete ordinary functions')
        parameters=[]
        for parameter in function.get('inner',[]):
            if parameter.get('kind')!='ParmVarDecl':continue
            info=parameter['type'];spelling=info.get('desugaredQualType',info['qualType'])
            match=re.fullmatch(r'(const )?(std::vector<(.+)>) &',spelling)
            if match:
                vector,element=match.group(2),match.group(3)
                if vector not in audited['vector_types']:
                    raise ValueError('vector parameter must use the audited standard class')
                nested=re.fullmatch(r'std::vector<(.+)>',element)
                inner=nested.group(1) if nested else element
                pair_element=audited.get('pair_types',{}).get(element)
                if pair_element is not None:
                    # A vector of std::pair<T, T> is modelled as two rows of T (first, second) of equal length.
                    nested=True;inner=pair_element
                elif nested and element not in audited['vector_types']:
                    raise ValueError('nested vector parameter must use the audited standard class')
                if inner not in TYPES or inner=='bool':
                    raise ValueError('binding schemas currently require scalar integer vector elements')
                width,signed,boolean=TYPES[inner]
                if 'spellingLoc' in parameter.get('loc',{}) or 'expansionLoc' in parameter.get('loc',{}):
                    raise ValueError('macro parameter declarations are unsupported')
                name=parameter.get('name','')
                bodies=[c for c in function.get('inner',[]) if c.get('kind')=='CompoundStmt']
                if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name) or len(bodies)!=1:
                    raise ValueError('vector parameter identity requires a named parameter in a definition')
                location=bodies[0].get('range',{}).get('begin',{})
                if 'offset' not in location or 'spellingLoc' in location or 'expansionLoc' in location:
                    raise ValueError('macro function bodies are unsupported for vector parameter identity')
                constant='const ' if match.group(1) else ''
                assertion=(f'\n#if defined(__is_same) || defined(decltype) || defined(static_assert) || defined(std) || defined(vector) || defined(int) || defined(long) || defined(unsigned) || defined(signed) || defined(const)\n'
                    '#error vector identity keywords must not be macros\n#endif\n'
                    f'static_assert(__is_same(decltype({"(("+name+"))" if parameter.get("field") else name}),{constant}::std::vector<{element}> &),'
                    '"vector parameter must be the canonical standard type");\n')
                probes.append((location['offset']+location['tokLen'],assertion))
                entry={'kind':'nested' if nested else 'vector',
                       'element':{'width':width,'signed':signed,'boolean':boolean},
                       'writable':not bool(match.group(1))}
                if pair_element is not None:
                    entry['pair']=True
                parameters.append(entry)
            else:
                scalar=parameter_type(parameter)
                parameters.append({'kind':'scalar','element':scalar['type'],
                                   'reference':scalar['reference'],'writable':scalar['writable']})
        functions.append({'name':function['name'],'parameters':parameters})
    verify_type_probes(source,probes,include_dirs)
    names=[function['name'] for function in functions]
    if len(names)!=len(set(names)):
        raise ValueError('overloaded binding schema names require explicit declaration identifiers')
    return {'coverage':'parameter_bindings_only','functions':functions}


_IDENTITY=re.compile(r'static_assert\(__is_same\(decltype\((?P<entity>[^()]*|\(\([^()]*\)\))\),'
                     r'(?P<type>[^"]+)\),(?P<message>"[^"]*")\);')


def _identity(assertion):
    """Split a probe into its guard lines and a final identity assertion (linear time)."""
    if not assertion.endswith(');\n'):return None
    head,_,last=assertion[:-1].rpartition('\n')
    match=_IDENTITY.fullmatch(last)
    return (head+'\n',match['entity'],match['type'],match['message']) if match else None


def merge_type_probes(probes):
    """Several instantiations of one class template share a body position.

    Identity probes at one position are combined into one assertion that the
    declared entity has one of the audited types (each instantiation's type was
    read from that instantiation's AST); other probes must agree exactly."""
    groups={}
    for offset,assertion in probes:
        match=_identity(assertion)
        key=(offset,match[0],match[1],match[3]) if match else (offset,assertion)
        groups.setdefault(key,{})[match[2] if match else assertion]=None
    merged=[]
    for key,group in groups.items():
        if len(key)==2:
            merged.append(key);continue
        offset,guard,entity,message=key
        condition=' || '.join(f'__is_same(decltype({entity}),{ty})' for ty in group)
        merged.append((offset,f'{guard}static_assert({condition},{message});\n'))
    return merged


def verify_type_probes(source, probes, include_dirs=()):
    if probes:
        origin=Path(source).resolve(strict=True)
        text=origin.read_bytes()
        for offset,assertion in sorted(merge_type_probes(probes),reverse=True):
            text=text[:offset]+assertion.encode()+text[offset:]
        with tempfile.TemporaryDirectory(prefix='vector-parameter-identity-') as directory:
            root=Path(directory);probe=root/'source.hpp';probe.write_bytes(text)
            overlay=root/'overlay.json'
            overlay.write_text(json.dumps({'version':0,'use-external-names':False,'roots':[
                {'type':'file','name':str(origin),'external-contents':str(probe)}]}))
            command=clang_command()+['-ivfsoverlay',str(overlay)]
            for path in include_dirs:command+=['-I',str(Path(path).resolve(strict=True))]
            result=subprocess.run(command+[str(origin)],cwd=ROOT,text=True,capture_output=True)
            if result.returncode:
                raise ValueError('vector parameter identity probe failed: '+result.stderr)


def emit_lean(ir,namespace='VectorBindingInstances'):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',namespace):
        raise ValueError('invalid Lean namespace')
    lines=['-- Generated from audited Clang parameter declarations.',
           'import Proofs.CppVectorBindings','',f'namespace {namespace}',
           'open Proofs.CppVectorBindings','']
    for function in ir['functions']:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',function['name']):
            raise ValueError('unsupported function declaration name')
        params=[]
        for parameter in function['parameters']:
            ty=lean_type(parameter['element'])
            writable=str(parameter['writable']).lower()
            if parameter['kind']=='vector':params.append(f'.vector {ty} {writable}')
            elif parameter['kind']=='nested':params.append(f'.nested {ty} {writable}')
            else:params.append(f'.scalar {ty} {str(parameter["reference"]).lower()} {writable}')
        lines.append(f'def «{function["name"]}» : List Parameter := [{", ".join(params)}]')
    lines.extend(['',f'end {namespace}',''])
    return '\n'.join(lines)
