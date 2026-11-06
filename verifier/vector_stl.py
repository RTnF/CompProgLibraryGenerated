"""Same-translation-unit provenance checks for pinned std::vector operations.

This is an AST identity gate, not yet a vector execution-model generator.
"""
from functools import lru_cache
import json
import re
from pathlib import Path
import subprocess
import tempfile
import uuid
import hashlib

from ast_stream import root_objects, node_header, direct_functions, forced_class_records, forced_source_functions
from clang_ast import clang_command, gcc_include_dirs, normalized, ROOT
from scalar_stl import walk
from scalar_ir import TYPES
from class_templates import TemplateInstance, collect_template_record
from scalar_choose import lower_scalar_choices
from scalar_assert import verify_scalar_asserts

OPERATIONS = {'size', 'reserve', 'operator[]', 'begin', 'end', 'assign', 'emplace_back', 'push_back', 'erase'}
ALGORITHMS = {'sort': 'verifiedStdSort', 'unique': 'verifiedStdUnique'}


def primary_view(node):
    if isinstance(node,list):
        return [primary_view(child) for child in node
                if not (isinstance(child,dict) and
                    (child.get('kind')=='ClassTemplateSpecializationDecl' or
                     child.get('kind') in {'FunctionDecl','CXXMethodDecl'} and
                     any(c.get('kind')=='TemplateArgument' for c in child.get('inner',[]))))]
    if isinstance(node,dict):
        return {key:primary_view(value) for key,value in node.items()
                if key not in {'isUsed','isReferenced'}}
    return node


def standard_include_profile(report, unit):
    """Validate Clang's resolved, ordered user-to-system include JSON report.

    This is emitted by the same invocation as the AST, including forced inputs,
    after macro/conditional processing and include-search resolution.
    """
    data = json.loads(report)
    if (not isinstance(data, dict) or set(data) != {'source', 'includes'} or
            not isinstance(data['source'], str) or
            Path(data['source']).resolve() != Path(unit).resolve() or
            not isinstance(data['includes'], list)):
        raise ValueError('invalid compiler standard include report')
    return pinned_includes(data['includes'])


def pinned_includes(includes):
    """Resolve replay headers only within the pinned compiler's system roots."""
    directories = [Path(p).resolve(strict=True) for p in gcc_include_dirs()]
    paths = []
    for name in includes:
        if not isinstance(name, str) or not re.fullmatch(r'[A-Za-z_0-9./+-]+', name):
            raise ValueError('invalid standard include profile')
        path = Path(name)
        candidates = [path] if path.is_absolute() else [d / path for d in directories]
        found = next((p.resolve() for p in candidates if p.is_file()), None)
        if found is None or not any(found.is_relative_to(d) for d in directories):
            raise ValueError('standard include profile must use pinned system headers')
        paths.append(str(found))
    return tuple(paths)


def translation_unit(source, include_dirs=(), callees=None, sorts=None, *, construction_stages=False,
                     copy_class=None, copy_records=None, class_callers=None, copy_assignment=False, move_kind=None,
                     class_destruction=False, template_instance=None):
    source=Path(source).resolve(strict=True)
    if not isinstance(copy_assignment,bool) or copy_assignment and copy_class is None:
        raise ValueError('assignment witness requires a class materialization')
    if move_kind not in (None,'construct','assign') or move_kind is not None and (copy_class is None or copy_assignment):
        raise ValueError('move witness requires one class and one distinct move operation')
    if (not isinstance(class_destruction,bool) or class_destruction and
            (copy_class is None or copy_assignment or move_kind is not None)):
        raise ValueError('destruction witness requires one class and no copy or move operation')
    if copy_class is not None and (not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:::[A-Za-z_][A-Za-z_0-9]*)*',copy_class)
                                   or not isinstance(copy_records,list) or copy_records or construction_stages):
        raise ValueError('copy witness requires a qualified identifier, record collector and no construction stages')
    destructor_name=copy_class.split('::')[-1] if copy_class is not None else None
    if template_instance is not None:
        if not isinstance(template_instance,TemplateInstance) or copy_class is None:
            raise ValueError('template instance requires a class materialization')
        copy_class=template_instance.target(copy_class)
        witness_digest=hashlib.sha256(template_instance.witness.read_bytes()).hexdigest()
    copy_digest=hashlib.sha256(source.read_bytes()).hexdigest() if copy_class is not None else None
    if class_callers is not None and (copy_class is None or not isinstance(class_callers,list) or class_callers):
        raise ValueError('class callers require a copy witness and an empty collector')
    command=clang_command()
    for directory in include_dirs:
        command += ['-I',str(Path(directory).resolve(strict=True))]
    macros=subprocess.check_output([arg for arg in command if arg!='-fsyntax-only']+
                                   ['-dM','-E','/dev/null'],cwd=ROOT,text=True)
    for name,value in [('__SIZEOF_INT__','4'),('__SIZEOF_LONG__','8'),
                       ('__SIZEOF_LONG_LONG__','8'),('__SIZEOF_SIZE_T__','8'),
                       ('__SIZEOF_PTRDIFF_T__','8'),('__CHAR_BIT__','8'),
                       ('__INT_WIDTH__','32'),('__LONG_WIDTH__','64'),
                       ('__LLONG_WIDTH__','64'),('__PTRDIFF_WIDTH__','64')]:
        if f'#define {name} {value}\n' not in macros:
            raise ValueError('unsupported vector ABI: '+name)
    with tempfile.TemporaryDirectory(prefix='class-copy-witness-') as directory, tempfile.TemporaryFile() as output:
        inputs=[str(source)]
        if copy_class is not None:
            witness=Path(directory)/'copy.cpp'
            nonce=uuid.uuid4().hex
            if class_destruction:
                witness.write_text('#include <vector>\nnamespace codex_copy_audit_'+nonce+' { void witness_'+nonce+'(::'+copy_class+
                                   '* object_'+nonce+') { object_'+nonce+'->~'+destructor_name+'(); } }\n')
            elif move_kind is not None:
                prefix='namespace codex_copy_audit_'+nonce+' { void witness_'+nonce+'(::'+copy_class
                if move_kind == 'construct':
                    witness.write_text(prefix+'& source_'+nonce+') { ::'+copy_class+' target_'+nonce+
                                       '(static_cast<::'+copy_class+'&&>(source_'+nonce+')); } }\n')
                else:
                    witness.write_text(prefix+'& target_'+nonce+',::'+copy_class+'& source_'+nonce+') { target_'+nonce+
                                       '=static_cast<::'+copy_class+'&&>(source_'+nonce+'); } }\n')
            elif copy_assignment:
                witness.write_text('namespace codex_copy_audit_'+nonce+' { void witness_'+nonce+'(::'+copy_class+
                                   '& target_'+nonce+',const ::'+copy_class+'& source_'+nonce+') { target_'+nonce+
                                   '=source_'+nonce+'; } }\n')
            else:
                witness.write_text('namespace codex_copy_audit_'+nonce+' { void witness_'+nonce+'(const ::'+copy_class+
                                   '& source_'+nonce+') { ::'+copy_class+' target_'+nonce+'(source_'+nonce+'); } }\n')
            if template_instance is not None:
                alias_namespace='codex_template_audit_'+nonce
                witness.write_text('namespace '+alias_namespace+' { using Selected = ::'+copy_class+'; }\n'+
                                   witness.read_text()+'\n#include "'+str(template_instance.witness)+'"\n')
            inputs=['-include',str(source),str(witness)]
        profile_file = Path(directory)/'includes.json'
        include_flags = ['-Xclang','-header-include-file','-Xclang',str(profile_file),
                         '-Xclang','-header-include-format=json',
                         '-Xclang','-header-include-filtering=only-direct-system']
        subprocess.run(command+include_flags+['-Xclang','-ast-dump=json',*inputs],
                       cwd=ROOT,stdout=output,check=True)
        profile = standard_include_profile(profile_file.read_text(), inputs[-1])
        output.seek(0)
        if copy_class is None:
            functions=direct_functions(output,source,construction_stages=construction_stages)
        else:
            copy_records.extend(collect_template_record(output,source,copy_class,alias_namespace,witness)
                                if template_instance is not None else forced_class_records(output,source,copy_class))
            functions=[]
            if template_instance is not None and callees is not None:
                output.seek(0)
                callees.extend(forced_source_functions(output,source))
            if class_callers is not None:
                output.seek(0)
                class_callers.extend(forced_source_functions(output,source))
        output.seek(0)
        standard=[]
        system_dirs=[Path(p).resolve() for p in gcc_include_dirs()]
        current_file=''
        for raw in root_objects(output):
            header=node_header(raw)
            current_file=header.get('loc',{}).get('file',current_file)
            if template_instance is None and callees is not None and header.get('kind')=='NamespaceDecl' and header.get('name')=='cp':
                # Callee candidates share this dump's declaration IDs; any user header may define them.
                origin=header.get('loc',{}).get('file',current_file)
                if origin and not any(Path(origin).resolve().is_relative_to(p) for p in system_dirs):
                    callees.extend(child for child in json.loads(raw).get('inner',[])
                                   if child.get('kind')=='FunctionDecl')
            if header.get('kind')!='NamespaceDecl' or header.get('name') not in ('std','__gnu_cxx'):
                continue
            origin=header.get('loc',{}).get('file',current_file)
            if origin and not any(Path(origin).resolve().is_relative_to(p) for p in system_dirs):
                raise ValueError('user declarations in standard library namespaces are unsupported')
            if not origin and 'includedFrom' not in header.get('loc',{}):
                raise ValueError('user declarations in standard library namespaces are unsupported')
            if sorts is not None and header.get('name')=='std' and any(
                    f'"name": "{name}"'.encode() in raw for name in ALGORITHMS):
                # Instances of the `std::sort`/`std::unique` function templates declared by the system headers
                # (user declarations in namespace std were rejected above).
                for template in json.loads(raw).get('inner',[]):
                    if template.get('kind')=='FunctionTemplateDecl' and template.get('name') in ALGORITHMS:
                        sorts.update(c['id'] for c in template.get('inner',[]) if c.get('kind')=='FunctionDecl')
            if (b'"name": "vector"' in raw or b'"name": "__normal_iterator"' in raw
                    or b'"name": "numeric_limits"' in raw or Path(origin).name=='vector.tcc'
                    or Path(origin).name=='stl_algobase.h' and
                       (b'"name": "min"' in raw or b'"name": "max"' in raw)):
                root=json.loads(raw)
                if origin:root.setdefault('loc',{})['file']=origin
                root['_standard_include_profile'] = profile
                standard.append(root)
        if copy_class is not None:
            if template_instance is not None and hashlib.sha256(template_instance.witness.read_bytes()).hexdigest()!=witness_digest:
                raise ValueError('template instantiation witness changed during materialization')
            if hashlib.sha256(source.read_bytes()).hexdigest()!=copy_digest:
                raise ValueError('copy source changed during materialization')
            dump_id=uuid.uuid4().hex
            for node in [*copy_records,*standard,*(class_callers or [])]:
                node['_copy_translation_unit']=dump_id
                node['_copy_source']=str(source)
                node['_copy_source_sha256']=copy_digest
                if template_instance is not None:
                    node['_template_instance_witness']=str(template_instance.witness)
                    node['_template_instance_witness_sha256']=witness_digest
    return functions,standard


def vector_declarations(roots):
    headers={(Path(directory)/'bits/stl_vector.h').resolve() for directory in gcc_include_dirs()}
    primary=[]
    instances=[]
    for root in roots:
        if Path(root.get('loc',{}).get('file','')).resolve() not in headers:
            continue
        for node in root.get('inner',[]):
            if node.get('kind')!='ClassTemplateDecl' or node.get('name')!='vector':
                continue
            records=[c for c in node.get('inner',[]) if c.get('kind')=='CXXRecordDecl'
                     and c.get('completeDefinition')]
            if len(records)!=1:
                raise ValueError('std::vector primary record is missing or ambiguous')
            primary.append(records[0])
            instances.extend(c for c in node.get('inner',[]) if c.get('kind')=='ClassTemplateSpecializationDecl')
    if len(primary)!=1:
        raise ValueError('exactly one pinned std::vector primary declaration required')
    return primary[0],instances


def trusted_views(roots, primary):
    definitions=[node for root in roots for node in walk(root)
                 if node.get('parentDeclContextId')==primary['id']]
    return normalized(primary_view({'record':primary,'definitions':definitions}))


def iterator_declarations(roots):
    headers={(Path(directory)/'bits/stl_iterator.h').resolve() for directory in gcc_include_dirs()}
    primary=[];instances=[]
    for root in roots:
        if (root.get('name')!='__gnu_cxx' or
                Path(root.get('loc',{}).get('file','')).resolve() not in headers):
            continue
        for node in root.get('inner',[]):
            if node.get('kind')!='ClassTemplateDecl' or node.get('name')!='__normal_iterator':
                continue
            records=[c for c in node.get('inner',[]) if c.get('kind')=='CXXRecordDecl'
                     and c.get('completeDefinition')]
            if len(records)!=1:raise ValueError('standard iterator primary is missing or ambiguous')
            primary.extend(records)
            instances.extend(c for c in node.get('inner',[]) if c.get('kind')=='ClassTemplateSpecializationDecl')
    if len(primary)!=1:raise ValueError('exactly one pinned iterator primary required')
    return primary[0],instances


@lru_cache(maxsize=1)
def pristine_iterator():
    with tempfile.TemporaryDirectory(prefix='iterator-pristine-') as directory:
        source=Path(directory)/'standard.cpp';source.write_text('#include <vector>\n')
        _,roots=translation_unit(source)
        primary,_=iterator_declarations(roots)
        return trusted_views(roots,primary)


def audit_iterators(roots):
    primary,instances=iterator_declarations(roots)
    if trusted_views(roots,primary)!=pristine_iterator():
        raise ValueError('standard iterator primary differs from the pristine pinned library')
    primary_ids={n['id'] for n in walk(primary) if 'id' in n}
    for root in roots:
        for node in walk(root):
            if node.get('parentDeclContextId')==primary['id']:
                primary_ids.update(n['id'] for n in walk(node) if 'id' in n)
    for instance in instances:
        if not instance.get('completeDefinition'):
            continue
        if instance.get('TemplateInstantiationPattern')!=primary['id']:
            raise ValueError('standard iterator specialization is unsupported')
        members=[c for c in instance.get('inner',[]) if c.get('kind') in
                 ('CXXMethodDecl','CXXConstructorDecl','CXXDestructorDecl')]
        members.extend(c for t in instance.get('inner',[]) if t.get('kind')=='FunctionTemplateDecl'
                       for c in t.get('inner',[]) if c.get('kind') in ('CXXMethodDecl','CXXConstructorDecl'))
        for member in members:
            if member.get('isUsed') and member.get('TemplateInstantiationPattern') not in primary_ids:
                # Implicit special members contain no user-provided behavior.
                if not member.get('isImplicit'):
                    raise ValueError('used standard iterator member specialization is unsupported')


@lru_cache(maxsize=None)
def pristine_primary(includes=('vector',)):
    """The vector primary seen after exactly these standard headers (their order changes dependent-name lookups)."""
    includes = pinned_includes(includes)
    with tempfile.TemporaryDirectory(prefix='vector-pristine-') as directory:
        source=Path(directory)/'standard.cpp'
        source.write_text(''.join(f'#include <{name}>\n' for name in includes))
        _,roots=translation_unit(source)
        primary,_=vector_declarations(roots)
        return trusted_views(roots,primary)


def audit_vector_operations(source, include_dirs=(), callees=None, *, construction_stages=False):
    sorts=set()
    functions,roots=translation_unit(source,include_dirs,callees,sorts,construction_stages=construction_stages)
    return audit_vector_nodes(source,functions,roots,include_dirs,sorts)


def audit_vector_nodes(source,functions,roots,include_dirs=(),sorts=(),*,copy_assignment=False,move_assignment=False):
    """Audit nodes and standard declarations from the same compiler dump."""
    if (not isinstance(copy_assignment,bool) or not isinstance(move_assignment,bool) or
            copy_assignment and move_assignment):
        raise ValueError('invalid vector assignment audit mode')
    operations=OPERATIONS | ({'operator='} if copy_assignment or move_assignment else set())
    verify_scalar_asserts(source,functions,include_dirs)
    assert_arguments={id(child) for function in functions for node in walk(function)
                      if node.get('verifiedScalarAssert')
                      for child in walk(node['inner'][0])}
    primary,instances=vector_declarations(roots)
    view=trusted_views(roots,primary)
    if view!=pristine_primary():
        profiles = [root.get('_standard_include_profile') for root in roots]
        if not profiles or not profiles[0] or any(p != profiles[0] for p in profiles):
            raise ValueError('standard include profile is missing or inconsistent')
        if view!=pristine_primary(tuple(profiles[0])):
            raise ValueError('std::vector primary differs from the pristine pinned library')
    audit_iterators(roots)
    all_nodes=[node for root in roots for node in walk(root)]
    # A class-template instance must originate in the pristine primary. User
    # full specializations and vector<bool> partial specialization do not.
    methods={}
    candidates={}
    for instance in instances:
        args=[c.get('type',{}).get('qualType') for c in instance.get('inner',[])
              if c.get('kind')=='TemplateArgument']
        if (instance.get('TemplateInstantiationPattern')==primary['id'] and len(args)==2
                and args[1]==f'std::allocator<{args[0]}>'):
            candidates[f'std::vector<{args[0]}>']=args[0]
    def supported_element(element, seen=()):
        if element in TYPES:
            return element!='bool'
        return (element in candidates and element not in seen and
                supported_element(candidates[element],seen+(element,)))
    for instance in instances:
        if instance.get('TemplateInstantiationPattern')!=primary['id']:
            continue
        args=[c.get('type',{}).get('qualType') for c in instance.get('inner',[])
              if c.get('kind')=='TemplateArgument']
        if len(args)!=2 or args[1]!=f'std::allocator<{args[0]}>' or not supported_element(args[0]):
            continue
        for node in walk(instance):
            if node.get('kind')=='CXXMethodDecl':
                methods[node['id']]=(node,args[0])
    # `std::numeric_limits<I>::min()/max()/lowest()` of a scalar integer type: the specializations belong to the system
    # header (user declarations in namespace std were rejected), so a call is the literal value of its type.
    limit_methods={}
    for node in all_nodes:
        if node.get('kind')=='ClassTemplateSpecializationDecl' and node.get('name')=='numeric_limits':
            args=[c for c in node.get('inner',[]) if c.get('kind')=='TemplateArgument']
            spelling=args[0].get('type',{}).get('qualType') if len(args)==1 else None
            if spelling in TYPES and not TYPES[spelling][2]:
                for member in node.get('inner',[]):
                    if (member.get('kind')=='CXXMethodDecl' and member.get('name') in ('min','max','lowest')
                            and member.get('storageClass')=='static'):
                        limit_methods[member['id']]=(member['name'],spelling)
    for function in functions:
        for call in walk(function):
            children=call.get('inner',[])
            if call.get('kind')!='CallExpr' or len(children)!=1:
                continue
            callee=children[0]
            while callee.get('kind')=='ImplicitCastExpr' and len(callee.get('inner',[]))==1:
                callee=callee['inner'][0]
            selected=limit_methods.get(callee.get('referencedDecl',{}).get('id'))
            if callee.get('kind')=='DeclRefExpr' and selected is not None:
                width,signed,_=TYPES[selected[1]]
                low=-(1<<(width-1)) if signed else 0
                high=(1<<(width-1))-1 if signed else (1<<width)-1
                call['verifiedNumericLimit']=high if selected[0]=='max' else low
    primary_ids={node['id'] for node in walk(primary) if 'id' in node}
    # Out-of-class definitions point back into the primary via previousDecl
    # and parentDeclContextId. Their IDs also come from this compiler process.
    for node in all_nodes:
        if node.get('parentDeclContextId')==primary['id']:
            primary_ids.update(c['id'] for c in walk(node) if 'id' in c)
    # Reject used helper specializations as well as a specialized public entry.
    # A pristine constructor can call a specialized private fill helper.
    constructors={}
    for instance in instances:
        args=[c.get('type',{}).get('qualType') for c in instance.get('inner',[])
              if c.get('kind')=='TemplateArgument']
        if (instance.get('TemplateInstantiationPattern')!=primary['id'] or len(args)!=2 or
            args[1]!=f'std::allocator<{args[0]}>' or not supported_element(args[0])):
            continue
        members=[child for child in instance.get('inner',[])
                 if child.get('kind') in ('CXXMethodDecl','CXXConstructorDecl','CXXDestructorDecl')]
        members.extend(member for template in instance.get('inner',[]) if template.get('kind')=='FunctionTemplateDecl'
                       for member in template.get('inner',[])
                       if member.get('kind') in ('CXXMethodDecl','CXXConstructorDecl'))
        for node in members:
            if node.get('kind') in ('CXXMethodDecl','CXXConstructorDecl','CXXDestructorDecl') and node.get('isUsed'):
                if node.get('TemplateInstantiationPattern') not in primary_ids:
                    raise ValueError('used vector helper or constructor specialization is unsupported: '+node.get('name',''))
            if node.get('kind')=='CXXConstructorDecl' and node.get('TemplateInstantiationPattern') in primary_ids:
                key=(f'std::vector<{args[0]}>',node.get('type',{}).get('qualType'))
                constructors.setdefault(key,[]).append(node)
    for function in functions:
        for call in walk(function):
            if call.get('kind')!='CXXConstructExpr' or call.get('constructionKind')!='complete':
                continue
            for marker in ('verifiedVectorConstructor','verifiedVectorElement','verifiedVectorConstructorDecl'):
                call.pop(marker,None)
            ty=call.get('type',{}).get('desugaredQualType',call.get('type',{}).get('qualType'))
            if ty is not None: ty=ty.removeprefix('const ')
            signature=call.get('ctorType',{}).get('qualType')
            selected=constructors.get((ty,signature),[])
            if (len(selected)==1 and signature=='void (size_type, const value_type &, const allocator_type &)' and
                candidates.get(ty) in TYPES and candidates.get(ty)!='bool'):
                call['verifiedVectorConstructor']='fill'
                call['verifiedVectorElement']=candidates[ty]
                call['verifiedVectorConstructorDecl']=selected[0]['id']
            elif (len(selected)==1 and ty in candidates and supported_element(candidates[ty]) and
                  signature=='void (size_type, const allocator_type &)'):
                call['verifiedVectorConstructor']='count'
                call['verifiedVectorElement']=candidates[ty]
                call['verifiedVectorConstructorDecl']=selected[0]['id']
            elif (len(selected)==1 and ty in candidates and supported_element(candidates[ty]) and
                  signature=='void () noexcept' and not call.get('inner')):
                call['verifiedVectorConstructor']='default'
                call['verifiedVectorElement']=candidates[ty]
                call['verifiedVectorConstructorDecl']=selected[0]['id']
            elif (len(selected)==1 and ty in candidates and supported_element(candidates[ty]) and
                  signature==f'void (vector<{candidates[ty]}> &&) noexcept'):
                call['verifiedVectorConstructor']='move'
                call['verifiedVectorElement']=candidates[ty]
                call['verifiedVectorConstructorDecl']=selected[0]['id']
            elif (len(selected)==1 and candidates.get(ty) in TYPES and candidates.get(ty)!='bool' and
                  signature==f'void (const vector<{candidates[ty]}> &)' and len(call.get('inner',[]))==1):
                origin=call['inner'][0]
                origin_type=origin.get('type',{}).get('desugaredQualType',origin.get('type',{}).get('qualType'))
                qualified=origin_type=='const '+ty
                if (not qualified and origin.get('kind')=='ImplicitCastExpr' and origin.get('castKind')=='NoOp'
                        and origin_type==f'const vector<{candidates[ty]}>' and len(origin.get('inner',[]))==1):
                    inner_type=origin['inner'][0].get('type',{})
                    qualified=inner_type.get('desugaredQualType',inner_type.get('qualType')) in (ty,'const '+ty)
                if qualified and origin.get('valueCategory')=='lvalue':
                    call['verifiedVectorConstructor']='copy'
                    call['verifiedVectorElement']=candidates[ty]
                    call['verifiedVectorConstructorDecl']=selected[0]['id']
    records=[]
    for function in functions:
        for call in walk(function):
            children=call.get('inner',[])
            if call.get('kind')=='CallExpr' and children:
                callee=children[0]
                while callee.get('kind')=='ImplicitCastExpr' and len(callee.get('inner',[]))==1:
                    callee=callee['inner'][0]
                referenced=callee.get('referencedDecl',{})
                if referenced.get('name') in ALGORITHMS and referenced.get('id') in sorts:
                    call[ALGORITHMS[referenced['name']]]=True
                    records.append({'function':function.get('name'),'operation':'std::'+referenced['name'],'element':None,
                                    'callee_id':referenced['id'],'pattern_id':None})
            if call.get('kind')=='CXXMemberCallExpr' and children and children[0].get('kind')=='MemberExpr':
                member=children[0]
                identifier=member.get('referencedMemberDecl')
            elif call.get('kind')=='CXXOperatorCallExpr' and children:
                callee=children[0]
                while callee.get('kind')=='ImplicitCastExpr' and len(callee.get('inner',[]))==1:
                    callee=callee['inner'][0]
                identifier=callee.get('referencedDecl',{}).get('id')
                member=callee
            else:
                continue
            selected=methods.get(identifier)
            if selected is None:
                raise ValueError('member call must resolve to a pinned std::vector instance')
            method,element=selected
            if method.get('TemplateInstantiationPattern') not in primary_ids:
                raise ValueError('vector method specialization is unsupported')
            operation=method.get('name')
            if operation not in operations:
                raise ValueError(f'unsupported vector operation: {operation}')
            if operation=='operator=':
                parameters=[n for n in method.get('inner',[]) if n.get('kind')=='ParmVarDecl']
                parameter_type=(parameters[0].get('type',{}) if len(parameters)==1 else {})
                spelling=parameter_type.get('desugaredQualType',parameter_type.get('qualType',''))
                expected = ({f'std::vector<{element}> &&',f'vector<{element}> &&'} if move_assignment else
                            {f'const std::vector<{element}> &',f'const vector<{element}> &'})
                if element not in TYPES or element=='bool' or len(parameters)!=1 or spelling not in expected:
                    raise ValueError('only scalar vector '+('rvalue-reference move' if move_assignment else
                                     'const-reference copy')+' assignment is audited')
            for location in (call.get('range',{}).get('begin',{}),call.get('range',{}).get('end',{})):
                if 'spellingLoc' in location or 'expansionLoc' in location:
                    spelling=location.get('spellingLoc',{})
                    expansion=location.get('expansionLoc',{})
                    if (id(call) not in assert_arguments or not expansion.get('isMacroArgExpansion')
                            or 'offset' not in spelling or 'offset' not in expansion
                            or spelling['offset']<expansion['offset']
                            or Path(spelling.get('file',str(source))).resolve()!=Path(source).resolve()):
                        raise ValueError('macro vector calls are unsupported outside verified assert arguments')
                elif 'offset' not in location:
                    raise ValueError('vector call source location required')
            call['verifiedVectorOperation']=operation
            call['verifiedVectorElement']=element
            records.append({'function':function.get('name'),'operation':operation,'element':element,
                            'callee_id':identifier,'pattern_id':method['TemplateInstantiationPattern']})
    functions,scalar_choices=lower_scalar_choices(functions,roots)
    result={'coverage':'callee_identity_only','operations':records,'functions':functions,
            'vector_types':sorted(name for name,element in candidates.items() if supported_element(element))}
    if scalar_choices:
        result['scalar_choices']=scalar_choices
    return result
