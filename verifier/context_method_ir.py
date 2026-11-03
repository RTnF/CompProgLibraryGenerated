"""Audited same-TU FieldDecl receiver mapping to non-resizing Context methods."""
import hashlib
import json
import re
from pathlib import Path
from ast_stream import class_method_functions, _field_parameter, _replace_this_members, _function_class_name
from class_copy import audit_copy_record
from class_call_ir import _element, _parameter_defaults
from inline_ast import inline_functions
from nested_ir import NestedBody, emit_lean
from scalar_ir import apply_conversion_policy, lean_type
from state_ir import ValueCalls, parameter_type
from scalar_stl import walk
from vector_bindings import bindings_from_audit, verify_type_probes
from vector_stl import translation_unit, audit_vector_nodes


def _require_non_resizing(statements):
    for statement in statements:
        kind=statement['kind']
        if kind in {'check','declare','assign','write','return','break'}:
            continue
        if kind in {'scope','while'}:
            _require_non_resizing(statement['body'])
        elif kind=='branch':
            _require_non_resizing(statement['yes'])
            _require_non_resizing(statement['no'])
        else:
            raise ValueError(f'non-resizing Context method body required: {kind}')


def _receiver_functions(record,source,raw):
    functions=[f for f in class_method_functions(record,source) if f['id'] in raw]
    mutable_reference=False
    for method in raw.values():
        for parameter in method.get('inner',[]):
            if parameter.get('kind')!='ParmVarDecl':continue
            try:
                info=parameter_type(parameter)
            except ValueError:
                # Nonscalar parameters still pass through the ordinary schema audit.
                continue
            mutable_reference |= info['reference'] and info['writable']
    if mutable_reference:
        fields=[n for n in record['inner'] if n.get('kind')=='FieldDecl']
        for function in functions:
            method=raw[function['id']]
            constant=method['type']['qualType'].endswith(' const')
            synthetic=[_field_parameter(_function_class_name(record),field,constant,False) for field in fields]
            parameters={field['id']:parameter for field,parameter in zip(fields,synthetic,strict=True)}
            function['_fields']=synthetic
            function['inner']=synthetic+[
                _replace_this_members(child,fields,parameters) if child.get('kind')=='CompoundStmt' else child
                for child in method.get('inner',[])]
    return functions


def _require_class_declarations(record):
    """Reject explicitly declared members omitted by the method/layout generators.

    Implicit copy/move/destruction retain their separately documented obligations.
    """
    for member in record.get('inner', []):
        kind = member.get('kind')
        if kind in {'FieldDecl', 'AccessSpecDecl'}:
            continue
        if kind == 'CXXDestructorDecl' and member.get('isImplicit'):
            continue
        if kind == 'CXXConstructorDecl' and (member.get('isImplicit') or any(
                child.get('kind') == 'CompoundStmt' for child in member.get('inner', []))):
            continue
        if kind == 'CXXRecordDecl' and member.get('isImplicit') and member.get('name') == record.get('name'):
            continue
        if kind == 'CXXMethodDecl':
            if member.get('isImplicit'):
                continue
            if member.get('storageClass') != 'static' and any(
                    child.get('kind') == 'CompoundStmt' for child in member.get('inner', [])):
                continue
        raise ValueError(f'class declaration omitted by constructor/method generation: {kind}')


def lower_context_methods(source,qualified,include_dirs=(),signed_conversion='checked',*,method_names=None,strict_declarations=False,backend='context'):
    if backend not in ('context','members'):
        raise ValueError('unknown class method backend')
    if method_names is not None:
        if isinstance(method_names,str):
            raise ValueError('method_names must be a nonempty sequence of distinct source names')
        method_names=tuple(method_names)
        if (not method_names or any(not isinstance(n,str) or not n for n in method_names)
            or len(set(method_names))!=len(method_names)):
            raise ValueError('method_names must be a nonempty sequence of distinct source names')
    source=Path(source).resolve(strict=True)
    digest=hashlib.sha256(source.read_bytes()).hexdigest()
    records,callees=[],[]
    _,roots=translation_unit(source,include_dirs,callees=callees,copy_class=qualified,copy_records=records)
    if len(records)!=1:raise ValueError('one original class definition required')
    record=records[0];record['_copy_qualified']=qualified
    if strict_declarations:
        if method_names is not None:
            raise ValueError('strict class declarations cannot select only some methods')
        _require_class_declarations(record)
    plan=audit_copy_record(source,qualified,record,roots,include_dirs,vector_anywhere=True,
                           multiple_vectors=backend=='members')
    fields=[n for n in record['inner'] if n.get('kind')=='FieldDecl']
    declared_fields=list(fields)
    order=sorted(range(len(fields)),key=lambda i:plan['fields'][i]['kind']!='vector_copy')
    fields=[fields[i] for i in order]
    plan['fields']=[plan['fields'][i] for i in order]
    kinds=[f['kind'] for f in plan['fields']]
    if backend=='context' and (not kinds or kinds[0]!='vector_copy' or any(k!='scalar_copy' for k in kinds[1:])):
        raise ValueError('one flat vector and scalar fields required')
    raw={n['id']:n for n in record['inner'] if n.get('kind')=='CXXMethodDecl' and not n.get('isImplicit')
         and n.get('storageClass')!='static' and any(c.get('kind')=='CompoundStmt' for c in n.get('inner',[]))}
    selected=set(raw) if method_names is None else {key for key,m in raw.items() if m['name'] in method_names}
    if method_names is not None and (not method_names or set(method_names)!={raw[key]['name'] for key in selected}):
        raise ValueError('selected methods must exist exactly by source name')
    reachable=set(selected)
    pending=list(selected)
    while pending:
        for node in walk(raw[pending.pop()]):
            target=node.get('referencedMemberDecl')
            if target in raw and target not in reachable:
                reachable.add(target)
                pending.append(target)
    functions=[]
    # Keep all methods in the receiver permission/alias audit, including omitted ones.
    for function in _receiver_functions(record,source,raw):
        if function['id'] not in reachable:
            continue
        # Reorder synthetic parameters by actual FieldDecl identity; retain all scalar order.
        original=function['_fields']
        reordered=[original[i] for i in order]
        function['_fields']=reordered
        function['inner']=reordered+function['inner'][len(original):]
        clean,defaults=_parameter_defaults(function)
        if any(default is not None for default in defaults):
            raise ValueError('default argument call expressions require their own source adapter')
        functions.append(clean)
    library=[f for f in functions if f['id'] not in selected]
    functions=inline_functions([f for f in functions if f['id'] in selected],[*library,*callees])
    audited=audit_vector_nodes(source,functions,roots,include_dirs)
    schemas=bindings_from_audit(source,audited,include_dirs)['functions']
    apply_conversion_policy([*audited['functions'],*callees],signed_conversion)
    methods,used,probes=[],{},[]
    for function,schema in zip(audited['functions'],schemas,strict=True):
        synthetic=function.get('_fields',[])
        if len(synthetic)!=len(fields) or len(schema['parameters'])<len(fields):
            raise ValueError('method field parameter count mismatch')
        for field,parameter,profile,formal in zip(fields,synthetic,plan['fields'],schema['parameters'][:len(fields)],strict=True):
            if (field['id']!=profile['field_id'] or parameter['id']!=f"field:{record['name']}:{field['name']}"
                or formal['kind']!=('vector' if profile['kind']=='vector_copy' else 'scalar')
                or formal['element']!=_element(profile.get('element',profile.get('type')))):
                raise ValueError('method field identity, order or type mismatch')
            if formal['kind']=='scalar':
                expected=parameter_type(parameter)
                if (formal['reference']!=expected['reference'] or formal['writable']!=expected['writable']
                    or formal['element']!=expected['type']):
                    raise ValueError('method field reference mode or permission mismatch')
            else:
                spelling=parameter['type'].get('desugaredQualType',parameter['type']['qualType'])
                if formal['writable']!=(not spelling.startswith('const ')):
                    raise ValueError('method vector field permission mismatch')
        body=NestedBody(function,schema,ValueCalls(callees),source)
        program=body.lower();program['parameters']=schema['parameters']
        if backend=='context':
            _require_non_resizing(program['body'])
        if backend=='context' and ('vector' in program['result'] or 'unit' in program['result']):
            raise ValueError('scalar method result required by Context call backend')
        method=dict(program=program,fields=schema['parameters'][:len(fields)],arguments=len(schema['parameters'])-len(fields))
        if backend=='members':
            method['constant']=raw[function['id']]['type']['qualType'].endswith(' const')
        methods.append(method)
        used.update(body.callees);probes.extend(body.probes)
    if not methods or len(methods)!=len(selected) or len({m['program']['name'] for m in methods})!=len(methods):
        raise ValueError('every selected nonstatic method must have one unique program')
    verify_type_probes(source,probes,include_dirs)
    if hashlib.sha256(source.read_bytes()).hexdigest()!=digest:raise ValueError('source changed during method generation')
    return dict(coverage='context_method_receivers' if method_names is None else 'selected_context_method_receivers',declared_fields=[f['name'] for f in declared_fields],field_permutation=order,selected_methods=[raw[k]['name'] for k in raw if k in selected],available_methods=[m['name'] for m in raw.values()],dependency_methods=[raw[k]['name'] for k in raw if k in reachable-selected],qualified_class=qualified,source_sha256=digest,fields=[f['name'] for f in fields],methods=methods,
                callees=[used[n] for n in sorted(used)],vector=methods[0]['fields'][0]['element'])


def _object_receiver_profile(method):
    fields=method['fields']
    if len(fields)!=3 or not fields[0]['writable']:
        return False
    element=fields[0]['element']
    def scalar(parameter,reference):
        return (parameter['kind']=='scalar' and parameter['element']==element
                and parameter['reference']==reference and parameter['writable'])
    return (scalar(fields[1],True) and scalar(fields[2],False)
            and all(scalar(parameter,False) for parameter in method['program']['parameters'][3:]))


def emit_member_methods(source, qualified, namespace='Proofs.Generated.MemberMethods',
                        include_dirs=(), signed_conversion='checked'):
    """Generate actual multi-member slots for the existing NProgram interpreter.

    This path covers constructors/methods, not implicit class copy or lifetime.
    Receiver constness belongs to the call expression and is explicit here.
    """
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', namespace):
        raise ValueError('invalid Lean namespace')
    source = Path(source).resolve(strict=True)
    ir = lower_context_methods(source, qualified, include_dirs, signed_conversion,
                               strict_declarations=True, backend='members')
    programs = emit_lean(dict(functions=[m['program'] for m in ir['methods']],
                              callees=ir['callees']), namespace+'.Methods', share_commands=True)
    lines = ['import Proofs.CppConstructorMultiFinish', programs, f'namespace {namespace}',
             'open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop',
             f'def sourceSHA256 : String := {json.dumps(ir["source_sha256"])}',
             'def coverage : String := "constructor_member_method_calls"',
             'def fieldNames : List String := '+json.dumps(ir['fields']),
             'def declaredFieldNames : List String := '+json.dumps(ir['declared_fields']),
             'def fieldPermutation : List Nat := '+json.dumps(ir['field_permutation'])]
    for method in ir['methods']:
        name = method['program']['name']
        fields = method['fields']
        vectors = sum(f['kind']=='vector' for f in fields)
        scalars = len(fields)-vectors
        lines += [f'def «{name}_arguments» (receiver : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (arguments : List NArgument) : Option (List NArgument) := do',
                  f'  if receiver.vectorSlots.length != {vectors} || receiver.scalarSlots.length != {scalars} ||',
                  f'      arguments.length != {method["arguments"]} then none else pure ()']
        arguments = []
        positions = {'vector':0, 'scalar':0}
        for index, field in enumerate(fields):
            kind = field['kind']
            position = positions[kind]
            positions[kind] += 1
            slots = 'vectorSlots' if kind=='vector' else 'scalarSlots'
            lines.append(f'  let slot{index} ← receiver.{slots}[{position}]?')
            if kind=='vector':
                arguments.append(f'.vectorReference slot{index}')
            elif field['reference']:
                arguments.append(f'.scalarReference slot{index}')
            else:
                arguments.append(f'.value (.variable {lean_type(field["element"])} slot{index})')
        lines.append('  pure (['+', '.join(arguments)+'] ++ arguments)')
        vector_slots = ','.join(f'slot{i}' for i,f in enumerate(fields) if f['kind']=='vector')
        scalar_slots = ','.join(f'slot{i}' for i,f in enumerate(fields) if f['kind']=='scalar')
        binders = ' '.join(f'slot{i}' for i in range(len(fields)))
        lines += [f'theorem «{name}_arguments_of_fields»',
                  '    (receiver : Proofs.CppConstructorMultiFinish.ObjectRef) (arguments : List NArgument)',
                  f'    ({binders} : Nat)',
                  f'    (vectors : receiver.vectorSlots = [{vector_slots}])',
                  f'    (scalars : receiver.scalarSlots = [{scalar_slots}])',
                  f'    (arity : arguments.length = {method["arguments"]}) :',
                  f'    «{name}_arguments» receiver arguments = some (['+', '.join(arguments)+'] ++ arguments) := by',
                  f'  simp [«{name}_arguments»,vectors,scalars,arity]']
        lines += [f'def «{name}_callFuel» (fuel : Nat) (caller : NState)',
                  '    (receiver : Proofs.CppConstructorMultiFinish.ObjectRef) (receiverConst : Bool)',
                  '    (arguments : List NArgument) : Outcome (NState × Ret) :=',
                  f'  if receiverConst && !{str(method["constant"]).lower()} then .fault else do',
                  f'    let expanded ← liftChecked («{name}_arguments» receiver arguments)',
                  f'    Methods.«{name}».callFuel fuel caller expanded',
                  f'theorem «{name}_call_of_arguments» (fuel : Nat) (caller : NState)',
                  '    (receiver : Proofs.CppConstructorMultiFinish.ObjectRef) (arguments expanded : List NArgument)',
                  f'    (mapped : «{name}_arguments» receiver arguments = some expanded) :',
                  f'    «{name}_callFuel» fuel caller receiver false arguments =',
                  f'      Methods.«{name}».callFuel fuel caller expanded := by',
                  f'  simp [«{name}_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]']
    if hashlib.sha256(source.read_bytes()).hexdigest()!=ir['source_sha256']:
        raise ValueError('source changed during method generation')
    return '\n'.join([*lines, f'end {namespace}', ''])


def emit_context_methods(source,qualified,namespace='Proofs.Generated.ContextMethods',include_dirs=(),signed_conversion='checked',*,method_names=None,strict_declarations=False):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',namespace):
        raise ValueError('invalid Lean namespace')
    source=Path(source).resolve(strict=True)
    digest=hashlib.sha256(source.read_bytes()).hexdigest()
    ir=lower_context_methods(source,qualified,include_dirs,signed_conversion,method_names=method_names,strict_declarations=strict_declarations)
    if ir['source_sha256']!=digest:raise ValueError('source changed before method generation')
    methods=emit_lean(dict(functions=[m['program'] for m in ir['methods']],callees=ir['callees']),namespace+'.Methods')
    lines=['import Proofs.CppMoveCallBindings','import Proofs.CppMoveObjectReceiver',methods,f'namespace {namespace}',
      'open Proofs.CppMoveContext Proofs.CppNestedCall Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.CppLoop',
      f'def sourceSHA256 : String := "{ir["source_sha256"]}"',
      'def fieldNames : List String := ['+', '.join(json.dumps(name,ensure_ascii=False) for name in ir['fields'])+']']
    if method_names is not None or ir['fields']!=ir['declared_fields']:
        lines.extend([
            f'def coverage : String := {json.dumps(ir["coverage"])}',
            'def declaredFieldNames : List String := '+json.dumps(ir['declared_fields']),
            'def fieldPermutation : List Nat := '+json.dumps(ir['field_permutation']),
            'def selectedMethods : List String := '+json.dumps(ir['selected_methods']),
            'def availableMethods : List String := '+json.dumps(ir['available_methods']),
            'def dependencyMethods : List String := '+json.dumps(ir['dependency_methods'])])
    vector_ty=lean_type(ir['vector'])
    for method in ir['methods']:
        name=method['program']['name'];fields=method['fields']
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name):raise ValueError('invalid generated method identifier')
        args=['.vectorReference receiver.vectorSlot']
        lines.append(f'def «{name}_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do')
        lines.append(f'  if receiver.scalarSlots.length != {len(fields)-1} || arguments.length != {method["arguments"]} then none else pure ()')
        for i,field in enumerate(fields[1:]):
            lines.append(f'  let slot{i} ← receiver.scalarSlots[{i}]?')
            args.append(f'.scalarReference slot{i}' if field['reference'] else f'.value (.variable {lean_type(field["element"])} slot{i})')
        lines.append('  pure (['+', '.join(args)+'] ++ arguments)')
        slots=','.join(f'slot{i}' for i in range(len(fields)-1))
        binders=(' ('+' '.join(f'slot{i}' for i in range(len(fields)-1))+' : Nat)') if len(fields)>1 else ''
        lines.append(f'theorem «{name}_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument){binders}')
        lines.append(f'    (fields : receiver.scalarSlots = [{slots}]) (arity : arguments.length = {method["arguments"]}) :')
        lines.append(f'    «{name}_arguments» receiver arguments = some (['+', '.join(args)+'] ++ arguments) := by')
        lines.append(f'  simp [«{name}_arguments»,fields,arity]')
        if _object_receiver_profile(method):
            lines.append(f'theorem «{name}_resolve_of_receiver» (caller : Context) (object : ObjectRef)')
            lines.append(f'    (receiver : Proofs.CppMoveObjectReceiver.Receiver caller object {vector_ty})')
            lines.append('    (expressions : List (NExpr × Int))')
            lines.append(f'    (ready : Proofs.CppMoveReceiverResolve.Ready caller {vector_ty} expressions)')
            lines.append(f'    (arity : expressions.length = {method["arguments"]}) :')
            lines.append('    ∃ expanded last,')
            lines.append(f'      «{name}_arguments» object (Proofs.CppMoveReceiverResolve.arguments expressions) = some expanded ∧')
            lines.append(f'      resolveArguments caller {vector_ty} Methods.«{name}».parameters expanded =')
            lines.append(f'        some (last,Proofs.CppMoveReceiverLayout.receiverArguments ⟨receiver.view.header,true⟩ {vector_ty}')
            lines.append('          receiver.counter.address true (receiver.size.value::Proofs.CppMoveReceiverResolve.values expressions)) := by')
            lines.append(f'  have mapped := «{name}_arguments_of_fields» object (Proofs.CppMoveReceiverResolve.arguments expressions)')
            lines.append('    receiver.counter.slot receiver.size.slot receiver.fields (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)')
            lines.append(f'  obtain ⟨last,run⟩ := Proofs.CppMoveObjectReceiver.Receiver.resolve caller object {vector_ty} receiver expressions ready')
            lines.append(f'  have params : Methods.«{name}».parameters =')
            lines.append(f'      (.vector {vector_ty} true :: .scalar {vector_ty} true true :: .scalar {vector_ty} false true ::')
            lines.append(f'        Proofs.CppMoveReceiverResolve.parameters {vector_ty} expressions) := by')
            lines.append('    simp only [Proofs.CppMoveReceiverResolve.parameters,List.map_const\',arity]')
            lines.append('    rfl')
            lines.append('  rw [← params] at run')
            lines.append('  exact ⟨_,last,mapped,run⟩')
        lines.append(f'def «{name}_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do')
        lines.append(f'  let prepared ← liftChecked («{name}_arguments» receiver arguments)')
        lines.append(f'  Proofs.CppMoveCallBindings.callFuel Methods.«{name}» fuel caller {vector_ty} prepared')
        lines.append(f'theorem «{name}_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)')
        lines.append(f'    (mapped : «{name}_arguments» receiver arguments = some expanded) :')
        lines.append(f'    «{name}_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«{name}» fuel caller {vector_ty} expanded := by')
        lines.append(f'  simp [«{name}_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]')
        lines.append(f'theorem «{name}_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«{name}» = true := by decide +kernel')
    result='\n'.join([*lines,f'end {namespace}',''])
    if hashlib.sha256(source.read_bytes()).hexdigest()!=digest:raise ValueError('source changed during method generation')
    return result
