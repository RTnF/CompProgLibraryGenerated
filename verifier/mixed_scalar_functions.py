"""Lower a source-owned bundle of single- and multiple-field scalar records.

Multiple-field returns evaluate every constructor argument/field or trivial
copy field before projection. This remains a finite scalar-value frontend.
"""
import copy
import re
from ast_stream import _display_name, _function_class_name
from class_templates import require_method_bodies
from class_lowering import ErasedClass, build_functions, erase_functions, selected_type_pattern
from class_split import SplitClass, Splitter, split_functions, split_one


def mixed_scalar_functions(records, source):
    names=[_function_class_name(record) for record in records]
    displays=[_display_name(record) for record in records]
    if len(set(names))!=len(names) or len(set(displays))!=len(displays):
        raise ValueError('mixed records require distinct scoped model names')
    erased,split=[],[]
    friends={}
    for record,name,display in zip(records,names,displays,strict=True):
        require_method_bodies(record)
        fields=[n for n in record.get('inner',[]) if n.get('kind')=='FieldDecl']
        if not fields:
            raise ValueError('mixed scalar record needs at least one field')
        cls=ErasedClass(record,name,display) if len(fields)==1 else SplitClass(record,name,display,strict_returns=True)
        cls.pattern=selected_type_pattern(record,display)
        if cls.pattern is None:
            raise ValueError('mixed record needs audited source provenance')
        friends[id(cls)]=[n for n in record.get('inner',[]) if n.get('kind')=='FriendDecl']
        (erased if len(fields)==1 else split).append(cls)
    own_functions=[]
    owners={}
    for cls in erased:
        functions=build_functions(cls,source,friends[id(cls)])
        for function in functions:
            owners[function['id']]=cls
        own_functions.extend(functions)
    # Remove single-field receivers' CXXThisExpr before asking Splitter to
    # process their unrelated multi-field arguments/results. Other record
    # constructors are deliberately kept by Eraser.construct when unknown.
    own_functions=erase_functions(erased,own_functions) if erased else own_functions
    result=[]
    splitter=Splitter(split)
    for function in own_functions:
        result_type=re.sub(r'\s*\(.*$','',function['type']['qualType']).strip()
        touches=splitter.class_of({'qualType':result_type}) is not None or any(
            splitter.class_of(p.get('type',{})) is not None
            for p in function.get('inner',[]) if p.get('kind')=='ParmVarDecl')
        if not touches:
            result.append(function)
            continue
        owner=owners[function['id']]
        declaration=copy.deepcopy(function)
        prefix=owner.class_name+'_'
        if not declaration['name'].startswith(prefix):
            raise ValueError('mixed function must retain its source owner name')
        declaration['name']=declaration['name'][len(prefix):]
        result.extend(split_one(splitter,owner,declaration,False,source))
    result.extend(split_functions(split,source,{id(cls):friends[id(cls)] for cls in split}))
    # Split-class methods may still mention single-field companions in their
    # parameters/results. Their CXXThisExpr has already been split by field ID.
    return erase_functions(erased,result) if erased else result
