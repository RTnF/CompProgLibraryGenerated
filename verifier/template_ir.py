"""Primary-template syntax and explicit builtin integral specialization.

Dependent operations remain unresolved in primary IR. Specialization is only
permitted for canonical builtin types supported by the scalar frontend. No
user-defined operator is assumed pure, total, constant-cost or builtin.
"""
import argparse
import json
import re
from pathlib import Path

from scalar_ir import (TYPES, SIGNED_CONVERSIONS, source_ast, integer_cast,
                       apply_conversion_policy)
from state_ir import sequence
from offline import disable_network
from clang_ast import normalized

COMPARISONS={'<':'lt','<=':'le','>':'gt','>=':'ge','==':'eq','!=':'ne'}
RANK={'bool':0,'int':1,'unsigned int':1,'long':2,'unsigned long':2,
      'long long':3,'unsigned long long':3}


def scalar(spelling):
    if spelling not in TYPES:
        raise ValueError(f'unsupported builtin template argument: {spelling}')
    width,signed,boolean=TYPES[spelling]
    return {'width':width,'signed':signed,'boolean':boolean}


class Primary:
    def __init__(self,names):
        self.names=names
        self.slots={}
        self.parameters=[]

    def type(self,spelling):
        base=re.sub(r'^const\s+','',spelling)
        if base in self.names:
            return {'kind':'parameter','index':self.names[base]}
        scalar(base)
        return {'kind':'scalar','spelling':base}

    def expression(self,node):
        kind=node.get('kind');children=node.get('inner',[])
        if kind=='ParenExpr' and len(children)==1:
            return self.expression(children[0])
        if kind=='DeclRefExpr' and not children:
            ref=node.get('referencedDecl',{})
            if ref.get('kind')!='ParmVarDecl' or ref.get('id') not in self.slots:
                raise ValueError('primary expression must refer to a parameter')
            slot=self.slots[ref['id']]
            ty=self.type(node['type']['qualType'])
            if ty!=self.parameters[slot]['type']:
                raise ValueError('primary reference type mismatch')
            return {'kind':'variable','type':ty,'slot':slot}
        if kind in ('IntegerLiteral','CXXBoolLiteralExpr') and not children:
            return {'kind':'literal','type':self.type(node['type']['qualType']),
                    'value':int(node['value'])}
        if kind=='ImplicitCastExpr' and len(children)==1:
            if node.get('castKind')=='LValueToRValue':
                return self.expression(children[0])
            if node.get('castKind') in ('IntegralCast','IntegralToBoolean'):
                return {'kind':'cast','type':self.type(node['type']['qualType']),
                        'operand':self.expression(children[0])}
            raise ValueError('unsupported primary implicit conversion')
        if kind=='BinaryOperator' and node.get('opcode') in COMPARISONS and len(children)==2:
            dependent=node['type']['qualType']=='<dependent type>'
            if not dependent and node['type']['qualType']!='bool':
                raise ValueError('unsupported primary comparison result')
            return {'kind':'comparison','operator':node['opcode'],
                    'resolution':'dependent' if dependent else 'builtin',
                    'left':self.expression(children[0]),'right':self.expression(children[1])}
        if (kind=='CXXOperatorCallExpr' and len(children)==3
                and node['type']['qualType']=='<dependent type>'):
            callee=children[0]
            operator=callee.get('name','').removeprefix('operator')
            if (callee.get('kind')!='UnresolvedLookupExpr' or operator not in COMPARISONS
                    or callee.get('inner')):
                raise ValueError('unsupported dependent operator lookup')
            return {'kind':'comparison','operator':operator,'resolution':'dependent',
                    'lookup':normalized(callee),
                    'left':self.expression(children[1]),'right':self.expression(children[2])}
        raise ValueError(f'unsupported primary expression: {kind}')

    def statement(self,node):
        kind=node.get('kind');children=node.get('inner',[])
        if kind=='CompoundStmt':
            return {'kind':'scope','body':sequence([self.statement(c) for c in children])}
        if kind=='IfStmt' and len(children) in (2,3):
            if node.get('hasInit') or node.get('hasVar') or node.get('isConstexpr'):
                raise ValueError('unsupported primary if form')
            return {'kind':'branch','condition':self.expression(children[0]),
                    'yes':{'kind':'scope','body':self.statement(children[1])},
                    'no':{'kind':'scope','body':self.statement(children[2])} if len(children)==3 else {'kind':'skip'},
                    'condition_conversion':'requires_resolution'}
        if kind=='BinaryOperator' and node.get('opcode')=='=' and len(children)==2:
            target=self.expression(children[0])
            if target['kind']!='variable' or not self.parameters[target['slot']]['writable']:
                raise ValueError('primary assignment requires a writable parameter')
            return {'kind':'assignment','slot':target['slot'],
                    'value':self.expression(children[1]),'resolution':'requires_resolution'}
        if kind=='ReturnStmt' and len(children)==1:
            return {'kind':'return','value':self.expression(children[0])}
        if kind=='NullStmt' and not children:
            return {'kind':'skip'}
        raise ValueError(f'unsupported primary statement: {kind}')


def lower_template(node):
    if node.get('kind')!='FunctionTemplateDecl':
        raise ValueError('primary function templates required')
    names={};function=None
    for child in node.get('inner',[]):
        if child.get('kind')=='TemplateTypeParmDecl' and function is None:
            name=child.get('name')
            if (not name or name in names or child.get('depth')!=0 or child.get('index')!=len(names)
                    or child.get('isParameterPack') or child.get('defaultArg') or child.get('inner')):
                raise ValueError('only unnested named type parameters without defaults or packs are supported')
            names[name]=len(names)
        elif child.get('kind')=='FunctionDecl' and function is None:
            function=child
        else:
            raise ValueError('primary syntax entrypoint refuses attributes, specializations and instance declarations')
    if not names or function is None:
        raise ValueError('type parameters and a primary definition required')
    if function.get('variadic') or function.get('storageClass') or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',function.get('name','')):
        raise ValueError('unsupported primary function')
    signature=function['type']['qualType']
    if not signature.endswith(')'):
        raise ValueError('unsupported primary function qualifier')
    result=signature.split('(',1)[0].strip()
    scalar(result)  # Dependent object returns need lifetime/copy contracts.
    primary=Primary(names);body=None
    for child in function.get('inner',[]):
        if child.get('kind')=='ParmVarDecl' and body is None and not child.get('inner'):
            spelling=child['type']['qualType']
            if 'volatile' in spelling or '&&' in spelling or not spelling.endswith(' &'):
                raise ValueError('primary syntax currently requires lvalue-reference parameters')
            base=spelling[:-2]
            primary.slots[child['id']]=len(primary.parameters)
            primary.parameters.append({'type':primary.type(base),'reference':True,
                                       'writable':not base.startswith('const ')})
        elif child.get('kind')=='CompoundStmt' and body is None:
            body=primary.statement(child)
        else:
            raise ValueError('unsupported primary function child')
    if body is None:
        raise ValueError('primary body required')
    return {'name':function['name'],'type_parameters':len(names),'parameters':primary.parameters,
            'result_type':{'kind':'scalar','spelling':result},'body':body,
            'coverage':'primary_syntax_only'}


def lower_source(source,declaration_filter='cp::',include_dirs=()):
    templates=[lower_template(n) for n in source_ast(source,declaration_filter,include_dirs)]
    if not templates or len({t['name'] for t in templates})!=len(templates):
        raise ValueError('nonempty uniquely named primary templates required')
    return {'abi':'LP64: int32, long64, long-long64','templates':templates}


def common_integer(left,right):
    left='int' if left=='bool' else left
    right='int' if right=='bool' else right
    if left==right:return left
    if RANK[left]<RANK[right]:left,right=right,left
    if scalar(left)['signed']==scalar(right)['signed']:return left
    if not scalar(left)['signed']:return left
    if scalar(left)['width']>scalar(right)['width']:return left
    return 'unsigned '+left


def specialize(template,arguments,signed_conversion='checked'):
    if len(arguments)!=template['type_parameters']:
        raise ValueError('template argument count mismatch')
    for spelling in arguments:scalar(spelling)
    apply_conversion_policy([],signed_conversion)
    def spelling(ty):
        return arguments[ty['index']] if ty['kind']=='parameter' else ty['spelling']
    def convert(value,source,target):
        return value if source==target else integer_cast(scalar(target),value,signed_conversion)
    def expression(e):
        kind=e['kind']
        if kind in ('variable','literal'):
            name=spelling(e['type']);value={k:v for k,v in e.items() if k!='type'}
            return {**value,'type':scalar(name)},name
        if kind=='cast':
            operand,_=expression(e['operand']);target=spelling(e['type'])
            return integer_cast(scalar(target),operand,signed_conversion),target
        if kind=='comparison':
            left,lt=expression(e['left']);right,rt=expression(e['right'])
            common=common_integer(lt,rt)
            return {'kind':'binary','type':scalar('bool'),'operation':COMPARISONS[e['operator']],
                    'left':convert(left,lt,common),'right':convert(right,rt,common)},'bool'
        raise ValueError('unresolved primary expression')
    def statement(s):
        kind=s['kind']
        if kind=='skip':return dict(s)
        if kind=='scope':return {'kind':'scope','body':statement(s['body'])}
        if kind=='sequence':return {'kind':'sequence','first':statement(s['first']),'rest':statement(s['rest'])}
        if kind=='branch':
            condition,ty=expression(s['condition'])
            return {'kind':'branch','condition':convert(condition,ty,'bool'),
                    'yes':statement(s['yes']),'no':statement(s['no'])}
        if kind=='assignment':
            value,ty=expression(s['value']);target=spelling(template['parameters'][s['slot']]['type'])
            return {'kind':'assign','slot':s['slot'],'value':convert(value,ty,target)}
        if kind=='return':
            value,ty=expression(s['value']);target=spelling(template['result_type'])
            return {'kind':'return','value':convert(value,ty,target)}
        raise ValueError('unresolved primary statement')
    name=template['name']
    return {'name':name+'__'+'__'.join(a.replace(' ','_') for a in arguments),
            'cpp_name':name,'template_arguments':list(arguments),
            'parameters':[{**p,'type':scalar(spelling(p['type']))} for p in template['parameters']],
            'result_type':scalar(spelling(template['result_type'])),'body':statement(template['body'])}


INTEGRAL_NAMES={'bool':'boolean','int':'i32','unsigned int':'u32',
                'long':'signedLong','unsigned long':'unsignedLong',
                'long long':'signedLongLong','unsigned long long':'unsignedLongLong'}


def emit_lean(ir,namespace='Proofs.IntegralExtrema'):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',namespace):
        raise ValueError('invalid Lean template namespace')
    def type_expr(ty):
        if ty['kind']=='parameter':return f'(.parameter {ty["index"]})'
        return f'(.scalar .{INTEGRAL_NAMES[ty["spelling"]]})'
    def expression(e):
        kind=e['kind']
        if kind=='variable':return f'(.variable {type_expr(e["type"])} {e["slot"]})'
        if kind=='literal':return f'(.literal {type_expr(e["type"])} ({e["value"]}))'
        if kind=='cast':return f'(.cast {type_expr(e["type"])} {expression(e["operand"])})'
        if kind=='comparison':return f'(.comparison .{COMPARISONS[e["operator"]]} {expression(e["left"])} {expression(e["right"])})'
        raise ValueError('unsupported Lean template expression')
    def statement(s):
        kind=s['kind']
        if kind=='skip':return '.skip'
        if kind=='scope':return f'(.scope {statement(s["body"])})'
        if kind=='sequence':return f'(.sequence {statement(s["first"])} {statement(s["rest"])})'
        if kind=='branch':return f'(.branch {expression(s["condition"])} {statement(s["yes"])} {statement(s["no"])})'
        if kind=='assignment':return f'(.assign {s["slot"]} {expression(s["value"])})'
        if kind=='return':return f'(.ret {expression(s["value"])})'
        raise ValueError('unsupported Lean template statement')
    lines=['-- Generated integral template family from primary syntax.',
           '-- Class, enum and floating arguments remain unresolved in the JSON IR.',
           'import Proofs.CppTemplate','',f'namespace {namespace}',
           'open Proofs.CppTemplate','']
    for t in ir['templates']:
        params=', '.join(f'⟨{type_expr(p["type"])}, {str(p["reference"]).lower()}, {str(p["writable"]).lower()}⟩' for p in t['parameters'])
        lines += [f'def «{t["name"]}» : TemplateProgram :=',
                  f'  ⟨{t["type_parameters"]}, [{params}], {type_expr(t["result_type"])},',
                  f'   {statement(t["body"])}⟩','']
    return '\n'.join(lines+[f'end {namespace}',''])


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('source',type=Path);parser.add_argument('--declaration-filter',default='cp::')
    args=parser.parse_args();disable_network()
    print(json.dumps(lower_source(args.source,args.declaration_filter),indent=2))
