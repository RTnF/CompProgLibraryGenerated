"""Sequence scalar-only constructor delegation before constructor field export.

A returned record is materialized once, then every field is copied/moved into
its destination. Nontrivial special members and non-scalar fields stay outside
this path; arbitrary object/lifetime semantics are not inferred from it.
"""
import copy
from pathlib import Path
import re

from class_lowering import SCALAR_FIELD_TYPES, scalar_record_type, selected_type_pattern, validate_scalar_value_record
from inline_ast import Inliner, select_constexpr_body


def spelling(node):
    info=node.get('type',{})
    return info.get('desugaredQualType',info.get('qualType',''))


def unwrap(node):
    while (node.get('kind') in ('ExprWithCleanups','MaterializeTemporaryExpr','CXXBindTemporaryExpr','ParenExpr') or
           node.get('kind') in ('ImplicitCastExpr','CXXFunctionalCastExpr') and node.get('castKind')=='ConstructorConversion'):
        children=node.get('inner',[])
        if len(children)!=1:
            raise ValueError('scalar delegation wrapper requires one expression')
        node=children[0]
    return node


class ScalarDelegation:
    def __init__(self,record,fields,source,display,rewrite_this,standard_roots=(),include_dirs=()):
        self.record,self.fields,self.source=record,fields,Path(source).resolve()
        self.rewrite_this=rewrite_this
        self.counter=0
        self.root_constructor=''
        self.pattern=selected_type_pattern(record,display)
        if self.pattern is None:
            choices={display,record.get('_copy_qualified',display)}
            self.pattern=re.compile(r'(?:::)?(?:'+'|'.join(re.escape(n) for n in choices)+')')
        if record.get('tagUsed') not in ('class','struct') or any(
                spelling(f).removeprefix('const ') not in SCALAR_FIELD_TYPES for f in fields):
            raise ValueError('object delegation currently requires scalar fields')
        try:
            validate_scalar_value_record(record,fields)
        except ValueError as error:
            raise ValueError('object delegation requires trivial copy/move/destruction') from error
        self.constructors=[c for c in record.get('inner',[]) if c.get('kind')=='CXXConstructorDecl']
        self.cloner=Inliner(())
        self.cloner.fresh=self.fresh
        self.receiver_methods=None
        self.standard_roots,self.include_dirs=standard_roots,include_dirs
        self.argument_calls=set()

    def receiver_calls(self,node,locals_):
        """Give every call its materialized receiver, including nested calls."""
        if isinstance(node,list):return [self.receiver_calls(c,locals_) for c in node]
        if not isinstance(node,dict):return node
        if node.get('kind')=='CXXMemberCallExpr':
            children=node.get('inner',[])
            if not children or children[0].get('kind')!='MemberExpr':
                raise ValueError('temporary receiver requires a direct member call')
            member=children[0];bases=member.get('inner',[])
            base=bases[0] if len(bases)==1 else {}
            while base.get('kind')=='ImplicitCastExpr' and base.get('castKind')=='NoOp' and len(base.get('inner',[]))==1:
                base=base['inner'][0]
            method=self.receiver_methods.get(member.get('referencedMemberDecl'))
            if base.get('kind')!='CXXThisExpr' or method is None or '_fields' not in method:
                raise ValueError('temporary receiver calls must name a method of the selected record')
            # An lvalue call expression carries the referred-to scalar type;
            # only the declaration distinguishes a reference result.
            result=spelling(method).split('(',1)[0].strip().removeprefix('const ')
            if result!='void' and result not in SCALAR_FIELD_TYPES:
                raise ValueError('temporary receiver methods require scalar or void results')
            if any(f['id'] not in locals_ for f in self.fields):
                raise ValueError('temporary receiver calls require all fields to be initialized')
            refs=[Inliner.field_reference(locals_[f['id']]) for f in self.fields]
            head=dict(kind='DeclRefExpr',type=method['type'],valueCategory='lvalue',
                referencedDecl={k:method[k] for k in ('kind','id','name','type')})
            return dict(node,kind='CallExpr',inner=[head,*refs,*self.receiver_calls(children[1:],locals_)])
        return {k:self.receiver_calls(v,locals_) if k=='inner' else v for k,v in node.items()}

    def receiver_inliner(self):
        if self.receiver_methods is None:
            # The ordinary method lowering retains the exact declaration IDs,
            # const/mutable field references and source audit. Explicit field
            # arguments keep nested calls tied to the same temporary object.
            from ast_stream import class_method_functions
            methods=class_method_functions(self.record,self.source,include_constructors=False)
            self.receiver_methods={m['id']:m for m in methods}
            normalized=[]
            for method in methods:
                if '_fields' not in method:continue
                self.body(method)
                locals_={f['id']:p for f,p in zip(self.fields,method['_fields'],strict=True)}
                normalized.append(dict(method,inner=[self.receiver_calls(c,locals_)
                    if c.get('kind')=='CompoundStmt' else c for c in method['inner']]))
            self.cloner=Inliner(normalized)
            self.cloner.fresh=self.fresh
        return self.cloner

    def fresh(self,name):
        self.counter+=1
        return f'delegate:{self.record["id"]}:{self.root_constructor}:{self.counter}:{name}'

    def owned(self,node):
        loc=node.get('loc',{})
        if ('offset' not in loc or 'spellingLoc' in loc or 'expansionLoc' in loc or
                loc.get('includedFrom',{}).get('file') not in (None,'<built-in>') or
                Path(loc.get('file',self.source)).resolve()!=self.source):
            raise ValueError('delegated declarations must belong to the original source')

    def body(self,node):
        self.owned(node)
        bodies=[c for c in node.get('inner',[]) if c.get('kind')=='CompoundStmt']
        if len(bodies)!=1 or any(c.get('kind','').endswith('Attr') for c in node.get('inner',[])):
            raise ValueError('delegated declaration needs one original body without attributes')
        return select_constexpr_body(bodies[0])

    def constructor(self,expression):
        if expression.get('kind') not in ('CXXConstructExpr','CXXTemporaryObjectExpr') or not scalar_record_type(
                expression.get('type',{}),self.pattern):
            raise ValueError('delegation must construct the selected record itself')
        signature=expression.get('ctorType',{}).get('qualType','')
        found=[c for c in self.constructors if c.get('type',{}).get('qualType')==signature]
        if len(found)!=1:
            raise ValueError('delegated constructor requires an exact source signature')
        if found[0].get('isDeleted') or found[0].get('explicitlyDeleted'):
            raise ValueError('delegation cannot use a deleted constructor')
        return found[0]

    def pure_argument(self,node):
        kind=node.get('kind');children=node.get('inner',[])
        if kind=='DeclRefExpr':
            return not children and node.get('referencedDecl',{}).get('kind') in ('ParmVarDecl','VarDecl')
        if kind in ('IntegerLiteral','CXXBoolLiteralExpr'):
            return not children
        if kind=='ImplicitCastExpr':
            return len(children)==1 and node.get('castKind') in ('LValueToRValue','IntegralCast','IntegralToBoolean','NoOp') and self.pure_argument(children[0])
        if kind=='ParenExpr':return len(children)==1 and self.pure_argument(children[0])
        if kind=='UnaryOperator':return node.get('opcode') in ('+','-','!','~') and len(children)==1 and self.pure_argument(children[0])
        if kind=='BinaryOperator':return node.get('opcode') in ('+','-','*','/','%','<','<=','>','>=','==','!=','&','|','^','<<','>>') and len(children)==2 and all(self.pure_argument(c) for c in children)
        if kind=='CallExpr' and children:
            head=children[0]
            while head.get('kind')=='ImplicitCastExpr' and len(head.get('inner',[]))==1:
                head=head['inner'][0]
            return (head.get('kind')=='DeclRefExpr' and head.get('referencedDecl',{}).get('id') in self.argument_calls
                    and all(self.pure_argument(c) for c in children[1:]))
        return False

    def audit_arguments(self,target,parameters,arguments):
        if all(self.pure_argument(a) for a in arguments) or not self.standard_roots:
            return
        # Run the existing STL identity audit on a disposable copy. Keep the
        # original call for the final stage audit and numeric-limit probes.
        # A user function with the same spelling does not earn permission.
        from vector_stl import audit_vector_nodes
        declarations=[]
        for p,arg in zip(parameters,arguments,strict=True):
            local=dict(kind='VarDecl',id=self.fresh('audit_value'),name='audit_value',
                type={'qualType':spelling(p)},init='c',inner=[copy.deepcopy(arg)],loc=p.get('loc',{}))
            declarations.append(dict(kind='DeclStmt',inner=[local]))
        body=dict(self.body(target),inner=declarations)
        function=dict(kind='FunctionDecl',id=self.fresh('argument_audit'),name='argument_audit',
            type={'qualType':'void ()'},loc=target.get('loc',{}),inner=[body])
        audited=audit_vector_nodes(self.source,[function],self.standard_roots,self.include_dirs)
        self.argument_calls.update(c['callee_id'] for c in audited.get('scalar_choices',[]))
        def collect(node):
            if node.get('kind')=='CallExpr' and 'verifiedNumericLimit' in node:
                head=node['inner'][0]
                while head.get('kind')=='ImplicitCastExpr' and len(head.get('inner',[]))==1:head=head['inner'][0]
                if head.get('kind')=='DeclRefExpr':self.argument_calls.add(head['referencedDecl']['id'])
            for child in node.get('inner',[]):collect(child)
        for function in audited['functions']:collect(function)

    def bind(self,target,arguments):
        parameters=[p for p in target.get('inner',[]) if p.get('kind')=='ParmVarDecl']
        if len(parameters)!=len(arguments):raise ValueError('delegated constructor argument count mismatch')
        if any(spelling(p).removeprefix('const ') not in SCALAR_FIELD_TYPES or p.get('inner') for p in parameters):
            raise ValueError('delegation requires scalar value parameters and pure scalar arguments')
        self.audit_arguments(target,parameters,arguments)
        prefix=[];subst={}
        for p,arg in zip(parameters,arguments,strict=True):
            ty=spelling(p)
            if ty.removeprefix('const ') not in SCALAR_FIELD_TYPES or p.get('inner') or not self.pure_argument(arg):
                raise ValueError('delegation requires scalar value parameters and pure scalar arguments')
            identity=self.fresh(p.get('name','argument'))
            declaration=dict(kind='VarDecl',id=identity,name=p.get('name','argument'),type={'qualType':ty},
                init='c',inner=[copy.deepcopy(arg)],loc=p.get('loc',{}))
            prefix.append(dict(kind='DeclStmt',inner=[declaration]))
            subst[p['id']]=('value',identity,ty,declaration['name'])
        body=self.body(target)
        def returns(node):
            return node.get('kind')=='ReturnStmt' or any(returns(c) for c in node.get('inner',[]))
        if returns(body):
            raise ValueError('early returns in delegated constructor bodies require a separate call boundary')
        payload=dict(kind='DelegatedContents',inner=[
            dict(kind='DelegatedPrefix',inner=target.get('_construction_prefix',[])),
            dict(kind='DelegatedInitializers',inner=[c for c in target.get('inner',[]) if c.get('kind')=='CXXCtorInitializer']),body])
        cloned=self.cloner.clone(payload,subst,{})['inner']
        prefix.extend(cloned[0]['inner'])
        initializers=cloned[1]['inner']
        body=cloned[2]
        return prefix,initializers,body

    def factory(self,expression,active):
        call=unwrap(expression)
        if call.get('kind')!='CallExpr' or len(call.get('inner',[]))!=1:
            raise ValueError('delegated temporary requires one zero-argument factory call')
        head=call['inner'][0]
        if head.get('kind')=='ImplicitCastExpr' and head.get('castKind')=='FunctionToPointerDecay' and len(head.get('inner',[]))==1:
            head=head['inner'][0]
        if head.get('kind')!='DeclRefExpr':raise ValueError('delegated factory must use an exact declaration')
        identity=head.get('referencedDecl',{}).get('id')
        candidates=[m for m in self.record.get('inner',[]) if m.get('kind')=='CXXMethodDecl' and m.get('id')==identity]
        if len(candidates)!=1:raise ValueError('delegated factory must belong to the selected record')
        method=candidates[0]
        result=method.get('type',{}).get('qualType','').split('(',1)[0].strip()
        if (method.get('storageClass')!='static' or '&' in result or
                not scalar_record_type({'qualType':result},self.pattern) or
                any(p.get('kind')=='ParmVarDecl' for p in method.get('inner',[]))):
            raise ValueError('delegation needs a static factory returning the record by value')
        prefix,locals_=self.materialize_factory(method,active)
        result=[]
        for field in self.fields:
            local=locals_[field['id']]
            ref=dict(kind='DeclRefExpr',type=field['type'],valueCategory='lvalue',
                referencedDecl={k:local[k] for k in ('kind','id','name','type')})
            result.append(dict(kind='CXXCtorInitializer',anyInit={k:field[k] for k in ('kind','id','name','type')},
                inner=[dict(kind='ImplicitCastExpr',type=field['type'],valueCategory='prvalue',castKind='LValueToRValue',inner=[ref])]))
        return prefix,result

    def factory_parameters(self,method):
        """Retain record references or trivial value copies as complete typed fields."""
        parameters=[];groups=[];records={}
        receiver=method.get('_factory_receiver_fields',[])
        original=[p for p in method.get('inner',[]) if p.get('kind')=='ParmVarDecl']
        if receiver and [p['id'] for p in original[:len(receiver)]]!=receiver:
            raise ValueError('receiver fields must precede explicit member parameters')
        for p in method.get('inner',[]):
            if p.get('kind')!='ParmVarDecl':continue
            ty=spelling(p)
            if p.get('id') in receiver:
                if not groups:groups.append(dict(kind='record_reference',count=len(receiver)))
                parameters.append(p)
                continue
            if scalar_record_type(p.get('type',{}),self.pattern):
                if ty.endswith('&&') or p.get('inner'):
                    raise ValueError('record factory parameters require values or lvalue references without defaults')
                by_reference=ty.endswith('&')
                constant=ty.removesuffix('&').strip().startswith('const ')
                mapped={}
                for f in self.fields:
                    field_ty=spelling(f)
                    if constant and not f.get('mutable') and not field_ty.startswith('const '):
                        field_ty='const '+field_ty
                    field=dict(kind='ParmVarDecl',id=self.fresh(p.get('name','object')+'_'+f['name']),
                        name=p.get('name','object')+'_'+f['name'],type={'qualType':field_ty+(' &' if by_reference else '')},
                        loc=p.get('loc',{}),_factory_field=True)
                    parameters.append(field);mapped[f['id']]=field
                records[p['id']]=mapped
                groups.append(dict(kind='record_reference' if by_reference else 'record_value',count=len(self.fields)))
            else:
                parameters.append(p);groups.append(dict(kind='scalar_value',count=1))
        def record_view(node,conditional=True):
            while node.get('kind') in ('ParenExpr','ImplicitCastExpr') and len(node.get('inner',[]))==1:
                if node.get('kind')=='ImplicitCastExpr' and node.get('castKind')!='NoOp':break
                node=node['inner'][0]
            if not scalar_record_type(node.get('type',{}),self.pattern):
                raise ValueError('record copy source must be the selected record')
            if node.get('kind')=='DeclRefExpr':
                mapped=records.get(node.get('referencedDecl',{}).get('id'))
                if mapped is not None:
                    return dict(kind='FactoryRecordFields',inner=[mapped[f['id']] for f in self.fields])
            if conditional and node.get('kind')=='ConditionalOperator' and len(node.get('inner',[]))==3:
                condition,yes,no=node['inner']
                condition=rewrite(condition)
                if spelling(condition)!='bool' or not self.pure_argument(condition):
                    raise ValueError('record copy conditions require pure scalar booleans')
                return dict(kind='FactoryRecordChoice',inner=[condition,record_view(yes,False),record_view(no,False)])
            raise ValueError('record copy sources require direct parameter views or one conditional')
        def rewrite(node):
            if isinstance(node,list):return [rewrite(c) for c in node]
            if not isinstance(node,dict):return node
            if records and node.get('kind') in ('CXXConstructExpr','CXXTemporaryObjectExpr') and scalar_record_type(
                    node.get('type',{}),self.pattern):
                target=self.constructor(node)
                if target.get('isImplicit'):
                    self.implicit_copy(node,target)
                    return dict(node,inner=[record_view(node['inner'][0])])
            if node.get('kind')=='MemberExpr' and len(node.get('inner',[]))==1:
                base=node['inner'][0]
                while base.get('kind') in ('ParenExpr','ImplicitCastExpr') and len(base.get('inner',[]))==1:
                    if base.get('kind')=='ImplicitCastExpr' and base.get('castKind')!='NoOp':break
                    base=base['inner'][0]
                mapped=records.get(base.get('referencedDecl',{}).get('id')) if base.get('kind')=='DeclRefExpr' else None
                if mapped is not None:
                    parameter=mapped.get(node.get('referencedMemberDecl'))
                    if parameter is None:raise ValueError('record factory arguments require direct field accesses')
                    return dict(kind='DeclRefExpr',type=node['type'],valueCategory='lvalue',
                        referencedDecl={k:parameter[k] for k in ('kind','id','name','type')})
            if node.get('kind')=='DeclRefExpr' and node.get('referencedDecl',{}).get('id') in records:
                raise ValueError('record factory argument escapes its field view')
            return {k:rewrite(v) if k=='inner' else v for k,v in node.items()}
        body=rewrite(self.body(method))
        return dict(method,inner=parameters+[body]),groups

    def implicit_copy(self,expression,target):
        parameters=[p for p in target.get('inner',[]) if p.get('kind')=='ParmVarDecl']
        if (not target.get('isImplicit') or target.get('explicitlyDefaulted')!='default' or
                len(parameters)!=1 or len(expression.get('inner',[]))!=1 or
                not spelling(parameters[0]).endswith('&') or
                not scalar_record_type(parameters[0].get('type',{}),self.pattern)):
            raise ValueError('record returns require an implicit defaulted copy or move')

    def materialize_copy(self,expression,target):
        self.implicit_copy(expression,target)
        view=expression['inner'][0];prefix=[]
        def read(parameter):
            ty=spelling(parameter).removesuffix(' &')
            ref=dict(kind='DeclRefExpr',type={'qualType':ty},valueCategory='lvalue',
                referencedDecl={k:parameter[k] for k in ('kind','id','name','type')})
            return dict(kind='ImplicitCastExpr',castKind='LValueToRValue',type={'qualType':ty.removeprefix('const ')},
                valueCategory='prvalue',inner=[ref])
        if view.get('kind')=='FactoryRecordChoice':
            condition,yes,no=view['inner']
            flag=dict(kind='VarDecl',id=self.fresh('copy_condition'),name='copy_condition',
                type={'qualType':'const bool'},init='c',inner=[condition])
            prefix.append(dict(kind='DeclStmt',inner=[flag]))
            values=[dict(kind='ConditionalOperator',type={'qualType':spelling(f).removeprefix('const ')},
                valueCategory='prvalue',inner=[read(flag),read(a),read(b)])
                for f,a,b in zip(self.fields,yes['inner'],no['inner'],strict=True)]
        elif view.get('kind')=='FactoryRecordFields':
            values=[read(p) for p in view['inner']]
        else:
            raise ValueError('implicit record copies require audited parameter field views')
        locals_={}
        for f,value in zip(self.fields,values,strict=True):
            if value.get('kind')=='ConditionalOperator':
                value,selected=self.cloner.conditional(value,{})
                prefix.extend(selected)
            local=dict(kind='VarDecl',id=self.fresh(f['name']),name='returned_'+f['name'],
                type=f['type'],init='c',inner=[value],loc=f.get('loc',{}))
            prefix.append(dict(kind='DeclStmt',inner=[local]));locals_[f['id']]=local
        return prefix,locals_

    def materialize_member_choice(self,method,value,leading,active):
        children=value.get('inner',[])
        if (len(children)!=3 or spelling(children[0])!='bool' or not self.pure_argument(children[0]) or
                not scalar_record_type(value.get('type',{}),self.pattern) or
                any(unwrap(a).get('kind')=='ConditionalOperator' for a in children[1:])):
            raise ValueError('record member choices require one pure boolean and direct constructor/copy branches')
        locals_={};prefix=list(leading)
        for field in self.fields:
            info={'qualType':spelling(field).removeprefix('const ')}
            local=dict(kind='VarDecl',id=self.fresh('choice_'+field['name']),name='choice_'+field['name'],
                type=info,init='c',inner=[dict(kind='IntegerLiteral',type=info,value='0',valueCategory='prvalue')])
            locals_[field['id']]=local;prefix.append(dict(kind='DeclStmt',inner=[local]))
        branches=[]
        parameters=[p for p in method.get('inner',[]) if p.get('kind')=='ParmVarDecl']
        for expression in children[1:]:
            branch=dict(method,inner=parameters+[dict(kind='CompoundStmt',inner=[dict(kind='ReturnStmt',inner=[expression])])])
            statements,values=self.materialize_factory(branch,active)
            for field in self.fields:
                local=locals_[field['id']];source=values[field['id']];info=local['type']
                target_ref=dict(kind='DeclRefExpr',type=info,valueCategory='lvalue',
                    referencedDecl={k:local[k] for k in ('kind','id','name','type')})
                source_ref=dict(kind='DeclRefExpr',type=source['type'],valueCategory='lvalue',
                    referencedDecl={k:source[k] for k in ('kind','id','name','type')})
                read=dict(kind='ImplicitCastExpr',castKind='LValueToRValue',type=info,valueCategory='prvalue',inner=[source_ref])
                statements.append(dict(kind='BinaryOperator',opcode='=',type=info,valueCategory='lvalue',inner=[target_ref,read]))
            branches.append(dict(kind='CompoundStmt',inner=statements))
        prefix.append(dict(kind='IfStmt',hasElse=True,inner=[children[0],*branches]))
        return prefix,locals_

    def materialize_factory(self,method,active=()):
        result=spelling(method).split('(',1)[0].strip()
        parameters=[p for p in method.get('inner',[]) if p.get('kind')=='ParmVarDecl']
        if ((method.get('storageClass')!='static' and not method.get('_factory_friend') and not method.get('_factory_member')) or '&' in result or
                not scalar_record_type({'qualType':result},self.pattern)):
            raise ValueError('factory must return the selected record by value')
        if any((spelling(p).removeprefix('const ').removesuffix(' &') if p.get('_factory_field')
                else spelling(p).removeprefix('const ')) not in SCALAR_FIELD_TYPES or p.get('inner') for p in parameters):
            raise ValueError('factory stages require scalar value parameters without defaults')
        statements=self.body(method).get('inner',[])
        leading=statements[:-1] if method.get('_factory_member') else []
        def returns(node):
            return node.get('kind')=='ReturnStmt' or any(returns(c) for c in node.get('inner',[]))
        if (not statements or (not method.get('_factory_member') and len(statements)!=1) or
                statements[-1].get('kind')!='ReturnStmt' or len(statements[-1].get('inner',[]))!=1 or
                any(returns(n) for n in leading)):
            raise ValueError('delegated factory must contain exactly one returned construction')
        value=unwrap(statements[-1]['inner'][0])
        if method.get('_factory_member') and value.get('kind')=='ConditionalOperator':
            return self.materialize_member_choice(method,value,leading,active)
        target=self.constructor(value)
        if target.get('isImplicit'):
            prefix,locals_=self.materialize_copy(value,target)
            return leading+prefix,locals_
        target=self.normalize(target,active)
        prefix,inits,body=self.bind(target,value.get('inner',[]))
        prefix=leading+prefix
        inliner=self.receiver_inliner()
        by_field={i.get('anyInit',{}).get('id'):i for i in inits}
        locals_={}
        for field in self.fields:
            init=by_field.get(field['id'],{}).get('inner',[])
            if len(init)!=1:raise ValueError('factory construction must initialize every original field')
            local=dict(kind='VarDecl',id=self.fresh(field['name']),name='returned_'+field['name'],
                type=field['type'],init='c',inner=[self.receiver_calls(
                    self.rewrite_this(init[0],self.fields,locals_),locals_)],loc=field.get('loc',{}))
            prefix.append(dict(kind='DeclStmt',inner=[local]));locals_[field['id']]=local
        materialized=self.receiver_calls(self.rewrite_this(body,self.fields,locals_),locals_)
        prefix.extend(inliner.expand_statement(materialized,target))
        return prefix,locals_

    def normalize(self,ctor,active=()):
        if not active:self.root_constructor=ctor.get('id','')
        if ctor.get('id') in active:raise ValueError('recursive constructor delegation is unsupported')
        active=(*active,ctor.get('id'))
        body=self.body(ctor)
        inits=[i for i in ctor.get('inner',[]) if i.get('kind')=='CXXCtorInitializer']
        if {i.get('anyInit',{}).get('id') for i in inits}=={f['id'] for f in self.fields}:
            return ctor
        if len(inits)!=1 or not scalar_record_type(inits[0].get('delegatingInit',{}),self.pattern) or len(inits[0].get('inner',[]))!=1:
            raise ValueError('construction stages require every field initializer or one audited scalar delegation')
        expression=unwrap(inits[0]['inner'][0]);target=self.constructor(expression)
        if target.get('isImplicit'):
            if target.get('explicitlyDefaulted')!='default' or len(expression.get('inner',[]))!=1:
                raise ValueError('delegated copy/move must use the implicit defaulted declaration')
            prefix,initializers=self.factory(expression['inner'][0],active)
            rewritten=body
        else:
            target=self.normalize(target,active)
            prefix,initializers,delegated_body=self.bind(target,expression.get('inner',[]))
            rewritten=dict(body,inner=[delegated_body]+body.get('inner',[]))
        parameters=[p for p in ctor.get('inner',[]) if p.get('kind')=='ParmVarDecl']
        return dict(ctor,inner=parameters+initializers+[rewritten],_construction_prefix=prefix)


def expand_scalar_delegation(record,ctor,fields,source,display,rewrite_this,standard_roots=(),include_dirs=()):
    return ScalarDelegation(record,fields,source,display,rewrite_this,standard_roots,include_dirs).normalize(ctor)
