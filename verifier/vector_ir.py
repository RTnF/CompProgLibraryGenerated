"""Audited vector reads and updates composed with the shared scalar syntax.

This initial body subset has scalar returns, parameter vector references,
scalar automatic locals, fill-constructed local vectors and lexical scopes.
Pure conditions, for/while, branches, scalar increments and break are lowered
to the fuel-indexed control interpreter. Pure &&/|| preserve short circuiting,
and audited standard assertions become failing checks. Other nodes fail closed.
Range assign accepts pure begin/end endpoints with matching element types;
the runtime captures and validates both endpoints before changing the target.
"""
import re
from scalar_ir import expression, scalar_type, lean_type, lean_expression, function_return_type, TYPES
from vector_bindings import bindings_from_audit, verify_type_probes
from vector_stl import audit_vector_operations


def unwrap_lvalue(node):
    while node.get('kind')=='ParenExpr' or (node.get('kind')=='ImplicitCastExpr' and
            node.get('castKind')=='NoOp'):
        if len(node.get('inner',[]))!=1:
            raise ValueError('invalid lvalue wrapper')
        node=node['inner'][0]
    return node


class Body:
    def __init__(self, node, schema):
        self.node=node
        self.probes=[]
        self.loop_depth=0
        self.parameters=schema['parameters']
        self.bindings=list(self.parameters)
        params=[child for child in node.get('inner',[]) if child['kind']=='ParmVarDecl']
        self.slots={parameter['id']:index for index,parameter in enumerate(params)}
        if any(parameter.get('inner') for parameter in params):
            raise ValueError('parameter defaults or attributes are unsupported')

    def binding(self, node, kind):
        node=unwrap_lvalue(node)
        if node['kind']!='DeclRefExpr' or node['referencedDecl']['id'] not in self.slots:
            raise ValueError('direct local binding required')
        slot=self.slots[node['referencedDecl']['id']]
        binding=self.bindings[slot]
        if binding['kind']!=kind:
            raise ValueError('binding kind mismatch')
        return slot,binding

    def operation(self, node):
        operation=node.get('verifiedVectorOperation')
        element=node.get('verifiedVectorElement')
        if operation is None or element not in TYPES or element=='bool':
            raise ValueError('operation must resolve to an audited scalar-element std::vector')
        children=node.get('inner',[])
        if node['kind']=='CXXOperatorCallExpr' and operation=='operator[]' and len(children)==3:
            owner,args=children[1],children[2:]
        elif (node['kind']=='CXXMemberCallExpr' and children and
              children[0]['kind']=='MemberExpr' and len(children[0].get('inner',[]))==1):
            owner,args=children[0]['inner'][0],children[1:]
        else:
            raise ValueError('unsupported vector operation AST shape')
        slot,binding=self.binding(owner,'vector')
        width,signed,boolean=TYPES[element]
        ty=dict(width=width,signed=signed,boolean=boolean)
        if binding['element']!=ty:
            raise ValueError('audited vector element type and binding differ')
        return operation,slot,binding,args

    def extension(self, node, slots):
        if node['kind']=='BinaryOperator' and node.get('opcode') in ('&&','||'):
            children=node.get('inner',[])
            if len(children)!=2 or scalar_type(node)!=dict(width=1,signed=False,boolean=True):
                raise ValueError('boolean short-circuit operation required')
            return dict(kind='logical',type=scalar_type(node),conjunction=node['opcode']=='&&',
                left=self.expr(children[0]),right=self.expr(children[1]))
        if node.get('verifiedVectorOperation'):
            operation,slot,binding,args=self.operation(node)
            ty=binding['element']
            if operation=='size' and not args:
                result=dict(kind='vector_size',type=dict(width=64,signed=False,boolean=False),
                    element=ty,slot=slot)
            elif operation=='operator[]' and len(args)==1:
                result=dict(kind='vector_read',type=ty,element=ty,slot=slot,index=self.expr(args[0]))
            else:
                raise ValueError('effectful vector operations cannot occur in scalar expressions')
            if scalar_type(node)!=result['type']:
                raise ValueError('vector operation result type mismatch')
            return result
        if node['kind']=='MaterializeTemporaryExpr':
            children=node.get('inner',[])
            if len(children)!=1 or node.get('storageDuration')!='full expression':
                raise ValueError('only scalar full-expression temporaries are supported')
            value=self.expr(children[0])
            if scalar_type(node)!=value['type']:
                raise ValueError('scalar temporary type mismatch')
            return value
        if node['kind']=='ImplicitCastExpr' and node.get('castKind')=='NoOp':
            children=node.get('inner',[])
            if len(children)!=1:
                raise ValueError('invalid scalar const binding')
            value=self.expr(children[0])
            if scalar_type(node)!=value['type']:
                raise ValueError('const scalar wrapper changed type')
            return value
        if node['kind']=='DeclRefExpr':
            slot,binding=self.binding(node,'scalar')
            if scalar_type(node)!=binding['element']:
                raise ValueError('scalar binding type mismatch')
            return dict(kind='variable',type=binding['element'],slot=slot)
        return None

    def expr(self, node):
        return expression(node,self.slots,node_lowerer=self.extension)

    def scoped(self, node, loop=False):
        saved_slots=self.slots.copy();saved_bindings=self.bindings.copy()
        if loop:self.loop_depth+=1
        body=self.statement(node)
        if loop:self.loop_depth-=1
        self.slots=saved_slots;self.bindings=saved_bindings
        return body if node.get('kind')=='CompoundStmt' else [dict(kind='scope',body=body)]

    def statement(self, node):
        children=node.get('inner',[])
        kind=node['kind']
        if kind=='ParenExpr' and len(children)==1:
            return self.statement(children[0])
        if kind=='ConditionalOperator' and node.get('verifiedScalarAssert'):
            return [dict(kind='check',condition=self.expr(children[0]))]
        if kind=='NullStmt':return []
        if kind=='BreakStmt' and not children:
            if self.loop_depth==0:raise ValueError('break requires a supported enclosing loop')
            return [dict(kind='break')]
        if kind=='IfStmt' and len(children) in (2,3):
            if node.get('hasInit') or node.get('hasVar') or node.get('isConstexpr'):
                raise ValueError('if declarations and constexpr conditions are unsupported')
            condition=self.expr(children[0])
            yes=self.scoped(children[1])
            no=self.scoped(children[2]) if len(children)==3 else []
            return [dict(kind='branch',condition=condition,yes=yes,no=no)]
        if kind=='WhileStmt' and len(children)==2 and not node.get('hasVar'):
            condition=self.expr(children[0]);body=self.scoped(children[1],True)
            return [dict(kind='while',condition=condition,body=body)]
        if kind=='ForStmt' and len(children)==5:
            initial,condition_variable,condition,increment,body=children
            if condition_variable:raise ValueError('for condition declarations are unsupported')
            saved_slots=self.slots.copy();saved_bindings=self.bindings.copy()
            start=self.statement(initial) if initial else []
            test=self.expr(condition) if condition else dict(kind='literal',type=dict(width=1,signed=False,boolean=True),value=1)
            iteration=self.scoped(body,True)
            update=self.statement(increment) if increment else []
            self.slots=saved_slots;self.bindings=saved_bindings
            return [dict(kind='scope',body=start+[dict(kind='while',condition=test,body=iteration+update)])]
        if kind=='UnaryOperator' and node.get('opcode') in ('++','--') and len(children)==1:
            slot,binding=self.binding(children[0],'scalar')
            ty=binding['element']
            if not binding['writable'] or ty['boolean']:raise ValueError('writable integer increment required')
            value=dict(kind='binary',type=ty,operation='add' if node['opcode']=='++' else 'sub',
                left=self.expr(children[0]),right=dict(kind='literal',type=ty,value=1))
            return [dict(kind='assign',slot=slot,type=ty,value=value)]
        if node['kind']=='CompoundStmt':
            saved_slots=self.slots.copy();saved_bindings=self.bindings.copy()
            body=[]
            for child in children:
                body.extend(self.statement(child))
            self.slots=saved_slots;self.bindings=saved_bindings
            return [dict(kind='scope',body=body)]
        if node['kind']=='ReturnStmt' and len(children)==1:
            value=self.expr(children[0])
            if value['type']!=function_return_type(self.node):
                raise ValueError('return type mismatch')
            return [dict(kind='return',value=value)]
        if node['kind']=='DeclStmt':
            result=[]
            for declaration in children:
                spelling=declaration.get('type',{}).get('desugaredQualType',declaration.get('type',{}).get('qualType',''))
                if re.fullmatch(r'(const )?std::vector<.+>',spelling):
                    if declaration.get('storageClass') or len(declaration.get('inner',[]))!=1:
                        raise ValueError('automatic vector declaration required')
                    constructor=declaration['inner'][0]
                    if constructor['kind']=='ExprWithCleanups' and len(constructor.get('inner',[]))==1:
                        constructor=constructor['inner'][0]
                    if constructor.get('verifiedVectorConstructor')!='fill':
                        raise ValueError('audited standard fill constructor required')
                    arguments=constructor.get('inner',[])
                    if len(arguments)!=3 or arguments[2]['kind']!='CXXDefaultArgExpr':
                        raise ValueError('fill constructor requires the standard default allocator')
                    element=constructor['verifiedVectorElement']
                    allocator=arguments[2].get('type',{}).get('desugaredQualType','')
                    if allocator!=f'const std::allocator<{element}>':
                        raise ValueError('canonical default allocator required')
                    width,signed,boolean=TYPES[element]
                    ty=dict(width=width,signed=signed,boolean=boolean)
                    count,value=self.expr(arguments[0]),self.expr(arguments[1])
                    if count['type']!=dict(width=64,signed=False,boolean=False) or value['type']!=ty:
                        raise ValueError('constructor argument type mismatch')
                    name=declaration.get('name','')
                    location=node.get('range',{}).get('end',{})
                    if (not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name) or
                        'offset' not in location or 'spellingLoc' in location or 'expansionLoc' in location):
                        raise ValueError('named nonmacro local vector declaration required')
                    readonly=spelling.startswith('const ')
                    canonical=('const ' if readonly else '')+f'::std::vector<{element}>'
                    probe=('\n#if defined(__is_same) || defined(decltype) || defined(static_assert) || defined(std) || defined(vector) || defined(int) || defined(long) || defined(unsigned) || defined(signed) || defined(const)\n'
                        '#error vector identity keywords must not be macros\n#endif\n'
                        f'static_assert(__is_same(decltype({name}),{canonical}),"canonical local vector required");\n')
                    self.probes.append((location['offset']+location['tokLen'],probe))
                    result.append(dict(kind='construct',element=ty,writable=not readonly,count=count,value=value))
                    self.slots[declaration['id']]=len(self.bindings)
                    self.bindings.append(dict(kind='vector',element=ty,writable=not readonly))
                    continue
                if (declaration['kind']!='VarDecl' or declaration.get('storageClass') or
                    declaration.get('init')!='c' or len(declaration.get('inner',[]))!=1):
                    raise ValueError('only initialized scalar automatic locals are supported')
                ty=scalar_type(declaration)
                value=self.expr(declaration['inner'][0])
                if ty!=value['type']:
                    raise ValueError('initializer type mismatch')
                spelling=declaration['type'].get('desugaredQualType',declaration['type']['qualType'])
                writable='const' not in spelling.split()
                result.append(dict(kind='declare',type=ty,writable=writable,value=value))
                self.slots[declaration['id']]=len(self.bindings)
                self.bindings.append(dict(kind='scalar',element=ty,reference=False,writable=writable))
            return result
        if node['kind']=='BinaryOperator' and node.get('opcode')=='=' and len(children)==2:
            left=unwrap_lvalue(children[0]);value=self.expr(children[1])
            if left.get('verifiedVectorOperation'):
                operation,slot,binding,args=self.operation(left)
                if operation!='operator[]' or len(args)!=1 or not binding['writable']:
                    raise ValueError('writable vector subscript required')
                if value['type']!=binding['element']:
                    raise ValueError('element assignment type mismatch')
                return [dict(kind='write',slot=slot,element=binding['element'],index=self.expr(args[0]),value=value)]
            slot,binding=self.binding(left,'scalar')
            if not binding['writable'] or value['type']!=binding['element']:
                raise ValueError('writable scalar assignment of matching type required')
            return [dict(kind='assign',slot=slot,type=binding['element'],value=value)]
        if node.get('verifiedVectorOperation'):
            operation,slot,binding,args=self.operation(node)
            if operation=='assign' and len(args)==2:
                if not binding['writable']:raise ValueError('assign requires a writable destination')
                endpoints=[]
                for argument in args:
                    endpoint,source,source_binding,values=self.operation(unwrap_lvalue(argument))
                    if endpoint not in ('begin','end') or values or source_binding['element']!=binding['element']:
                        raise ValueError('assign requires pure begin/end of matching vector element types')
                    endpoints.append((source,endpoint=='end'))
                return [dict(kind='assign_range',slot=slot,element=binding['element'],
                    first=endpoints[0][0],last=endpoints[1][0],first_end=endpoints[0][1],last_end=endpoints[1][1])]
            if not binding['writable'] or len(args)!=1:
                raise ValueError('writable single-argument vector update required')
            value=self.expr(args[0])
            if operation=='reserve' and value['type']==dict(width=64,signed=False,boolean=False):
                return [dict(kind='reserve',slot=slot,element=binding['element'],value=value)]
            if operation in ('push_back','emplace_back') and value['type']==binding['element']:
                return [dict(kind='append_reserved',slot=slot,element=binding['element'],value=value)]
            raise ValueError('unsupported vector update or argument type')
        raise ValueError('unsupported vector body statement: '+node['kind'])

    def lower(self):
        if self.node.get('variadic') or self.node.get('storageClass'):
            raise ValueError('only ordinary nonvariadic function definitions are supported')
        bodies=[child for child in self.node.get('inner',[]) if child['kind']=='CompoundStmt']
        if len(bodies)!=1 or any(child['kind'] not in ('ParmVarDecl','CompoundStmt') for child in self.node.get('inner',[])):
            raise ValueError('function body required; attributes and templates are unsupported')
        statements=[]
        for child in bodies[0].get('inner',[]):
            if statements and statements[-1]['kind']=='return':
                raise ValueError('statements after return are unsupported')
            statements.extend(self.statement(child))
        if not statements or statements[-1]['kind']!='return':
            raise ValueError('one final scalar return is required')
        return dict(name=self.node['name'],parameters=self.parameters,
            result_type=function_return_type(self.node),body=statements)


def lower_source(source, include_dirs=()):
    audited=audit_vector_operations(source,include_dirs)
    schemas=bindings_from_audit(source,audited,include_dirs)['functions']
    functions=[]
    probes=[]
    for node,schema in zip(audited['functions'],schemas,strict=True):
        body=Body(node,schema)
        function=body.lower()
        probes.extend(body.probes)
        function['parameters']=schema['parameters']
        functions.append(function)
    verify_type_probes(source,probes,include_dirs)
    coverage='control_flow_scalar_return' if any(has_control(f['body']) for f in functions) else 'straight_line_scalar_return'
    return dict(coverage=coverage,functions=functions)


def has_control(value):
    if isinstance(value,dict):
        return value.get('kind') in ('branch','while','break') or any(has_control(v) for v in value.values())
    return isinstance(value,list) and any(has_control(v) for v in value)


def render_commands(statements):
    body='(.primitive .skip)'
    for statement in reversed(statements):
        kind=statement['kind']
        if kind=='scope':command=f"(.scope {render_commands(statement['body'])})"
        elif kind=='while':command=f"(.whileLoop {render_expression(statement['condition'])} {render_commands(statement['body'])})"
        elif kind=='branch':command=f"(.branch {render_expression(statement['condition'])} {render_commands(statement['yes'])} {render_commands(statement['no'])})"
        elif kind=='break':command='.breakLoop'
        else:command=f'(.primitive {render_statement(statement)})'
        body=f'(.sequence {command} {body})'
    return body


def render_expression(expr):
    def extension(value):
        if value['kind']=='logical':
            return f"(.logical {str(value['conjunction']).lower()} {render_expression(value['left'])} {render_expression(value['right'])})"
        if value['kind']=='vector_size':
            return f"(.size {lean_type(value['element'])} {value['slot']})"
        if value['kind']=='vector_read':
            return f"(.read {lean_type(value['element'])} {value['slot']} {render_expression(value['index'])})"
        return None
    return lean_expression(expr,extension)


def render_statement(statement):
    kind=statement['kind']
    if kind=='scope':
        body='.skip'
        for child in reversed(statement['body']):
            body=f'(.sequence {render_statement(child)} {body})'
        return f'(.scope {body})'
    if kind=='check':return f"(.check {render_expression(statement['condition'])})"
    if kind=='assign_range':return f"(.assignRange {statement['slot']} {statement['first']} {statement['last']} {lean_type(statement['element'])} {str(statement['first_end']).lower()} {str(statement['last_end']).lower()})"
    if kind=='return':return f"(.ret {render_expression(statement['value'])})"
    if kind=='declare':return f"(.declare {lean_type(statement['type'])} {str(statement['writable']).lower()} {render_expression(statement['value'])})"
    if kind=='construct':return f"(.construct {lean_type(statement['element'])} {str(statement['writable']).lower()} {render_expression(statement['count'])} {render_expression(statement['value'])})"
    if kind=='assign':return f"(.assign {statement['slot']} {lean_type(statement['type'])} {render_expression(statement['value'])})"
    constructor={'write':'write','reserve':'reserve','append_reserved':'appendReserved'}[kind]
    index=f"{render_expression(statement['index'])} " if kind=='write' else ''
    return f"(.{constructor} {statement['slot']} {lean_type(statement['element'])} {index}{render_expression(statement['value'])})"


def emit_lean(ir, namespace='VectorProgramInstances'):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',namespace):
        raise ValueError('invalid Lean namespace')
    control=ir['coverage']=='control_flow_scalar_return'
    lines=['-- Generated from audited Clang vector operations and scalar syntax.',
        'import Proofs.CppVectorLoop' if control else 'import Proofs.CppVectorProgram','',f'namespace {namespace}',
        'open Proofs.CppVectorLoop' if control else 'open Proofs.CppVectorProgram','']
    for function in ir['functions']:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',function['name']):
            raise ValueError('unsupported function name')
        params=[]
        for p in function['parameters']:
            ty=lean_type(p['element']);writable=str(p['writable']).lower()
            if p['kind']=='vector':params.append(f'.vector {ty} {writable}')
            else:params.append(f'.scalar {ty} {str(p["reference"]).lower()} {writable}')
        body='.skip'
        if not control:
            for statement in reversed(function['body']):
                body=f'(.sequence {render_statement(statement)} {body})'
        if control:body=render_commands(function['body'])
        program_type='LoopProgram' if control else 'Program'
        lines.append(f'def «{function["name"]}» : {program_type} := ⟨[{", ".join(params)}],{lean_type(function["result_type"])},{body}⟩')
    return '\n'.join([*lines,'',f'end {namespace}',''])
