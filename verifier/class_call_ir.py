"""Same-TU class reference receivers lowered to the nested caller interpreter.

The class profile is the audited flat-vector-plus-scalars profile. Implicit
local copies and defined local constructors use audited declaration-ordered fields. Method
bodies use the existing nested lowering, including their early returns. Free
callers accept reference receivers and scalar parameters/locals/control.
Scalar calls occupy a complete initializer, assignment, return or discarded
expression; calls in conditions or compound expressions fail closed. Default
arguments resolve to the original same-TU parameter initializer at each use;
existing pure scalar argument and reference restrictions still apply.
"""
import copy
import hashlib
import re
from pathlib import Path

from ast_stream import class_method_functions, class_construction_stages
from class_copy import audit_copy_record
from class_assign import audit_assignment_record
from class_copy_layout import _field_layout
from inline_ast import inline_functions
from nested_ir import NestedBody, emit_lean, render_expression, render_statement, terminal_return_kinds
from scalar_ir import apply_conversion_policy, function_return_type, lean_type, scalar_type, TYPES
from scalar_stl import walk
from state_ir import ValueCalls, parameter_type
from vector_bindings import bindings_from_audit, verify_type_probes
from vector_ir import Body, unwrap_lvalue
from vector_stl import translation_unit, audit_vector_nodes


def _element(spelling):
    width, signed, boolean = TYPES[spelling]
    return dict(width=width, signed=signed, boolean=boolean)


def _pure_argument(node):
    if any(n.get('kind') in ('CallExpr','CXXMemberCallExpr','CXXOperatorCallExpr',
                             'CompoundAssignOperator','ConditionalOperator') or
           n.get('kind') == 'UnaryOperator' and n.get('opcode') in ('++','--') or
           n.get('kind') == 'BinaryOperator' and n.get('opcode') == '=' for n in walk(node)):
        raise ValueError('method arguments must be side-effect-free scalar expressions')


def _parameter_defaults(function):
    """Keep original declaration expressions separate from executable parameters."""
    defaults = []
    clean = copy.deepcopy(function)
    for original, parameter in zip(
            [n for n in function.get('inner', []) if n.get('kind') == 'ParmVarDecl'],
            [n for n in clean.get('inner', []) if n.get('kind') == 'ParmVarDecl'],strict=True):
        children = original.get('inner', [])
        if children:
            if len(children) != 1 or original.get('init') != 'c':
                raise ValueError('one declaration-owned default argument expression required')
            defaults.append(copy.deepcopy(children[0]))
            parameter.pop('inner',None)
            parameter.pop('init',None)
        else:
            defaults.append(None)
    return clean,defaults


def _default_expression_identity(node):
    # Clang elides repeated source-location fields in a declaration dump but
    # repeats them in CXXDefaultArgExpr. Keep all node IDs and semantic fields.
    if isinstance(node,dict):
        return {k:_default_expression_identity(v) for k,v in node.items() if k not in ('loc','range')}
    if isinstance(node,list):
        return [_default_expression_identity(v) for v in node]
    return node


def _default_arguments(arguments, defaults):
    if len(arguments) != len(defaults):
        raise ValueError('parameter and argument counts differ')
    resolved = []
    for argument,default in zip(arguments,defaults,strict=True):
        if argument.get('kind') == 'CXXDefaultArgExpr':
            expanded = argument.get('inner', [])
            if default is None or (expanded and
                    _default_expression_identity(expanded) != _default_expression_identity([default])):
                raise ValueError('default argument requires its original declaration expression')
            argument = copy.deepcopy(default)
        resolved.append(argument)
    return resolved


class CallerBody(Body):
    def __init__(self, node, schema, objects, methods, copy_context):
        super().__init__(node,schema)
        self.objects, self.methods = objects, methods
        self.copy_context = copy_context
        self.pending = []
        self.calls_allowed = False
        self.discarded = False
        self.returns_unit = node['type'].get('desugaredQualType',node['type']['qualType']).split('(',1)[0].strip() == 'void'

    def extension(self, node, slots):
        if node.get('kind') != 'CXXMemberCallExpr':
            return super().extension(node,slots)
        if not self.calls_allowed:
            raise ValueError('class calls require a complete scalar expression outside conditions')
        children = node.get('inner', [])
        if not children or children[0].get('kind') != 'MemberExpr':
            raise ValueError('direct method member required')
        member = children[0]
        method = self.methods.get(member.get('referencedMemberDecl'))
        if method is None or len(member.get('inner', [])) != 1 or member.get('isArrow'):
            raise ValueError('method declaration must belong to the original class receiver')
        if self.copy_context.get('assignment'):
            obj = self.object_expression(member['inner'][0])
        else:
            receiver = unwrap_lvalue(member['inner'][0])
            if receiver.get('kind') != 'DeclRefExpr':
                raise ValueError('a class reference parameter receiver is required')
            obj = self.objects.get(receiver.get('referencedDecl', {}).get('id'))
        if obj is None or obj['const'] and not method['const']:
            raise ValueError('receiver identity or method const qualification mismatch')
        args = []
        parameters = method['program']['parameters']
        for slot, formal in zip(obj['slots'], parameters[:method['fields']], strict=True):
            if formal['kind'] == 'vector':
                args.append(dict(kind='vector',slot=slot))
            elif formal['reference']:
                args.append(dict(kind='reference',slot=slot))
            else:
                args.append(dict(kind='value',value=dict(kind='variable',type=formal['element'],slot=slot)))
        explicit = parameters[method['fields']:]
        if len(explicit) != len(children)-1:
            raise ValueError('method parameter and argument counts differ')
        actuals = _default_arguments(children[1:],method['defaults'])
        for child, formal in zip(actuals,explicit,strict=True):
            _pure_argument(child)
            if formal['kind'] != 'scalar':
                raise ValueError('explicit method arguments currently require scalar parameters')
            if formal['reference']:
                slot, binding = self.binding(child,'scalar')
                if binding['element'] != formal['element'] or formal['writable'] and not binding['writable']:
                    raise ValueError('method scalar reference type or permission mismatch')
                args.append(dict(kind='reference',slot=slot))
            else:
                value = self.expr(child)
                if value['type'] != formal['element']:
                    raise ValueError('method scalar argument type mismatch')
                args.append(dict(kind='value',value=value))
        ty = method['program']['result']
        if 'unit' in ty:
            if not self.discarded:raise ValueError('void method calls require a discarded expression')
            self.pending.append(dict(kind='class_invoke',name=method['program']['name'],arguments=args))
            return dict(kind='literal',type=dict(width=1,signed=False,boolean=True),value=0)
        if ty != scalar_type(node):
            raise ValueError('method call result type mismatch')
        self.pending.append(dict(kind='class_invoke',name=method['program']['name'],arguments=args))
        slot = len(self.bindings)
        self.bindings.append(dict(kind='scalar',element=ty,reference=False,writable=False))
        return dict(kind='variable',type=ty,slot=slot)

    def assignment_expression(self, node):
        plan = self.copy_context.get('assignment')
        if not plan:return None
        children = node.get('inner', [])
        if node.get('kind') == 'CXXOperatorCallExpr' and len(children) == 3:
            callee = children[0]
            while callee.get('kind') == 'ImplicitCastExpr' and callee.get('castKind') == 'FunctionToPointerDecay' and len(callee.get('inner', [])) == 1:
                callee = callee['inner'][0]
            if (callee.get('kind') != 'DeclRefExpr' or callee.get('referencedDecl', {}).get('id') != plan['assignment_id']):
                return None
            if callee['referencedDecl'].get('kind') != 'CXXMethodDecl':
                raise ValueError('assignment callee must be the audited class method')
            return 'operator',children[1],children[2]
        if node.get('kind') == 'CXXMemberCallExpr' and len(children) == 2:
            member = children[0]
            if member.get('kind') != 'MemberExpr' or member.get('referencedMemberDecl') != plan['assignment_id']:
                return None
            if member.get('isArrow') or len(member.get('inner', [])) != 1:
                raise ValueError('explicit assignment requires a direct object member')
            return 'member',member['inner'][0],children[1]
        return None

    def object_expression(self, node):
        if not self.calls_allowed:raise ValueError('class assignments require a complete expression outside conditions')
        names = {self.copy_context['qualified'],self.copy_context['qualified'].split('::')[-1]}
        while node.get('kind') in ('ParenExpr','ExprWithCleanups') or node.get('kind') == 'ImplicitCastExpr' and node.get('castKind') == 'NoOp':
            if len(node.get('inner', [])) != 1:raise ValueError('one class object operand required')
            node = node['inner'][0]
        if node.get('valueCategory') != 'lvalue' or node.get('type',{}).get('desugaredQualType',node.get('type',{}).get('qualType','')).removeprefix('const ') not in names:
            raise ValueError('assignment operands require original class lvalues')
        action = self.assignment_expression(node)
        if action:
            order,targetNode,sourceNode = action
            if order == 'operator':
                source = self.object_expression(sourceNode)
                target = self.object_expression(targetNode)
            else:
                target = self.object_expression(targetNode)
                source = self.object_expression(sourceNode)
            if target['const']:raise ValueError('assignment destination cannot be a const class receiver')
            fields = self.copy_context['assignment']['fields']
            self.pending.append(dict(kind='class_assign',target=target['slots'],source=source['slots'],profile=fields))
            return target
        if node.get('kind') != 'DeclRefExpr':raise ValueError('live object declaration or audited assignment result required')
        obj = self.objects.get(node.get('referencedDecl',{}).get('id'))
        if obj is None:raise ValueError('assignment object identity is not in scope')
        return obj

    def class_declaration(self, declaration, statement):
        if (declaration.get('kind') != 'VarDecl' or declaration.get('storageClass') or
                declaration.get('tls') or len(declaration.get('inner', [])) != 1):
            raise ValueError('automatic class copy declaration required')
        expr = declaration['inner'][0]
        if expr.get('kind') == 'ExprWithCleanups' and len(expr.get('inner', [])) == 1:
            expr = expr['inner'][0]
        context = self.copy_context
        if expr.get('kind') != 'CXXConstructExpr' or expr.get('constructionKind') != 'complete':
            raise ValueError('complete class construction expression required')
        signature = expr.get('ctorType', {}).get('qualType')
        constructor = None
        arguments = []
        source = None
        prefix = []
        if signature == context['constructor_signature']:
            if len(expr.get('inner', [])) != 1:
                raise ValueError('class copy requires one source')
            if context.get('assignment'):
                previous,self.calls_allowed = self.calls_allowed,True
                self.pending = []
                try:source = self.object_expression(expr['inner'][0])
                finally:self.calls_allowed = previous
                prefix,self.pending = self.pending,[]
            else:
                origin = unwrap_lvalue(expr['inner'][0])
                if origin.get('kind') != 'DeclRefExpr':
                    raise ValueError('class copy source requires a live object declaration')
                source = self.objects.get(origin.get('referencedDecl', {}).get('id'))
            if source is None:
                raise ValueError('class copy source identity is not in scope')
        else:
            constructor = context['constructors'].get(signature)
            if constructor is None:
                raise ValueError('audited implicit copy or defined constructor stage required')
            params = constructor['parameters']
            if len(params) != len(expr.get('inner', [])):
                raise ValueError('constructor argument count mismatch')
            actuals = _default_arguments(expr.get('inner', []),context['constructor_defaults'][signature])
            for child,formal in zip(actuals,params,strict=True):
                _pure_argument(child)
                if formal['kind'] != 'scalar':
                    raise ValueError('constructor caller arguments currently require scalars')
                if formal['reference']:
                    slot,binding = self.binding(child,'scalar')
                    if binding['element'] != formal['element'] or formal['writable'] and not binding['writable']:
                        raise ValueError('constructor scalar reference type or permission mismatch')
                    arguments.append(dict(kind='reference',slot=slot))
                else:
                    value = self.expr(child)
                    if value['type'] != formal['element']:
                        raise ValueError('constructor scalar argument type mismatch')
                    arguments.append(dict(kind='value',value=value))
        spelling = declaration['type'].get('desugaredQualType',declaration['type']['qualType'])
        constant = spelling.startswith('const ')
        name = declaration.get('name','')
        location = statement.get('range', {}).get('end', {})
        if (not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name) or
                'offset' not in location or 'spellingLoc' in location or 'expansionLoc' in location):
            raise ValueError('named nonmacro class copy declaration required')
        probe = ('\n#if defined(__is_same) || defined(decltype) || defined(static_assert)\n'
                 '#error class identity keywords must not be macros\n#endif\n'
                 f'static_assert(__is_same(decltype({name}),'+
                 ('const ' if constant else '')+f'::{context["qualified"]}),"class copy type identity");\n')
        self.probes.append((location['offset']+location['tokLen'],probe))
        start = len(self.bindings)
        profile = []
        for field, original in zip(context['plan']['fields'],context['fields'],strict=True):
            vector = field['kind'] in ('vector_copy','vector_assign')
            writable = field['writable'] and (not constant or bool(original.get('mutable')))
            formal = dict(kind='vector' if vector else 'scalar',element=_element(field.get('element',field.get('type'))),
                          writable=writable)
            if not vector:formal['reference']=False
            self.bindings.append(formal)
            profile.append(formal)
        self.objects[declaration['id']] = dict(slots=list(range(start,len(self.bindings))),const=constant)
        if constructor is not None:
            return [dict(kind='class_construct',name=constructor['name'],arguments=arguments,
                         export=constructor['class_export'],profile=profile)]
        return prefix+[dict(kind='class_copy',source=source['slots'],profile=profile)]

    def scoped(self, node, loop=False):
        saved = self.objects.copy()
        try:return super().scoped(node,loop)
        finally:self.objects = saved

    def statement(self, node):
        kind, children = node['kind'], node.get('inner', [])
        expression = node
        while expression.get('kind') in ('ParenExpr','ExprWithCleanups') and len(expression.get('inner',[])) == 1:
            expression = expression['inner'][0]
        if self.assignment_expression(expression):
            previous,self.calls_allowed = self.calls_allowed,True
            self.pending = []
            try:self.object_expression(expression)
            finally:self.calls_allowed = previous
            result,self.pending = self.pending,[]
            return result
        if kind == 'ReturnStmt' and not children:
            if not self.returns_unit:raise ValueError('bare return requires a void caller')
            return [dict(kind='return_unit')]
        if kind == 'ReturnStmt' and self.returns_unit and len(children) == 1:
            # A C++ void return expression still evaluates the called method
            # before terminating this caller. General expressions fail closed.
            expression = children[0]
            while expression.get('kind') == 'ParenExpr' and len(expression.get('inner', [])) == 1:
                expression = expression['inner'][0]
            if expression.get('kind') != 'CXXMemberCallExpr':
                raise ValueError('void return expression requires a direct unit method')
            self.pending = [];saved_slots,saved_bindings = self.slots.copy(),self.bindings.copy()
            self.calls_allowed = True;self.discarded = True
            try:self.expr(expression)
            finally:self.calls_allowed = False;self.discarded = False
            if len(self.bindings) != len(saved_bindings):
                raise ValueError('void caller cannot return a scalar method result')
            pending,self.pending = self.pending,[]
            self.slots,self.bindings = saved_slots,saved_bindings
            return [dict(kind='scope',body=pending+[dict(kind='return_unit')])]
        if kind == 'DeclStmt' and any(d.get('storageClass') or d.get('tls') or d.get('tlsKind')
                                      for d in children):
            raise ValueError('caller locals require automatic storage')
        if kind == 'DeclStmt' and len(children) == 1:
            try:scalar_type(children[0])
            except ValueError:return self.class_declaration(children[0],node)
        if kind in ('CompoundStmt','ForStmt'):
            saved = self.objects.copy()
            try:return super().statement(node)
            finally:self.objects = saved
        if kind == 'DeclStmt' and len(children) > 1:
            return [s for child in children for s in self.statement(dict(node,inner=[child]))]
        if kind in ('CompoundStmt','IfStmt','WhileStmt','ForStmt','NullStmt','BreakStmt'):
            return super().statement(node)
        calls = [n for n in walk(node) if n.get('kind') == 'CXXMemberCallExpr' and not self.assignment_expression(n)]
        if not calls:
            return super().statement(node)
        expression = (children[0]['inner'][0] if kind == 'DeclStmt' and len(children) == 1 and
                      len(children[0].get('inner', [])) == 1 else
                      children[-1] if kind in ('ReturnStmt','BinaryOperator') else node)
        while expression.get('kind') in ('ImplicitCastExpr','ParenExpr') and len(expression.get('inner', [])) == 1:
            expression = expression['inner'][0]
        if len(calls) != 1 or expression is not calls[0]:
            raise ValueError('one method call must occupy the complete scalar expression')
        saved_slots, saved_bindings = self.slots.copy(), self.bindings.copy()
        self.pending = []
        self.calls_allowed = True
        try:
            if kind == 'CXXMemberCallExpr':
                self.discarded = True
                try:self.expr(node)
                finally:self.discarded = False
                result = []
            else:
                result = super().statement(node)
        finally:
            self.calls_allowed = False
        pending, self.pending = self.pending, []
        if kind != 'DeclStmt':
            # In particular a for increment executes repeatedly without the
            # body's scope. Its hidden result must not accumulate or make a
            # statically compiled result slot read the previous iteration.
            self.slots, self.bindings = saved_slots, saved_bindings
            return [dict(kind='scope',body=pending+result)]
        return pending+result

    def lower(self):
        if self.node.get('variadic') or self.node.get('storageClass'):
            raise ValueError('ordinary nonvariadic class caller required')
        bodies = [n for n in self.node.get('inner', []) if n.get('kind') == 'CompoundStmt']
        if len(bodies) != 1 or any(n.get('kind') not in ('ParmVarDecl','CompoundStmt') for n in self.node['inner']):
            raise ValueError('class caller attributes and templates are unsupported')
        statements = []
        for child in bodies[0].get('inner', []):statements.extend(self.statement(child))
        if not self.returns_unit and terminal_return_kinds(statements) != {'return'}:
            raise ValueError('a scalar return on every terminal path is required')
        return dict(name=self.node['name'],parameters=self.parameters,
                    result_type=dict(unit=True) if self.returns_unit else function_return_type(self.node),body=statements)


def lower_class_callers(source, qualified, include_dirs=(), signed_conversion='checked', *, assignment=False):
    source = Path(source).resolve(strict=True)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    records, callers, callees = [], [], []
    if not isinstance(assignment,bool):raise ValueError('invalid class assignment mode')
    options = dict(copy_class=qualified,copy_records=records,class_callers=callers)
    if assignment:options['copy_assignment']=True
    _, roots = translation_unit(source,include_dirs,callees=callees,**options)
    if len(records) != 1:
        raise ValueError('one original class definition required')
    record = records[0]
    record['_copy_qualified'] = qualified
    assignment_plan = audit_assignment_record(source,qualified,record,roots,include_dirs) if assignment else None
    copy_used = any(n.get('kind')=='CXXConstructorDecl' and n.get('isUsed') and any(
        p.get('kind')=='ParmVarDecl' and p.get('type',{}).get('qualType') in
        {f'const {record["name"]} &',f'const {qualified} &'} for p in n.get('inner',[])) for n in record['inner'])
    copy_plan = audit_copy_record(source,qualified,record,roots,include_dirs) if not assignment or copy_used else None
    plan = assignment_plan if assignment else copy_plan
    original_fields = [n for n in record['inner'] if n.get('kind') == 'FieldDecl']
    raw_methods = {n['id']:n for n in record['inner'] if n.get('kind') == 'CXXMethodDecl' and
                   not n.get('isImplicit') and n.get('storageClass') != 'static' and
                   any(c.get('kind') == 'CompoundStmt' for c in n.get('inner', []))}
    functions = [f for f in class_method_functions(record,source) if f['id'] in raw_methods]
    method_defaults = {}
    clean_functions = []
    for function in functions:
        clean,defaults = _parameter_defaults(function)
        # Synthetic field parameters are explicit receiver arguments.
        method_defaults[function['id']] = defaults[len(function.get('_fields', [])):]
        clean_functions.append(clean)
    functions = inline_functions(clean_functions,callees)
    audited = audit_vector_nodes(source,functions,roots,include_dirs)
    schemas = bindings_from_audit(source,audited,include_dirs)['functions']
    apply_conversion_policy([*audited['functions'],*callers,*callees],signed_conversion)
    apply_conversion_policy([d for defaults in method_defaults.values() for d in defaults if d is not None],signed_conversion)
    methods, used, probes = {}, {}, []
    for function, schema in zip(audited['functions'],schemas,strict=True):
        fields = function.get('_fields', [])
        if len(fields) != len(original_fields):
            raise ValueError('method field parameter count mismatch')
        # The replacement map is built from these exact FieldDecls by
        # class_method_functions; verify its ordered synthetic parameters too.
        for original, parameter, field, formal in zip(original_fields,fields,plan['fields'],schema['parameters'][:len(fields)],strict=True):
            if (original['id'] != field['field_id'] or parameter['id'] !=
                    f"field:{record['name']}:{original['name']}" or
                    formal['kind'] != ('vector' if field['kind'] in ('vector_copy','vector_assign') else 'scalar') or
                    formal['element'] != _element(field.get('element',field.get('type')))):
                raise ValueError('method field identity, order or type mismatch')
        body = NestedBody(function,schema,ValueCalls(callees),source)
        program = body.lower()
        program['parameters'] = schema['parameters']
        if 'vector' in program['result']:
            raise ValueError('caller adapter cannot yet return vectors from methods')
        methods[function['id']] = dict(program=program,fields=len(fields),
            const=raw_methods[function['id']]['type']['qualType'].endswith(' const'),
            defaults=method_defaults[function['id']])
        used.update(body.callees);probes.extend(body.probes)
    # Constructor IDs and field layouts share this exact translation unit.
    construction_record = record
    if assignment:
        # Deleted constructors cannot produce stages and are irrelevant to
        # copy assignment. Keep every usable constructor and its declaration ID.
        construction_record = dict(record,inner=[n for n in record['inner'] if not
            (n.get('kind') == 'CXXConstructorDecl' and n.get('explicitlyDeleted'))])
    stages = class_construction_stages(construction_record,source)
    for stage in stages:
        stage['_fields'] = [dict(kind='ParmVarDecl',id=f['id'],name=f['name'],type=original['type'])
                            for f,original in zip(stage['_construction_fields'],original_fields,strict=True)]
    constructor_defaults = {}
    clean_stages = []
    for stage in stages:
        clean,defaults = _parameter_defaults(stage)
        constructor_defaults[stage['type']['qualType']] = defaults
        clean_stages.append(clean)
    stages = inline_functions(clean_stages,functions)
    constructor_audit = audit_vector_nodes(source,stages,roots,include_dirs)
    constructor_schemas = bindings_from_audit(source,constructor_audit,include_dirs)['functions']
    apply_conversion_policy(constructor_audit['functions'],signed_conversion)
    apply_conversion_policy([d for defaults in constructor_defaults.values() for d in defaults if d is not None],signed_conversion)
    constructors = {}
    for stage,schema in zip(constructor_audit['functions'],constructor_schemas,strict=True):
        body = NestedBody(stage,schema,ValueCalls(callees),source)
        program = body.lower();program['parameters'] = schema['parameters']
        layout = _field_layout(record,plan,stage,body)
        vector,*scalars = layout
        program['class_export'] = dict(vector_slot=vector['slot'],element=vector['element'],
            scalar_fields=[dict(slot=f['slot'],type=f['element']) for f in scalars])
        original = next(n for n in record['inner'] if n.get('id') == stage['id'])
        signature = original['type']['qualType']
        if signature in constructors:raise ValueError('ambiguous constructor signature')
        constructors[signature] = program
        used.update(body.callees);probes.extend(body.probes)
    lowered = []
    names = set()
    for caller in callers:
        if caller.get('_copy_translation_unit') != record.get('_copy_translation_unit'):
            raise ValueError('caller and class must share their translation unit')
        params = [n for n in caller['inner'] if n.get('kind') == 'ParmVarDecl']
        class_spellings = {qualified,record['name']}
        has_method = any(n.get('kind') == 'MemberExpr' and n.get('referencedMemberDecl') in methods for n in walk(caller))
        has_constructor = any(n.get('kind') == 'CXXConstructExpr' and
            n.get('type',{}).get('desugaredQualType',n.get('type',{}).get('qualType','')).removeprefix('const ') in class_spellings
            for n in walk(caller))
        if not has_method and not has_constructor and not any(p['type'].get('desugaredQualType',p['type']['qualType']).removeprefix('const ').removesuffix(' &') in class_spellings for p in params):
            continue
        node = copy.deepcopy(caller)
        parameters, synthetic, objects, arguments = [], [], {}, []
        body_nodes = [n for n in node['inner'] if n.get('kind') == 'CompoundStmt']
        if len(body_nodes) != 1:
            raise ValueError('caller body required')
        for parameter in [n for n in node['inner'] if n.get('kind') == 'ParmVarDecl']:
            try:
                scalar = parameter_type(parameter)
            except ValueError:
                spelling = parameter['type'].get('desugaredQualType',parameter['type']['qualType'])
                if not spelling.endswith(' &') or 'volatile' in spelling or '*' in spelling or '&&' in spelling:
                    raise ValueError('class receiver parameters require lvalue references')
                constant = spelling.startswith('const ')
                name = parameter.get('name','')
                if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name) or parameter.get('inner'):
                    raise ValueError('named class reference without defaults/attributes required')
                location = body_nodes[0]['range']['begin']
                if 'offset' not in location or 'expansionLoc' in location or 'spellingLoc' in location:
                    raise ValueError('nonmacro class caller body required')
                probe = ('\n#if defined(__is_same) || defined(decltype) || defined(static_assert)\n'
                         '#error class identity keywords must not be macros\n#endif\n'
                         f'static_assert(__is_same(decltype({name}),'+
                         ('const ' if constant else '')+f'::{qualified} &),"class receiver identity");\n')
                probes.append((location['offset']+location['tokLen'],probe))
                slots = []
                for original, field in zip(original_fields,plan['fields'],strict=True):
                    slot = len(parameters);slots.append(slot)
                    vector = field['kind'] in ('vector_copy','vector_assign')
                    writable = field['writable'] and (not constant or bool(original.get('mutable')))
                    formal = dict(kind='vector' if vector else 'scalar',
                                  element=_element(field.get('element',field.get('type'))),writable=writable)
                    if not vector:formal['reference']=True
                    parameters.append(formal)
                    synthetic.append(dict(kind='ParmVarDecl',id=f"receiver:{parameter['id']}:{original['id']}",type=original['type']))
                objects[parameter['id']] = dict(slots=slots,const=constant)
                arguments.append(dict(kind='object',fields=len(plan['fields'])))
            else:
                parameters.append(dict(kind='scalar',element=scalar['type'],reference=scalar['reference'],
                                       writable=scalar['writable']))
                synthetic.append(parameter)
                arguments.append(dict(kind='scalar'))
        if not objects and not has_method and not has_constructor:
            # Ordinary helper functions are used by the method lowerer; they
            # are not silently passed through as class callers.
            continue
        name = caller['_qualified_name'].replace('::','_')
        if name in names:
            raise ValueError('overloaded caller names require a distinct exported name')
        names.add(name)
        node['name'] = name
        node['inner'] = synthetic+[n for n in node['inner'] if n.get('kind') != 'ParmVarDecl']
        copy_ctor = next((n for n in record['inner'] if copy_plan and n.get('id') == copy_plan['constructor_id']),None)
        context = dict(source=source,qualified=qualified,plan=plan,fields=original_fields,constructors=constructors,
                       constructor_signature=copy_ctor['type']['qualType'] if copy_ctor else None,constructor_defaults=constructor_defaults,
                       assignment=assignment_plan)
        body = CallerBody(node,dict(parameters=parameters),objects,methods,context)
        function = body.lower()
        probes.extend(body.probes)
        function['result'] = function.pop('result_type')
        function['arguments'] = arguments
        lowered.append(function)
    verify_type_probes(source,probes,include_dirs)
    if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
        raise ValueError('class caller source changed during generation')
    return dict(coverage='class_reference_callers',source_sha256=digest,qualified_class=qualified,
                methods=[m['program'] for m in methods.values()],constructors=list(constructors.values()),
                callees=[used[n] for n in sorted(used)],functions=lowered)


def _arguments(arguments):
    return '['+', '.join(f".vectorReference {a['slot']}" if a['kind']=='vector' else
        f".scalarReference {a['slot']}" if a['kind']=='reference' else
        f".value {render_expression(a['value'])}" for a in arguments)+']'


def _commands(statements):
    body = '(.nested (.primitive .skip))'
    for statement in reversed(statements):
        kind = statement['kind']
        if kind == 'class_construct':
            vector,*scalars=statement['profile'];export=statement['export']
            pairs=', '.join(f"({lean_type(f['element'])},{str(f['writable']).lower()})" for f in scalars)
            fields=', '.join(f"⟨{f['slot']},{lean_type(f['type'])}⟩" for f in export['scalar_fields'])
            command=(f"(.constructObject Constructors.«{statement['name']}» {_arguments(statement['arguments'])} "
                     f"{export['vector_slot']} [{fields}] ⟨{lean_type(vector['element'])},"
                     f"{str(vector['writable']).lower()},[{pairs}]⟩)")
        elif kind == 'class_copy':
            source=statement['source'];vector,*scalars=statement['profile']
            pairs=', '.join(f"({lean_type(f['element'])},{str(f['writable']).lower()})" for f in scalars)
            fields=', '.join(map(str,source[1:]))
            command=(f"(.copyObject ⟨{source[0]},[{fields}]⟩ ⟨{lean_type(vector['element'])},"
                     f"{str(vector['writable']).lower()},[{pairs}]⟩)")
        elif kind == 'class_assign':
            target,source=statement['target'],statement['source'];vector,*scalars=statement['profile']
            pairs=', '.join(f"({lean_type(_element(f['type']))},true)" for f in scalars)
            dest=', '.join(map(str,target[1:]));origin=', '.join(map(str,source[1:]))
            command=(f"(.assignObject ⟨{target[0]},[{dest}]⟩ ⟨{source[0]},[{origin}]⟩ "
                     f"⟨{lean_type(_element(vector['element']))},true,[{pairs}]⟩)")
        elif kind == 'class_invoke':
            command = f"(.invoke Methods.«{statement['name']}» {_arguments(statement['arguments'])})"
        elif kind == 'scope':command=f"(.scope {_commands(statement['body'])})"
        elif kind == 'branch':
            command=f"(.branch {render_expression(statement['condition'])} {_commands(statement['yes'])} {_commands(statement['no'])})"
        elif kind == 'while':command=f"(.whileLoop {render_expression(statement['condition'])} {_commands(statement['body'])})"
        elif kind == 'break':command='.breakLoop'
        else:command=f"(.nested (.primitive {render_statement(statement)}))"
        body=f'(.sequence {command} {body})'
    return body


def emit_class_callers(source,qualified,namespace='Proofs.Generated.ClassCallers',include_dirs=(),
                       signed_conversion='checked', *, assignment=False):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',namespace):
        raise ValueError('invalid Lean namespace')
    ir=lower_class_callers(source,qualified,include_dirs,signed_conversion,assignment=assignment)
    methods=emit_lean(dict(functions=ir['methods'],callees=ir['callees']),namespace+'.Methods')
    constructors=emit_lean(dict(functions=ir['constructors'],callees=ir['callees']),namespace+'.Constructors')
    lines=['import Proofs.CppNestedInvoke',methods,constructors,f'namespace {namespace}',
           'open Proofs.CppNestedInvoke Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish',
           f'def sourceSHA256 : String := "{ir["source_sha256"]}"']
    for function in ir['functions']:
        name=function['name']
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name):raise ValueError('invalid caller identifier')
        params=[]
        for p in function['parameters']:
            ty=lean_type(p['element']);wr=str(p['writable']).lower()
            params.append(f'.vector {ty} {wr}' if p['kind']=='vector' else
                          f'.scalar {ty} {str(p["reference"]).lower()} {wr}')
        if 'unit' in function['result']:
            lines.append(f'def «{name}» : UnitCallerProgram := ⟨[{", ".join(params)}],'
                         f'\n  {_commands(function["body"])}⟩')
        else:
            lines.append(f'def «{name}» : CallerProgram := ⟨[{", ".join(params)}],{lean_type(function["result"])},'
                         f'\n  {_commands(function["body"])}⟩')
        binders=[];builders=[]
        for i,argument in enumerate(function['arguments']):
            if argument['kind']=='scalar':
                binders.append(f'(arg{i} : NArgument)');builders.append(f'arg{i}')
            else:
                binders.append(f'(arg{i} : ObjectRef)')
                builders.append(f'.vectorReference arg{i}.vectorSlot')
                for j in range(argument['fields']-1):builders.append(f'.scalarReference s{i}_{j}')
        lines.append(f'def «{name}_arguments» {" ".join(binders)} : Option (List NArgument) := do')
        for i,argument in enumerate(function['arguments']):
            if argument['kind']=='object':
                lines.append(f"  if arg{i}.scalarSlots.length != {argument['fields']-1} then none else pure ()")
                for j in range(argument['fields']-1):lines.append(f'  let s{i}_{j} ← arg{i}.scalarSlots[{j}]?')
        lines.append(f'  pure [{", ".join(builders)}]')
    return '\n'.join([*lines,f'end {namespace}',''])
