"""Evaluate all scalar fields before returning a projected record value.

Used by companion bundles. Legacy per-field models retain their existing
programs until their proof fixtures migrate to this evaluation order.
Trivial record copies are validated by SplitClass before reaching this helper.
"""
from class_lowering import SCALAR_FIELD_TYPES, constructor_body_may_change_state
from class_split import strip, substitute


def strict_return(splitter, result_class, declaration, node, params_, field):
    if not node.get('inner'):
        raise ValueError('a function returning a split class must return a value')
    value = strip(node['inner'][0])
    if value.get('kind') not in ('CXXTemporaryObjectExpr', 'CXXConstructExpr'):
        raise ValueError('a function returning a split class must return a constructor call')
    signature_key = value.get('ctorType', {}).get('qualType', '').replace(' noexcept', '')
    if signature_key not in result_class.constructors:
        implicit_signatures = {
            member.get('type',{}).get('qualType','').replace(' noexcept','')
            for member in result_class.record.get('inner',[])
            if member.get('kind')=='CXXConstructorDecl' and member.get('isImplicit')
            and not member.get('isDeleted')}
        copied = value.get('inner',[])
        if signature_key not in implicit_signatures or len(copied)!=1 or not result_class.is_class_type(copied[0].get('type',{})):
            raise ValueError('unknown constructor: '+signature_key)
        # SplitClass validates trivial copy/move/destruction for this
        # same source-owned record. Read every copied scalar field.
        def copy_return(expression, branch):
            expression = strip(expression)
            if expression.get('kind')=='ConditionalOperator':
                children=expression.get('inner',[])
                if len(children)!=3:
                    raise ValueError('a copied conditional needs three operands')
                return dict(kind='IfStmt',range=node.get('range',{}),inner=[
                    splitter.rewrite(children[0],params_),
                    copy_return(children[1],branch+'t'),copy_return(children[2],branch+'f')])
            if expression.get('kind')!='DeclRefExpr':
                raise ValueError('a trivial returned copy needs a known value parameter')
            mapping=params_.get(expression.get('referencedDecl',{}).get('id'))
            if mapping is None or set(mapping)!={f['id'] for f in result_class.fields}:
                raise ValueError('a trivial returned copy needs all source-owned fields')
            statements=[];chosen=None
            identity=node.get('id',declaration.get('id','copy'))+':'+branch
            for index,copied_field in enumerate(result_class.fields):
                parameter=mapping[copied_field['id']]
                info=copied_field['type']
                read=dict(kind='DeclRefExpr',type=info,valueCategory='lvalue',
                    referencedDecl={k:parameter[k] for k in ('id','kind','name','type')})
                temporary=dict(kind='VarDecl',id='copy-field:'+identity+':'+copied_field['id'],
                    name='copy_field_'+str(index),type=info,init='c',inner=[read])
                statements.append(dict(kind='DeclStmt',inner=[temporary]))
                if copied_field['id']==field['id']:
                    chosen=dict(kind='DeclRefExpr',type=info,valueCategory='lvalue',
                        referencedDecl={k:temporary[k] for k in ('id','kind','name','type')})
            assert chosen is not None
            return dict(kind='CompoundStmt',range=node.get('range',{}),_splice=True,
                inner=statements+[dict(kind='ReturnStmt',range=node.get('range',{}),inner=[chosen])])
        return copy_return(copied[0],'')
    constructor_parameters, inits, ctor_body = result_class.constructors[signature_key]
    # Projection must not erase or duplicate argument/initializer effects,
    # even when a parameter or another field is unused by this result.
    # Such constructors need the object-state sequencing frontend.
    if any(constructor_body_may_change_state(a) for a in value.get('inner', [])):
        raise ValueError('split constructor arguments must be free of runtime effects')
    if any(constructor_body_may_change_state(a) for a in inits.values()):
        raise ValueError('split field initializers must be free of runtime effects')
    if any(constructor_body_may_change_state(statement) for statement in ctor_body):
        raise ValueError('split constructor body needs object-state sequencing')
    arguments = [splitter.rewrite(a_, params_) for a_ in value.get('inner', [])]
    if len(arguments) != len(constructor_parameters):
        raise ValueError('default arguments of constructors are not supported')
    prefix = []
    mapping = {}
    identity = node.get('id', declaration.get('id', 'return'))
    for index, (parameter, argument) in enumerate(zip(constructor_parameters, arguments, strict=True)):
        info = parameter['type']
        text = info.get('desugaredQualType', info['qualType'])
        if text not in SCALAR_FIELD_TYPES:
            raise ValueError('strict construction needs primitive value parameters')
        temporary = dict(kind='VarDecl', id='strict-arg:'+identity+':'+parameter['id'],
            name='strict_arg_'+str(index), type=info, init='c', inner=[argument])
        prefix.append(dict(kind='DeclStmt', inner=[temporary]))
        mapping[parameter['id']] = dict(kind='DeclRefExpr', type=info, valueCategory='lvalue',
            referencedDecl={k:temporary[k] for k in ('id','kind','name','type')})
    field_values = {}
    all_field_ids = {f['id'] for f in result_class.fields}
    def checked_this(expression):
        if (expression.get('kind') == 'MemberExpr' and
                expression.get('referencedMemberDecl') in all_field_ids and
                expression.get('inner', [{}])[0].get('kind') == 'CXXThisExpr' and
                expression['referencedMemberDecl'] not in field_values):
            raise ValueError('constructor reads a field before its initialization')
        for child in expression.get('inner', []):
            checked_this(child)
    for index, member_field in enumerate(result_class.fields):
        expression = substitute(inits[member_field['id']], mapping)
        checked_this(expression)
        expression = splitter.rewrite(expression, {'this':field_values})
        temporary = dict(kind='VarDecl', id='strict-field:'+identity+':'+member_field['id'],
            name='strict_field_'+str(index), type=member_field['type'], init='c', inner=[expression])
        prefix.append(dict(kind='DeclStmt', inner=[temporary]))
        field_values[member_field['id']] = dict(kind='ParmVarDecl',
            id=temporary['id'], name=temporary['name'], type=temporary['type'])
    body = []
    for statement in ctor_body:
        statement = substitute(statement, mapping)
        checked_this(statement)
        body.append(splitter.rewrite(statement, {'this':field_values}))
    chosen = field_values[field['id']]
    expression = dict(kind='DeclRefExpr', type=chosen['type'], valueCategory='lvalue',
        referencedDecl=chosen)
    returned = dict(kind='ReturnStmt', range=node.get('range', {}), inner=[expression])
    return dict(kind='CompoundStmt', range=node.get('range', {}), _splice=True,
                inner=prefix+body+[returned])
