"""Check original nested template types without editing their C++ API.

Finite long-long instance proofs do not establish arbitrary-T/object-lifetime coverage.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tests'), str(ROOT/'verifier'), str(ROOT/'tools')]
from ast_stream import node_header, root_objects
from class_templates import TemplateInstance, RecordArgument, instantiate_members
from class_lowering import ErasedClass, scalar_record_type, selected_type_pattern
from nested_templates import select_nested_records
from template_class_ir import lower_template_class
from nested_ir import emit_lean
from offline import disable_network
import test_scalar_class_delegation as scalar_checks

results = []
def walk(node):
    yield node
    for child in node.get('inner', []):
        yield from walk(child)

def check_collect(stream, original, requested, alias_namespace, witness):
    roots = [json.loads(raw) for raw in root_objects(stream)
             if node_header(raw).get('name') in {'RangeAddRangeMaxMin',alias_namespace}]
    selected = select_nested_records(roots, original, requested, alias_namespace, witness)
    origin = selected[0]['_template_witness_origin']

    def nodes(rs):
        return {n['id']: n for r in rs for n in walk(r) if 'id' in n}

    def parts(rs):
        ns = nodes(rs)
        actual = ns[origin['record_id']]
        outer = ns[origin['outer_record_id']]
        primary = ns[origin['primary_id']]
        generic = ns[outer['TemplateInstantiationPattern']]
        alias = next(n for n in ns.values() if n.get('kind')=='TypeAliasDecl' and n.get('name')=='Selected')
        ref = next(n for n in walk(alias) if n.get('kind')=='RecordType')
        return ns, actual, outer, primary, generic, alias, ref

    def alias_outer(rs):
        ns,a,o,p,g,al,ref = parts(rs)
        ref['decl']['id'] = o['id']

    def sibling_pattern(rs):
        ns,a,o,p,g,al,ref = parts(rs)
        sibling = next(c for c in g['inner'] if c.get('name')=='RangeMin' and c.get('completeDefinition'))
        a['TemplateInstantiationPattern'] = sibling['id']

    def outer_pattern(rs):
        parts(rs)[2]['TemplateInstantiationPattern'] = 'missing-primary'

    def foreign_definition(rs):
        parts(rs)[1]['loc']['file'] = str(witness)

    def macro_pattern(rs):
        ns,a,o,p,g,al,ref = parts(rs)
        ns[a['TemplateInstantiationPattern']]['loc']['expansionLoc'] = {'file':str(original)}

    def alias_in_source(rs):
        parts(rs)[5]['loc']['file'] = str(original)

    def wrong_parent(rs):
        ns,a,o,p,g,al,ref = parts(rs)
        o['inner'] = [c for c in o['inner'] if c.get('id')!=a['id']]
        g['inner'].append(a)

    def wrong_spelling(rs):
        parts(rs)[6]['type']['qualType'] = '::Other<long long>::RangeMax'

    def duplicate_record(rs):
        ns,a,o,p,g,al,ref = parts(rs)
        o['inner'].append(copy.deepcopy(a))

    def no_primary_owner(rs):
        ns,a,o,p,g,al,ref = parts(rs)
        p['inner'] = [c for c in p['inner'] if c.get('id')!=o['id']]
        rs.append(o)

    def wrong_root_name(rs):
        parts(rs)[2]['name'] = 'Other'

    for name, mutation in [('alias_outer',alias_outer),('sibling_pattern',sibling_pattern),
            ('outer_pattern',outer_pattern),('foreign_definition',foreign_definition),
            ('macro_pattern',macro_pattern),('alias_in_source',alias_in_source),
            ('wrong_parent',wrong_parent),('wrong_spelling',wrong_spelling),
            ('duplicate_record',duplicate_record),('no_primary_owner',no_primary_owner),
            ('wrong_root_name',wrong_root_name)]:
        altered = copy.deepcopy(roots)
        mutation(altered)
        try:
            select_nested_records(altered, original, requested, alias_namespace, witness)
        except ValueError as error:
            results.append(dict(case=name,status='rejected',reason=str(error)))
        else:
            raise AssertionError('accepted mutation '+name)
    cls = ErasedClass(selected[0], 'NestedRangeMax', 'RangeMax')
    for spelling in ['Other::RangeMax','::RangeMax','OtherRangeMax','RangeMaxExtra',
                     'Other<long long>::RangeMax',requested+'::Child']:
        assert cls.erase_text(spelling)==spelling, spelling
    assert cls.erase_text('const ::'+requested+' &')=='const long long &'
    assert cls.erase_text('const RangeMax &')=='const long long &'
    return selected

class NestedTemplateTests(unittest.TestCase):
    def test_original_nested_max(self):
        source = ROOT/'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp'
        witness = ROOT/'tests/imports/original_nested_max.cpp'
        before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
        instance = TemplateInstance(('long long',), witness, nested_members=('RangeMax',))
        ir, coverage = lower_template_class(source,'RangeAddRangeMaxMin',instance,
                                            [ROOT/'experiments/library/cpp'])
        self.assertEqual(len(ir['functions']),4)
        self.assertEqual(coverage['nested_members'],['RangeMax'])
        self.assertEqual(coverage['selected_type'],'RangeAddRangeMaxMin<long long>::RangeMax')
        self.assertEqual(coverage['source_sha256'],before[source])
        self.assertEqual(coverage['witness_sha256'],before[witness])
        self.assertFalse(coverage['generic_types_verified'])
        self.assertFalse(coverage['full_cpp_object_lifetime_verified'])
        proof = 'import Proofs.MonoidCall\n'+emit_lean(ir,'OriginalNestedMax')
        proof += (ROOT/'tests/lean/original_nested_max.lean').read_text()
        roots = ['NestedMaxAudit.'+name for name in
                 ('new0','call_new0','new1','call_new1','e','call_e','op','call_op',
                  'default_correct','new_correct','e_correct','op_correct')]
        with tempfile.TemporaryDirectory(prefix='original-nested-max-') as tmp:
            directory=Path(tmp)
            scalar_checks.ScalarDelegationTests().kernel(directory,'NestedMaxCheck',roots,proof)
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                '-fno-sanitize-recover=all','-I',str(ROOT/'experiments/library/cpp'),
                '-include',str(source),str(witness),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
        results.clear()
        with patch('class_templates.collect_nested_template_record',check_collect):
            guarded, _ = lower_template_class(source,'RangeAddRangeMaxMin',instance,
                                              [ROOT/'experiments/library/cpp'])
        self.assertEqual(guarded,ir)
        self.assertEqual(len(results),11)
        for path,digest in before.items():
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),digest)

    def test_nested_depth_and_split_fields(self):
        cases = [
            (ROOT/'tests/imports/nested_depth.hpp',ROOT/'tests/imports/nested_depth.cpp',
             'other::Outer',('long long','3'),('Middle','Leaf'),3,[]),
            (ROOT/'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp',
             ROOT/'tests/imports/original_nested_sum.cpp','RangeAddRangeSum',
             ('long long',),('RangeSum',),8,[ROOT/'experiments/library/cpp'])]
        for source,witness,qualified,args,members,count,includes in cases:
            with self.subTest(qualified=qualified), tempfile.TemporaryDirectory(prefix='nested-split-') as tmp:
                before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
                instance = TemplateInstance(args,witness,nested_members=members)
                ir, coverage = lower_template_class(source,qualified,instance,includes)
                self.assertEqual(len(ir['functions']),count)
                if qualified == 'RangeAddRangeSum':
                    proof = 'import Proofs.MonoidLazyCall\n'+emit_lean(ir,'OriginalNestedSum')
                    proof += (ROOT/'tests/lean/original_nested_sum.lean').read_text()
                    roots = ['NestedSumAudit.'+name for name in
                             ('prepare_values2t','value2t_correct','const_t_correct',
                              'e_x_correct','e_size_correct','new1_x_correct','new1_size_correct',
                              'new_x_correct','new_size_correct','op_x_program','op_x_call',
                              'op_x_correct','op_size_program','op_size_call','op_size_correct')]
                    scalar_checks.ScalarDelegationTests().kernel(Path(tmp),'NestedSumCheck',roots,proof)
                self.assertEqual(coverage['nested_members'],list(members))
                self.assertEqual(coverage['selected_type'],instance.target(qualified))
                self.assertFalse(coverage['generic_types_verified'])
                self.assertFalse(coverage['full_cpp_object_lifetime_verified'])
                exe=Path(tmp)/'native'
                command=['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all']
                for include in includes:
                    command += ['-I',str(include)]
                subprocess.run([*command,'-include',str(source),str(witness),'-o',str(exe)],
                               check=True,timeout=60)
                subprocess.run([str(exe)],check=True,timeout=10)
                for path,digest in before.items():
                    self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),digest)

    def test_record_member_arguments(self):
        source=ROOT/'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp'
        witness=ROOT/'tests/imports/original_record_apply.cpp'
        main=TemplateInstance(('long long',),witness,nested_members=('RangeAdd',))
        companions=tuple(('RangeAddRangeMaxMin',TemplateInstance(('long long',),witness,
            nested_members=(name,))) for name in ['RangeMax','RangeMin'])
        requested={'apply':[(RecordArgument(1),),(RecordArgument(2),)]}
        before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
        negative=[]
        def checked_members(record, schema, *, record_arguments):
            def reject(name, change=None, request=None):
                copied=copy.deepcopy([record,*record_arguments])
                r,context=copied[0],copied[1:]
                if change is not None:
                    change(r,context)
                with self.subTest(case=name), self.assertRaises(ValueError):
                    instantiate_members(r,schema if request is None else request,record_arguments=context)
                negative.append(name)
            def argument(r):
                template=next(n for n in r['inner'] if n.get('kind')=='FunctionTemplateDecl')
                method=next(n for n in template['inner'] if any(c.get('kind')=='TemplateArgument' for c in n.get('inner',[])))
                return next(n for n in method['inner'] if n.get('kind')=='TemplateArgument')
            reject('wrong record ID',lambda r,c: argument(r)['inner'][0]['decl'].update(id=c[2]['id']))
            reject('missing RecordType',lambda r,c: argument(r).update(inner=[]))
            reject('wrong RecordType spelling',lambda r,c: argument(r)['inner'][0]['type'].update(qualType='Other'))
            reject('foreign TU',lambda r,c: c[1].update(_copy_translation_unit='foreign'))
            reject('wrong source hash',lambda r,c: c[1].update(_copy_source_sha256='changed'))
            reject('foreign source',lambda r,c: c[1].update(_copy_source='foreign.hpp'))
            reject('wrong provenance ID',lambda r,c: c[1]['_template_witness_origin'].update(record_id='other'))
            def selected_method(r):
                template=next(n for n in r['inner'] if n.get('kind')=='FunctionTemplateDecl')
                return next(n for n in template['inner'] if any(c.get('kind')=='TemplateArgument' for c in n.get('inner',[])))
            reject('foreign member body',lambda r,c: selected_method(r)['loc'].update(file=str(witness)))
            reject('wrong member pattern',lambda r,c: selected_method(r).update(TemplateInstantiationPattern='foreign'))
            reject('unselected record',request={'apply':[(RecordArgument(99),)]})
            reject('uninstantiated self argument',request={'apply':[(RecordArgument(0),)]})
            reject('raw C++ spelling',request={'apply':[(companions[0][1].target(companions[0][0]),)]})
            return instantiate_members(record,schema,record_arguments=record_arguments)
        with patch('template_class_ir.instantiate_members',checked_members):
            ir,coverage=lower_template_class(source,'RangeAddRangeMaxMin',main,
                [ROOT/'experiments/library/cpp'],companion_instances=companions,member_instances=requested)
        self.assertEqual(len(negative),12)
        self.assertEqual(len(ir['functions']),13)
        self.assertEqual(coverage['source_sha256'],before[source])
        self.assertEqual(coverage['witness_sha256'],before[witness])
        self.assertEqual([c['selected_type'] for c in coverage['companions']],
                         [i.target(q) for q,i in companions])
        self.assertEqual(coverage['member_instances'],[dict(source_name='apply',type_arguments=[i.target(q)]) for q,i in companions])
        self.assertFalse(coverage['generic_types_verified'])
        self.assertFalse(coverage['full_cpp_object_lifetime_verified'])
        proof='import Proofs.MonoidLazyCall\n'+emit_lean(ir,'OriginalRecordApply')
        proof+=(ROOT/'tests/lean/original_record_apply.lean').read_text()
        names=['prep_mutable_value','add_exec','apply_same','apply_call','apply_correct','apply_min_correct']
        for name in ['add_new','add_id',*[c+'_'+op for c in ['max','min'] for op in ['new0','new1','e','op']]]:
            names.extend([name,'call_'+name])
        with tempfile.TemporaryDirectory(prefix='original-record-apply-') as tmp:
            scalar_checks.ScalarDelegationTests().kernel(Path(tmp),'RecordApplyCheck',
                ['RecordApplyAudit.'+name for name in names],proof)
            exe=Path(tmp)/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I',str(ROOT/'experiments/library/cpp'),'-include',str(source),str(witness),'-o',str(exe)],
                check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
        for path,digest in before.items():
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),digest)

    def test_companion_scope_and_foreign_member(self):
        cases=[(ROOT/'tests/imports/flat_companions.hpp',ROOT/'tests/imports/flat_companions.cpp',
                'other::Action',(),['other::Box','other::OtherBox'],None),
               (ROOT/'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp',
                ROOT/'tests/imports/record_apply_specialized.cpp','RangeAddRangeMaxMin',('RangeAdd',),
                ['RangeMax','RangeMin'],'foreign')]
        for source,witness,qualified,members,names,mode in cases:
            with self.subTest(mode=mode), tempfile.TemporaryDirectory(prefix='companion-scope-') as tmp:
                before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
                main=TemplateInstance(('long long',),witness,nested_members=members)
                companions=tuple((name if mode is None else qualified,
                    TemplateInstance(('long long',),witness,nested_members=() if mode is None else (name,)))
                    for name in names)
                arguments=dict(companion_instances=companions,
                               member_instances={'apply':[(RecordArgument(1),),(RecordArgument(2),)]})
                if mode is None:
                    ir,coverage=lower_template_class(source,qualified,main,**arguments)
                    self.assertEqual(len(ir['functions']),5)
                    self.assertEqual([x['selected_type'] for x in coverage['companions']],
                                     [i.target(q) for q,i in companions])
                else:
                    with self.assertRaisesRegex(ValueError,
                            'requested member specialization is not instantiated|member specialization must derive from the original source pattern'):
                        lower_template_class(source,qualified,main,[ROOT/'experiments/library/cpp'],**arguments)
                exe=Path(tmp)/'native'
                subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                    '-I',str(ROOT/'experiments/library/cpp'),'-include',str(source),str(witness),'-o',str(exe)],
                    check=True,timeout=60)
                subprocess.run([str(exe)],check=True,timeout=10)
                for path,digest in before.items():
                    self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),digest)

    def test_original_mixed_add_sum_general_callers(self):
        source=ROOT/'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp'
        witness=ROOT/'tests/imports/original_mixed_add_sum.cpp'
        before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
        ir,coverage=lower_template_class(source,'RangeAddRangeSum',
            TemplateInstance(('long long',),witness,nested_members=('RangeAdd',)),
            [ROOT/'experiments/library/cpp'],companion_instances=((
                'RangeAddRangeSum',TemplateInstance(('long long',),witness,nested_members=('RangeSum',))),))
        expected={'RangeAdd_new0','RangeAdd_id','RangeAdd_compose','RangeAdd_apply_x','RangeAdd_apply_size'}
        expected.update('RangeSum_'+op+'_'+field for op in ('e','new0','new1','op') for field in ('x','size'))
        self.assertEqual({f['name'] for f in ir['functions']},expected)
        self.assertFalse(coverage['generic_types_verified'])
        self.assertFalse(coverage['full_cpp_object_lifetime_verified'])
        proof='import Proofs.MonoidLazyCall\n'+emit_lean(ir,'OriginalMixedAddSum')
        proof+=(ROOT/'tests/lean/original_mixed_add_sum.lean').read_text()
        names=('fields_exec','apply_body','apply_exec','prep_mutable_values2','mutable_values2_correct',
            'apply_correct','constant_body_correct','default_fields_exec','e_correct','default_correct',
            'prepare_mixed_values','two_values_body_correct','new_correct','op_correct',
            'add_new_correct_program','add_new_correct','add_id_correct_program','add_id_correct','compose_correct')
        with tempfile.TemporaryDirectory(prefix='mixed-add-sum-') as tmp:
            directory=Path(tmp)
            scalar_checks.ScalarDelegationTests().kernel(directory,'MixedAddSumCheck',
                ['StrictMixedBodyAudit.'+name for name in names],proof)
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I',str(ROOT/'experiments/library/cpp'),'-include',str(source),str(witness),'-o',str(exe)],
                check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
        for path,digest in before.items():
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),digest)

    def test_original_mixed_set_sum_copied_returns_and_callers(self):
        source=ROOT/'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp'
        witness=ROOT/'tests/imports/original_mixed_set_sum.cpp'
        add_witness=ROOT/'tests/imports/original_mixed_add_sum.cpp'
        before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness,add_witness)}
        ir,coverage=lower_template_class(source,'RangeSetRangeSum',
            TemplateInstance(('long long',),witness,nested_members=('RangeSet',)),
            [ROOT/'experiments/library/cpp'],companion_instances=((
                'RangeSetRangeSum',TemplateInstance(('long long',),witness,nested_members=('RangeSum',))),))
        self.assertEqual(len(ir['functions']),18)
        self.assertFalse(coverage['generic_types_verified'])
        self.assertFalse(coverage['full_cpp_object_lifetime_verified'])
        fixture=(ROOT/'tests/lean/original_mixed_set_sum_samples.lean').read_text()
        roots=['CopyReturnSamples.'+line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
        self.assertEqual(len(roots),38)
        add_ir,_=lower_template_class(source,'RangeAddRangeSum',
            TemplateInstance(('long long',),add_witness,nested_members=('RangeAdd',)),
            [ROOT/'experiments/library/cpp'],companion_instances=((
                'RangeAddRangeSum',TemplateInstance(('long long',),add_witness,nested_members=('RangeSum',))),))
        proof='import Proofs.MonoidLazyCall\n'
        for bundle,namespace in [(add_ir,'OriginalMixedAddSum'),(ir,'OriginalSetSum')]:
            proof+='\n'.join(line for line in emit_lean(bundle,namespace).splitlines()
                if not line.startswith('import '))+'\n'
        for name in ['original_mixed_add_sum.lean','scalar_record_copy_fields.lean',
                'original_mixed_set_sum_callers.lean']:
            proof+=(ROOT/'tests/lean'/name).read_text()
        proof+=fixture
        roots+=['SetSumTransferred.'+name for name in ['e_program','e_correct','new1_program',
            'default_correct','new0_program','new_correct','op_program','op_correct',
            'set_default_correct','set_id_program','set_id_correct']]
        roots+=['CopiedScalarFieldsAudit.copy_exec','CopiedScalarFieldsAudit.copy_block_exec']
        with tempfile.TemporaryDirectory(prefix='mixed-set-sum-') as tmp:
            directory=Path(tmp)
            scalar_checks.ScalarDelegationTests().kernel(directory,'MixedSetSumCheck',roots,proof)
            for cpp,guarded in [(witness,False),(ROOT/'tests/imports/original_mixed_set_sum_guarded.cpp',True)]:
                exe=directory/('guarded' if guarded else 'native')
                subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                    '-I',str(ROOT/'experiments/library/cpp'),'-include',str(source),str(cpp),'-o',str(exe)],
                    check=True,timeout=60)
                subprocess.run([str(exe)],check=True,timeout=10)
                if guarded:
                    result=subprocess.run([str(exe),'overflow'],capture_output=True,text=True,timeout=10)
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn('signed integer overflow',result.stderr)
        for path,digest in before.items():
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),digest)

    def test_mixed_copy_guards(self):
        cases=[
            ('custom_copy','Probe(const Probe& p):first(p.first+1),second(p.second){}',
                'return yes?a:b;','trivial copy'),
            ('custom_move','Probe(const Probe&)=default;Probe(Probe&& p):first(p.first+1),second(p.second){}',
                'return a;','trivial copy'),
            ('custom_dtor','~Probe(){first=0;}','return yes?a:b;','trivial destruction'),
            ('local_object','','Probe p(1,2);return p;','unsupported use of a class value')]
        for label,special,body,reason in cases:
            with self.subTest(case=label),tempfile.TemporaryDirectory(prefix='mixed-copy-guard-') as tmp:
                directory=Path(tmp);source=directory/'probe.hpp';witness=directory/'main.cpp'
                source.write_text('#include <vector>\nnamespace local {template<class T> struct Probe {'
                    'T first,second;Probe(T a,T b):first(a),second(b){} '+special+
                    ' static Probe choose(Probe a,Probe b,bool yes){'+body+'}};'
                    'template<class T> struct Tag{T value;Tag(T v):value(v){}};}\n')
                witness.write_text('int main(){using P=local::Probe<long long>;local::Tag<long long> t(1);'
                    'auto x=P::choose(P(1,2),P(3,4),true);return x.first==t.value;}\n')
                with self.assertRaisesRegex(ValueError,reason):
                    lower_template_class(source,'local::Probe',TemplateInstance(('long long',),witness),
                        companion_instances=(('local::Tag',TemplateInstance(('long long',),witness)),))

    def test_mixed_constructor_field_evaluation(self):
        proof='import Proofs.MonoidLazyCall\n';roots=[]
        cases=[('division','first(value),second(7/value)'),
               ('declaration_order','second(7/first),first(value)'),
               ('forward_read','first(second),second(value)')]
        with tempfile.TemporaryDirectory(prefix='mixed-fields-') as tmp:
            directory=Path(tmp)
            for label,initializers in cases:
                with self.subTest(case=label):
                    source=directory/(label+'.hpp');witness=directory/(label+'.cpp')
                    source.write_text('#include <vector>\nnamespace local {template<class T> struct Probe {'
                        'T first,second;Probe(T value):'+initializers+'{}'
                        ' static Probe make(T value){return Probe(value);}};'
                        'template<class T>struct Tag{T value;Tag(T v):value(v){}};}\n')
                    witness.write_text('int main(){using P=local::Probe<long long>;P a(1);auto b=P::make(1);'
                        'local::Tag<long long> t(1);return a.first==1 && a.second==7 && '
                        'b.first==1 && b.second==7 && t.value==1?0:1;}\n')
                    instance=TemplateInstance(('long long',),witness)
                    companions=(('local::Tag',instance),)
                    if label=='forward_read':
                        with self.assertRaisesRegex(ValueError,'reads a field before its initialization'):
                            lower_template_class(source,'local::Probe',instance,companion_instances=companions)
                        continue
                    ir,_=lower_template_class(source,'local::Probe',instance,companion_instances=companions)
                    self.assertEqual(len(ir['functions']),5)
                    ns='MixedFields_'+label
                    emitted=emit_lean(ir,ns)
                    proof+='\n'.join(line for line in emitted.splitlines() if not line.startswith('import '))+'\n'
                    audit='FieldsAudit_'+label
                    proof+='namespace '+audit+'\nopen Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine\n'
                    proof+='def sample (v : Int) : PS := ⟨[⟨⟨64,true,false⟩,v⟩],[⟨0,true⟩]⟩\n'
                    for op in ('new0','make'):
                        for field,value in [('first',1),('second',7)]:
                            prog=ns+'.Probe_long_long_'+op+'_'+field
                            name=op+'_'+field+'_zero';roots.append(audit+'.'+name)
                            proof+='theorem '+name+' : pexec 1 '+prog+'.body (sample 0) = none := by\n  simp only ['+prog+',pexec]\n  decide +kernel\n'
                            name=op+'_'+field+'_one';roots.append(audit+'.'+name)
                            proof+='theorem '+name+' : (pexec 1 '+prog+'.body (sample 1)).map (fun r => r.ret) = some (some '+str(value)+') := by\n  simp only ['+prog+',pexec]\n  decide +kernel\n'
                    proof+='end '+audit+'\n'
                    exe=directory/(label+'_native')
                    subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                        '-include',str(source),str(witness),'-o',str(exe)],check=True,timeout=60)
                    subprocess.run([str(exe)],check=True,timeout=10)
            self.assertEqual(len(roots),16)
            scalar_checks.ScalarDelegationTests().kernel(directory,'MixedFieldsCheck',roots,proof)

    def test_record_value_type_boundaries(self):
        full='local::Probe<long long>'
        pattern=selected_type_pattern({'_template_witness_origin':{'requested':full}},'Probe<long long>')
        for text in [full,'const '+full+' &',full+' &&',full+' const &']:
            with self.subTest(type=text):
                self.assertTrue(scalar_record_type({'qualType':text},pattern))
        for text in [full+' *',full+' *const',full+' [2]',full+' (&)[2]',
                full+' (*)()','std::vector<'+full+'>','typename std::vector<'+full+'>::iterator']:
            with self.subTest(type=text):
                self.assertFalse(scalar_record_type({'qualType':text},pattern))
        cases=[
            ('pointer','static Probe ignore(Probe *p){return{1,2};}','auto b=P::ignore(nullptr);'),
            ('vector','static Probe ignore(std::vector<Probe> p){return{1,2};}',
                'auto b=P::ignore(std::vector<P>{});'),
            ('array','static Probe ignore(Probe (&p)[2]){return{1,2};}',
                'P a[2]={P(1,2),P(3,4)};auto b=P::ignore(a);'),
            ('function','static Probe ignore(Probe (*p)()){return{1,2};}',
                'auto b=P::ignore(nullptr);'),
            ('pointer_result','static Probe *ignore(){return nullptr;}',
                'auto b=P::ignore();'),
            ('vector_result','static std::vector<Probe> ignore(){return{};}',
                'auto b=P::ignore();'),
            ('local_pointer','static Probe ignore(){Probe *p=nullptr;return{1,2};}',
                'auto b=P::ignore();'),
            ('local_vector','static Probe ignore(){std::vector<Probe> p;return{1,2};}',
                'auto b=P::ignore();'),
            ('local_array','static Probe ignore(){Probe p[2]={Probe(1,2),Probe(3,4)};return{1,2};}',
                'auto b=P::ignore();')]
        for fields in (1,2):
            for label,method,call in cases:
                with self.subTest(fields=fields,case=label),tempfile.TemporaryDirectory(prefix='record-type-') as tmp:
                    directory=Path(tmp);source=directory/'probe.hpp';witness=directory/'main.cpp'
                    members='T first,second;' if fields==2 else 'T first;'
                    initializers='first(a),second(b)' if fields==2 else 'first(a)'
                    source.write_text('#include <vector>\nnamespace local {template<class T>struct Probe{'+
                        members+'Probe(T a,T b):'+initializers+'{}'+method+'};'
                        'template<class T>struct Tag{T value;Tag(T v):value(v){}};}\n')
                    check='b==nullptr' if label=='pointer_result' else 'b.empty()' if label=='vector_result' else 'b.first==1'
                    witness.write_text('int main(){using P=local::Probe<long long>;local::Tag<long long> t(1);'+
                        'P observed(1,2);'+call+'return '+check+' && observed.first==1 && t.value==1?0:1;}\n')
                    exe=directory/'native'
                    subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                        '-include',str(source),str(witness),'-o',str(exe)],check=True,timeout=60)
                    subprocess.run([str(exe)],check=True,timeout=10)
                    with self.assertRaisesRegex(ValueError,'compound types containing'):
                        lower_template_class(source,'local::Probe',TemplateInstance(('long long',),witness),
                            companion_instances=(('local::Tag',TemplateInstance(('long long',),witness)),))

    def test_structured_path(self):
        witness=ROOT/'tests/imports/original_nested_max.cpp'
        self.assertEqual(TemplateInstance(('long long',),witness).target('Root'),'Root<long long>')
        for members in [('RangeMax<int>',),('RangeMax;int injected',),['RangeMax'],(7,)]:
            with self.subTest(members=members), self.assertRaises(ValueError):
                TemplateInstance(('long long',),witness,nested_members=members)
        for index in [-1,True,'1']:
            with self.subTest(index=index), self.assertRaises(ValueError):
                RecordArgument(index)
        source=ROOT/'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp'
        main=TemplateInstance(('long long',),witness,nested_members=('RangeMax',))
        for companions in [[],(('RangeAddRangeMaxMin',main),),
                           (('RangeAddRangeMaxMin',TemplateInstance(('long long',),
                            ROOT/'tests/imports/original_record_apply.cpp',nested_members=('RangeMin',))),)]:
            with self.subTest(companions=companions), self.assertRaises(ValueError):
                lower_template_class(source,'RangeAddRangeMaxMin',main,companion_instances=companions)
        with self.assertRaises(TypeError):
            TemplateInstance(('long long',),witness,('RangeMax',))
        with self.assertRaises(ValueError):
            TemplateInstance(('long long',),witness,nested_members=('RangeMax',)).target('Root;bad')

if __name__ == '__main__':
    disable_network()
    unittest.main()
