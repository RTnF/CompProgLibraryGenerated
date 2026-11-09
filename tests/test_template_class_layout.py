"""Original nested templates use the ordinary constructor/member-copy evaluator.

Coverage is a concrete scalar-field instance, not arbitrary T/object semantics.
"""
from pathlib import Path
import hashlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tests'),str(ROOT/'verifier'),str(ROOT/'tools')]
import class_copy_layout as layout
from ast_stream import class_construction_stages
from scalar_ir import source_ast
from class_templates import TemplateInstance,RecordArgument
from offline import disable_network
import test_scalar_class_delegation as scalar_checks

SOURCE=ROOT/'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp'
WITNESS=ROOT/'tests/imports/original_mixed_set_sum.cpp'
CANDIDATE_SOURCE=ROOT/'experiments/verification/algebraic_structure/monoid_lazy.hpp'
INCLUDES=[ROOT/'experiments/library/cpp']

class TemplateClassLayoutTests(unittest.TestCase):
    def test_original_set_record_constructor_general_callers(self):
        self._check_set_record_constructors(SOURCE)

    def test_candidate_set_record_constructor_general_callers(self):
        self._check_set_record_constructors(CANDIDATE_SOURCE,'cp::','candidate')

    def _check_set_record_constructors(self,source,family_prefix='',witness_prefix='original'):
        for base,kind in [('RangeSetRangeMaxMin','set_extrema'),('RangeSetRangeSum','set_sum')]:
            family=family_prefix+base
            witness=ROOT/'tests/imports'/(witness_prefix+'_mixed_'+kind+'.cpp')
            with self.subTest(source=str(source),family=family):
                before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
                generated=layout.emit_class_layout(source,family,'ValueObject',INCLUDES,
                    member_exports=True,factory_exports=True,
                    template_instance=TemplateInstance(('long long',),witness,nested_members=('RangeSet',)))
                aliases='namespace SelectedSet\n'
                for tag,name in [('value','RangeSet_construct0'),('default','RangeSet_construct1'),('id','RangeSet_factory_id')]:
                    aliases+=('abbrev '+tag+'Program := ValueObject.'+name+
                        '\nabbrev '+tag+'View := ValueObject.'+name+'_exportViewFuel'+
                        '\nabbrev '+tag+'Fields := ValueObject.Stages.'+name+'.scalarFields\n')
                aliases+='abbrev permissions := ValueObject.scalarPermissions\nend SelectedSet\n'
                fixture=(ROOT/'tests/lean/original_set_record_constructor_general.lean').read_text()
                roots=['SetRecordConstructorGeneral.'+line.split()[1]
                    for line in fixture.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(roots),27)
                generated=('import Proofs.MonoidLazyCall\nimport Proofs.CppScalarContents\n'
                    'import Proofs.CppScalarValuePrepare\nimport Proofs.CppFrameResolveExtension\n'+generated)
                with tempfile.TemporaryDirectory(prefix='set-record-constructor-') as tmp:
                    directory=Path(tmp)
                    scalar_checks.ScalarDelegationTests().kernel(directory,'SetRecordConstructorCheck',roots,
                        generated+aliases+fixture)
                    main=directory/'native.cpp'
                    main.write_text('int main(){using R='+family+'<long long>::RangeSet;'
                        'const R zero;const auto id=R::id();if(zero.v!=0 || !zero.noop || id.v!=0 || !id.noop)return 1;'
                        'const long long xs[]={LLONG_MIN,-7,0,LLONG_MAX};for(auto x:xs){'
                        'const R a(x);R b(a);if(a.v!=x || a.noop || b.v!=x || b.noop)return 2;'
                        'b.v=23;b.noop=true;if(a.v!=x || a.noop)return 3;}return 0;}\n')
                    exe=directory/'native'
                    subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                        '-I',str(INCLUDES[0]),'-include',str(source),str(main),'-o',str(exe)],check=True,timeout=60)
                    subprocess.run([str(exe)],check=True,timeout=10)
                for p,digest in before.items():self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),digest)

    def test_original_scalar_record_constructors_and_id_general_callers(self):
        self._check_scalar_record_constructors(SOURCE)

    def test_candidate_scalar_record_constructors_and_id_general_callers(self):
        self._check_scalar_record_constructors(CANDIDATE_SOURCE,'cp::','candidate')

    def _check_scalar_record_constructors(self,source,family_prefix='',witness_prefix='original'):
        cases=[('RangeAddRangeMaxMin','add_extrema',('RangeMax','RangeMin','RangeAdd')),
               ('RangeSetRangeMaxMin','set_extrema',('RangeMax','RangeMin')),
               ('RangeAddRangeSum','add_sum',('RangeAdd',))]
        for base,kind,records in cases:
            family=family_prefix+base
            witness=ROOT/'tests/imports'/(witness_prefix+'_mixed_'+kind+'.cpp')
            for record in records:
                with self.subTest(source=str(source),family=family,record=record):
                    before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
                    generated=layout.emit_class_layout(source,family,'ValueObject',INCLUDES,
                        member_exports=True,factory_exports=True,
                        template_instance=TemplateInstance(('long long',),witness,nested_members=(record,)))
                    aliases=('namespace SelectedConstructor\nabbrev program := ValueObject.'+record+'_construct0'+
                        '\nabbrev view := ValueObject.'+record+'_construct0_exportViewFuel'+
                        '\nabbrev fields := ValueObject.Stages.'+record+'_construct0.scalarFields'+
                        '\nabbrev permissions := ValueObject.scalarPermissions\nend SelectedConstructor\n')
                    fixture=(ROOT/'tests/lean/original_scalar_record_constructor_general.lean').read_text()
                    roots=['ScalarRecordConstructorGeneral.'+line.split()[1]
                        for line in fixture.splitlines() if line.startswith('theorem ')]
                    self.assertEqual(len(roots),12)
                    if record=='RangeAdd':
                        aliases+=('namespace SelectedZeroFactory\nabbrev program := ValueObject.RangeAdd_factory_id'+
                            '\nabbrev view := ValueObject.RangeAdd_factory_id_exportViewFuel'+
                            '\nabbrev fields := ValueObject.Stages.RangeAdd_factory_id.scalarFields'+
                            '\nend SelectedZeroFactory\n')
                        zero=(ROOT/'tests/lean/original_scalar_record_zero_factory_general.lean').read_text()
                        zero_roots=['ScalarRecordZeroFactoryGeneral.'+line.split()[1]
                            for line in zero.splitlines() if line.startswith('theorem ')]
                        self.assertEqual(len(zero_roots),6)
                        roots+=zero_roots;fixture+=zero
                    generated=('import Proofs.MonoidLazyCall\nimport Proofs.CppScalarContents\n'
                        'import Proofs.CppScalarValuePrepare\nimport Proofs.CppFrameResolveExtension\n'+generated)
                    with tempfile.TemporaryDirectory(prefix='scalar-record-constructor-') as tmp:
                        directory=Path(tmp)
                        scalar_checks.ScalarDelegationTests().kernel(directory,'ScalarRecordConstructorCheck',roots,
                            generated+aliases+fixture)
                        field='v' if record=='RangeAdd' else 'x'
                        main=directory/'native.cpp'
                        main.write_text('int main(){using R='+family+'<long long>::'+record+';'
                            'const long long xs[]={LLONG_MIN,-7,0,LLONG_MAX};for(auto x:xs){'
                            'const R a(x);R b(x),c(a);b.'+field+'=23;'
                            'if(a.'+field+'!=x || c.'+field+'!=x || b.'+field+'!=23)return 1;}' +
                            ('auto id=R::id();return id.v==0?0:2;' if record=='RangeAdd' else 'return 0;')+'}\n')
                        exe=directory/'native'
                        subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                            '-I',str(INCLUDES[0]),'-include',str(source),str(main),'-o',str(exe)],check=True,timeout=60)
                        subprocess.run([str(exe)],check=True,timeout=10)
                    for p,digest in before.items():self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),digest)

    def test_original_scalar_object_construction_copy_permissions_and_scope(self):
        instance=TemplateInstance(('long long',),WITNESS,nested_members=('RangeSet',))
        before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (SOURCE,WITNESS)}
        original=layout.lower_class_layout
        plans=[]
        def captured(*args,**kwargs):
            ir=original(*args,**kwargs);plans.append(ir);return ir
        with mock.patch.object(layout,'lower_class_layout',side_effect=captured):
            generated=layout.emit_class_layout(SOURCE,'RangeSetRangeSum','OriginalRangeSetObject',
                INCLUDES,member_exports=True,template_instance=instance)
        self.assertEqual(len(plans),1)
        ir=plans[0]
        self.assertEqual(ir['qualified_class'],'RangeSetRangeSum<long long>::RangeSet')
        self.assertEqual([(f['name'],f['kind'],f['type']) for f in ir['fields']],
            [('v','scalar_copy','long long'),('noop','scalar_copy','bool')])
        self.assertEqual(ir['source_sha256'],before[SOURCE])
        self.assertEqual(ir['template_instance']['witness_sha256'],before[WITNESS])
        self.assertFalse(ir['template_instance']['generic_types_verified'])
        self.assertFalse(ir['template_instance']['full_cpp_object_lifetime_verified'])
        fixture=(ROOT/'tests/lean/original_template_object_layout.lean').read_text()
        roots=['TemplateObjectAudit.'+line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
        self.assertEqual(len(roots),9)
        roots+=['OriginalRangeSetObject.'+name for name in ('copy_layout_of_fields',
            'copy_observers_of_fields','copy_values_of_fields','copy_positions_of_fields',
            'copy_work_of_fields','copy_space_of_fields')]
        with tempfile.TemporaryDirectory(prefix='template-class-object-') as tmp:
            directory=Path(tmp)
            scalar_checks.ScalarDelegationTests().kernel(directory,'TemplateObjectCheck',roots,generated+fixture)
            main=directory/'native.cpp'
            main.write_text('int main(){using A=RangeSetRangeSum<long long>::RangeSet;const A a(7);A b=a;'
                'b.v=11;b.noop=true;{A c=a;c.v=19;c.noop=true;if(c.v!=19)return 1;}'
                'A d;return a.v==7 && !a.noop && b.v==11 && b.noop && d.v==0 && d.noop?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I',str(INCLUDES[0]),'-include',str(SOURCE),str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
        for p,digest in before.items():self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),digest)

    def test_layout_rejects_nonstructured_template_requests(self):
        with mock.patch.object(layout,'translation_unit') as compiler:
            for value in ('RangeSetRangeSum<long long>::RangeSet',{'arguments':['long long']}):
                with self.subTest(value=value),self.assertRaisesRegex(ValueError,'a structured template instance'):
                    layout.lower_class_layout(SOURCE,'RangeSetRangeSum',INCLUDES,
                        multiple_vectors=True,template_instance=value)
            compiler.assert_not_called()

    def test_original_delegating_construction_retains_all_fields(self):
        self._check_delegating_construction(SOURCE,'RangeSetRangeSum',WITNESS)

    def test_candidate_delegating_construction_retains_all_fields(self):
        for family,kind in [('RangeSetRangeSum','set'),('RangeAddRangeSum','add')]:
            with self.subTest(family=family):
                self._check_delegating_construction(CANDIDATE_SOURCE,'cp::'+family,
                    ROOT/'tests/imports'/('candidate_mixed_'+kind+'_sum.cpp'))

    def _check_delegating_construction(self,source,qualified,witness):
        instance=TemplateInstance(('long long',),witness,nested_members=('RangeSum',))
        generated=layout.emit_class_layout(source,qualified,'OriginalRangeSumObject',
            INCLUDES,member_exports=True,factory_exports=True,template_instance=instance)
        generated='import Proofs.MonoidLazyCall\nimport Proofs.CppScalarContents\nimport Proofs.CppScalarValuePrepare\nimport Proofs.CppFrameResolveExtension\n'+generated
        fixture=(ROOT/'tests/lean/original_delegating_object_layout.lean').read_text()
        roots=['DelegatingObjectAudit.'+line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
        self.assertEqual(len(roots),7)
        fixture+=(ROOT/'tests/lean/original_delegating_constructor_general.lean').read_text()
        roots+=['RangeSumConstructorGeneral.'+name for name in ('body_shape','raw_exec','stage_ready',
            'finish_export','default_construct_correct','existing_scalar_read','destination_readable',
            'frame_extension','existing_vector_resolve','existing_vector_read')]
        value_fixture=(ROOT/'tests/lean/original_value_constructor_general.lean').read_text()
        value_roots=['RangeSumValueConstructorGeneral.'+line.split()[1]
            for line in value_fixture.splitlines() if line.startswith('theorem ')]
        self.assertEqual(len(value_roots),11)
        fixture+=value_fixture
        roots+=value_roots
        factory_fixture=(ROOT/'tests/lean/original_factory_export_general.lean').read_text()
        factory_roots=['RangeSumFactoryGeneral.'+line.split()[1]
            for line in factory_fixture.splitlines() if line.startswith('theorem ')]
        self.assertEqual(len(factory_roots),10)
        fixture+=factory_fixture
        roots+=factory_roots
        roots+=['OriginalRangeSumObject.'+name for name in ('copy_positions_of_fields','copy_work_of_fields','copy_space_of_fields')]
        with tempfile.TemporaryDirectory(prefix='delegating-original-object-') as tmp:
            directory=Path(tmp)
            scalar_checks.ScalarDelegationTests().kernel(directory,'DelegatingOriginalCheck',roots,generated+fixture)
            main=directory/'native.cpp'
            main.write_text('int main(){using R='+qualified+'<long long>::RangeSum;const R x;R y=x;'
                'const R identity=R::e();if(identity.x!=0 || identity.size!=0)return 4;'
                'y.x=23;y.size=-4;R z(7,-4);if(!(x.x==0 && x.size==0 && y.x==23 && y.size==-4 && z.x==7 && z.size==-4))return 1;'
                'const long long xs[]={LLONG_MIN,-1,0,LLONG_MAX};const int ns[]={INT_MIN,-4,0,INT_MAX};'
                'for(auto v:xs)for(auto n:ns){const R a(v,n);R b=a;if(a.x!=v || a.size!=n || b.x!=v || b.size!=n)return 2;'
                'b.x=23;b.size=4;if(a.x!=v || a.size!=n)return 3;}return 0;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I',str(INCLUDES[0]),'-include',str(source),str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)

    def test_original_friend_returns_the_complete_object(self):
        self.check_original_friend_return('RangeSetRangeSum',WITNESS)

    def test_add_sum_friend_returns_the_complete_object(self):
        self.check_original_friend_return('RangeAddRangeSum',ROOT/'tests/imports/original_mixed_add_sum.cpp')

    def test_candidate_sum_friends_return_complete_objects(self):
        for family,kind in [('RangeSetRangeSum','set'),('RangeAddRangeSum','add')]:
            with self.subTest(family=family):
                self.check_original_friend_return('cp::'+family,
                    ROOT/'tests/imports'/('candidate_mixed_'+kind+'_sum.cpp'),CANDIDATE_SOURCE)

    def check_original_friend_return(self,qualified,witness,source=SOURCE):
        instance=TemplateInstance(('long long',),witness,nested_members=('RangeSum',))
        generated=layout.emit_class_layout(source,qualified,'OriginalFriendSumObject',
            INCLUDES,member_exports=True,factory_exports=True,friend_exports=True,template_instance=instance)
        fixture=(ROOT/'tests/lean/original_friend_object_return.lean').read_text()
        roots=['FriendObjectReturnAudit.'+line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
        self.assertEqual(len(roots),11)
        general=(ROOT/'tests/lean/original_friend_object_return_general.lean').read_text()
        general_roots=['FriendObjectReturnGeneral.'+line.split()[1]
            for line in general.splitlines() if line.startswith('theorem ')]
        self.assertEqual(len(general_roots),3)
        roots+=general_roots
        fixture+=general
        call=(ROOT/'tests/lean/original_friend_object_call.lean').read_text()
        call_roots=['FriendObjectCallGeneral.'+line.split()[1]
            for line in call.splitlines() if line.startswith('theorem ')]
        self.assertEqual(len(call_roots),12)
        roots+=call_roots
        fixture+=call
        generated='import Proofs.MonoidLazyCall\nimport Proofs.CppScalarContents\n'+generated
        with tempfile.TemporaryDirectory(prefix='friend-return-object-') as tmp:
            directory=Path(tmp)
            scalar_checks.ScalarDelegationTests().kernel(directory,'FriendReturnCheck',roots,generated+fixture)
            main=directory/'native.cpp';main.write_text('int main(int argc,char**){using R='+qualified+'<long long>::RangeSum;'
                'if(argc==2){auto bad=op(R(LLONG_MAX,0),R(2,1));return bad.x==0;}'
                'if(argc==3){auto bad=op(R(7,INT_MAX),R(2,1));return bad.size==0;}'
                'const R a(7,-4),b(2,1);const auto c=op(a,b);auto same=op(a,a);'
                'return a.x==7 && a.size==-4 && b.x==2 && b.size==1 && c.x==9 && c.size==-3 '
                '&& same.x==14 && same.size==-8?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O0','-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I',str(INCLUDES[0]),'-include',str(source),str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
            for args in (['first'],['second','field']):
                failed=subprocess.run([str(exe),*args],capture_output=True,text=True,timeout=10)
                self.assertNotEqual(failed.returncode,0)
                self.assertIn('signed integer overflow',failed.stderr)

    def test_extrema_friends_return_complete_objects_for_both_families(self):
        self._check_extrema_friends(SOURCE)

    def test_candidate_extrema_friends_return_complete_objects(self):
        self._check_extrema_friends(CANDIDATE_SOURCE,'cp::','candidate')

    def _check_extrema_friends(self,source,family_prefix='',witness_prefix='original'):
        witnesses=[('RangeSetRangeMaxMin',ROOT/'tests/imports/original_mixed_set_extrema.cpp'),
                   ('RangeAddRangeMaxMin',ROOT/'tests/imports/original_mixed_add_extrema.cpp')]
        for qualified,witness in witnesses:
            qualified=family_prefix+qualified
            witness=ROOT/'tests/imports'/witness.name.replace('original_',witness_prefix+'_',1)
            for kind,operation,low in [('RangeMax','max',True),('RangeMin','min',False)]:
                with self.subTest(family=qualified,record=kind):
                    instance=TemplateInstance(('long long',),witness,nested_members=(kind,))
                    generated=layout.emit_class_layout(source,qualified,'OriginalExtremaObject',
                        INCLUDES,member_exports=True,factory_exports=True,friend_exports=True,template_instance=instance)
                    neutral=-9223372036854775808 if low else 9223372036854775807
                    left,right=(0,1) if low else (1,0)
                    neutral_cpp="LLONG_MIN" if low else "LLONG_MAX"
                    aliases=('namespace SelectedExtrema\n'
                        f'abbrev program := OriginalExtremaObject.{kind}_factory_op\n'
                        f'abbrev defaultExport := OriginalExtremaObject.{kind}_construct1_exportViewFuel\n'
                        f'abbrev identityExport := OriginalExtremaObject.{kind}_factory_e_exportViewFuel\n'
                        f'abbrev combineExport := OriginalExtremaObject.{kind}_factory_op_exportObjectsFuel\n'
                        f'abbrev viewExport := OriginalExtremaObject.{kind}_factory_op_exportViewFuel\n'
                        f'abbrev selectedFields := OriginalExtremaObject.Stages.{kind}_factory_op.scalarFields\n'
                        f'def neutral : Int := ({neutral})\n'
                        f'def leftIndex : Nat := {left}\ndef rightIndex : Nat := {right}\n'
                        f'def expected (x y : Int) : Int := {operation} x y\n'
                        'theorem expected_value (x y : Int) :\n'
                        ' (if (if leftIndex=0 then x else y) < (if rightIndex=0 then x else y) then y else x) = expected x y :=\n'
                        f' ExtremaObjectGeneral.selected_{operation} x y\nend SelectedExtrema\n')
                    general=(ROOT/'tests/lean/original_extrema_object_general.lean').read_text()
                    fixture=(ROOT/'tests/lean/original_extrema_object_values.lean').read_text()
                    roots=['ExtremaObjectGeneral.'+line.split()[1] for line in general.splitlines() if line.startswith('theorem ')]
                    self.assertEqual(len(roots),4)
                    roots+=['SelectedExtrema.expected_value']
                    value_roots=['ExtremaObjectAudit.'+line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
                    self.assertEqual(len(value_roots),10)
                    roots+=value_roots
                    call=(ROOT/'tests/lean/original_extrema_object_call.lean').read_text()
                    call_roots=['ExtremaObjectCallGeneral.'+line.split()[1]
                        for line in call.splitlines() if line.startswith('theorem ')]
                    self.assertEqual(len(call_roots),11)
                    roots+=call_roots
                    with tempfile.TemporaryDirectory(prefix='extrema-complete-object-') as tmp:
                        directory=Path(tmp)
                        scalar_checks.ScalarDelegationTests().kernel(directory,'ExtremaCompleteCheck',roots,
                            'import Proofs.MonoidLazyCall\nimport Proofs.CppScalarContents\n'+generated+general+aliases+fixture+call)
                        main=directory/'native.cpp';main.write_text(f'int main(){{using M={qualified}<long long>::{kind};'
                            f'const M zero;const auto id=M::e();if(zero.x!={neutral_cpp} || id.x!=zero.x)return 1;'
                            'const long long values[]={LLONG_MIN,-1,0,LLONG_MAX};'
                            f'for(auto x:values)for(auto y:values){{const M a(x),b(y);auto c=op(a,b);auto same=op(a,a);'
                            f'if(c.x!=std::{operation}(x,y) || same.x!=x)return 2;c.x=17;'
                            'if(a.x!=x || b.x!=y)return 3;}return 0;}\n')
                        exe=directory/'native'
                        subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                            '-I',str(INCLUDES[0]),'-include',str(source),str(main),'-o',str(exe)],check=True,timeout=60)
                        subprocess.run([str(exe)],check=True,timeout=10)

    def test_factory_standard_arguments_require_callee_identity(self):
        base='''#include <algorithm>
#include <limits>
#include <vector>
struct Box {
 long long x;
 Box(long long a):x(a){}
 Box():Box(e()){}
 static Box e(){return std::numeric_limits<long long>::min();}
 friend Box op(const Box &a,const Box &b){return std::max(a.x,b.x);}
};
'''
        fake='namespace fake {long long max(const long long &a,const long long &b){return 99;}}\n'
        fake_limits='namespace fake {template<class T>struct numeric_limits{static T min(){return 42;}};}\n'
        cases=[(base.replace('struct Box',fake+'struct Box').replace('std::max(a.x,b.x)','fake::max(a.x,b.x)'),
                'pure scalar arguments'),
            (base.replace('struct Box',fake_limits+'struct Box').replace('std::numeric_limits','fake::numeric_limits'),None),
            (base.replace('long long x;','mutable long long x;').replace('std::max(a.x,b.x)','std::max(++a.x,b.x)'),
                'plain scalar lvalue arguments'),
            (base.replace('std::max(a.x,b.x)','std::max(a.x+1,b.x)'), 'plain scalar lvalue arguments'),
            (base.replace('struct Box','namespace std {template<> const long long &max<long long>(const long long &a,const long long &b){return b;}}\nstruct Box'),
                'user declarations in standard library namespaces')]
        with tempfile.TemporaryDirectory(prefix='factory-standard-identity-') as tmp:
            source=Path(tmp)/'box.hpp'
            for text,error in cases:
                source.write_text(text)
                with self.subTest(error=error):
                    if error:
                        with self.assertRaisesRegex(ValueError,error):
                            layout.emit_class_layout(source,'Box',member_exports=True,factory_exports=True,friend_exports=True)
                    else:
                        with self.assertRaises(ValueError):
                            layout.emit_class_layout(source,'Box',member_exports=True,factory_exports=True,friend_exports=True)

    def test_extrema_identities_support_floating_values_and_opaque_types(self):
        driver=ROOT/'tests/imports/monoid_lazy_floating_identity.cpp'
        with tempfile.TemporaryDirectory(prefix='extrema-floating-identity-') as tmp:
            exe=Path(tmp)/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I',str(INCLUDES[0]),str(driver),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)

    def test_constexpr_factory_cannot_discard_runtime_initializer(self):
        text='''#include <vector>
struct Box {
 long long x;
 Box(long long a):x(a){}
 static Box make(long long seed){if constexpr(long long value=seed;true){return value;}else{return 0;}}
};
'''
        with tempfile.TemporaryDirectory(prefix='factory-constexpr-init-') as tmp:
            source=Path(tmp)/'box.hpp';source.write_text(text)
            with self.assertRaisesRegex(ValueError,'constexpr factory branch cannot have runtime initializers'):
                layout.emit_class_layout(source,'Box',member_exports=True,factory_exports=True)

    def test_factory_body_and_chained_delegation_order(self):
        text='''#include <vector>
struct Pair {
 long long first; int second;
 Pair(long long a,int b):second(b+1),first(a){a=91;first=first+10;}
 Pair():Pair(make()){first=first+100;second=second+1000;}
 Pair(bool):Pair(){second=second+10000;}
 static Pair make(){return {3,4};}
};
'''
        with tempfile.TemporaryDirectory(prefix='delegating-body-order-') as tmp:
            directory=Path(tmp);source=directory/'pair.hpp';source.write_text(text)
            generated=layout.emit_class_layout(source,'Pair','DelegatedPairObject',member_exports=True)
            fixture=(ROOT/'tests/lean/scalar_delegation_bodies.lean').read_text()
            roots=['DelegationBodyAudit.'+line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
            self.assertEqual(len(roots),5)
            scalar_checks.ScalarDelegationTests().kernel(directory,'DelegationBodyCheck',roots,generated+fixture)
            main=directory/'native.cpp';main.write_text('#include "pair.hpp"\nint main(){Pair a(3,4),b,c(true);'
                'return a.first==13 && a.second==5 && b.first==113 && b.second==1005 && c.first==113 && c.second==11005?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)

    def test_delegating_factory_evaluates_failing_field(self):
        text='''#include <vector>
struct Pair {
 long long first;int second;
 Pair(long long a,int n):first(a),second(7/n){}
 Pair():Pair(make()){}
 static Pair make(){return {11,0};}
};
'''
        with tempfile.TemporaryDirectory(prefix='delegating-failed-field-') as tmp:
            directory=Path(tmp);source=directory/'pair.hpp';source.write_text(text)
            generated=layout.emit_class_layout(source,'Pair','FailurePairObject',member_exports=True)
            fixture=(ROOT/'tests/lean/scalar_delegation_failure.lean').read_text()
            roots=['DelegationFailureAudit.'+line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
            self.assertEqual(len(roots),4)
            scalar_checks.ScalarDelegationTests().kernel(directory,'DelegationFailureCheck',roots,generated+fixture)
            main=directory/'native.cpp';main.write_text('#include "pair.hpp"\nint main(int argc,char**){'
                'if(argc>1){Pair p;return p.first==11?0:1;}Pair p(11,1);return p.first==11 && p.second==7?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
            failed=subprocess.run([str(exe),'invalid'],capture_output=True,text=True,timeout=10)
            self.assertNotEqual(failed.returncode,0)
            self.assertIn('division by zero',failed.stderr)

    def test_factory_exports_capture_all_fields_and_parameters_once(self):
        text='''#include <vector>
struct Pair {
 long long first;int second;
 Pair(long long a,int b):first(a),second(b){touch(1);first=first+sum();quotient();}
 Pair(long long a,int b,int unused):Pair(a,b){}
 Pair():Pair(make()){}
 static Pair make(){return {3,4};}
 static Pair from(long long a,int b){return {a,b};}
 static Pair bad(){return {3,-2};}
 static Pair unused(){return {3,4,7/0};}
 void touch(long long delta){first=first+delta;touch2();}
 void touch2(){second=second+2;}
 long long sum()const{return first+second;}
 long long quotient()const{return 7/second;}
};
'''
        with tempfile.TemporaryDirectory(prefix='factory-member-export-') as tmp:
            directory=Path(tmp);source=directory/'pair.hpp';source.write_text(text)
            original=layout.lower_class_layout;plans=[]
            def captured(*args,**kwargs):
                result=original(*args,**kwargs);plans.append(result);return result
            with mock.patch.object(layout,'lower_class_layout',side_effect=captured):
                generated=layout.emit_class_layout(source,'Pair','FactoryPairObject',member_exports=True,factory_exports=True)
            factories=[f for f in plans[0]['functions'] if 'class_factory' in f]
            self.assertEqual([(f['name'],f['class_factory']['method']) for f in factories],
                [('Pair_factory_make','make'),('Pair_factory_from','from'),('Pair_factory_bad','bad'),('Pair_factory_unused','unused')])
            self.assertEqual([len(f['parameters']) for f in factories],[0,2,0,0])
            fixture=(ROOT/'tests/lean/scalar_factory_exports.lean').read_text()
            roots=['FactoryExportAudit.'+line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
            self.assertEqual(len(roots),10)
            scalar_checks.ScalarDelegationTests().kernel(directory,'FactoryExportCheck',roots,generated+fixture)
            main=directory/'native.cpp';main.write_text('#include "pair.hpp"\nint main(int argc,char**){'
                'if(argc==2){auto bad=Pair::bad();return bad.first==0;}'
                'if(argc==3){auto bad=Pair::from(3,-2);return bad.first==0;}'
                'if(argc==4){auto bad=Pair::unused();return bad.first==0;}'
                'const auto a=Pair::make();auto b=Pair::from(7,8);auto neg=Pair::from(3,-4);auto c=a;'
                'c.first=23;c.second=-4;return a.first==14 && a.second==6 && b.first==26 && b.second==10 '
                '&& neg.first==6 && neg.second==-2 && c.first==23 && c.second==-4?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O0','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
            for args in (['bad'],['from','bad'],['unused','argument','bad']):
                failed=subprocess.run([str(exe),*args],capture_output=True,text=True,timeout=10)
                self.assertNotEqual(failed.returncode,0)
                self.assertIn('division by zero',failed.stderr)

    def test_factory_exports_reject_unsupported_results_and_effects(self):
        from ast_stream import class_factory_stages
        base='''#include <vector>
struct Pair {
 long long first;int second;
 Pair(long long a,int b):first(a),second(b){}
 static Pair make(){return {3,4};}
 EXTRA
};
'''
        cases=[(base.replace('EXTRA','').replace('return {3,4};','static int count=0;++count;return {3,4};'),
                'exactly one returned construction'),
            (base.replace('EXTRA','').replace('static Pair make(){return {3,4};}',
                'static Pair &make(){static Pair p(3,4);return p;}'),'return the selected record by value'),
            (base.replace('EXTRA','').replace('Pair make(){return {3,4};}',
                'Pair make(const long long &a){return {a,4};}'),'scalar value parameters without defaults'),
            (base.replace('EXTRA','').replace('Pair make(){return {3,4};}',
                'Pair make(long long a=3){return {a,4};}'),'scalar value parameters without defaults'),
            (base.replace('EXTRA','~Pair(){}'),'trivial copy/move/destruction'),
            (base.replace('EXTRA','Pair(const Pair &p):first(p.first),second(p.second){}'),
                'trivial copy/move/destruction')]
        with tempfile.TemporaryDirectory(prefix='factory-export-boundaries-') as tmp:
            source=Path(tmp)/'pair.hpp'
            for text,error in cases:
                source.write_text(text)
                records=[n for n in source_ast(source,'Pair') if n.get('kind')=='CXXRecordDecl' and
                    n.get('name')=='Pair' and n.get('completeDefinition')]
                self.assertEqual(len(records),1)
                with self.subTest(error=error),self.assertRaisesRegex(ValueError,error):
                    class_factory_stages(records[0],source)
            with mock.patch.object(layout,'translation_unit') as compiler,self.assertRaisesRegex(
                    ValueError,'factory exports require member exports'):
                layout.emit_class_layout(source,'Pair',factory_exports=True)
            compiler.assert_not_called()

    def test_friend_exports_are_explicit_and_keep_record_value_parameters(self):
        from ast_stream import class_factory_stages
        text='''#include <vector>
struct Pair {
 long long first;int second;
 Pair(long long a,int b):first(a),second(b){}
 static Pair make(){return {3,4};}
 friend Pair op(Pair a,const Pair &b){return {a.first+b.first,a.second+b.second};}
};
'''
        with tempfile.TemporaryDirectory(prefix='friend-export-boundaries-') as tmp:
            source=Path(tmp)/'pair.hpp';source.write_text(text)
            records=[n for n in source_ast(source,'Pair') if n.get('kind')=='CXXRecordDecl' and
                n.get('name')=='Pair' and n.get('completeDefinition')]
            self.assertEqual(len(records),1)
            self.assertEqual([f['name'] for f in class_factory_stages(records[0],source)],['Pair_factory_make'])
            functions=class_factory_stages(records[0],source,include_friends=True)
            self.assertEqual([f['name'] for f in functions],['Pair_factory_make','Pair_factory_op'])
            self.assertEqual(functions[1]['_factory_stage']['arguments'],[
                dict(kind='record_value',count=2),dict(kind='record_reference',count=2)])
            with mock.patch.object(layout,'translation_unit') as compiler,self.assertRaisesRegex(
                    ValueError,'friend exports require factory exports'):
                layout.emit_class_layout(source,'Pair',member_exports=True,friend_exports=True)
            compiler.assert_not_called()

    def test_record_value_factory_copies_all_fields_before_export(self):
        text='''#include <vector>
struct Pair {
 long long first;int second;
 Pair(long long a,int b):first(a),second(b){}
 friend Pair op(Pair a,const Pair &b){return {a.first+b.first,a.second+b.second};}
};
'''
        with tempfile.TemporaryDirectory(prefix='record-value-factory-') as tmp:
            directory=Path(tmp);source=directory/'pair.hpp';source.write_text(text)
            generated=layout.emit_class_layout(source,'Pair','ValuePairObject',member_exports=True,
                factory_exports=True,friend_exports=True)
            fixture=(ROOT/'tests/lean/scalar_factory_value_arguments.lean').read_text()
            roots=['FactoryValueArgumentsAudit.'+line.split()[1]
                for line in fixture.splitlines() if line.startswith('theorem ')]
            self.assertEqual(len(roots),8)
            scalar_checks.ScalarDelegationTests().kernel(directory,'FactoryValueArgumentsCheck',roots,generated+fixture)
            main=directory/'native.cpp';main.write_text('#include "pair.hpp"\nint main(int argc,char**){'
                'if(argc>1){auto bad=op(Pair(9223372036854775807LL,0),Pair(2,1));return bad.first==0;}'
                'const Pair a(7,-4),b(2,1);auto c=op(a,b);const auto d=op(a,a);c.first=19;'
                'return a.first==7 && a.second==-4 && b.first==2 && b.second==1 && '
                'c.first==19 && c.second==-3 && d.first==14 && d.second==-8?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
            failed=subprocess.run([str(exe),'overflow'],capture_output=True,text=True,timeout=10)
            self.assertNotEqual(failed.returncode,0)
            self.assertIn('signed integer overflow',failed.stderr)
            nontrivial=text.replace(' friend Pair op(',
                ' Pair(const Pair &a):first(a.first+1),second(a.second){}\n friend Pair op(')
            source.write_text(nontrivial)
            with self.assertRaisesRegex(ValueError,'copy constructor must be the used implicit defaulted declaration'):
                layout.emit_class_layout(source,'Pair',member_exports=True,factory_exports=True,friend_exports=True)
            source.write_text(text.replace('op(Pair a,','op(Pair &&a,'))
            with self.assertRaisesRegex(ValueError,'require values or lvalue references'):
                layout.emit_class_layout(source,'Pair',member_exports=True,factory_exports=True,friend_exports=True)

    def test_original_add_compose_keeps_record_value_parameters(self):
        self._check_add_compose(SOURCE)

    def test_candidate_add_compose_keeps_record_value_parameters(self):
        self._check_add_compose(CANDIDATE_SOURCE,'cp::','candidate')

    def _check_add_compose(self,source,family_prefix='',witness_prefix='original'):
        witnesses=[('RangeAddRangeMaxMin',ROOT/'tests/imports/original_mixed_add_extrema.cpp'),
                   ('RangeAddRangeSum',ROOT/'tests/imports/original_mixed_add_sum.cpp')]
        for family,witness in witnesses:
            family=family_prefix+family
            witness=ROOT/'tests/imports'/witness.name.replace('original_',witness_prefix+'_',1)
            with self.subTest(family=family):
                before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
                instance=TemplateInstance(('long long',),witness,nested_members=('RangeAdd',))
                generated=layout.emit_class_layout(source,family,'OriginalValueAdd',INCLUDES,
                    member_exports=True,factory_exports=True,friend_exports=True,template_instance=instance)
                fixture=(ROOT/'tests/lean/original_value_add_objects.lean').read_text()
                roots=['OriginalValueAddAudit.'+line.split()[1]
                    for line in fixture.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(roots),8)
                general=(ROOT/'tests/lean/original_value_add_call.lean').read_text()
                call_roots=['ValueAddCallGeneral.'+line.split()[1]
                    for line in general.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(call_roots),13)
                roots+=call_roots
                generated='import Proofs.MonoidLazyCall\nimport Proofs.CppScalarContents\nimport Proofs.CppScalarValuePrepare\n'+generated
                with tempfile.TemporaryDirectory(prefix='original-value-add-') as tmp:
                    directory=Path(tmp)
                    scalar_checks.ScalarDelegationTests().kernel(directory,'OriginalValueAddCheck',roots,generated+fixture+general)
                    main=directory/'native.cpp';main.write_text('int main(int argc,char**){using A='+family+'<long long>::RangeAdd;'
                        'if(argc>1){auto bad=compose(A(LLONG_MAX),A(2));return bad.v==0;}'
                        'const A a(7),b(2);auto c=compose(a,b);const auto d=compose(a,a);auto id=A::id();c.v=19;'
                        'return a.v==7 && b.v==2 && c.v==19 && d.v==14 && id.v==0?0:1;}\n')
                    exe=directory/'native'
                    subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                        '-I',str(INCLUDES[0]),'-include',str(source),str(main),'-o',str(exe)],check=True,timeout=60)
                    subprocess.run([str(exe)],check=True,timeout=10)
                    failed=subprocess.run([str(exe),'overflow'],capture_output=True,text=True,timeout=10)
                    self.assertNotEqual(failed.returncode,0)
                    self.assertIn('signed integer overflow',failed.stderr)
                for p,digest in before.items():self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),digest)

    def test_original_set_compose_copies_the_selected_complete_object(self):
        self._check_set_compose(SOURCE)

    def test_candidate_set_compose_copies_the_selected_complete_object(self):
        self._check_set_compose(CANDIDATE_SOURCE,'cp::','candidate')

    def _check_set_compose(self,source,family_prefix='',witness_prefix='original'):
        witnesses=[('RangeSetRangeMaxMin',ROOT/'tests/imports/original_mixed_set_extrema.cpp'),
                   ('RangeSetRangeSum',WITNESS)]
        for family,witness in witnesses:
            family=family_prefix+family
            witness=ROOT/'tests/imports'/witness.name.replace('original_',witness_prefix+'_',1)
            with self.subTest(family=family):
                before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
                generated=layout.emit_class_layout(source,family,'OriginalSetObject',INCLUDES,
                    member_exports=True,factory_exports=True,friend_exports=True,
                    template_instance=TemplateInstance(('long long',),witness,nested_members=('RangeSet',)))
                fixture=(ROOT/'tests/lean/original_set_object_values.lean').read_text()
                roots=['OriginalSetObjectAudit.'+line.split()[1]
                    for line in fixture.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(roots),10)
                general=(ROOT/'tests/lean/original_set_object_general.lean').read_text()
                general_roots=['SetObjectGeneral.'+line.split()[1]
                    for line in general.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(general_roots),4)
                call=(ROOT/'tests/lean/original_set_object_call.lean').read_text()
                call_roots=['SetObjectCallGeneral.'+line.split()[1]
                    for line in call.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(call_roots),11)
                roots+=general_roots+call_roots
                generated='import Proofs.MonoidLazyCall\nimport Proofs.CppScalarContents\nimport Proofs.CppScalarValuePrepare\n'+generated
                with tempfile.TemporaryDirectory(prefix='original-set-copy-') as tmp:
                    directory=Path(tmp)
                    scalar_checks.ScalarDelegationTests().kernel(directory,'OriginalSetCopyCheck',roots,generated+fixture+general+call)
                    main=directory/'native.cpp';main.write_text('int main(){using A='+family+'<long long>::RangeSet;'
                        'const long long values[]={LLONG_MIN,-7,22,LLONG_MAX};'
                        'for(auto x:values)for(auto y:values)for(bool f:{false,true})for(bool g:{false,true}){'
                        'A a(x),b(y);a.noop=f;b.noop=g;const A ca=a,cb=b;auto c=compose(ca,cb);auto same=compose(ca,ca);'
                        'if(c.v!=(f?y:x) || c.noop!=(f?g:f) || same.v!=x || same.noop!=f)return 1;'
                        'c.v=19;c.noop=false;if(a.v!=x || b.v!=y || a.noop!=f || b.noop!=g)return 2;}'
                        'auto id=A::id();return id.v==0 && id.noop?0:3;}\n')
                    exe=directory/'native'
                    subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                        '-I',str(INCLUDES[0]),'-include',str(source),str(main),'-o',str(exe)],check=True,timeout=60)
                    subprocess.run([str(exe)],check=True,timeout=10)
                for p,digest in before.items():self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),digest)

    def test_record_copy_return_keeps_unhandled_conditions_rejected(self):
        text='''#include <vector>
struct Choice {
 long long value;bool noop;
 Choice(long long v,bool n):value(v),noop(n){}
 friend Choice choose(Choice a,Choice b){return a.noop ? b : a;}
};
'''
        cases=[(text.replace('a.noop ? b : a','(++a.value>0) ? b : a'),
                    'record copy conditions require pure scalar booleans'),
               (text.replace('a.noop ? b : a','a.noop ? (b.noop ? a : b) : a'),
                    'record copy sources require direct parameter views or one conditional')]
        with tempfile.TemporaryDirectory(prefix='record-copy-condition-') as tmp:
            source=Path(tmp)/'choice.hpp'
            for candidate,error in cases:
                source.write_text(candidate)
                with self.subTest(error=error),self.assertRaisesRegex(ValueError,error):
                    layout.emit_class_layout(source,'Choice',member_exports=True,factory_exports=True,friend_exports=True)

    def test_direct_record_returns_copy_and_move_all_fields(self):
        text='''#include <vector>
struct Choice {
 long long value;bool noop;
 Choice(long long v,bool n):value(v),noop(n){}
 static Choice copy(const Choice &a){return a;}
 static Choice moved(Choice a){return a;}
};
'''
        with tempfile.TemporaryDirectory(prefix='direct-record-return-') as tmp:
            directory=Path(tmp);source=directory/'choice.hpp';source.write_text(text)
            generated=layout.emit_class_layout(source,'Choice','CopyChoiceObject',member_exports=True,
                factory_exports=True,friend_exports=True)
            fixture=(ROOT/'tests/lean/scalar_record_copy_returns.lean').read_text()
            roots=['RecordCopyReturnAudit.'+line.split()[1]
                for line in fixture.splitlines() if line.startswith('theorem ')]
            self.assertEqual(len(roots),4)
            scalar_checks.ScalarDelegationTests().kernel(directory,'RecordCopyReturnCheck',roots,generated+fixture)
            main=directory/'native.cpp';main.write_text('#include "choice.hpp"\nint main(){const Choice a(22,true);'
                'auto b=Choice::copy(a);auto c=Choice::moved(a);b.value=19;b.noop=false;'
                'return a.value==22 && a.noop && b.value==19 && !b.noop && c.value==22 && c.noop?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)

    def test_original_members_return_complete_copied_range_sum(self):
        self._check_sum_members(SOURCE)

    def test_candidate_members_return_complete_copied_range_sum(self):
        self._check_sum_members(CANDIDATE_SOURCE,'cp::','candidate')

    def _check_sum_members(self,source,family_prefix='',witness_prefix='original'):
        for family,owner,witness in [('RangeSetRangeSum','RangeSet',WITNESS),
                ('RangeAddRangeSum','RangeAdd',ROOT/'tests/imports/original_mixed_add_sum.cpp')]:
            family=family_prefix+family
            witness=ROOT/'tests/imports'/witness.name.replace('original_',witness_prefix+'_',1)
            with self.subTest(family=family):
                before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
                instance=TemplateInstance(('long long',),witness,nested_members=('RangeSum',))
                companion=TemplateInstance(('long long',),witness,nested_members=(owner,))
                plans=[];original=layout.lower_class_layout
                def capture(*args,**kwargs):
                    result=original(*args,**kwargs);plans.append(result);return result
                with mock.patch.object(layout,'lower_class_layout',side_effect=capture):
                    generated=layout.emit_class_layout(source,family,'OriginalMemberResult',INCLUDES,
                        member_exports=True,factory_exports=True,template_instance=instance,
                        companion_instances=((family,companion),),receiver_methods=((1,'apply'),))
                method=[f for f in plans[0]['functions'] if 'receiver' in f.get('class_factory',{})]
                self.assertEqual(len(method),1)
                self.assertEqual(method[0]['class_factory']['receiver']['qualified_class'],companion.target(family))
                self.assertEqual(method[0]['class_factory']['arguments'],[
                    dict(kind='record_reference',count=2 if owner=='RangeSet' else 1),dict(kind='record_value',count=2)])
                is_set=owner=='RangeSet'
                aliases=('namespace SelectedMember\nabbrev applyExport := '
                    'OriginalMemberResult.RangeSum_factory_receiver1_apply_exportObjectsFuel\n'
                    'def receiverSlots : List Nat := '+('[0,1]' if is_set else '[0]')+'\n'
                    'def isSet : Bool := '+str(is_set).lower()+'\n'
                    'def expected (v '+('f' if is_set else '_f')+' x n : Int) : Int := '+
                    ('if f=0 then v*n else x' if is_set else 'x+n*v')+'\nend SelectedMember\n')
                fixture=(ROOT/'tests/lean/original_member_record_return.lean').read_text()
                roots=['OriginalMemberReturnAudit.'+line.split()[1]
                    for line in fixture.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(roots),9)
                general=(ROOT/'tests/lean'/('original_set_member_general.lean' if is_set
                    else 'original_add_member_general.lean')).read_text()
                namespace='SetMemberGeneral' if is_set else 'AddMemberGeneral'
                general_roots=[namespace+'.'+line.split()[1]
                    for line in general.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(general_roots),4 if is_set else 3)
                roots+=general_roots;fixture+=general
                preparation=(ROOT/'tests/lean/original_member_prepare.lean').read_text()
                prepare_roots=['MemberPrepareGeneral.'+line.split()[1]
                    for line in preparation.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(prepare_roots),2)
                call=(ROOT/'tests/lean'/('original_set_member_call.lean' if is_set
                    else 'original_add_member_call.lean')).read_text()
                call_namespace='SetMemberCallGeneral' if is_set else 'AddMemberCallGeneral'
                call_roots=[call_namespace+'.'+line.split()[1]
                    for line in call.splitlines() if line.startswith('theorem ')]
                self.assertEqual(len(call_roots),11)
                roots+=prepare_roots+call_roots;fixture+=preparation+call
                generated='import Proofs.MonoidLazyCall\nimport Proofs.CppScalarValuePrepare\nimport Proofs.CppScalarContents\n'+generated
                with tempfile.TemporaryDirectory(prefix='original-member-result-') as tmp:
                    directory=Path(tmp)
                    scalar_checks.ScalarDelegationTests().kernel(directory,'OriginalMemberResultCheck',roots,generated+aliases+fixture)
                    main=directory/'native.cpp'
                    statement='a.noop=flag;' if is_set else ''
                    expected='flag?x:v*n' if is_set else 'x+v*n'
                    main.write_text('int main(int argc,char**){using R='+family+'<long long>;using A=R::'+owner+';using S=R::RangeSum;'
                        'if(argc>1){A bad(LLONG_MAX);auto result=bad.apply(S(7,2));return result.x==0;}'
                        'for(long long v:{-3LL,3LL})for(long long x:{-7LL,7LL})'
                        'for(int n:{INT_MIN,-4,0,4,INT_MAX})for(bool flag:{false,true}){A a(v);'+statement+
                        'const S input(x,n);auto output=a.apply(input);'
                        'if(output.x!=('+expected+') || output.size!=n || input.x!=x || input.size!=n || a.v!=v)return 1;}'
                        'A id=A::id();const S input(7,4);auto kept=id.apply(input);return kept.x==7 && kept.size==4?0:2;}\n')
                    exe=directory/'native'
                    subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                        '-I',str(INCLUDES[0]),'-include',str(source),str(main),'-o',str(exe)],check=True,timeout=60)
                    subprocess.run([str(exe)],check=True,timeout=10)
                    failed=subprocess.run([str(exe),'overflow'],capture_output=True,text=True,timeout=10)
                    self.assertNotEqual(failed.returncode,0)
                    self.assertIn('signed integer overflow',failed.stderr)
                for p,digest in before.items():self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),digest)

    def test_record_member_preserves_receiver_updates_and_value_snapshot(self):
        text='''#include <vector>
struct Box {
 long long value;int size;
 Box(long long v,int n):value(v),size(n){}
 Box apply(Box x){value=value+1;if(size){x.value=x.value+value*x.size;}return x;}
};
'''
        with tempfile.TemporaryDirectory(prefix='record-member-prefix-') as tmp:
            directory=Path(tmp);source=directory/'box.hpp';source.write_text(text)
            generated=layout.emit_class_layout(source,'Box','PrefixBoxResult',member_exports=True,
                factory_exports=True,receiver_methods=((0,'apply'),))
            fixture=(ROOT/'tests/lean/member_record_prefix_updates.lean').read_text()
            roots=['MemberPrefixUpdateAudit.'+line.split()[1]
                for line in fixture.splitlines() if line.startswith('theorem ')]
            self.assertEqual(len(roots),5)
            scalar_checks.ScalarDelegationTests().kernel(directory,'MemberPrefixUpdateCheck',roots,generated+fixture)
            main=directory/'native.cpp';main.write_text('#include "box.hpp"\n#include <limits>\nint main(int argc,char**){'
                'if(argc>1){Box bad(std::numeric_limits<long long>::max(),1);auto r=bad.apply(Box(7,4));return r.value==0;}'
                'Box a(3,1);const Box input(7,4);auto result=a.apply(input);Box b(3,1);auto alias=b.apply(b);'
                'return a.value==4 && input.value==7 && input.size==4 && result.value==23 && result.size==4 && '
                'b.value==4 && alias.value==7 && alias.size==1?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
            failed=subprocess.run([str(exe),'overflow'],capture_output=True,text=True,timeout=10)
            self.assertNotEqual(failed.returncode,0)
            self.assertIn('signed integer overflow',failed.stderr)
            source.write_text(text.replace('value=value+1;if(size){x.value=x.value+value*x.size;}return x;',
                'if(size)return x;x.value=9;return x;'))
            with self.assertRaisesRegex(ValueError,'exactly one returned construction'):
                layout.emit_class_layout(source,'Box',member_exports=True,factory_exports=True,receiver_methods=((0,'apply'),))

    def test_record_member_rejects_namesake_return_and_argument_records(self):
        text='''#include <vector>
template<class T> struct A {struct Data {T x;Data(T v):x(v){}};};
template<class T> struct B {
 struct Data {T x;Data(T v):x(v+100){}};
 struct Receiver {
  T v;Receiver(T a):v(a){}
  Data make(){return Data(7);}
  typename A<T>::Data take(Data x){return {x.x};}
 };
};
'''
        with tempfile.TemporaryDirectory(prefix='record-member-namesake-') as tmp:
            directory=Path(tmp);source=directory/'source.hpp';source.write_text(text)
            witness=directory/'witness.cpp'
            witness.write_text('int main(){A<long long>::Data a(1);B<long long>::Receiver f(3);'
                'B<long long>::Data b(7);return f.make().x==107 && f.take(b).x==107 && a.x==1?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                '-include',str(source),str(witness),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
            result=TemplateInstance(('long long',),witness,nested_members=('Data',))
            receiver=TemplateInstance(('long long',),witness,nested_members=('Receiver',))
            for method in ('make','take'):
                with self.subTest(method=method),self.assertRaisesRegex(ValueError,
                        'record member signature identity probe failed'):
                    layout.emit_class_layout(source,'A',member_exports=True,factory_exports=True,
                        template_instance=result,companion_instances=(('B',receiver),),
                        receiver_methods=((1,method),))

    def test_original_member_templates_return_complete_extrema_records(self):
        self._check_member_templates_return_complete_extrema_records(SOURCE)

    def test_original_api_candidate_returns_complete_extrema_records(self):
        self._check_member_templates_return_complete_extrema_records(
            ROOT/'experiments/verification/algebraic_structure/monoid_lazy.hpp','cp::','candidate')

    def _check_member_templates_return_complete_extrema_records(self, source, family_prefix='', witness_prefix='original'):
        for family,owner,witness in [('RangeAddRangeMaxMin','RangeAdd','original_mixed_add_extrema.cpp'),
                ('RangeSetRangeMaxMin','RangeSet','original_mixed_set_extrema.cpp')]:
            family=family_prefix+family
            witness=ROOT/'tests/imports'/witness.replace('original_',witness_prefix+'_',1)
            for result_name in ('RangeMax','RangeMin'):
                with self.subTest(family=family,result=result_name):
                    plans=[];original=layout.lower_class_layout
                    def capture(*args,**kwargs):
                        plan=original(*args,**kwargs);plans.append(plan);return plan
                    instance=TemplateInstance(('long long',),witness,nested_members=(result_name,))
                    receiver=TemplateInstance(('long long',),witness,nested_members=(owner,))
                    before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,witness)}
                    with mock.patch.object(layout,'lower_class_layout',side_effect=capture):
                        generated=layout.emit_class_layout(source,family,'TemplateMemberResult',INCLUDES,
                            member_exports=True,factory_exports=True,template_instance=instance,
                            companion_instances=((family,receiver),),receiver_methods=((1,'apply',(RecordArgument(0),)),))
                    members=[f for f in plans[0]['functions'] if 'receiver' in f.get('class_factory',{})]
                    self.assertEqual(len(members),1);member=members[0]
                    self.assertEqual(member['class_factory']['receiver']['template_instance']['type_arguments'],[instance.target(family)])
                    self.assertEqual(plans[0]['receiver_methods'],[
                        dict(record_index=1,method='apply',type_arguments=[instance.target(family)])])
                    is_set=owner=='RangeSet'
                    aliases=('namespace SelectedTemplateMember\nabbrev applyExport := TemplateMemberResult.'+
                        member['name']+'_exportObjectsFuel\ndef receiverSlots : List Nat := '+('[0,1]' if is_set else '[0]')+
                        '\ndef isSet : Bool := '+str(is_set).lower()+'\ndef expected (v '+('f' if is_set else '_f')+
                        ' x : Int) : Int := '+('if f=0 then v else x' if is_set else 'x+v')+'\nend SelectedTemplateMember\n')
                    fixture=(ROOT/'tests/lean/original_template_member_result.lean').read_text()
                    roots=['TemplateMemberResultAudit.'+line.split()[1]
                        for line in fixture.splitlines() if line.startswith('theorem ')]
                    self.assertEqual(len(roots),8)
                    kind = 'set' if is_set else 'add'
                    namespace = 'ExtremaSetMember' if is_set else 'ExtremaAddMember'
                    aliases+=('namespace SelectedExtrema\nabbrev applyProgram := TemplateMemberResult.'+member['name']+
                        '\nabbrev applyFields := TemplateMemberResult.Stages.'+member['name']+'.scalarFields'+
                        '\nabbrev scalarPermissions := TemplateMemberResult.scalarPermissions'+
                        '\nabbrev applyView := TemplateMemberResult.'+member['name']+'_exportViewFuel'+
                        '\nabbrev applyObjects := TemplateMemberResult.'+member['name']+'_exportObjectsFuel'+
                        '\nend SelectedExtrema\n')
                    general=(ROOT/f'tests/lean/original_extrema_{kind}_member_general.lean').read_text()
                    preparation=(ROOT/'tests/lean/original_extrema_member_prepare.lean').read_text()
                    call=(ROOT/f'tests/lean/original_extrema_{kind}_member_call.lean').read_text()
                    general_roots=[namespace+'General.'+line.split()[1]
                        for line in general.splitlines() if line.startswith('theorem ')]
                    prepare_roots=['ExtremaPrepareGeneral.'+line.split()[1]
                        for line in preparation.splitlines() if line.startswith('theorem ')]
                    call_roots=[namespace+'CallGeneral.'+line.split()[1]
                        for line in call.splitlines() if line.startswith('theorem ')]
                    self.assertEqual(len(general_roots),4 if is_set else 2)
                    self.assertEqual(len(prepare_roots),2)
                    self.assertEqual(len(call_roots),11)
                    roots+=general_roots+prepare_roots+call_roots
                    fixture+=general+preparation+call
                    generated='import Proofs.MonoidLazyCall\nimport Proofs.CppScalarValuePrepare\nimport Proofs.CppScalarContents\n'+generated
                    with tempfile.TemporaryDirectory(prefix='original-member-template-') as tmp:
                        directory=Path(tmp)
                        scalar_checks.ScalarDelegationTests().kernel(directory,'TemplateMemberResultCheck',roots,generated+aliases+fixture)
                        main=directory/'native.cpp'
                        main.write_text('int main(int argc,char**){using R='+family+'<long long>;using A=R::'+owner+
                            ';using M=R::'+result_name+';if(argc>1){A a(LLONG_MAX);auto r=a.apply(M(1));return r.x==0;}'
                            'for(long long v:{-3LL,0LL,3LL})for(long long x:{-7LL,0LL,7LL})for(bool flag:{false,true}){'
                            'A a(v);'+('a.noop=flag;' if is_set else '')+'const M input(x);auto r=a.apply(input);'
                            'if(r.x!=('+('flag?x:v' if is_set else 'x+v')+') || input.x!=x || a.v!=v)return 1;}'
                            'A id=A::id();const M input(7);return id.apply(input).x==7?0:2;}\n')
                        exe=directory/'native'
                        subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                            '-I',str(INCLUDES[0]),'-include',str(source),str(main),'-o',str(exe)],check=True,timeout=60)
                        subprocess.run([str(exe)],check=True,timeout=10)
                        overflow=subprocess.run([str(exe),'overflow'],capture_output=True,text=True,timeout=10)
                        if is_set:self.assertEqual(overflow.returncode,0)
                        else:
                            self.assertNotEqual(overflow.returncode,0);self.assertIn('signed integer overflow',overflow.stderr)
                    for p,digest in before.items():self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),digest)

    def test_member_choice_copies_or_constructs_every_field_in_selected_branch(self):
        text='''#include <vector>
template<class T> struct Family {
 struct Data {T x;int size;Data(T v,int n):x(v+100),size(n+1){}};
 struct Action {T v;bool noop;Action(T a):v(a),noop(false){}
  template<class M> M apply(M x){return noop?x:M(v,4);}
 };
};
'''
        with tempfile.TemporaryDirectory(prefix='member-constructor-choice-') as tmp:
            directory=Path(tmp);source=directory/'source.hpp';source.write_text(text)
            witness=directory/'witness.cpp';witness.write_text('int main(){Family<long long>::Action a(3);'
                'Family<long long>::Data input(7,4);auto r=a.apply(input);return r.x==103 && r.size==5?0:1;}\n')
            result=TemplateInstance(('long long',),witness,nested_members=('Data',))
            receiver=TemplateInstance(('long long',),witness,nested_members=('Action',))
            options=dict(member_exports=True,factory_exports=True,template_instance=result,
                companion_instances=(('Family',receiver),),receiver_methods=((1,'apply',(RecordArgument(0),)),))
            plans=[];original=layout.lower_class_layout
            def capture(*args,**kwargs):
                plan=original(*args,**kwargs);plans.append(plan);return plan
            with mock.patch.object(layout,'lower_class_layout',side_effect=capture):
                generated=layout.emit_class_layout(source,'Family','ChoiceMemberResult',**options)
            member=next(f for f in plans[0]['functions'] if 'receiver' in f.get('class_factory',{}))
            aliases='namespace SelectedConstructorChoice\nabbrev applyExport := ChoiceMemberResult.'+member['name']+'_exportObjectsFuel\nend SelectedConstructorChoice\n'
            fixture=(ROOT/'tests/lean/member_constructor_choice.lean').read_text()
            roots=['MemberConstructorChoiceAudit.'+line.split()[1]
                for line in fixture.splitlines() if line.startswith('theorem ')]
            self.assertEqual(len(roots),5)
            scalar_checks.ScalarDelegationTests().kernel(directory,'MemberConstructorChoiceCheck',roots,generated+aliases+fixture)
            main=directory/'native.cpp';main.write_text('#include "source.hpp"\n#include <limits>\nint main(int argc,char**){'
                'using R=Family<long long>;const R::Data input(7,4);R::Action a(3);auto active=a.apply(input);'
                'R::Action b(std::numeric_limits<long long>::max());b.noop=argc==1;auto chosen=b.apply(input);'
                'return input.x==107 && input.size==5 && active.x==103 && active.size==5 && chosen.x==107 && chosen.size==5?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
            failed=subprocess.run([str(exe),'overflow'],capture_output=True,text=True,timeout=10)
            self.assertNotEqual(failed.returncode,0);self.assertIn('signed integer overflow',failed.stderr)
            for bad in ((RecordArgument(1),),('int',)):
                with self.subTest(bad=bad),self.assertRaisesRegex(ValueError,'requested member specialization is not instantiated'):
                    layout.emit_class_layout(source,'Family',**dict(options,receiver_methods=((1,'apply',bad),)))
            source.write_text(text.replace('return noop?','return (noop=!noop)?'))
            with self.assertRaisesRegex(ValueError,'record member choices require one pure boolean'):
                layout.emit_class_layout(source,'Family',**options)

    def test_record_member_request_validation_precedes_compilation(self):
        cases=[dict(receiver_methods=[(0,'apply')]),dict(receiver_methods=((False,'apply'),)),
               dict(receiver_methods=((1,'apply'),)),dict(receiver_methods=((0,'apply'),(0,'apply'))),
               dict(receiver_methods=((0,'apply'),),factory_exports=False),
               dict(receiver_methods=((0,'apply',()),)),dict(receiver_methods=((0,'apply',['int']),)),
               dict(receiver_methods=((0,'apply',(RecordArgument(1),)),)),
               dict(receiver_methods=((0,'apply',('unselected_record',)),))]
        for request in cases:
            options=dict(member_exports=True,factory_exports=True);options.update(request)
            with self.subTest(request=request),mock.patch.object(layout,'translation_unit') as compiler:
                with self.assertRaises(ValueError):layout.emit_class_layout(SOURCE,'Box',**options)
                compiler.assert_not_called()

    def test_const_record_member_retains_const_and_noexcept_receiver(self):
        text='''#include <vector>
struct Box {
 long long value;int size;
 Box(long long v,int n):value(v),size(n){}
 Box apply(Box x)const noexcept{if(size){x.value=value*x.size;}return x;}
};
'''
        with tempfile.TemporaryDirectory(prefix='const-record-member-') as tmp:
            directory=Path(tmp);source=directory/'box.hpp';source.write_text(text)
            plan=layout.lower_class_layout(source,'Box',multiple_vectors=True,factory_exports=True,receiver_methods=((0,'apply'),))
            stage=[f for f in plan['functions'] if 'receiver' in f.get('class_factory',{})][0]
            self.assertTrue(stage['class_factory']['receiver']['constant'])
            self.assertTrue(stage['class_factory']['receiver']['method_type'].endswith(' const noexcept'))
            self.assertEqual([p['writable'] for p in stage['parameters'][:2]],[False,False])
            generated=layout.emit_class_layout(source,'Box','ConstBoxResult',member_exports=True,
                factory_exports=True,receiver_methods=((0,'apply'),))
            fixture=(ROOT/'tests/lean/const_record_member.lean').read_text()
            roots=['ConstRecordMemberAudit.'+line.split()[1]
                for line in fixture.splitlines() if line.startswith('theorem ')]
            self.assertEqual(len(roots),3)
            scalar_checks.ScalarDelegationTests().kernel(directory,'ConstRecordMemberCheck',roots,generated+fixture)
            main=directory/'native.cpp';main.write_text('#include "box.hpp"\nint main(){const Box receiver(3,1),arg(7,4);'
                'auto result=receiver.apply(arg);return receiver.value==3 && arg.value==7 && result.value==12 && result.size==4?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)

    def test_factory_constructor_methods_use_the_materialized_receiver(self):
        text='''#include <vector>
struct Pair {
 long long first;int second;
 Pair(long long a,int b):first(a),second(b){touch(1);first=first+sum();quotient();}
 Pair():Pair(make()){first=first+100;second=second+1000;}
 Pair(bool):Pair(bad()){}
 static Pair make(){return {3,4};}
 static Pair bad(){return {3,-2};}
 void touch(long long delta){first=first+delta;touch2();}
 void touch2(){second=second+2;}
 long long sum()const{return first+second;}
 long long quotient()const{return 7/second;}
};
'''
        with tempfile.TemporaryDirectory(prefix='delegating-method-receiver-') as tmp:
            directory=Path(tmp);source=directory/'pair.hpp';source.write_text(text)
            generated=layout.emit_class_layout(source,'Pair','ReceiverPairObject',member_exports=True)
            fixture=(ROOT/'tests/lean/scalar_delegation_receiver.lean').read_text()
            roots=['DelegationReceiverAudit.'+line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
            self.assertEqual(len(roots),8)
            scalar_checks.ScalarDelegationTests().kernel(directory,'DelegationReceiverCheck',roots,generated+fixture)
            main=directory/'native.cpp';main.write_text('#include "pair.hpp"\nint main(int argc,char**){'
                'if(argc>1){Pair bad(true);return bad.first==0;}Pair a(3,4);const Pair b;Pair c=b;'
                'c.first=99;c.second=-4;return a.first==14 && a.second==6 && b.first==114 && b.second==1006 '
                '&& c.first==99 && c.second==-4?0:1;}\n')
            exe=directory/'native'
            subprocess.run(['g++','-std=c++17','-O0','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
            failed=subprocess.run([str(exe),'invalid'],capture_output=True,text=True,timeout=10)
            self.assertNotEqual(failed.returncode,0)
            self.assertIn('division by zero',failed.stderr)

    def test_nontrivial_members_effectful_factories_and_early_returns_stay_rejected(self):
        base='''#include <vector>
struct Pair {
 long long first;int second;
 Pair(long long a,int b):first(a),second(b){}
 Pair():Pair(make()){}
 static Pair make(){return {3,4};}
 EXTRA
};
'''
        cases=[(base.replace('EXTRA','Pair(const Pair &p):first(p.first),second(p.second){}'),'trivial copy/move/destruction'),
            (base.replace('EXTRA','Pair(Pair &&p):first(p.first),second(p.second){}'),'trivial copy/move/destruction'),
            (base.replace('EXTRA','~Pair(){}'),'trivial copy/move/destruction'),
            (base.replace('EXTRA','').replace('return {3,4};','static int v=0;++v;return {v,4};'),'exactly one returned construction'),
            (base.replace('EXTRA','').replace('first(a),second(b){}','first(a),second(b){if(a<0)return;}'),
                'early returns in delegated constructor bodies'),
            (base.replace('EXTRA','long long &borrow(){return first;}').replace('first(a),second(b){}','first(a),second(b){borrow();}'),
                'temporary receiver methods require scalar or void results'),
            (base.replace('EXTRA','long long *address(){return &first;}').replace('first(a),second(b){}','first(a),second(b){address();}'),
                'temporary receiver methods require scalar or void results'),
            (base.replace('EXTRA','void recurse(){recurse();}').replace('first(a),second(b){}','first(a),second(b){recurse();}'),
                'recursive calls cannot be inlined'),
            (base.replace('EXTRA','long long get(){return second;}').replace('first(a),second(b){}','first(get()),second(b){}'),
                'temporary receiver calls require all fields to be initialized'),
            (base.replace('EXTRA','').replace('long long a,int b','const long long &a,int b'),
                'scalar value parameters and pure scalar arguments')]
        with tempfile.TemporaryDirectory(prefix='delegation-boundaries-') as tmp:
            source=Path(tmp)/'pair.hpp'
            for text,error in cases:
                source.write_text(text)
                records=[n for n in source_ast(source,'Pair') if n.get('kind')=='CXXRecordDecl' and
                    n.get('name')=='Pair' and n.get('completeDefinition')]
                self.assertEqual(len(records),1)
                with self.subTest(error=error),self.assertRaisesRegex(ValueError,error):
                    class_construction_stages(records[0],source)

    def test_witness_changed_after_ast_collection_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix='template-layout-witness-') as tmp:
            witness=Path(tmp)/'witness.cpp';witness.write_bytes(WITNESS.read_bytes())
            instance=TemplateInstance(('long long',),witness,nested_members=('RangeSet',))
            original=layout._field_layout
            def changed(*args,**kwargs):
                result=original(*args,**kwargs)
                witness.write_text(witness.read_text()+'\n')
                return result
            with mock.patch.object(layout,'_field_layout',side_effect=changed),self.assertRaisesRegex(
                    ValueError,'template witness changed during layout generation'):
                layout.lower_class_layout(SOURCE,'RangeSetRangeSum',INCLUDES,
                    multiple_vectors=True,template_instance=instance)

if __name__=='__main__':
    disable_network()
    unittest.main()
