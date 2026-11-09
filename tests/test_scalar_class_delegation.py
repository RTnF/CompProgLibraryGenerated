"""Scalar delegation, compile-time witnesses and original Group compatibility."""
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'),str(ROOT/'tools'),str(ROOT/'tests')]
from nested_ir import lower_source, emit_lean
from check_proof_security import BUILTINS
from proof_security import audit_source
from offline import disable_network
from test_scalar_ir import lean_environment

SINGLE_BASE = '#pragma once\n#include <vector>\nnamespace cp {\nclass ScalarIdentity {\n long long value;\npublic:\n ScalarIdentity(long long x):value(x){}\n ScalarIdentity():ScalarIdentity(e()){}\n static ScalarIdentity e(){return 7;}\n long long get()const{return value;}\n};\n}\n'

SINGLE_CASES=[('factory',SINGLE_BASE,None),
 ('direct',SINGLE_BASE.replace('ScalarIdentity(e())','ScalarIdentity(7)'),None),
 ('body',SINGLE_BASE.replace('ScalarIdentity(e()){}','ScalarIdentity(e()){++value;}'),'delegating constructor body must be empty'),
 ('destructor',SINGLE_BASE.replace(' static ScalarIdentity e()', ' ~ScalarIdentity(){}\n static ScalarIdentity e()'),'scalar value erasure requires trivial destruction'),
 ('copy',SINGLE_BASE.replace(' static ScalarIdentity e()', ' ScalarIdentity(const ScalarIdentity &other):value(other.value+1){}\n static ScalarIdentity e()'),'scalar value erasure requires trivial copy and move construction'),
 ('cleanup',SINGLE_BASE.replace('namespace cp {','struct Cleanup {~Cleanup(){} operator long long()const{return 7;}};\nnamespace cp {').replace('ScalarIdentity(e())','ScalarIdentity(Cleanup{})'),'delegated temporary has unsupported cleanup effects')]

SPLIT_BASE='''#include <vector>
namespace cp {
class Parcel {
 long long left,right;
public:
 Parcel(long long x,long long y):left(x),right(y){}
 Parcel():Parcel(e()){}
 static Parcel e(){return {11,17};}
 long long sum()const{return left+right;}
};
}
'''
triple=SPLIT_BASE.replace('left,right;','left,right,tail;').replace('long long x,long long y','long long x,long long y,long long z').replace('left(x),right(y)','left(x),right(y),tail(z)').replace('{11,17}','{11,17,23}')
SPLIT_CASES=[('literal',SPLIT_BASE,None),
 ('triple',triple,None),
 ('mixed',SPLIT_BASE.replace('long long left,right;','long long left;int right;').replace('long long x,long long y','long long x,int y'),None),
 ('hidden_division',triple.replace('tail(z)','tail(z/0)'),'split delegation currently requires literal-only field initializers'),
 ('changed',SPLIT_BASE.replace('{11,17}','{13,19}'),None),
 ('renamed',SPLIT_BASE.replace('Parcel','Bundle').replace('left','first').replace('right','second'),None),
 ('namespace',SPLIT_BASE.replace('namespace cp','namespace other'),None),
 ('delegated_body',SPLIT_BASE.replace('Parcel(e()){}','Parcel(e()){++left;}'),'split delegating constructor body must be empty'),
 ('factory_body',SPLIT_BASE.replace('namespace cp {','long long counter=0;\nnamespace cp {').replace('return {11,17};','++counter;return {11,17};'),'split delegation factory needs one return and no side effects'),
 ('division',SPLIT_BASE.replace('{11,17}','{11/0,17}'),'split delegation requires literal-only constructor arguments, including unused arguments'),
 ('field_division',SPLIT_BASE.replace('left(x)','left(x/0)'),'split delegation currently requires literal-only field initializers'),
 ('target_body',SPLIT_BASE.replace('left(x),right(y){}','left(x),right(y){++left;}'),'split delegation target needs an empty body and explicit arguments'),
 ('factory_argument',SPLIT_BASE.replace('Parcel e()','Parcel e(int n=0)'),'split delegation factory must have no arguments'),
 ('factory_attribute',SPLIT_BASE.replace('static Parcel e()','__attribute__((noinline)) static Parcel e()'),'split delegation factory parameters and attributes are unsupported'),
 ('destructor',SPLIT_BASE.replace(' static Parcel e()', ' ~Parcel(){}\n static Parcel e()'),'scalar value erasure requires trivial destruction'),
 ('custom_copy',SPLIT_BASE.replace(' static Parcel e()', ' Parcel(const Parcel &p):left(p.left+1),right(p.right){}\n static Parcel e()'),'scalar value erasure requires trivial copy and move construction')]

COMPILE_CASES=[
 ('baseline','long long f(long long n){return n+1;}',True),
 ('compile_only','long long f(long long n){using A=long long;typedef long long B;void unused(A);static_assert(sizeof(A)==8);if constexpr(true){using Z=int;static_assert(sizeof(Z)==4);}return n+1;}',True),
 ('ordinary_baseline','long long f(long long &n){if(false){}return n;}',True),
 ('ordinary_if','long long f(long long &n){if(false){using A=int;static_assert(sizeof(A)==4);}return n;}',True),
 ('vla_typedef','long long f(long long &n){typedef int A[++n];return n;}',False),
 ('vla_using','long long f(long long &n){using A=int[++n];return n;}',False),
 ('if_init','long long f(long long &n){if constexpr(int marker=(n=7);true){using A=int;}return n;}',False),
 ('if_body','long long f(long long &n){if constexpr(true){++n;}return n;}',False),
 ('false_assert','long long f(long long n){static_assert(false);return n;}',False),
 ('attributed_function','long long f(long long n){__attribute__((constructor)) void initializer();return n;}',False),
]


class ScalarDelegationTests(unittest.TestCase):
    def lower(self, source, directory, name):
        path = directory/(name+'.hpp')
        path.write_text(source)
        return lower_source(path)

    def kernel(self, directory, module, roots, source=None):
        lake, env = lean_environment()
        env = dict(env,LEAN_NUM_THREADS='1')
        env.pop('LEAN_PATH',None)
        if source is not None:
            proof = directory/(module+'.lean')
            proof.write_text(source)
            audit_source(proof)
            env['LEAN_PATH'] = str(directory)
            result = subprocess.run([lake,'env','lean','--root='+str(directory),'-o',
                str(proof.with_suffix('.olean')),str(proof)],cwd=ROOT,env=env,
                capture_output=True,text=True,timeout=120)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)
        permitted = ['propext','Classical.choice','Quot.sound']
        export = directory/'export.ndjson'
        with export.open('w') as output:
            result = subprocess.run([lake,'env',str(ROOT/'.tools/lean4export/.lake/build/bin/lean4export'),
                module,'--',*BUILTINS,*permitted,*roots],cwd=ROOT,env=env,
                stdout=output,stderr=subprocess.PIPE,text=True,timeout=120)
        self.assertEqual(result.returncode,0,result.stderr)
        config = directory/'nanoda.json'
        config.write_text(json.dumps(dict(export_file_path=str(export),permitted_axioms=permitted,
            unpermitted_axiom_hard_error=True,unsafe_permit_all_axioms=False,nat_extension=True,
            string_extension=True,num_threads=2,print_success_message=True,print_axioms=False)))
        result = subprocess.run([str(ROOT/'.tools/nanoda_lib/target/release/nanoda_bin'),str(config)],
            cwd=directory,env=env,capture_output=True,text=True,timeout=120)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertRegex(result.stdout,r'\AChecked [1-9][0-9]* declarations with no errors\s*\Z')
        print(result.stdout.strip(),flush=True)

    def test_single_field_delegation_and_cleanup_rejection(self):
        with tempfile.TemporaryDirectory(prefix='scalar-single-delegation-') as directory:
            scratch = Path(directory)
            for name,source,error in SINGLE_CASES:
                with self.subTest(name=name):
                    if error is None:
                        ir = self.lower(source,scratch,name)
                        if name == 'factory': model = emit_lean(ir,'DelegationCandidate')
                    else:
                        with self.assertRaisesRegex(ValueError,'^'+error+'$'):
                            self.lower(source,scratch,name)
            self.kernel(scratch,'SingleDelegationCheck',
                ['DelegationAudit.factory','DelegationAudit.delegated'],
                model+(ROOT/'tests/lean/scalar_single_delegation.lean').read_text())

    def test_split_factories_and_field_failure_rejection(self):
        with tempfile.TemporaryDirectory(prefix='scalar-split-delegation-') as directory:
            scratch = Path(directory)
            models = {}
            for name,source,error in SPLIT_CASES:
                with self.subTest(name=name):
                    if error is None:
                        models[name] = self.lower(source,scratch,name)
                    else:
                        with self.assertRaisesRegex(ValueError,'^'+error+'$'):
                            self.lower(source,scratch,name)
            self.assertNotEqual(models['literal'],models['changed'])
            recursive = SPLIT_BASE.replace('return {11,17};','return e();')
            with self.assertRaisesRegex(ValueError,'defined nonrecursive static member'):
                self.lower(recursive,scratch,'recursive')
            source = 'import Proofs.CppNestedCall\n'
            for name,ir in models.items():
                emitted = emit_lean(ir,'Case_'+name)
                source += '\n'+'\n'.join(s for s in emitted.splitlines() if not s.startswith('import '))+'\n'
            source += (ROOT/'tests/lean/scalar_split_delegation.lean').read_text()
            self.kernel(scratch,'SplitDelegationCheck',['CaseChecks.check_'+str(i) for i in range(15)],source)

    def test_compile_time_declarations_preserve_runtime_statements(self):
        with tempfile.TemporaryDirectory(prefix='scalar-compile-time-') as directory:
            scratch = Path(directory)
            models = {}
            for name,body,accept in COMPILE_CASES:
                source = '#include <vector>\nnamespace cp {\n'+body+'\n}\n'
                with self.subTest(name=name):
                    if accept:
                        models[name] = self.lower(source,scratch,name)
                    else:
                        exception = subprocess.CalledProcessError if name == 'false_assert' else ValueError
                        with self.assertRaises(exception): self.lower(source,scratch,name)
            self.assertEqual(models['baseline']['functions'],models['compile_only']['functions'])
            self.assertEqual(models['ordinary_baseline']['functions'],models['ordinary_if']['functions'])

    def test_helper_lifetime_bitfields_and_unused_arguments(self):
        helper = """#include <vector>
namespace cp {
class Item {long long value;public:Item(long long x):value(x){}
 long long get()const{return value;}};
class Holder {long long value;public:Holder(long long x):value(x){}
 Holder():Holder(e()){}
 static Holder e(){Item first(1);Item second(first);return second.get();}
 long long get()const{return value;}};
}
"""
        cases = [
            ('helper_copy', helper.replace('long long get()const{return value;}};',
                'Item(const Item &p):value(p.value+1){} long long get()const{return value;}};',1),
                'scalar value erasure requires trivial copy and move construction'),
            ('helper_destructor', helper.replace('namespace cp {','namespace cp { long long changes=0;').replace(
                'long long get()const{return value;}};',
                '~Item(){++changes;} long long get()const{return value;}};',1),
                'scalar value erasure requires trivial destruction'),
            ('bitfield',SINGLE_BASE.replace('long long value;','long long value:1;'),
                'scalar value erasure does not support bitfields'),
            ('base',SINGLE_BASE.replace('class ScalarIdentity {','struct Base {int hidden;};class ScalarIdentity:public Base {'),
                'scalar value erasure does not support base classes'),
            ('split_bitfield',SPLIT_BASE.replace('long long left,right;','long long left:1;long long right;'),
                'scalar value erasure does not support bitfields'),
            ('unused_argument',SPLIT_BASE.replace('#include <vector>','#include <vector>\n#include <cstdlib>').replace(
                'left(x),right(y)','left(11),right(17)').replace('{11,17}','{std::rand(),17}'),
                'split delegation requires literal-only constructor arguments, including unused arguments'),
        ]
        plain = SPLIT_BASE.replace(' Parcel():Parcel(e()){}\n','')
        cases += [
            ('unused_argument_without_delegation',plain.replace('#include <vector>',
                '#include <vector>\n#include <cstdlib>').replace('left(x),right(y)',
                'left(11),right(17)').replace('{11,17}','{std::rand(),17}'),
                'split constructor arguments must be free of runtime effects'),
            ('split_constructor_parameter_write',plain.replace('left(x),right(y){}',
                'left(x),right(y){x=x+1;}'),
                'split constructor body needs object-state sequencing'),
        ]
        with tempfile.TemporaryDirectory(prefix='scalar-erasure-effects-') as directory:
            scratch=Path(directory)
            for name,source,error in cases:
                with self.subTest(name=name):
                    with self.assertRaisesRegex(ValueError,'^'+error+'$'):
                        self.lower(source,scratch,name)

    def test_unused_split_argument_is_evaluated(self):
        source = SPLIT_BASE.replace(' Parcel():Parcel(e()){}\n','').replace(
            'left(x),right(y)','left(11),right(17)').replace('Parcel e()',
            'Parcel e(long long n)').replace('{11,17}','{7/n,17}')
        with tempfile.TemporaryDirectory(prefix='scalar-split-unused-') as directory:
            scratch=Path(directory)
            ir=self.lower(source,scratch,'unused')
            model=emit_lean(ir,'UnusedSplitArgument')
            driver=scratch/'native.cpp';binary=scratch/'native'
            driver.write_text('#include "'+str(scratch/'unused.hpp')+'"\nint main(){return cp::Parcel::e(1).sum()==28 ? 0 : 1;}\n')
            subprocess.run(['g++','-std=c++17','-O2','-fsanitize=undefined','-fno-sanitize-recover=all',
                            str(driver),'-o',str(binary)],check=True,capture_output=True,text=True,timeout=30)
            subprocess.run([str(binary)],check=True,capture_output=True,text=True,timeout=5)
            proof=model+(ROOT/'tests/lean/scalar_split_arguments.lean').read_text()
            self.kernel(scratch,'UnusedSplitArgumentCheck',['SplitArgumentAudit.'+name for name in
                ['left_ok','right_ok','left_zero_division','right_zero_division']],proof)

    def test_constructor_initialization_precedes_body(self):
        original = """#include <vector>
namespace cp {
class Holder {long long value;public:
 Holder(long long x):value(x){x=x+1;}
 Holder():Holder(1){}
 long long get()const{return value;}};
}
"""
        variants=[('parameter_write',original,1),
                  ('field_write',original.replace('x=x+1;','value=value+1;'),2),
                  ('both_writes',original.replace('x=x+1;','x=x+1;value=value+x;'),3),
                  ('body_constructor',original.replace('namespace cp {','namespace cp {\nclass Item {long long value;public:Item(long long &x):value(0){++x;}};').replace('x=x+1;','Item temporary(x);'),1),
                  ('initializer_call',original.replace('#include <vector>','#include <vector>\n#include <cassert>').replace(
                      'namespace cp {','namespace cp {\n[[gnu::always_inline]] long long bump(long long &x){++x;return x;}').replace(
                      'value(x){x=x+1;}','value(bump(x)){assert(x==2);}'),2)]
        with tempfile.TemporaryDirectory(prefix='scalar-constructor-order-') as directory:
            scratch=Path(directory)
            proof='import Proofs.CppNestedCall\n'
            for name,source,expected in variants:
                with self.subTest(name=name):
                    ir=self.lower(source,scratch,name)
                    emitted=emit_lean(ir,'Order_'+name)
                    proof+='\n'.join(line for line in emitted.splitlines() if not line.startswith('import '))+'\n'
                    header=scratch/(name+'.hpp')
                    driver=scratch/(name+'.cpp');binary=scratch/name
                    driver.write_text('#include "'+str(header)+'"\nint main(){cp::Holder value;return value.get() == '+str(expected)+' ? 0 : 1;}\n')
                    subprocess.run(['g++','-std=c++17','-O2','-fsanitize=undefined','-fno-sanitize-recover=all',
                                    str(driver),'-o',str(binary)],check=True,capture_output=True,text=True,timeout=30)
                    subprocess.run([str(binary)],check=True,capture_output=True,text=True,timeout=5)
            proof+=(ROOT/'tests/lean/scalar_constructor_order.lean').read_text()
            self.kernel(scratch,'ConstructorOrderCheck',['ConstructorOrderAudit.'+name for name,_,_ in variants],proof)

    def test_general_group_constructor_contracts(self):
        names = ['groupsum_default_correct','groupmul_default_correct','affine_new_a_correct',
                 'affine_new_b_correct','affine_default_a_correct','affine_default_b_correct',
                 'groupsum_friend_program','groupmul_friend_program','affine_friend_a_program','affine_friend_b_program']
        with tempfile.TemporaryDirectory(prefix='group-constructor-kernel-') as directory:
            self.kernel(Path(directory),'Proofs.GroupCall',['Proofs.GroupCall.'+name for name in names])

    def test_original_constructor_event_sequences(self):
        common = '''#include <vector>
#include <iostream>
struct Traced {
 int value;static std::vector<int> events;
 Traced(int x):value(x){events.push_back(x);}
 Traced(const Traced &x):value(x.value){events.push_back(100+value);}
};
std::vector<int> Traced::events;
'''
        driver = '''void emit(const std::vector<int> &events){for(int x:events)std::cout<<x<<" ";std::cout<<"\\n";}
int main(){Traced::events.clear();Group a;auto defaults=Traced::events;
 if(a.a().value!=1||a.b().value!=0)return 1;
 Traced::events.clear();auto e=Group::e();auto identities=Traced::events;
 if(e.a().value!=1||e.b().value!=0)return 2;
 emit(defaults);emit(identities);}
'''
        outputs = []
        with tempfile.TemporaryDirectory(prefix='group-original-events-') as directory:
            scratch = Path(directory)
            variants = [('original',ROOT/'experiments/library/cpp/algebraic_structure/group.hpp',''),
                        ('public',ROOT/'library/algebraic_structure/group.hpp','cp::')]
            for name,header,prefix in variants:
                source = scratch/(name+'.cpp')
                source.write_text(common+'#include "'+str(header)+'"\nusing Group = '+prefix+'GroupAffine<Traced>;\n'+driver)
                binary = scratch/name
                result = subprocess.run(['g++','-std=c++17','-O2','-fsanitize=undefined',
                    '-fno-sanitize-recover=all','-I',str(ROOT/'experiments/library/cpp'),str(source),'-o',str(binary)],
                    capture_output=True,text=True,timeout=60)
                self.assertEqual(result.returncode,0,result.stdout+result.stderr)
                result = subprocess.run([str(binary)],capture_output=True,text=True,timeout=10)
                self.assertEqual(result.returncode,0,result.stdout+result.stderr)
                outputs.append(result.stdout)
        self.assertEqual(outputs[0],outputs[1])


if __name__ == '__main__':
    disable_network()
    unittest.main()
