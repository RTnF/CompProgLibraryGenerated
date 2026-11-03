"""Lazy vector conditions and audited assertions retain actual failure paths."""
import itertools
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'));sys.path.insert(0,str(ROOT/'tools'))
from vector_ir import lower_source,emit_lean
from test_scalar_ir import lean_environment
from check_public import FLAGS,check_compiler
from offline import disable_network

SOURCE='''#include <vector>
#include <cassert>
bool either(const std::vector<int>& v){return v.size()==0 || v[0]==7;}
bool both(const std::vector<int>& v){return v.size()!=0 && v[0]==7;}
unsigned long prefix(const std::vector<int>& v){
 unsigned long i=0;while(i<v.size() && v[i]>0){++i;}return i;
}
int checked(const std::vector<int>& v){
 assert(v.size()>0 && (v[0]!=0 && 10/v[0]>0));return v[0];
}
unsigned long checked_or(const std::vector<int>& v){
 assert(v.size()==0 || (v[0]!=0 && 10/v[0]>0));return v.size();
}
'''
HEADER='''
open Proofs.CppScalar Proofs.CppMixedInvoke
 def i32 : Ty := ⟨32,true,false⟩
 def caller (values : List Int) : State := ⟨⟨[],[],0,0,0⟩,
  ⟨⟨[some ⟨0,values,values.length,100,0⟩],0,0,values.length+1⟩,[⟨i32,true⟩],[⟨0,i32,true⟩],0⟩,[.vector 0],0⟩
 def result (outcome : Proofs.CppLoop.Outcome State) : Option State := match outcome with
  | .finished s => some s
  | _ => none
'''

class VectorAssertTests(unittest.TestCase):
    def lean(self,scratch,text,succeeds=True):
        path=scratch/'checks.lean';path.write_text(text);lake,env=lean_environment()
        run=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(run.returncode==0,succeeds,run.stdout+run.stderr)

    def test_eager_rhs_and_ignored_assertions_fail_existing_proofs(self):
        model=(ROOT/'Proofs/CppVectorProgram.lean').read_text().replace(
            'Proofs.CppVectorProgram','Proofs.VectorProgramMutation')
        mutations=[
            ('if a == 0 then some (next.charge 1 1,0) else do',
             'if a == 0 then do\n          let _ ← right.eval next\n          some (next.charge 1 1,0)\n        else do'),
            ('else some (next.charge 1 1,1)',
             'else do\n          let _ ← right.eval next\n          some (next.charge 1 1,1)'),
            ('if value == 0 then none else some ⟨next.charge 1 0,none⟩',
             'if value == 0 then some ⟨next.charge 1 0,none⟩ else some ⟨next.charge 1 0,none⟩'),
        ]
        with tempfile.TemporaryDirectory(prefix='vector-lazy-proof-negative-') as directory:
            scratch=Path(directory);self.lean(scratch,model)
            for old,new in mutations:
                with self.subTest(mutation=old):
                    self.assertEqual(model.count(old),1)
                    self.lean(scratch,model.replace(old,new),False)
        print('vector logical/assert model: eager RHS and ignored false assertions rejected by existing proofs')

    def test_lazy_conditions_assertions_native_abort_and_costs(self):
        with tempfile.TemporaryDirectory(prefix='vector-assert-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            ir=lower_source(source);checks=[emit_lean(ir),HEADER]
            native=['#include "experiments/library/cpp/template/small_template.hpp"',
                '#include "source.hpp"','#include <cassert>','int main(int argc,char**){',
                'if(argc>1){std::vector<int> v;if(argc>2)v.push_back(0);checked(v);return 0;}']
            native_count=0
            for index,values in enumerate(v for n in range(5) for v in itertools.product([-2,0,7],repeat=n)):
                lv='['+','.join(map(str,values))+']';cv=','.join(map(str,values))
                for name,expected in [('either',not values or values[0]==7),('both',bool(values) and values[0]==7)]:
                    r=f'{name}{index}'
                    checks.append(f'def {r} := result (VectorProgramInstances.{name}.callFuel 128 (caller {lv}) [.vectorReference 0])')
                    checks.append(f'#guard ({r}.map (·.scalars.environment)) == some (some [{int(expected)}])')
                    checks.append(f'#guard ({r}.map (fun s => s.vectors.store.work)) == some {1+int(bool(values))}')
                    # Empty paths skip the read/comparison's6 work units. The
                    # expression observation conservatively includes both arms.
                    checks.append(f'#guard ({r}.map (·.work)) == some {11+6*int(bool(values))}')
                    checks.append(f'#guard ({r}.map (·.peak)) == some 16')
                    native.append(f'{{std::vector<int> v{{{cv}}};assert({name}(v)=={str(expected).lower()});}}')
                    native_count+=1
                prefix=next((i for i,v in enumerate(values) if v<=0),len(values))
                checks.append(f'#guard (result (VectorProgramInstances.prefix.callFuel 128 (caller {lv}) [.vectorReference 0]) |>.map (·.scalars.environment)) == some (some [{prefix}])')
                native.append(f'{{std::vector<int> v{{{cv}}};assert(::prefix(v)=={prefix}UL);}}');native_count+=1
                valid=bool(values) and values[0]==7
                for name,success,answer in [('checked',valid,7),('checked_or',not values or valid,len(values))]:
                    call=f'VectorProgramInstances.{name}.callFuel 128 (caller {lv}) [.vectorReference 0]'
                    if success:
                        checks.append(f'#guard (result ({call}) |>.map (·.scalars.environment)) == some (some [{answer}])')
                        native.append(f'{{std::vector<int> v{{{cv}}};assert({name}(v)=={answer});}}');native_count+=1
                    else:checks.append(f'#guard {call} == .fault')
            self.lean(scratch,'\n'.join(checks))
            native.append('}');cpp=scratch/'native.cpp';cpp.write_text('\n'.join(native));exe=scratch/'native'
            check_compiler()
            subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(ROOT),str(cpp),'-o',str(exe)],cwd=ROOT,check=True)
            subprocess.run([str(exe)],cwd=scratch,check=True)
            resource.setrlimit(resource.RLIMIT_CORE,(0,0))
            for args in [['false'],['false','zero']]:
                failed=subprocess.run([str(exe),*args],cwd=scratch,capture_output=True,text=True)
                self.assertEqual(failed.returncode,-signal.SIGABRT,failed.stderr)
                self.assertIn('Assertion',failed.stderr)
                self.assertNotIn('runtime error',failed.stderr)
        print(f'vector short circuit/assert: {sum(x.count("#guard") for x in checks)} Lean checks, {native_count} C++17 UBSan calls and two SIGABRT paths')

    def test_changed_condition_and_fake_assertions_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix='vector-assert-negative-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            original=lower_source(source)
            guard='\n#guard VectorProgramInstances.checked.callFuel 128 (caller []) [.vectorReference 0] == .fault\n'
            self.lean(scratch,emit_lean(original)+HEADER+guard)
            source.write_text(SOURCE.replace('assert(v.size()>0 && (v[0]!=0 && 10/v[0]>0))','assert(v.size()==0 || (v[0]!=0 && 10/v[0]>0))'))
            changed=lower_source(source);self.assertNotEqual(changed,original)
            self.lean(scratch,emit_lean(changed)+HEADER+guard)
            # The return still reads v[0], so this mutation alone remains a
            # fault for empty inputs. Use nonempty zero to weaken the guard.
            source.write_text(SOURCE.replace('assert(v.size()>0 && (v[0]!=0 && 10/v[0]>0))','assert(v.size()==0 || v[0]==0 || 10/v[0]>0)'))
            changed=lower_source(source)
            guard='\n#guard VectorProgramInstances.checked.callFuel 128 (caller [0]) [.vectorReference 0] == .fault\n'
            self.lean(scratch,emit_lean(changed)+HEADER+guard,False)
            negatives=[
                '#include <vector>\n#include <cassert>\n#undef assert\n#define assert(x) ((x)?(void)0:__assert_fail("x","x",1,"x"))\nint f(const std::vector<int>& v){assert(v.size()>0);return 0;}',
                '#include <vector>\n#include <cassert>\nnamespace cp{void __assert_fail(const char*,const char*,unsigned int,const char*);int f(const std::vector<int>& v){assert(v.size()>0);return 0;}}',
                '#include <vector>\n#include <cassert>\nextern "C" void __assert_fail(const char*,const char*,unsigned int,const char*) noexcept {}\nint f(const std::vector<int>& v){assert(v.size()>0);return 0;}',
                '#define NDEBUG\n#include <vector>\n#include <cassert>\nint f(const std::vector<int>& v){assert(v.size()>0);return 0;}',
                '#include <vector>\n#include <cassert>\nint f(std::vector<int>& v){assert(v.size()>0 && ++v[0]);return 0;}',
                '#include <vector>\n#include <cassert>\nint f(std::vector<int>& v){assert(v.size()>0 && (v[0]=1));return 0;}',
            ]
            for text in negatives:
                source.write_text(text)
                with self.subTest(source=text),self.assertRaises(ValueError):lower_source(source)
        print('vector assertions: weakened source condition and six fake/effectful/disabled assertion profiles rejected')

if __name__=='__main__':
    disable_network();unittest.main()
