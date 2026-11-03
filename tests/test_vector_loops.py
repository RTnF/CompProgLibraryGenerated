"""Generated vector control flow, lifetime cleanup, fuel and native execution."""
import itertools
from pathlib import Path
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
unsigned long mark(std::vector<int>& v,int& count){
 for(unsigned long i=0;i<v.size();++i){
  std::vector<int> scratch(1,v[i]);
  if(scratch[0]<0)break;
  v[i]=scratch[0]+1;count=count+1;
 }
 return v.size();
}
unsigned long find(const std::vector<int>& v){
 unsigned long i=0;
 while(i<v.size()){
  std::vector<int> scratch(1,v[i]);
  if(scratch[0]==7)return i;
  i=i+1;
 }
 return v.size();
}
unsigned long spin(const std::vector<int>& v){while(true){}return v.size();}
'''
HEADER='''
open Proofs.CppScalar Proofs.CppMixedInvoke
 def i32 : Ty := ⟨32,true,false⟩
 def u64 : Ty := ⟨64,false,false⟩
 def caller (values : List Int) : State := ⟨⟨[⟨i32,0⟩],[⟨0,true⟩],0,1,0⟩,
  ⟨⟨[some ⟨0,values,values.length,100,0⟩],0,0,values.length+1⟩,[⟨i32,true⟩],[⟨0,i32,true⟩],0⟩,
  [.scalar 0,.vector 0],0⟩
 def outcome (values : List Int) := VectorProgramInstances.mark.callFuel 256 (caller values)
  [.vectorReference 0,.scalarReference 0]
 def result (values : List Int) : Option State := match outcome values with
  | .finished s => some s
  | _ => none
'''

class VectorLoopTests(unittest.TestCase):
    def lean(self,scratch,text,succeeds=True):
        path=scratch/'checks.lean';path.write_text(text);lake,env=lean_environment()
        run=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(run.returncode==0,succeeds,run.stdout+run.stderr)

    def test_generated_for_while_break_return_lifetimes_and_costs(self):
        with tempfile.TemporaryDirectory(prefix='vector-loop-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            ir=lower_source(source);self.assertEqual(ir['coverage'],'control_flow_scalar_return')
            checks=[emit_lean(ir),HEADER]
            native=['#include "experiments/library/cpp/template/small_template.hpp"',
                '#include "source.hpp"','#include <cassert>','int main(){']
            count=0
            for n in range(5):
                for values in itertools.product([-2,0,7],repeat=n):
                    k=next((i for i,v in enumerate(values) if v<0),n)
                    expected=[v+1 if i<k else v for i,v in enumerate(values)]
                    visited=k+int(k<n)
                    # Entry/finalization18, each completed iteration41,
                    # and a breaking iteration21. Source-level conversions,
                    # scopes and vector primitive contracts are all charged.
                    work=18+41*k+21*int(k<n)
                    peak=20 if k else (18 if n else 12)
                    lv='['+','.join(map(str,values))+']';ev='['+','.join(map(str,expected))+']'
                    checks.append(f'def r{count} := result {lv}')
                    checks.append(f'#guard (r{count}.map (·.scalars.memory)) == some [⟨i32,{k}⟩,⟨u64,{n}⟩]')
                    checks.append(f'#guard (r{count}.map (·.vectors.store.objects)) == some ([some ⟨0,{ev},{n},100,0⟩] ++ List.replicate {visited} none)')
                    checks.append(f'#guard (r{count}.map (·.work)) == some {work}')
                    checks.append(f'#guard (r{count}.map (·.peak)) == some {peak}')
                    checks.append(f'#guard outcome {lv} == VectorProgramInstances.mark.callFuel 512 (caller {lv}) [.vectorReference 0,.scalarReference 0]')
                    found=next((i for i,v in enumerate(values) if v==7),n)
                    checks.append(f'def found{count} := VectorProgramInstances.find.callFuel 256 (caller {lv}) [.vectorReference 0]')
                    checks.append(f'#guard (match found{count} with | .finished s => s.scalars.environment | _ => none) == some [0,{found}]')
                    checks.append(f'#guard (match found{count} with | .finished s => some s.vectors.store.objects | _ => none) == some ([some ⟨0,{lv},{n},100,0⟩] ++ List.replicate {found+int(found<n)} none)')
                    cv=','.join(map(str,values));ce=','.join(map(str,expected))
                    native.append(f'{{std::vector<int> v{{{cv}}};int count=0;assert(mark(v,count)=={n}UL && count=={k} && v==std::vector<int>({{{ce}}}));}}')
                    native.append(f'{{std::vector<int> v{{{cv}}};assert(find(v)=={found}UL && v==std::vector<int>({{{cv}}}));}}')
                    count+=1
            checks.extend([
                '#guard VectorProgramInstances.mark.callFuel 0 (caller [0]) [.vectorReference 0,.scalarReference 0] == .exhausted',
                '#guard VectorProgramInstances.mark.callFuel 1 (caller [0]) [.vectorReference 0,.scalarReference 0] == .exhausted',
                '#guard VectorProgramInstances.mark.callFuel 256 (caller [2147483647]) [.vectorReference 0,.scalarReference 0] == .fault',
                '#guard VectorProgramInstances.spin.callFuel 256 (caller []) [.vectorReference 0] == .exhausted',
                '#guard VectorProgramInstances.mark.callFuel 256 (caller [0]) [] == .fault'])
            self.lean(scratch,'\n'.join(checks))
            native.append('}');cpp=scratch/'native.cpp';cpp.write_text('\n'.join(native));exe=scratch/'native'
            check_compiler()
            subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(ROOT),str(cpp),'-o',str(exe)],cwd=ROOT,check=True)
            subprocess.run([str(exe)],check=True)
        print(f'vector loops: {count*7+5} Lean checks and {count*2} C++17 UBSan calls')

    def test_mutations_and_unsupported_control(self):
        with tempfile.TemporaryDirectory(prefix='vector-loop-negative-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            original=lower_source(source)
            guard='\n#guard (result [0,7] |>.map (·.scalars.environment)) == some (some [2,2])\n'
            self.lean(scratch,emit_lean(original)+HEADER+guard)
            for old,new in [('scratch[0]+1','scratch[0]+2'),('count=count+1','count=count+2'),('scratch[0]<0','scratch[0]<=0')]:
                source.write_text(SOURCE.replace(old,new));changed=lower_source(source)
                self.assertNotEqual(changed,original)
                mutation_guard=guard if old!='scratch[0]+1' else '\n#guard (result [0,7] |>.map (·.vectors.store.objects)) == some [some ⟨0,[1,8],2,100,0⟩,none,none]\n'
                self.lean(scratch,emit_lean(changed)+HEADER+mutation_guard,False)
            for body in ['do{}while(v.size());','while(v.size()){continue;}',
                         'for(int x=0;int y=1;++x){}','if(int x=0;v.size())return x;',
                         'if(v.size() ? v[0] : 0)return 1;','goto finish;finish:return 0;']:
                source.write_text('#include <vector>\nunsigned long f(std::vector<int>& v){'+body+'return 0;}')
                with self.subTest(body=body),self.assertRaises(ValueError):lower_source(source)
        print('vector loops: three source mutations and six unsupported control profiles rejected')

if __name__=='__main__':
    disable_network();unittest.main()
