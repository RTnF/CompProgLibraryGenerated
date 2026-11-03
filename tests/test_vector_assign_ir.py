"""Actual begin/end assign bodies, ownership failures and native comparisons."""
import copy
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
namespace cp {
unsigned long copy(std::vector<int>& target,const std::vector<int>& source){target.assign(source.begin(),source.end());return target.size();}
unsigned long empty(std::vector<int>& target,std::vector<int>& source){target.assign(source.end(),source.end());return target.size();}
unsigned long start(std::vector<int>& target,const std::vector<int>& source){target.assign(source.begin(),source.begin());return target.size();}
unsigned long reversed(std::vector<int>& target,const std::vector<int>& source){target.assign(source.end(),source.begin());return target.size();}
unsigned long mixed(std::vector<int>& target,std::vector<int>& source){target.assign(source.begin(),target.end());return target.size();}
unsigned long local(const std::vector<int>& source){std::vector<int> target(1,7);target.assign(source.begin(),source.end());return target.size();}
unsigned long alias(std::vector<int>& target,const std::vector<int>& first,const std::vector<int>& last){target.assign(first.begin(),last.end());return target.size();}
}'''
HEADER='''
open Proofs.CppScalar Proofs.CppMixedInvoke
def i32 : Ty := ⟨32,true,false⟩
def caller (a b : List Int) (cap : Nat) : State := ⟨⟨[],[],0,0,0⟩,
 ⟨⟨[some ⟨0,a,cap,100,0⟩,some ⟨1,b,b.length,100,0⟩],0,0,cap+b.length+2⟩,[⟨i32,true⟩,⟨i32,true⟩],[⟨0,i32,true⟩,⟨1,i32,true⟩],0⟩,[.vector 0,.vector 1],0⟩
def runCopy (a b : List Int) (cap : Nat) := VectorProgramInstances.copy.call (caller a b cap) [.vectorReference 0,.vectorReference 1]
def runEmpty (a b : List Int) (cap : Nat) := VectorProgramInstances.empty.call (caller a b cap) [.vectorReference 0,.vectorReference 1]
'''

class VectorAssignIRTests(unittest.TestCase):
    def lean(self,scratch,text,succeeds=True):
        path=scratch/'checks.lean';path.write_text(text)
        lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode==0,succeeds,result.stdout+result.stderr)

    def test_generated_assign_native_and_rejections(self):
        with tempfile.TemporaryDirectory(prefix='vector-assign-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            ir=lower_source(source);checks=[emit_lean(ir),HEADER]
            native=['#include "experiments/library/cpp/template/small_template.hpp"','#include "source.hpp"','#include <cassert>','int main(){']
            count=0
            for length in range(4):
                for values in itertools.product([-2,0,7],repeat=length):
                    b='['+','.join(map(str,values))+']';cpp_b='{'+','.join(map(str,values))+'}'
                    for target_length in range(4):
                        a='['+','.join(str(11+i) for i in range(target_length))+']'
                        cpp_a='{'+','.join(str(11+i) for i in range(target_length))+'}'
                        for cap in [target_length,target_length+2]:
                            result=f'runCopy {a} {b} {cap}'
                            checks.extend([
                                f'#guard ({result} |>.map (·.vectors.store.objects)) == some [some ⟨0,{b},{max(cap,length)},100,1⟩,some ⟨1,{b},{length},100,0⟩]',
                                f'#guard ({result} |>.map (·.scalars.environment)) == some (some [{length}])',
                                f'#guard ({result} |>.map (·.work)) == some {length+16}',
                                f'#guard ({result} |>.map (·.peak)) == some {13+(length if cap<length else 0)}',
                                f'#guard (runEmpty {a} {b} {cap} |>.map (·.vectors.store.objects)) == some [some ⟨0,[],{cap},100,1⟩,some ⟨1,{b},{length},100,0⟩]',
                                f'#guard (VectorProgramInstances.start.call (caller {a} {b} {cap}) [.vectorReference 0,.vectorReference 1] |>.map (·.scalars.environment)) == some (some [0])',
                            ])
                            native.append(f'{{std::vector<int> a{cpp_a},b{cpp_b};a.reserve({cap});auto before=a.capacity();assert(cp::copy(a,b)=={length}UL && a==b && b==std::vector<int>({cpp_b}));assert(a.capacity()==std::max(before,b.size()));assert(cp::empty(a,b)==0 && a.empty());assert(cp::start(a,b)==0 && a.empty());}}')
                            count+=1
                    checks.append(f'#guard (VectorProgramInstances.local.call (caller [] {b} 0) [.vectorReference 1] |>.map (·.scalars.environment)) == some (some [{length}])')
                    checks.append(f'#guard (VectorProgramInstances.local.call (caller [] {b} 0) [.vectorReference 1] |>.map (·.vectors.store.objects)) == some [some ⟨0,[],0,100,0⟩,some ⟨1,{b},{length},100,0⟩,none]')
                    checks.append(f'#guard (VectorProgramInstances.alias.call (caller [] {b} 0) [.vectorReference 0,.vectorReference 1,.vectorReference 1] |>.map (·.vectors.store.objects)) == some [some ⟨0,{b},{length},100,1⟩,some ⟨1,{b},{length},100,0⟩]')
                    native.append(f'{{std::vector<int> a,b{cpp_b};assert(cp::local(b)=={length}UL && b==std::vector<int>({cpp_b}));assert(cp::alias(a,b,b)=={length}UL && a==b);}}')
            checks.extend([
                '#guard VectorProgramInstances.copy.call (caller [3] [7] 1) [.vectorReference 0,.vectorReference 0] == none',
                '#guard VectorProgramInstances.mixed.call (caller [3] [7] 1) [.vectorReference 0,.vectorReference 1] == none',
                '#guard VectorProgramInstances.reversed.call (caller [3] [7] 1) [.vectorReference 0,.vectorReference 1] == none',
                '#guard (VectorProgramInstances.reversed.call (caller [3] [] 1) [.vectorReference 0,.vectorReference 1] |>.map (·.scalars.environment)) == some (some [0])',
                '#guard ((runCopy [3] [7] 1).bind fun s => s.vectors.read ⟨0,i32,true,⟨0,0,0⟩⟩) == none',
                '#guard ((runCopy [3] [7] 1).bind fun s => s.vectors.read ⟨1,i32,true,⟨1,0,0⟩⟩ |>.map (·.2)) == some 7',
                '#guard VectorProgramInstances.copy.call (caller [3] [7] 0) [.vectorReference 0,.vectorReference 1] == none',
                '#guard (Proofs.CppVectorProgram.Stmt.assignRange 0 1 1 i32 false true).run {caller [] [7] 0 with vectors := {(caller [] [7] 0).vectors with bindings := [⟨0,i32,false⟩,⟨1,i32,true⟩]}} == none',
                '#guard (Proofs.CppVectorProgram.Stmt.assignRange 0 1 1 i32 false true).run {caller [] [7] 0 with vectors := {(caller [] [7] 0).vectors with types := [⟨i32,true⟩,⟨⟨64,true,false⟩,true⟩]}} == none',
                '#guard (Proofs.CppVectorProgram.Stmt.assignRange 0 1 1 i32 false true).run {caller [] [7,8] 0 with vectors := {(caller [] [7,8] 0).vectors with store := {(caller [] [7,8] 0).vectors.store with objects := [some ⟨0,[],0,1,0⟩,some ⟨1,[7,8],2,100,0⟩]}}} == none',
                '#guard (Proofs.CppVectorProgram.Stmt.assignRange 0 1 1 i32 false true).run {caller [] [7] 0 with vectors := {(caller [] [7] 0).vectors with store := {(caller [] [7] 0).vectors.store with objects := [some ⟨0,[],0,100,0⟩,none]}}} == none',
            ])
            self.lean(scratch,'\n'.join(checks));native.append('}')
            cpp=scratch/'native.cpp';cpp.write_text('\n'.join(native));executable=scratch/'native'
            check_compiler();subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(ROOT),str(cpp),'-o',str(executable)],cwd=ROOT,check=True)
            subprocess.run([str(executable)],check=True)
            print(f'vector assign: {sum(s.count("#guard") for s in checks)} Lean checks, {count*3+80} C++ calls')

    def test_source_mutations_and_unsupported_iterator_expressions(self):
        with tempfile.TemporaryDirectory(prefix='vector-assign-mutation-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            original=lower_source(source)
            guard='\n#guard (runCopy [3] [7,8] 1 |>.map (·.vectors.store.objects)) == some [some ⟨0,[7,8],2,100,1⟩,some ⟨1,[7,8],2,100,0⟩]\n'
            self.lean(scratch,emit_lean(original)+HEADER+guard)
            for before,after in [('source.begin(),source.end()','source.begin(),source.begin()'),('source.begin(),source.end()','target.begin(),target.end()')]:
                source.write_text(SOURCE.replace(before,after,1));changed=lower_source(source)
                self.lean(scratch,emit_lean(changed)+HEADER+guard,False)
            renamed=SOURCE.replace('target','destination').replace('source','origin')
            source.write_text(renamed);self.assertEqual(lower_source(source),original)
            for body in ['target.assign(source.begin()+1,source.end());','auto it=source.begin();target.assign(it,source.end());','target.assign(2,7);','target.assign(source.rbegin(),source.rend());']:
                source.write_text('#include <vector>\nunsigned long f(std::vector<int>& target,const std::vector<int>& source){'+body+'return target.size();}')
                with self.subTest(body=body),self.assertRaises(ValueError):lower_source(source)
            # A specialization in implementation namespace must not alter iterator behavior.
            for definition in ['template<> const int* const& __normal_iterator<const int*,std::vector<int>>::base() const noexcept {static const int* p=nullptr;return p;}',
                               'template<> __normal_iterator<const int*,std::vector<int>>::__normal_iterator(const int* const&) noexcept : _M_current(nullptr) {}']:
                source.write_text('#include <vector>\nnamespace __gnu_cxx {'+definition+'}\n'+SOURCE.split('\n',1)[1])
                with self.subTest(definition=definition),self.assertRaises(ValueError):lower_source(source)
            qualified='template<> const int* const& __gnu_cxx::__normal_iterator<const int*,std::vector<int>>::base() const noexcept {static const int* p=nullptr;return p;}'
            source.write_text('#include <vector>\n'+qualified+'\n'+SOURCE.split('\n',1)[1])
            with self.assertRaisesRegex(ValueError,'used standard iterator member specialization'):
                lower_source(source)

    def test_models_reject_owner_and_copy_mutations(self):
        with tempfile.TemporaryDirectory(prefix='iterator-model-mutation-') as directory:
            scratch=Path(directory)
            bindings=(ROOT/'Proofs/CppVectorBindings.lean').read_text().replace('namespace Proofs.CppVectorBindings','namespace Proofs.IteratorBindingsMutation').replace('end Proofs.CppVectorBindings','end Proofs.IteratorBindingsMutation')
            self.lean(scratch,bindings)
            owner='if origin.owner = ending.owner ∧ buffer.epoch = other.epoch then'
            self.assertEqual(bindings.count(owner),1)
            self.lean(scratch,bindings.replace(owner,'if buffer.epoch = other.epoch then'),False)
            program=(ROOT/'Proofs/CppVectorProgram.lean').read_text().replace('namespace Proofs.CppVectorProgram','namespace Proofs.IteratorProgramMutation').replace('end Proofs.CppVectorProgram','end Proofs.IteratorProgramMutation')
            self.lean(scratch,program)
            assign='let vectors ← next.vectors.assign destination origin ty range'
            self.assertEqual(program.count(assign),1)
            self.lean(scratch,program.replace(assign,'let vectors := next.vectors'),False)

if __name__=='__main__':disable_network();unittest.main()
