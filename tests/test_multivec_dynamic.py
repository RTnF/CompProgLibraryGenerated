"""Whole-family updates preserve other roots and update mutable/const aliases."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

from test_scalar_ir import lean_environment
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT / "tools"))
sys.path.insert(0,str(ROOT / "verifier"))
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network

HEADER = '''import Proofs.MultiVecDynamicSteps
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppRowsGraph Proofs.CppRowsContents Proofs.CppRowsFrame
open Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.MultiVecDynamicSteps
 def i32 : Ty := ⟨32,true,false⟩
 def atom : Element := .integer i32
 def row : Element := .vector atom
 def base : Frame :=
  ⟨⟨⟨[some ⟨row,none,some 0,[2]⟩,some ⟨row,none,some 1,[4]⟩,
      some ⟨atom,some 0,none,[]⟩,some ⟨atom,none,some 2,[]⟩,
      some ⟨atom,some 1,none,[]⟩,none]⟩,
    ⟨[some ⟨0,[.child 2],1,64,0⟩,some ⟨1,[.child 4],1,64,7⟩,
      some ⟨2,[.integer 10],1,64,0⟩,some ⟨3,[.integer 77],1,64,0⟩,
      some ⟨4,[.integer 99,.integer 100],2,64,4⟩,none],0,0,9⟩⟩,
    [true,true,false,true,false,false],
    [⟨0,row,true,.root 0⟩,⟨0,row,false,.root 0⟩,⟨1,row,false,.root 1⟩,
     ⟨1,row,true,.root 1⟩,⟨3,atom,false,.root 2⟩,⟨3,atom,true,.root 2⟩]⟩
 def a : View := .rows i32 0 [2] 0 [[10]]
 def b : View := .rows i32 1 [4] 7 [[99,100]]
 def c : View := .flat i32 2 [77]
 def heap : Heap := fun root => if root = 0 then some a else if root = 1 then some b else if root = 3 then some c else none
 def p0 : Parameter := ⟨0,0,row,0,true,true⟩
 def p1 : Parameter := ⟨1,0,row,0,false,true⟩
 def p2 : Parameter := ⟨2,1,row,1,false,true⟩
 def p3 : Parameter := ⟨3,1,row,1,true,true⟩
 def p4 : Parameter := ⟨4,3,atom,2,false,true⟩
 def p5 : Parameter := ⟨5,3,atom,2,true,true⟩
 def params := [p0,p1,p2,p3,p4,p5]
 def parent := (base.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩
'''


class MultiVecDynamicTests(unittest.TestCase):
    def test_family_aliases_other_rows_and_flat_root(self):
        checks = [HEADER]
        for label, root, ids, epoch, values in [('a',0,'[2]',0,'[[10]]'),('b',1,'[4]',7,'[[99,100]]')]:
            owner = 2 if root == 0 else 4
            checks += [f'theorem model_{label} : Models base.state {root} {label} := by',
                       f'  refine ⟨⟨by decide +kernel,by decide +kernel,(base.state.storage.lookup {root}).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩,rfl,?_⟩',
                       '  intro k owner lookup',
                       '  have bound := (List.getElem?_eq_some_iff.mp lookup).1',
                       '  have zero : k = 0 := by simp at bound; omega',
                       '  subst k; simp at lookup; subst owner',
                       f'  exact ⟨(base.state.storage.lookup {owner}).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩']
        checks += ['theorem model_c : Models base.state 3 c := ⟨by decide +kernel,by decide +kernel,(base.state.storage.lookup 3).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
                   'theorem models : HeapModels base.state heap := by',
                   '  intro root v lookup',
                   '  by_cases z : root = 0',
                   '  · subst root; simp [heap] at lookup; subst v; exact model_a',
                   '  by_cases o : root = 1',
                   '  · subst root; simp [heap] at lookup; subst v; exact model_b',
                   '  by_cases t : root = 3',
                   '  · subst root; simp [heap] at lookup; subst v; exact model_c',
                   '  simp [heap,z,o,t] at lookup',
                   'theorem family : Family params heap base (resources base) := by',
                   '  refine ⟨by decide +kernel,models,by decide +kernel,?_,?_,?_,?_,measured_resources base⟩',
                   '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel',
                   '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel',
                   '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel',
                   '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl|rfl|rfl|rfl',
                   '    all_goals first | exact ⟨a,by decide +kernel,by decide +kernel,by decide +kernel⟩ | exact ⟨b,by decide +kernel,by decide +kernel,by decide +kernel⟩ | exact ⟨c,by decide +kernel,by decide +kernel,by decide +kernel⟩',
                   'def start : NState := {scalars := ⟨[],[],0,0,0⟩,frame := base,slots := [.vector 0,.vector 1,.vector 2,.vector 3,.vector 4,.vector 5],scope := 3,peak := 0}',
                   'def outer := ((NStmt.appendRow (.local 0) i32).run start |>.getD ⟨start,none,false⟩).state',
                   'def fresh := (outer.frame.state.storage.lookup 6).getD ⟨0,[],0,64,0⟩',
                   'def inner := ((NStmt.append (.row (.local 0) atom (.literal i32 1)) i32 (.literal i32 17)).run outer |>.getD ⟨outer,none,false⟩).state',
                   'example : ∃ r0 r1, Family params (put (put heap 0 (.rows i32 0 [2,6] r0.buffer.epoch [[10],[]])) 0 (.rows i32 0 [2,6] r0.buffer.epoch [[10],[17]])) inner.frame (afterRow (afterRoot (resources base) parent r0) fresh r1) := by',
                   '  obtain ⟨r0,t0,run0,post0,_⟩ := appendRoot_stmt start params heap (resources base) family p0 (by simp [params]) 0 (by decide +kernel) i32 0 [2] 0 [[10]] (by decide +kernel) (by decide +kernel) (by decide +kernel) parent (by decide +kernel) (by decide +kernel)',
                   '  have eq0 : outer = t0 := by simp [outer,run0]', '  subst t0',
                   '  change Family params (put heap 0 (.rows i32 0 [2,6] r0.buffer.epoch [[10],[]])) outer.frame (afterRoot (resources base) parent r0) at post0',
                   '  obtain ⟨r1,t1,run1,post1,_⟩ := appendChild_stmt outer params _ (afterRoot (resources base) parent r0) post0 p0 (by simp [params]) 0 (by decide +kernel) i32 0 [2,6] r0.buffer.epoch [[10],[]] (by simp [put,p0]) (by decide +kernel) (by decide +kernel) (.literal i32 1) (.literal i32 17) 1 6 17 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) fresh (by decide +kernel) (by decide +kernel) (by decide +kernel)',
                   '  have eq1 : inner = t1 := by simp [inner,atom,run1]', '  subst t1',
                   '  exact ⟨r0,r1,post1⟩',
                   '#guard inner.frame.bindings == base.bindings',
                   '#guard (inner.frame.state.storage.lookup 4 |>.map (·.items)) == some [.integer 99,.integer 100]',
                   '#guard (inner.frame.state.storage.lookup 3 |>.map (·.items)) == some [.integer 77]',
                   '#guard (inner.frame.child 1 atom 1).isSome',
                   '#guard ((inner.frame.child 1 atom 1).bind fun p => p.1.append p.2 i32 0) == none']
        checks += ['def old_b := (base.state.storage.lookup 4).getD ⟨0,[],0,64,0⟩',
                   'def result_b := (Proofs.CppVectorGrowth.append old_b (accepts atom) true (.integer 18)).getD ⟨old_b,(),0,0⟩',
                   'example : Family params (put heap 1 (.rows i32 1 [4] 7 [[99,100,18]])) (base.updated 4 old_b result_b) (afterRow (resources base) old_b result_b) :=',
                   '  family.updateChild p3 (by simp [params]) i32 1 [4] 7 [[99,100]] (by decide +kernel) 0 4 (by decide +kernel) old_b (by decide +kernel) result_b [99,100,18] (by decide +kernel) (by decide +kernel)',
                   '#guard (base.updated 4 old_b result_b).state.liveSpace - (base.updated 4 old_b result_b).state.storage.baseSpace ≤ (base.updated 4 old_b result_b).state.storage.peak']
        source_text = '''#include <vector>
namespace cp {int grow(std::vector<std::vector<int>>& a,const std::vector<std::vector<int>>& alias,
std::vector<std::vector<int>>& b,const std::vector<int>& flat,int x){
int k = a.size(); a.emplace_back(); a[k].emplace_back(x); b[0].emplace_back(x);
return alias.size()+flat[0];}}
'''
        native = ['#include "experiments/library/cpp/template/small_template.hpp"', '#include "source.hpp"',
                  '#include <iostream>', '#include <cassert>',
                  'int main(){std::vector<std::vector<int>> a{{10}},b{{99,100}};std::vector<int> flat{77};']
        expected = []
        with tempfile.TemporaryDirectory(prefix='multivec-dynamic-') as directory:
            scratch = Path(directory)
            fixture = scratch/'source.hpp'
            fixture.write_text(source_text)
            generated = emit_lean(lower_source(fixture),'AliasedRows')
            checks[0] = 'import Proofs.MultiVecDynamicSteps\n'+generated+HEADER.replace('import Proofs.MultiVecDynamicSteps\n','')
            checks.append('def ast0 := start')
            rows_a, row_b = [[10]], [99,100]
            for step in range(5):
                x = step-2
                rows_a.append([x]); row_b.append(x)
                name = f'ast{step+1}'
                checks += [f'def call{step} := AliasedRows.grow.callFuel 300 ast{step} [.vectorReference 0,.vectorReference 1,.vectorReference 3,.vectorReference 4,.value (.literal i32 ({x}))]',
                           f'#guard (match call{step} with | .finished (_,.scalar x) => x == {len(rows_a)+77} | _ => false)',
                           f'def {name} := (match call{step} with | .finished (s,_) => s | _ => ast{step})',
                           f'#guard {name}.frame.state.wellFormed',
                           f'#guard {name}.frame.bindings == base.bindings',
                           f'#guard {name}.frame.state.storage.objects.length == {7+step}',
                           f'#guard {name}.frame.state.storage.lookup 5 == none',
                           f'#guard ({name}.frame.state.storage.lookup 3 |>.map (·.items)) == some [.integer 77]']
                for j, values in enumerate(rows_a):
                    owner = 2 if j == 0 else j+5
                    lit = '['+','.join(f'.integer ({v})' for v in values)+']'
                    checks.append(f'#guard ({name}.frame.state.storage.lookup {owner} |>.map (·.items)) == some {lit}')
                lit = '['+','.join(f'.integer ({v})' for v in row_b)+']'
                checks.append(f'#guard ({name}.frame.state.storage.lookup 4 |>.map (·.items)) == some {lit}')
                expected.append([len(rows_a)+77,len(rows_a),len(row_b),*row_b])
                native += [f'int r{step}=cp::grow(a,a,b,flat,{x});assert(flat[0]==77);',
                           f'std::cout<<r{step}<<" "<<a.size()<<" "<<b[0].size();for(int x:b[0])std::cout<<" "<<x;std::cout<<std::endl;']
            native.append('}')
            proof = scratch/'checks.lean'; proof.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler()
            source, exe = scratch/'native.cpp', scratch/'native'; source.write_text('\n'.join(native))
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env = os.environ.copy(); env['ASAN_OPTIONS'] = 'detect_leaks=0'
            result = subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual([list(map(int,line.split())) for line in result.stdout.splitlines()],expected)


if __name__ == '__main__':
    disable_network()
    unittest.main()
