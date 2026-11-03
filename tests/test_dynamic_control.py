"""Dynamic loop invariants, alias contents, and generated C++ control flow."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

from test_append_row import initial
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
HEADER = '''import Proofs.MultiVecDynamicScope
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedSim
open Proofs.CppRowsFrame Proofs.CppRowsContents Proofs.CppRowsGraph
open Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.MultiVecDynamicHoare Proofs.DynamicContents
open Proofs.CppLoop (Outcome)
def i32 : Ty := ⟨32,true,false⟩
def atom : Element := .integer i32
def row : Element := .vector atom
def p0 : Parameter := ⟨0,0,row,0,true,true⟩
def p1 : Parameter := ⟨1,0,row,0,false,true⟩
def p2 : Parameter := ⟨2,1,atom,1,false,true⟩
def params := [p0,p1,p2]
def condition : NExpr := .variable i32 3
def add : Command := .primitive (.appendRow (.local 0) i32)
def twice : Command := .sequence add add
def increment : Command := .primitive (.assign 3 i32 (.binary i32 .sub (.variable i32 3) (.literal i32 1)))
def choice : Command := .branch (.binary ⟨1,false,true⟩ .eq (.variable i32 3) (.literal i32 2)) twice add
def body : Command := .scope (.sequence choice increment)
def guarded (s : NState) := (((condition.eval s).getD (s,0)).1.release s).charge 1 0
'''


class DynamicControlTests(unittest.TestCase):
    def test_contents_loop_rules_and_native_control(self):
        checks = [HEADER, f'def base := {initial(0,0)}',
                  'def state0 : NState := {scalars := ⟨[⟨i32,3⟩],[⟨0,true⟩],0,0,0⟩,frame := base,slots := [.vector 0,.vector 1,.vector 2,.scalar 0],scope := 2,peak := 0}']
        for i in range(3):
            checks.append(f'def state{i+1} := (match runFuel 24 body (guarded state{i}) with | .finished step => step.state | _ => state{i})')
        counts, epochs = [0,1,3,4], [0,1,3,3]
        for i, (count, epoch) in enumerate(zip(counts,epochs)):
            ids = '['+','.join(str(j+3) for j in range(count))+']'
            vals = '['+','.join('[]' for _ in range(count))+']'
            checks += [f'def view{i} : View := .rows i32 0 {ids} {epoch} {vals}',
                       f'def heap{i} : Heap := fun root => if root = 0 then some view{i} else if root = 1 then some (.flat i32 1 [77]) else none',
                       f'theorem model{i} : Models state{i}.frame.state 0 view{i} := by',
                       f'  refine ⟨⟨by decide +kernel,by decide +kernel,(state{i}.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩,rfl,?_⟩',
                       '  intro k owner lookup']
            if count:
                checks += [f'  refine ⟨(state{i}.frame.state.storage.lookup owner).getD ⟨0,[],0,64,0⟩,?_,?_⟩',
                           f'  all_goals have bound : k < {count} := (List.getElem?_eq_some_iff.mp lookup).1',
                           f'  all_goals have positions : {" ∨ ".join(f"k = {k}" for k in range(count))} := by omega',
                           f'  all_goals rcases positions with {" | ".join("hk" for _ in range(count))} <;> subst k <;> simp at lookup <;> subst owner',
                           '  all_goals decide +kernel']
            else:
                checks.append('  simp at lookup')
            checks += [f'theorem family{i} : Family params heap{i} state{i}.frame (resources state{i}.frame) := by',
                       '  refine ⟨by decide +kernel,?_,by decide +kernel,?_,?_,?_,?_,measured_resources _⟩',
                       '  · intro root v lookup',
                       '    by_cases z : root = 0',
                       f'    · subst root; simp [heap{i}] at lookup; subst v; exact model{i}',
                       '    by_cases o : root = 1',
                       f'    · subst root; simp [heap{i}] at lookup; subst v; exact ⟨by decide +kernel,by decide +kernel,(state{i}.frame.state.storage.lookup 1).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
                       f'    simp [heap{i},z,o] at lookup',
                       '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl <;> decide +kernel',
                       '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl <;> decide +kernel',
                       '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl <;> decide +kernel',
                       '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl',
                       f'    all_goals first | exact ⟨view{i},by decide +kernel,rfl,rfl⟩ | exact ⟨.flat i32 1 [77],by decide +kernel,rfl,rfl⟩']
        alternatives = [f'(g = {3-i} ∧ h = heap{i} ∧ m = resources state{i}.frame ∧ s = state{i})' for i in range(4)]
        checks += ['def LoopInv (g : Nat) (h : Heap) (m : Resources) (s : NState) : Prop := '+ ' ∨ '.join(alternatives),
                   'def Final : Proofs.MultiVecDynamicHoare.Post := fun h m step => h = heap3 ∧ m = resources state3.frame ∧ step.state = guarded state3 ∧ step.returned = none ∧ step.breaking = false',
                   'theorem loop_verified : Runs params (.whileLoop condition body) state0 Final := by',
                   '  apply Runs.whileGhost LoopInv Final (step := ?_) 3 3 heap0 (resources state0.frame) state0 (by omega) family0 (by simp [LoopInv])',
                   '  intro g h m s family inv',
                   '  rcases inv with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩']
        for i in range(4):
            checks += [f'  · refine ⟨((condition.eval state{i}).getD (state{i},0)).1,{3-i},by decide +kernel,?_,?_⟩']
            if i < 3:
                checks += ['    · intro zero; omega',
                           f'    · intro nonzero; refine ⟨24,⟨state{i+1},none,false⟩,by decide +kernel,heap{i+1},resources state{i+1}.frame,family{i+1},rfl,rfl,{2-i},by omega,?_⟩',
                           '      simp [LoopInv]']
            else:
                checks += ['    · intro zero; refine ⟨heap3,resources state3.frame,?_,?_⟩',
                           '      · have frame : (guarded state3).frame = state3.frame := by decide +kernel',
                           '        change Family params heap3 (guarded state3).frame (resources state3.frame)',
                           '        rw [frame]; exact family3', '      · exact ⟨rfl,rfl,rfl,rfl,rfl⟩',
                           '    · intro nonzero; contradiction']
        checks += ['#guard (match runFuel 80 (.whileLoop condition body) state0 with | .finished step => step.state.frame.state.storage.objects.length == 7 && !step.breaking && step.state.work ≤ 80 && step.state.peak ≤ 20 | _ => false)',
                   'example : Runs params (.branch (.literal i32 1) (.primitive .skip) (.primitive .skip)) state0 (fun _ _ _ => True) := by',
                   '  apply Runs.branch_scalar family0 1 (by decide +kernel) (by decide +kernel)',
                   '  intro next eval family',
                   '  exact Runs.primitive (step := ⟨(next.release state0).charge 1 0,none,false⟩) (by simp [NStmt.run]) family True.intro',
                   'example (s : NState) (h : Heap) (m : Resources) (family : Family params h s.frame m) : Runs params (.whileLoop (.literal i32 1) .breakLoop) s (fun _ _ step => step.returned = none ∧ step.breaking = false) := by',
                   '  apply Runs.whileGhostStop (fun _ _ _ _ => True) _ (step := ?_) 0 h m s family True.intro',
                   '  intro g h m s family inv',
                   '  obtain ⟨next,eval,familyGuard,_⟩ := scalar_condition s params h m family (.literal i32 1) 1 (by decide +kernel) (by simp [NExpr.denote]; decide)',
                   '  refine ⟨next,1,eval,(by intro zero; contradiction),?_⟩',
                   '  intro nonzero',
                   '  exact ⟨1,⟨((next.release s).charge 1 0).charge 1 0,none,true⟩,by simp [runFuel,pure],h,m,familyGuard,Or.inr ⟨rfl,Or.inl ⟨rfl,rfl,rfl⟩⟩⟩',
                   'example : Proofs.DynamicContents.appendRoot (eraseHeap heap0) 0 i32 = some (eraseHeap heap1) := by',
                   '  have proof := appendRoot_erased heap0 0 i32 0 [] [3] 0 1 [] (by decide +kernel)',
                   '  have heaps : put heap0 0 (.rows i32 0 [3] 1 [[]]) = heap1 := by',
                   '    funext owner; by_cases zero : owner = 0 <;> simp [put,heap0,heap1,view0,view1,zero]',
                   '  simpa [heaps] using proof']
        checks += ['example (s : NState) (h : Heap) (m : Resources) (family : Family params h s.frame m) : Runs params (.whileLoop (.literal i32 1) (.primitive (.ret (.literal i32 7)))) s (fun _ _ step => step.returned = some (.scalar 7) ∧ step.breaking = false) := by',
                   '  apply Runs.whileGhostStop (fun _ _ _ _ => True) _ (step := ?_) 0 h m s family True.intro',
                   '  intro g h m s family inv',
                   '  obtain ⟨next,eval,familyGuard,_⟩ := scalar_condition s params h m family (.literal i32 1) 1 (by decide +kernel) (by simp [NExpr.denote]; decide)',
                   '  refine ⟨next,1,eval,(by intro zero; contradiction),?_⟩',
                   '  intro nonzero',
                   '  let guard := (next.release s).charge 1 0',
                   '  let retState := ((guard.charge 1 1).release guard).charge 1 0',
                   '  have lit : (NExpr.literal i32 7).eval guard = some (guard.charge 1 1,7) := by simp [NExpr.eval,show i32.valid 7 = true from by decide +kernel]',
                   '  have frame : retState.frame = guard.frame := by simp [retState,NState.release]',
                   '  have postFamily : Family params h retState.frame m := by rw [frame]; exact familyGuard',
                   '  have retRun : (NStmt.ret (.literal i32 7)).run guard = some ⟨retState,some (.scalar 7),false⟩ := by simp [NStmt.run,lit,retState]',
                   '  exact Runs.primitive retRun postFamily (Or.inl ⟨rfl,rfl,rfl⟩)',
                   'def logical : ContentsHeap := putContents (eraseHeap heap0) 0 (.rows i32 0 [[1]])',
                   '#guard (Proofs.DynamicContents.appendChild logical 0 i32 1 4).isNone',
                   '#guard (Proofs.DynamicContents.appendChild logical 0 ⟨64,true,false⟩ 0 4).isNone',
                   '#guard (Proofs.DynamicContents.appendChild logical 0 i32 0 2147483648).isNone',
                   '#guard ((Proofs.DynamicContents.appendChild logical 0 i32 0 4).bind fun h => h 0) == some (.rows i32 0 [[1,4]])']
        source_text = '''#include <vector>
namespace cp {int build(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& alias,
const std::vector<int>& other,int n){while(n>0){if(n==2){g.emplace_back();g.emplace_back();}else{g.emplace_back();}n=n-1;}return alias.size()+other[0];}}
'''
        native = ['#include "experiments/library/cpp/template/small_template.hpp"','#include "source.hpp"','#include <iostream>','#include <cassert>','int main(){']
        expected = []
        with tempfile.TemporaryDirectory(prefix='dynamic-control-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'LoopRows')
            checks[0]='import Proofs.MultiVecDynamicScope\n'+generated+HEADER.replace('import Proofs.MultiVecDynamicScope\n','')
            for case,n in enumerate([0,1,3,8]):
                count=n+int(n>=2)
                checks += [f'def caller{case} : NState := {{scalars := ⟨[],[],0,0,0⟩,frame := base,slots := [.vector 0,.vector 1,.vector 2],scope := 2,peak := 0}}',
                           f'def call{case} := LoopRows.build.callFuel 500 caller{case} [.vectorReference 0,.vectorReference 1,.vectorReference 2,.value (.literal i32 {n})]',
                           f'#guard (match call{case} with | .finished (s,.scalar x) => x == {count+77} && s.frame.state.wellFormed && s.frame.bindings == base.bindings | _ => false)',
                           f'#guard (match call{case} with | .finished (s,_) => (s.frame.state.storage.lookup 0).map (·.items.length) == some {count} | _ => false)']
                native += [f'{{std::vector<std::vector<int>> g;std::vector<int> other{{77}};int r=cp::build(g,g,other,{n});',
                           'assert(other[0]==77);for(const auto& row:g)assert(row.empty());std::cout<<r<<" "<<g.size()<<std::endl;}']
                expected.append([count+77,count])
            native.append('}')
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks))
            lake,env=lean_environment();result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); source,exe=scratch/'native.cpp',scratch/'native';source.write_text('\n'.join(native))
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0';result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual([list(map(int,line.split())) for line in result.stdout.splitlines()],expected)


if __name__ == '__main__':
    disable_network()
    unittest.main()
