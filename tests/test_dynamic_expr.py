"""Pure contents evaluation agrees with reads after noncontiguous row growth."""
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
HEADER = '''import Proofs.DynamicReadSound
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedStmt Proofs.CppNestedEval
open Proofs.CppRowsFrame Proofs.CppRowsContents Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes
 def i32 : Ty := ⟨32,true,false⟩
 def atom : Element := .integer i32
 def row : Element := .vector atom
 def p0 : Parameter := ⟨0,0,row,0,true,true⟩
 def p1 : Parameter := ⟨1,0,row,0,false,true⟩
 def p2 : Parameter := ⟨2,2,atom,1,false,true⟩
 def params := [p0,p1,p2]
'''


def fixture_checks():
    checks = [HEADER, f'def initial := {initial(1,1)}']
    for step in range(3):
        prev='initial' if step == 0 else f'grown{step}'
        checks.append(f'def grown{step+1} := ({prev}.appendRow 0 i32).getD {prev}')
    checks += ['def withRow := ((grown3.child 0 atom 1).map Prod.fst).getD grown3',
               'def written1 := (withRow.append 3 i32 17).getD withRow',
               'def written2 := (written1.append 3 i32 (-3)).getD written1',
               'def base : Frame := {written2 with bindings := initial.bindings}',
               'def state : NState := {scalars := ⟨[⟨i32,1⟩,⟨i32,1⟩],[⟨0,true⟩,⟨1,true⟩],0,0,0⟩,frame := base,slots := [.vector 0,.vector 1,.vector 2,.scalar 0,.scalar 1],scope := 2,peak := 0}',
               'def values : List (List Int) := [[10,0],[17,-3],[],[]]',
               'def view : View := .rows i32 0 [1,4,5,6] 2 values',
               'def heap : Heap := fun root => if root = 0 then some view else if root = 2 then some (.flat i32 1 [77]) else none',
               'def logical := eraseHeap heap',
               'theorem model : Models state.frame.state 0 view := by',
               '  refine ⟨⟨by decide +kernel,by decide +kernel,(base.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩,rfl,?_⟩',
               '  intro k owner lookup',
               '  refine ⟨(base.state.storage.lookup owner).getD ⟨0,[],0,64,0⟩,?_,?_⟩',
               '  all_goals have bound : k < 4 := (List.getElem?_eq_some_iff.mp lookup).1',
               '  all_goals have positions : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega',
               '  all_goals rcases positions with h|h|h|h <;> subst k <;> simp at lookup <;> subst owner',
               '  all_goals decide +kernel',
               'theorem family : Family params heap state.frame (resources state.frame) := by',
               '  refine ⟨by decide +kernel,?_,by decide +kernel,?_,?_,?_,?_,measured_resources _⟩',
               '  · intro root v lookup',
               '    by_cases zero : root = 0',
               '    · subst root; simp [heap] at lookup; subst v; exact model',
               '    by_cases two : root = 2',
               '    · subst root; simp [heap] at lookup; subst v; exact ⟨by decide +kernel,by decide +kernel,(base.state.storage.lookup 2).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
               '    simp [heap,zero,two] at lookup',
               '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl <;> decide +kernel',
               '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl <;> decide +kernel',
               '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl <;> decide +kernel',
               '  · intro p hp; simp [params] at hp; rcases hp with rfl|rfl|rfl',
               '    all_goals first | exact ⟨view,by decide +kernel,rfl,rfl⟩ | exact ⟨.flat i32 1 [77],by decide +kernel,rfl,rfl⟩',
               'theorem realizes : Realizes params (snapshot state) logical state := of_family params heap (resources state.frame) state family',
               'def idx : NExpr := .variable i32 3', 'def pos : NExpr := .variable i32 4',
               'def rootSize : NExpr := .size row (.local 1)',
               'def rowSize : NExpr := .size atom (.row (.local 1) atom idx)',
               'def rowRead : NExpr := .read i32 (.row (.local 1) atom idx) pos',
               'example : Proofs.DynamicExpr.denote params (snapshot state) logical rootSize = some 4 ∧ ∃ t, Ev state rootSize t 4 [] 3 3 ∧ Realizes params (snapshot state) logical ((t.release state).charge 1 0) :=',
               '  Proofs.DynamicSizeSound.root_size params (snapshot state) logical state realizes 1 p1 (by decide +kernel) (by decide +kernel) i32 0 values (by decide +kernel) (by decide +kernel)',
               'example : Proofs.DynamicExpr.denote params (snapshot state) logical rowSize = some 2 ∧ ∃ t extra, Ev state rowSize t 2 extra 4 5 ∧ Realizes params (snapshot state) logical ((t.release state).charge 1 0) :=',
               '  Proofs.DynamicReadSound.row_size params (snapshot state) logical state realizes 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 values [17,-3] idx (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)',
               'example : Proofs.DynamicExpr.denote params (snapshot state) logical rowRead = some (-3) ∧ ∃ t extra, Ev state rowRead t (-3) extra 5 6 ∧ Realizes params (snapshot state) logical ((t.release state).charge 1 0) :=',
               '  Proofs.DynamicReadSound.row_read params (snapshot state) logical state realizes 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 1 values [17,-3] idx pos (-3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)',
               'def combined : NExpr := .binary i32 .add (.cast i32 rootSize) rowRead',
               '#guard Proofs.DynamicExpr.denote params (snapshot state) logical combined == some 1',
               '#guard Proofs.DynamicExpr.denote params (snapshot state) logical (.read i32 (.local 2) (.literal i32 0)) == some 77',
               'def bad : NExpr := .read i32 (.row (.local 1) atom (.literal i32 (-1))) pos',
               '#guard (Proofs.DynamicExpr.denote params (snapshot state) logical bad).isNone',
               '#guard Proofs.DynamicExpr.denote params (snapshot state) logical (.logical true (.literal i32 0) bad) == some 0',
               '#guard Proofs.DynamicExpr.denote params (snapshot state) logical (.logical false (.literal i32 1) bad) == some 1',
               '#guard (Proofs.DynamicExpr.denote params (snapshot state) logical (.logical true (.literal i32 1) bad)).isNone',
               '#guard (Proofs.DynamicExpr.denote params (snapshot state) logical (.divrem i32 false rowRead (.literal i32 0))).isNone',
               '#guard (Proofs.DynamicExpr.denote params (snapshot state) logical (.binary i32 .add (.literal i32 2147483647) (.cast i32 rootSize))).isNone',
               '#guard (Proofs.DynamicExpr.denote params (snapshot state) logical (.variable ⟨64,false,false⟩ 3)).isNone']
    checks += ['def probes : List NExpr := [rootSize,rowSize,rowRead,combined,bad,.logical true (.literal i32 0) bad,.logical false (.literal i32 1) bad,.logical true (.literal i32 1) bad,.divrem i32 false rowRead (.literal i32 0),.binary i32 .add (.literal i32 2147483647) (.cast i32 rootSize),.targetCast i32 rootSize,.unary i32 .neg rowRead,.divrem i32 true rowRead (.literal i32 2),.read i32 (.local 2) (.literal i32 0),.size atom (.local 2),.size atom (.local 1)]',
               '#guard probes.all (fun e => (e.eval state).map Prod.snd == Proofs.DynamicExpr.denote params (snapshot state) logical e)']
    return checks


class DynamicExprTests(unittest.TestCase):
    def test_sound_reads_pure_expression_composition_and_native_source(self):
        checks = fixture_checks()
        source_text = '''#include <vector>
namespace cp {int inspect(const std::vector<std::vector<int>>& g,const std::vector<int>& other,int k,int j){
int n=g.size();int len=g[k].size();int v=g[k][j];return n+len+v+other[0];}}
'''
        native=['#include "experiments/library/cpp/template/small_template.hpp"','#include "source.hpp"','#include <iostream>','int main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};std::vector<int> other{77};']
        expected=[]
        with tempfile.TemporaryDirectory(prefix='dynamic-expr-') as directory:
            scratch=Path(directory);fixture=scratch/'source.hpp';fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'InspectRows')
            checks[0]='import Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n','')
            for case,(k,j,value) in enumerate([(1,1,-3),(0,0,10),(0,1,0)]):
                want=4+2+value+77
                checks += [f'def call{case} := InspectRows.inspect.callFuel 200 state [.vectorReference 1,.vectorReference 2,.value (.literal i32 {k}),.value (.literal i32 {j})]',
                           f'#guard (match call{case} with | .finished (s,.scalar x) => x == {want} && s.frame.state.wellFormed && s.frame.bindings == base.bindings | _ => false)']
                native.append(f'std::cout<<cp::inspect(g,other,{k},{j})<<std::endl;');expected.append(want)
            for case,(k,j) in enumerate([(-1,0),(0,2),(4,0)]):
                checks += [f'def refused{case} := InspectRows.inspect.callFuel 200 state [.vectorReference 1,.vectorReference 2,.value (.literal i32 ({k})),.value (.literal i32 {j})]',
                           f'#guard (match refused{case} with | .fault => true | _ => false)']
            native.append('}')
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler();source,exe=scratch/'native.cpp',scratch/'native';source.write_text('\n'.join(native))
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0';result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(list(map(int,result.stdout.splitlines())),expected)


if __name__ == '__main__':
    disable_network()
    unittest.main()
