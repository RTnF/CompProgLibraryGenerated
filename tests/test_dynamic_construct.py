"""Vector-reading constructor expressions release temporaries before binding."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from test_dynamic_expr import fixture_checks, HEADER
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
SOURCE='''#include <vector>
namespace cp {int construct(const std::vector<std::vector<int>>&g,int k,int j){std::vector<std::vector<int>>local((int)g.size()+g[k][j]);const std::vector<int>v(g[k].size(),g[k][j]);local.emplace_back();return (int)local.size()+v[1];}}
'''

class DynamicConstructTests(unittest.TestCase):
    def test_expression_construction_registration_and_cleanup(self):
        checks=fixture_checks()
        checks += ['open Proofs.DynamicConstructCore',
          'def entered : NState := {state with scope := 3}',
          'theorem enteredReal : Realizes params (snapshot entered) logical entered := of_family params heap (resources state.frame) entered family',
          'def rowsStmt : NStmt := .constructRows i32 true combined',
          'def rowsOut := (rowsStmt.run entered).getD ⟨entered,none,false⟩ |>.state',
          'def p3 : Parameter := ⟨3,7,row,3,true,true⟩',
          'def rowsParams := params ++ [p3]',
          'def rowsHeap := put heap 7 (.rows i32 3 [8] 0 [[]])',
          'def rowsPure : Proofs.DynamicStmt.State := ⟨appended (snapshot entered) 3,putContents logical 7 (.rows i32 3 [[]])⟩',
          'theorem rowsCertified : Family rowsParams rowsHeap rowsOut.frame (resources rowsOut.frame) ∧ Realizes rowsParams rowsPure.locals rowsPure.contents rowsOut := by',
          '  obtain ⟨out,ran,post,real,_⟩ := Proofs.DynamicConstructRows.sound params heap (resources state.frame) (snapshot entered) entered family enteredReal i32 true combined 1 (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)',
          '  have same : rowsOut = out := by simp [rowsOut,rowsStmt,ran]',
          '  have owner : entered.frame.state.storage.objects.length = 7 := by decide +kernel',
          '  have index : entered.frame.bindings.length = 3 := by decide +kernel',
          '  have description : parameter entered (.vector (.integer i32)) true = p3 := by decide +kernel',
          '  rw [description,owner] at post real',
          '  rw [index] at real',
          '  rw [same]; exact ⟨post,real⟩',
          'theorem rowsErased : eraseHeap rowsHeap = rowsPure.contents := by simp only [rowsHeap,erase_put]; rfl',
          'theorem rowsReal : Realizes rowsParams rowsPure.locals (eraseHeap rowsHeap) rowsOut := by rw [rowsErased]; exact rowsCertified.2',
          'def fillStmt : NStmt := .fillVector i32 false rowSize rowRead',
          'def fillOut := (fillStmt.run rowsOut).getD ⟨rowsOut,none,false⟩ |>.state',
          'def p4 : Parameter := ⟨4,9,atom,3,false,false⟩',
          'def fillParams := rowsParams ++ [p4]',
          'def fillHeap := put rowsHeap 9 (.flat i32 3 [-3,-3])',
          'def fillPure : Proofs.DynamicStmt.State := ⟨appended rowsPure.locals 4,putContents rowsPure.contents 9 (.flat i32 3 [-3,-3])⟩',
          'theorem fillCertified : Family fillParams fillHeap fillOut.frame (resources fillOut.frame) ∧ Realizes fillParams fillPure.locals fillPure.contents fillOut := by',
          '  obtain ⟨out,ran,post,real,_⟩ := Proofs.DynamicConstructFill.sound rowsParams rowsHeap (resources rowsOut.frame) rowsPure.locals rowsOut rowsCertified.1 rowsReal i32 false rowSize rowRead 2 (-3) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)',
          '  have same : fillOut = out := by simp [fillOut,fillStmt,ran]',
          '  have owner : rowsOut.frame.state.storage.objects.length = 9 := by decide +kernel',
          '  have index : rowsOut.frame.bindings.length = 4 := by decide +kernel',
          '  have scope : rowsOut.scope = 3 := by decide +kernel',
          '  have description : parameter rowsOut (.integer i32) false = p4 := by decide +kernel',
          '  rw [description,owner] at post real',
          '  rw [scope] at post real',
          '  rw [index,rowsErased] at real',
          '  rw [same]; exact ⟨post,real⟩',
          'def zero : NExpr := .binary i32 .sub rowRead rowRead',
          'example := Proofs.DynamicConstructRows.sound params heap (resources state.frame) (snapshot entered) entered family enteredReal i32 false zero 0 (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)',
          'example := Proofs.DynamicConstructFill.sound params heap (resources state.frame) (snapshot entered) entered family enteredReal i32 true zero rowRead 0 (-3) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)',
          'example := Proofs.DynamicConstructRows.sound params heap (resources state.frame) (snapshot entered) entered family enteredReal i32 false (.logical false (.literal i32 1) bad) 1 (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)',
          'def generalRows (s : NState) (h : Heap) (m : Resources) (family : Family params h s.frame m) (erased : eraseHeap h = logical) (real : Realizes params (snapshot state) logical s) := Proofs.DynamicConstructRows.sound params h m (snapshot state) s family (by rw [erased]; exact real) i32 true combined 1 (by rw [erased]; decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)',
          'def generalFill (s : NState) (h : Heap) (m : Resources) (family : Family params h s.frame m) (erased : eraseHeap h = logical) (real : Realizes params (snapshot state) logical s) := Proofs.DynamicConstructFill.sound params h m (snapshot state) s family (by rw [erased]; exact real) i32 false rowSize rowRead 2 (-3) (by rw [erased]; decide +kernel) (by rw [erased]; decide +kernel) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)',
          'example := generalRows state heap (resources state.frame) family rfl realizes',
          'example := generalFill state heap (resources state.frame) family rfl realizes',
          '#guard rowsOut.frame.bindings.length == 4',
          '#guard fillOut.frame.bindings.length == 5',
          '#guard rowsOut.slots == entered.slots ++ [.vector 3]',
          '#guard fillOut.slots == rowsOut.slots ++ [.vector 4]',
          '#guard fillOut.frame.rootWritable == entered.frame.rootWritable ++ [true,false,false]',
          '#guard fillOut.scalars.memory == entered.scalars.memory',
          '#guard (fillOut.frame.state.storage.lookup 9).map (·.items) == some [.integer (-3),.integer (-3)]',
          '#guard fillOut.frame.state.storage.lookup 2 == entered.frame.state.storage.lookup 2',
          '#guard ((NStmt.append (.local 6) i32 (.literal i32 7)).run fillOut).isNone',
          'def readNew : NExpr := .read i32 (.local 6) (.literal i32 1)',
          'example := Proofs.DynamicExprCertified.sound (Proofs.DynamicExprDerive.derive (Proofs.DynamicExprAuto.ready fillParams fillPure.locals fillPure.contents readNew) (-3) (by decide +kernel)) fillOut fillCertified.2',
          'def append : NStmt := .appendRow (.local 5) i32',
          'def afterPure : Proofs.DynamicStmt.Step := ⟨⟨fillPure.locals,putContents fillPure.contents 7 (.rows i32 3 [[],[]])⟩,none⟩',
          'theorem pureAppend : Proofs.DynamicStmt.run fillParams append fillPure = some afterPure := by cbv',
          'theorem available : Proofs.DynamicAppendAuto.Available fillParams fillPure fillOut append := by',
          '  intro p selected',
          '  have chosen : Proofs.DynamicStmt.mutableRoot fillParams fillPure 5 (.vector atom) = some p3 := by decide +kernel',
          '  have same : p = p3 := Option.some.inj (selected.symm.trans chosen); subst p',
          '  exact ⟨(fillOut.frame.state.storage.lookup 7).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
          'def after := (append.run fillOut).getD ⟨fillOut,none,false⟩ |>.state',
          'theorem afterReal : Realizes fillParams afterPure.state.locals afterPure.state.contents after := by',
          '  obtain ⟨out,ran,matched,_⟩ := Proofs.DynamicStmtEffects.sound fillParams fillPure fillOut fillCertified.2 append afterPure pureAppend available',
          '  have same : after = out.state := by simp [after,ran]',
          '  rw [same]; exact matched.state',
          'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
          'def final : Proofs.DynamicStmt.State := ⟨snapshot state,Proofs.DynamicRetire.retireContents afterPure.state.contents 3⟩',
          'example : Realizes params final.locals final.contents (Proofs.DynamicOwnedScope.left state after) := by',
          '  apply (Proofs.DynamicOwnedScope.sound params fillParams st0 afterPure.state final state after realizes afterReal ?_ ?_ (some (-1)) (by cbv)).2.1',
          '  · intro p member; exact List.mem_append_left _ (List.mem_append_left _ member)',
          '  · intro p member; simp [params] at member; rcases member with rfl|rfl|rfl <;> decide +kernel',
          '#guard (after.frame.state.storage.lookup 7).map (·.items) == some [.child 8,.child 10]',
          '#guard after.frame.state.destroyWork 3 == 6',
          '#guard (Proofs.DynamicOwnedScope.left state after).work == after.work+7',
          '#guard [7,8,9,10].all (fun owner => ((Proofs.DynamicOwnedScope.left state after).frame.state.storage.lookup owner).isNone)',
          '#guard final.contents 0 == logical 0',
          '#guard (NStmt.constructRows i32 true rowRead |>.run entered).isNone',
          '#guard (NStmt.fillVector i32 true rowRead (.literal i32 0) |>.run entered).isNone',
          '#guard (NStmt.fillVector i32 true (.literal i32 1) (.literal ⟨64,false,false⟩ 2147483648) |>.run entered).isNone']
        with tempfile.TemporaryDirectory(prefix='dynamic-construct-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            generated=emit_lean(lower_source(source),'ConstructSource')
            checks[0]='import Proofs.DynamicConstructFill\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n','')
            checks += ['def call := ConstructSource.construct.callFuel 600 state [.vectorReference 1,.value (.literal i32 1),.value (.literal i32 1)]',
              '#guard (match call with | .finished (s,.scalar x) => x == -1 && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && [7,8,9,10].all (fun owner => (s.frame.state.storage.lookup owner).isNone) | _ => false)']
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler();source=scratch/'native.cpp';exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};std::cout<<cp::construct(g,1,1)<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout.splitlines(),['-1'])

if __name__=='__main__':
    disable_network();unittest.main()
