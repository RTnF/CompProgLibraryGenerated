"""Allocation registers all local roots without hand-built post models."""
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
from scalar_ir import SIGNED_CONVERSIONS
ROOT=Path(__file__).resolve().parent.parent
SOURCE='''#include <vector>
#include "helper.hpp"
namespace cp {int allocate(const std::vector<std::vector<int>>&g){std::vector<std::vector<int>>local(2);const std::vector<int>empty;std::vector<int>v(3,-7);local[0].emplace_back(g[1][1]);return local.size()+v[0]+empty.size();} int convert(const std::vector<int>&v,unsigned long long x){int n=v.size();int r=narrow(x);return r+(n-n);}}
'''

class DynamicAllocateTests(unittest.TestCase):
    def test_general_allocation_registration_and_scope(self):
        checks=fixture_checks()
        checks += ['open Proofs.DynamicAllocateModels Proofs.DynamicAllocateFamily',
          'def rowsNext := (state.frame.state.constructRows i32 3 2).getD state.frame.state',
          'theorem rowsRun : state.frame.state.constructRows i32 3 2 = some rowsNext := by decide +kernel',
          'def rowsHeap := put heap 7 (.rows i32 3 [8,9] 0 [[],[]])',
          'def p3 : Parameter := ⟨3,7,row,3,true,true⟩',
          'def rowsParams := params ++ [p3]',
          'def rowsBase := grown state.frame rowsNext true 2',
          'def rowsFrame : Frame := (rowsBase.bindRoot 7 row 3 true).getD (rowsBase,3) |>.fst',
          'theorem rowsFamily : Family rowsParams rowsHeap rowsFrame (resources rowsFrame) := by',
          '  have base := Proofs.DynamicAllocateFamily.rows family rowsNext i32 3 2 true rowsRun',
          '  have count : state.frame.state.storage.objects.length = 7 := by decide +kernel',
          '  have slots : state.frame.bindings.length = 3 := by decide +kernel',
          '  rw [count] at base',
          '  have flag := new_flag family rowsNext true 2',
          '  rw [count] at flag',
          '  obtain ⟨frame,ran,post⟩ := register base 7 (.rows i32 3 [8,9] 0 [[],[]]) (by decide +kernel) true flag',
          '  simp only [View.element,View.scope,grown] at ran post',
          '  rw [slots] at ran post',
          '  change rowsBase.bindRoot 7 row 3 true = some (frame,3) at ran',
          '  have same : rowsFrame = frame := by unfold rowsFrame; rw [ran]; rfl',
          '  rw [same]; exact Family.remeasured post',
          'def rowsState : NState := {state with frame := rowsFrame,scope := 3,slots := state.slots ++ [.vector 3]}',
          'theorem rowsReal : Realizes rowsParams (snapshot rowsState) (eraseHeap rowsHeap) rowsState := of_family rowsParams rowsHeap _ rowsState rowsFamily',
          'def emptyState := ((NStmt.declareVector i32 false).run rowsState).getD ⟨rowsState,none,false⟩ |>.state',
          'def p4 : Parameter := ⟨4,10,atom,3,false,false⟩',
          'def emptyParams := rowsParams ++ [p4]',
          'def emptyHeap := put rowsHeap 10 (.flat i32 3 [])',
          'theorem emptyFamily : Family emptyParams emptyHeap emptyState.frame (resources emptyState.frame) := by',
          '  obtain ⟨out,ran,family,_⟩ := Proofs.DynamicDeclareOwned.sound rowsParams rowsHeap (resources rowsFrame) rowsState rowsFamily i32 false (by decide +kernel)',
          '  have same : emptyState = out := by simp [emptyState,ran]',
          '  have count : rowsState.frame.state.storage.objects.length = 10 := by decide +kernel',
          '  have description : Proofs.DynamicDeclareOwned.parameter rowsState i32 false = p4 := by decide +kernel',
          '  rw [count,description] at family',
          '  rw [same]; exact family',
          'def filledNext := (emptyState.frame.state.fillVector i32 3 3 (-7)).getD emptyState.frame.state',
          'theorem filledRun : emptyState.frame.state.fillVector i32 3 3 (-7) = some filledNext := by decide +kernel',
          'def filledBase := grown emptyState.frame filledNext true 0',
          'def filledFrame : Frame := (filledBase.bindRoot 11 atom 3 true).getD (filledBase,5) |>.fst',
          'def filledHeap := put emptyHeap 11 (.flat i32 3 [-7,-7,-7])',
          'def p5 : Parameter := ⟨5,11,atom,3,true,true⟩',
          'def filledParams := emptyParams ++ [p5]',
          'theorem filledFamily : Family filledParams filledHeap filledFrame (resources filledFrame) := by',
          '  have base := Proofs.DynamicAllocateFamily.filled emptyFamily filledNext i32 3 3 (-7) true filledRun',
          '  have count : emptyState.frame.state.storage.objects.length = 11 := by decide +kernel',
          '  have slots : emptyState.frame.bindings.length = 5 := by decide +kernel',
          '  rw [count] at base',
          '  have flag := new_flag emptyFamily filledNext true 0',
          '  rw [count] at flag',
          '  obtain ⟨frame,ran,post⟩ := register base 11 (.flat i32 3 [-7,-7,-7]) (by decide +kernel) true flag',
          '  simp only [View.element,View.scope,grown] at ran post',
          '  rw [slots] at ran post',
          '  change filledBase.bindRoot 11 atom 3 true = some (frame,5) at ran',
          '  have same : filledFrame = frame := by unfold filledFrame; rw [ran]; rfl',
          '  rw [same]; exact Family.remeasured post',
          'def filledState : NState := {emptyState with frame := filledFrame,slots := emptyState.slots ++ [.vector 5]}',
          'theorem filledReal : Realizes filledParams (snapshot filledState) (eraseHeap filledHeap) filledState := of_family filledParams filledHeap _ filledState filledFamily',
          'example := Family.fresh family',
          'example := Family.fresh rowsFamily',
          'example := Family.fresh emptyFamily',
          'example (ps : List Parameter) (h : Heap) (f : Frame) (m : Resources) (valid : Family ps h f m) (next : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope count : Nat) (run : f.state.constructRows ty scope count = some next) := Proofs.DynamicAllocateFamily.rows valid next ty scope count true run',
          'example (ps : List Parameter) (h : Heap) (m : Resources) (s : NState) (valid : Family ps h s.frame m) (ty : Ty) (wr : Bool) (supported : Proofs.CppVectorBindings.supported ty) := Proofs.DynamicDeclareOwned.sound ps h m s valid ty wr supported',
          'def readFilled : NExpr := .read i32 (.local 7) (.literal i32 1)',
          'example := Proofs.DynamicExprCertified.sound (Proofs.DynamicExprDerive.derive (Proofs.DynamicExprAuto.ready filledParams (snapshot filledState) (eraseHeap filledHeap) readFilled) (-7) (by decide +kernel)) filledState filledReal',
          '#guard (Proofs.DynamicExpr.denote filledParams (snapshot filledState) (eraseHeap filledHeap) (.size row (.local 5))) == some 2',
          '#guard filledState.frame.rootWritable[10]? == some false',
          '#guard filledState.frame.rootWritable[0]? == some true',
          '#guard filledState.frame.state.storage.lookup 2 == state.frame.state.storage.lookup 2',
          '#guard (filledState.frame.state.storage.lookup 3).isNone',
          '#guard ((NStmt.append (.local 6) i32 (.literal i32 1)).run filledState).isNone',
          'def append : NStmt := .append (.row (.local 5) atom (.literal i32 0)) i32 readFilled',
          'def beforeAppend : Proofs.DynamicStmt.State := ⟨snapshot filledState,eraseHeap filledHeap⟩',
          'def afterAppend : Proofs.DynamicStmt.Step := ⟨⟨snapshot filledState,putContents (eraseHeap filledHeap) 7 (.rows i32 3 [[-7],[]])⟩,none⟩',
          'theorem pureAppend : Proofs.DynamicStmt.run filledParams append beforeAppend = some afterAppend := by cbv',
          'theorem available : Proofs.DynamicAppendAuto.Available filledParams beforeAppend filledState append := by',
          '  intro p k selected index',
          '  have chosen : Proofs.DynamicStmt.mutableRoot filledParams beforeAppend 5 (.vector atom) = some p3 := by decide +kernel',
          '  have same : p = p3 := Option.some.inj (selected.symm.trans chosen); subst p',
          '  have zero : (k : Int) = 0 := Option.some.inj index.symm',
          '  have natural : k = 0 := by omega',
          '  subst k',
          '  exact ⟨(filledState.frame.state.storage.lookup 7).getD ⟨0,[],0,64,0⟩,8,(filledState.frame.state.storage.lookup 8).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩',
          'def appended := (append.run filledState).getD ⟨filledState,none,false⟩ |>.state',
          'theorem appendedReal : Realizes filledParams afterAppend.state.locals afterAppend.state.contents appended := by',
          '  obtain ⟨out,ran,matched,_⟩ := Proofs.DynamicStmtEffects.sound filledParams beforeAppend filledState filledReal append afterAppend pureAppend available',
          '  have same : appended = out.state := by simp [appended,ran]',
          '  rw [same]; exact matched.state',
          'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
          'def final : Proofs.DynamicStmt.State := ⟨snapshot state,Proofs.DynamicRetire.retireContents afterAppend.state.contents 3⟩',
          'theorem finalReal : Realizes params final.locals final.contents (Proofs.DynamicOwnedScope.left state appended) := by',
          '  apply (Proofs.DynamicOwnedScope.sound params filledParams st0 afterAppend.state final state appended realizes appendedReal ?_ ?_ none (by cbv)).2.1',
          '  · intro p member; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))',
          '  · intro p member; simp [params] at member; rcases member with rfl|rfl|rfl <;> decide +kernel',
          '#guard [7,8,9,10,11].all (fun owner => ((Proofs.DynamicOwnedScope.left state appended).frame.state.storage.lookup owner).isNone)',
          '#guard final.contents 0 == logical 0',
          '#guard final.contents 2 == logical 2',
          'def zeroNext := (state.frame.state.constructRows i32 3 0).getD state.frame.state',
          'example := Proofs.DynamicAllocateFamily.rows family zeroNext i32 3 0 false (by decide +kernel)',
          '#guard (state.frame.state.constructRows i32 3 (Proofs.CppNestedConstruct.rowLimit+1)).isNone',
          '#guard (state.frame.state.fillVector i32 3 1 2147483648).isNone',
          '#guard (state.frame.state.fillVector i32 3 (Proofs.CppVectorBindings.sizeLimit i32+1) 0).isNone']
        with tempfile.TemporaryDirectory(prefix='dynamic-allocate-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            (scratch/'helper.hpp').write_text('namespace cp {int narrow(unsigned long long x){return x;}}\n')
            checked = lower_source(source)
            selected = lower_source(source, signed_conversion=SIGNED_CONVERSIONS[1])
            self.assertNotIn('signed_conversion', checked)
            self.assertEqual(selected['signed_conversion'], SIGNED_CONVERSIONS[1])
            generated=emit_lean(selected,'AllocateSource')
            checked_lean=emit_lean(checked,'CheckedAllocate')
            with self.assertRaisesRegex(ValueError,'unsupported signed conversion contract'):
                lower_source(source,signed_conversion='wrap-arithmetic')
            checks[0]='import Proofs.DynamicDeclareOwned\nimport Proofs.DynamicReadSound\n'+generated+checked_lean.replace('import Proofs.CppNestedCall\n','')+HEADER.replace('import Proofs.DynamicReadSound\n','')
            checks += ['#guard (match CheckedAllocate.allocate.callFuel 600 state [.vectorReference 1] with | .fault => true | _ => false)',
              'def call := AllocateSource.allocate.callFuel 600 state [.vectorReference 1]',
              'def converted := AllocateSource.convert.callFuel 600 state [.vectorReference 2,.value (.literal ⟨64,false,false⟩ 18446744073709551615)]',
              '#guard (match converted with | .finished (_, .scalar x) => x == -1 | _ => false)',
              '#guard (match CheckedAllocate.convert.callFuel 600 state [.vectorReference 2,.value (.literal ⟨64,false,false⟩ 18446744073709551615)] with | .fault => true | _ => false)',
              '#guard (match call with | .finished (s,.scalar x) => x == -5 && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && [7,8,9,10,11].all (fun owner => (s.frame.state.storage.lookup owner).isNone) | _ => false)']
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler();source=scratch/'native.cpp';exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};std::cout<<cp::allocate(g)<<std::endl;std::vector<int>v{77};std::cout<<cp::convert(v,18446744073709551615ULL)<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout.splitlines(),['-5','-1'])

if __name__=='__main__':
    disable_network();unittest.main()
