"""Restore caller grants and scalar prefix after a generated mixed call."""
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

ROOT = Path(__file__).resolve().parent.parent
SOURCE = '''#include <vector>
namespace cp {int touch(std::vector<std::vector<int>>& g,int& x){x=7;g[1].emplace_back(x);return g[1].size();}}
'''

class DynamicFinishTests(unittest.TestCase):
    def test_restore_after_generated_body(self):
        checks = fixture_checks()
        model_start = next(i for i,s in enumerate(checks) if s.startswith('theorem model :'))
        model_end = next(i for i,s in enumerate(checks) if s.startswith('theorem family :'))
        updated_model = '\n'.join(checks[model_start:model_end]).replace('theorem model :','theorem updatedModel :').replace('state.frame.state','out.state.frame.state').replace('base.state.storage','out.state.frame.state.storage').replace('0 view','0 updatedView')
        checks += ['open Proofs.DynamicFinish Proofs.DynamicControlBridge Proofs.CppNestedCall',
          'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
          'def args : List NArgument := [.vectorReference 0,.scalarReference 3]',
          'def resolvedArgs : List Proofs.CppNestedCall.Resolved := [.nestedRoot 0 0 i32 true,.scalarAddress i32 0 true]',
          'def callee := (prepare state FinishSource.touch.parameters args).getD state',
          'theorem prepared : prepare state FinishSource.touch.parameters args = some callee := by decide +kernel',
          'def cp := Proofs.DynamicFamilyInit.describe state.frame.rootWritable 0 resolvedArgs',
          'theorem cpKnown : cp = [⟨0,0,row,0,true,true⟩] := by decide +kernel',
          'def start : Proofs.DynamicStmt.State := ⟨snapshot callee,logical⟩',
          'theorem calleeReal : Realizes cp start.locals start.contents callee := by',
          '  obtain ⟨t,ran,real,_⟩ := Proofs.DynamicPrepareExists.prepare params st0 state realizes FinishSource.touch.parameters args resolvedArgs (by decide +kernel)',
          '  have same : t = callee := Option.some.inj (ran.symm.trans prepared)',
          '  subst t; exact real',
          'def out : NStep := match Proofs.CppNestedProgram.runFuel 300 FinishSource.touch.body callee with | .finished step => step | _ => ⟨callee,none,false⟩',
          'def updatedView : View := .rows i32 0 [1,4,5,6] 2 [[10,0],[17,-3,7],[],[]]',
          'def updatedHeap : Heap := put heap 0 updatedView',
          'def afterPure : Proofs.DynamicStmt.State := ⟨snapshot out.state,eraseHeap updatedHeap⟩',
          updated_model,
          'theorem afterFamily : Family cp updatedHeap out.state.frame (resources out.state.frame) := by',
          '  refine ⟨by decide +kernel,?_,by decide +kernel,?_,?_,?_,?_,measured_resources _⟩',
          '  · intro root v lookup',
          '    by_cases zero : root = 0',
          '    · subst root; simp [updatedHeap,put] at lookup; subst v; exact updatedModel',
          '    by_cases two : root = 2',
          '    · subst root; simp [updatedHeap,put,heap] at lookup; subst v; exact ⟨by decide +kernel,by decide +kernel,(out.state.frame.state.storage.lookup 2).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
          '    simp [updatedHeap,put,heap,zero,two] at lookup',
          '  · intro p member; have same : p = ⟨0,0,row,0,true,true⟩ := by simpa only [cpKnown,List.mem_singleton] using member',
          '    subst p; decide +kernel',
          '  · intro p member; have same : p = ⟨0,0,row,0,true,true⟩ := by simpa only [cpKnown,List.mem_singleton] using member',
          '    subst p; decide +kernel',
          '  · intro p member; have same : p = ⟨0,0,row,0,true,true⟩ := by simpa only [cpKnown,List.mem_singleton] using member',
          '    subst p; simp',
          '  · intro p member; have same : p = ⟨0,0,row,0,true,true⟩ := by simpa only [cpKnown,List.mem_singleton] using member',
          '    subst p; exact ⟨updatedView,by decide +kernel,rfl,rfl⟩',
          'theorem afterReal : Realizes cp afterPure.locals afterPure.contents out.state := of_family cp updatedHeap (resources out.state.frame) out.state afterFamily',
          'def pureOut : Proofs.DynamicControl.Step := ⟨afterPure,some 3,false⟩',
          'theorem matched : Matches cp pureOut out := ⟨afterReal,by decide +kernel,by decide +kernel⟩',
          'theorem actualRun : Proofs.CppNestedProgram.runFuel 300 FinishSource.touch.body callee = .finished out := by decide +kernel',
          'theorem pureRun : Proofs.DynamicControl.runFuel cp 300 FinishSource.touch.body start = .finished pureOut := by simp only [pureOut,afterPure,updatedHeap,erase_put]; cbv',
          'def final : Proofs.DynamicStmt.State := ⟨⟨[⟨i32,7⟩,⟨i32,1⟩],st0.locals.bindings,st0.locals.slots⟩,afterPure.contents⟩',
          'theorem pureFinish : Proofs.DynamicFinish.finish st0 afterPure (.scalar i32) (some 3) = some (final,.scalar 3) := by cbv',
          'theorem shapePreserved : SameShape st0.contents afterPure.contents := by simpa only [st0,afterPure,updatedHeap,erase_put,logical] using same_put logical 0 (erase view) (erase updatedView) (by decide +kernel) rfl',
          'theorem flags : ∃ extra, out.state.frame.rootWritable = state.frame.rootWritable ++ extra := ⟨[],by decide +kernel⟩',
          'theorem fresh : ∀ owner, out.state.frame.state.forest.context owner ≠ some out.state.scope := by',
          '  have scope : out.state.scope = state.scope+1 := by decide +kernel',
          '  rw [scope]; exact Proofs.DynamicScopeAuto.fresh_of_tags _ _ (by decide +kernel)',
          'theorem restoredReal : Realizes params final.locals final.contents (restored state out.state) := (Proofs.DynamicFinish.sound params cp st0 afterPure final state out.state realizes afterReal (.scalar i32) (some 3) (.scalar 3) pureFinish shapePreserved flags fresh).2.1',
          'example := Proofs.DynamicCallEffects.sound params st0 state realizes FinishSource.touch args resolvedArgs (by decide +kernel) (Proofs.DynamicForestEffects.NoScope.of_tags _ _ (by decide +kernel)) (by',
          '  intro initial ran real',
          '  have same : initial = callee := Option.some.inj (ran.symm.trans prepared)',
          '  subst initial',
          '  exact Runs.of_run pureRun actualRun matched ⟨rfl,⟨Proofs.DynamicPhysicalEffects.Authority.same (by decide +kernel) (by decide +kernel),by decide +kernel⟩,.scalar 3,by decide +kernel⟩)',
          '#guard (restored state out.state).scalars.memory == [⟨i32,7⟩,⟨i32,1⟩]',
          '#guard (restored state out.state).scalars.bindings == state.scalars.bindings',
          '#guard (restored state out.state).slots == state.slots',
          '#guard (restored state out.state).scope == state.scope',
          '#guard (restored state out.state).frame.bindings == state.frame.bindings',
          '#guard out.state.frame.bindings != state.frame.bindings',
          '#guard (restored state out.state).frame.state.storage.lookup 2 == state.frame.state.storage.lookup 2',
          '#guard (restored state out.state).work == out.state.work+1',
          'example := restored_peak state out.state (by decide +kernel)',
          'example := Proofs.DynamicFinish.sound params cp st0 afterPure final state out.state realizes afterReal .unit none .unit (by cbv) shapePreserved flags fresh',
          '#guard (Proofs.DynamicFinish.finish st0 afterPure (.scalar i32) (some 2147483648)).isNone',
          '#guard (Proofs.DynamicFinish.finish st0 afterPure .unit (some 3)).isNone',
          '#guard (Proofs.DynamicFinish.finish st0 afterPure (.scalar i32) none).isNone',
          '#guard (Proofs.DynamicFinish.finish st0 afterPure (.vector atom) none).isNone',
          'def wrong : Proofs.DynamicStmt.State := ⟨{afterPure.locals with memory := [⟨⟨64,false,false⟩,7⟩,⟨i32,1⟩]},afterPure.contents⟩',
          '#guard (Proofs.DynamicFinish.finish st0 wrong (.scalar i32) (some 3)).isNone',
          'def short : Proofs.DynamicStmt.State := ⟨{afterPure.locals with memory := []},afterPure.contents⟩',
          '#guard (Proofs.DynamicFinish.finish st0 short .unit none).isNone',
          'example : SameShape logical (putContents logical 0 (.rows i32 0 (values ++ [[]]))) := appendRoot_shape _ _ 0 i32 (by rfl)',
          'example : SameShape logical (putContents logical 0 (.rows i32 0 (values.set 1 [17,-3,7]))) := appendChild_shape _ _ 0 i32 1 7 (by rfl)',
          'example : ¬ SameShape logical (putContents logical 0 (.rows i32 9 values)) := by',
          '  intro same; have bad := same 0; have different : (some (.rows i32 9 values)).map shape ≠ (logical 0).map shape := by decide +kernel',
          '  exact different bad',
          'def owned : NState := ((NStmt.constructRows i32 true (.literal i32 0)).run callee).getD ⟨callee,none,false⟩ |>.state',
          'example : ¬ (∀ owner, owned.frame.state.forest.context owner ≠ some owned.scope) := by',
          '  intro fresh; exact fresh callee.frame.state.storage.objects.length (by decide +kernel)']
        with tempfile.TemporaryDirectory(prefix='dynamic-finish-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(SOURCE)
            generated=emit_lean(lower_source(fixture),'FinishSource')
            checks[0]='import Proofs.DynamicCallEffects\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n','')
            proof=scratch/'checks.lean'; proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); source=scratch/'native.cpp'; exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};int x=1;int r=cp::touch(g,x);std::cout<<r<<" "<<x<<" "<<g[1].back()<<" "<<g[1].capacity()<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout.splitlines(),['3 7 7 4'])

if __name__ == '__main__':
    disable_network();unittest.main()
