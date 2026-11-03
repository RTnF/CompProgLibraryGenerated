"""Non-resizing execution payload restoration and full Frame/Context projection."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from check_public import check_compiler
from test_cpp_move_headers import CHECKS as HEADER_CHECKS
from test_cpp_move_frame import CHECKS as FRAME_CHECKS
from test_cpp_move_write import CHECKS as WRITE_CHECKS
from test_cpp_move_context import CHECKS as CONTEXT_CHECKS
from offline import disable_network

CHECKS = r'''

namespace RestoreExamples
open Proofs.CppMoveRestore Proofs.CppMoveContext Proofs.CppNestedProgram
open HeaderMoveExamples ViewExamples FrameExamples ContextExamples

def before := callerContext
def command : Command := .sequence (.primitive (.write (.local 3) ty (.literal ty 0) (.literal ty 42)))
  (.sequence (.primitive (.write (.local 3) ty (.literal ty 1) (.literal ty 43)))
    (.primitive (.assign 1 ty (.literal ty 9))))
def evaluated : NStep := match runFuel 8 command (project before ty) with
  | .finished step => step
  | _ => ⟨project before ty,none,false⟩
theorem evaluatedRun : runFuel 8 command (project before ty) = .finished evaluated := by decide +kernel
#guard evaluated.state.frame.state.wellFormed
#guard evaluated.state.scalars.memory.map (·.value) == [9]
#guard (restore before.objects ty evaluated.state.frame).isSome
#guard (restoreContext before ty evaluated.state).isSome
def restored := (restoreContext before ty evaluated.state).getD before
#guard restored.scalars.memory.map (·.value) == [9]
#guard Proofs.CppMoveHeaders.read restored.objects.heap ty.valid 0 == some 43
#guard Proofs.CppMoveHeaders.read restored.objects.heap ty.valid 1 == some 42
#guard restored.objects.heap.header 0 == before.objects.heap.header 0
#guard restored.objects.heap.header 1 == before.objects.heap.header 1
#guard restored.objects.heap.grants == before.objects.heap.grants
#guard (restored.objects.heap.allocation 0).map (fun t => t.generation 1) == some 7
#guard (restored.objects.heap.allocation 1).isNone
#guard work restored == work before+12
#guard work restored == evaluated.state.work
#guard restored.peak == evaluated.state.peak
#guard restored.objects.heap.peak == evaluated.state.frame.state.storage.peak

theorem restoredRun : restoreContext before ty evaluated.state = some restored := by
  have live : (restoreContext before ty evaluated.state).isSome = true := by decide +kernel
  have nonempty : restoreContext before ty evaluated.state ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty before).symm
example := restoreContext_metadata before restored ty evaluated.state restoredRun

theorem contexts : ∀ owner scope, (project before ty).frame.state.forest.context owner = some scope → scope ≤ before.scope := by
  intro owner scope found
  have forestEq : (project before ty).frame.state.forest =
    ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 1,[]⟩,none]⟩ := rfl
  rw [forestEq] at found
  rcases owner with _ | owner
  · have ctx := context_of_root ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 1,[]⟩,none]⟩ 0 ⟨.integer ty,none,some 0,[]⟩ rfl rfl
    rw [ctx] at found
    cases Option.some.inj found
    decide
  rcases owner with _ | owner
  · rw [context_of_none ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 1,[]⟩,none]⟩ 1 rfl] at found
    contradiction
  rcases owner with _ | owner
  · have ctx := context_of_root ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 1,[]⟩,none]⟩ 2 ⟨.integer ty,none,some 1,[]⟩ rfl rfl
    rw [ctx] at found
    cases Option.some.inj found
    decide
  rcases owner with _ | owner
  · rw [context_of_none ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 1,[]⟩,none]⟩ 3 rfl] at found
    contradiction
  · rw [context_of_none ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 1,[]⟩,none]⟩ (owner+4) rfl] at found
    contradiction

example := command_restore_ready before ty 8 command evaluated (by decide) contexts evaluatedRun transferredCovered (by decide +kernel)

def resized := ((project before ty).frame.reserve 5 (.integer ty) 8).getD (project before ty).frame
#guard ((project before ty).frame.reserve 5 (.integer ty) 8).isSome
#guard (restore before.objects ty resized).isNone
#guard (restore before.objects ty {evaluated.state.frame with rootWritable := []}).isNone
#guard (restoreContext before ty {evaluated.state with scope := 99}).isNone
#guard (restoreContext before ty {evaluated.state with slots := []}).isNone
#guard (restoreContext before ty {evaluated.state with scalars := {evaluated.state.scalars with baseMemory := 99}}).isNone

def nested : Proofs.CppNestedVectorBindings.Frame := {evaluated.state.frame with state := {evaluated.state.frame.state with storage := {evaluated.state.frame.state.storage with objects := evaluated.state.frame.state.storage.objects.set 0 (some ⟨0,[.child 0,.integer 43],4,8,2⟩)}}}
#guard shape nested == shape evaluated.state.frame
#guard (restore before.objects ty nested).isNone

def stale : Proofs.CppMoveViews.State Int := {before.objects with heap := {before.objects.heap with grants := before.objects.heap.grants.map (fun g => {g with reference := {g.reference with generation := 6}})}}
#guard (Proofs.CppMoveHeaders.read stale.heap ty.valid 0).isNone
#guard (restore stale ty evaluated.state.frame).isSome
#guard ((restore stale ty evaluated.state.frame).bind (fun s => Proofs.CppMoveHeaders.read s.heap ty.valid 0)).isNone

def objects := (restore before.objects ty evaluated.state.frame).getD before.objects
theorem objectsRun : restore before.objects ty evaluated.state.frame = some objects := by
  have live : (restore before.objects ty evaluated.state.frame).isSome = true := by decide +kernel
  have nonempty : restore before.objects ty evaluated.state.frame ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty before.objects).symm
example := restore_metadata before.objects objects ty evaluated.state.frame objectsRun
example := restore_allocation before.objects objects ty evaluated.state.frame objectsRun 0 ⟨⟨0,[10,11],4,8,2⟩,fun _ => 7⟩ rfl
example := restore_dead before.objects objects ty evaluated.state.frame objectsRun 1 rfl
example := restore_allocationsValid before.objects objects ty evaluated.state.frame objectsRun
example := restore_unique before.objects objects ty evaluated.state.frame objectsRun transferredUnique
example := restore_ownsAll before.objects objects ty evaluated.state.frame objectsRun transferredCovered
example := restore_headersLive before.objects objects ty evaluated.state.frame objectsRun SpaceExamples.transferredLive
example := restore_grantBounds before.objects objects ty evaluated.state.frame objectsRun
  (Proofs.CppMoveWrite.assign_grantBounds initial transferred HeaderMoveExamples.allow 3 0 transferredRun WriteExamples.initialGrantBounds)
example := restore_liveSpace before.objects objects ty evaluated.state.frame objectsRun
example := restore_baseSpace before.objects objects ty evaluated.state.frame objectsRun
#guard objects.heap.liveSpace == before.objects.heap.liveSpace
example := restore_no_resurrection before.objects objects ty evaluated.state.frame objectsRun transferredValid 999 rfl

def staleObjects := (restore stale ty evaluated.state.frame).getD stale
theorem staleRun : restore stale ty evaluated.state.frame = some staleObjects := by
  have live : (restore stale ty evaluated.state.frame).isSome = true := by decide +kernel
  have nonempty : restore stale ty evaluated.state.frame ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty stale).symm
example := restore_no_resurrection stale staleObjects ty evaluated.state.frame staleRun transferredValid 0 rfl
example := restoreContext_ready before ty evaluated.state (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (Proofs.CppNoResizeRun.run_headers 8 command (project before ty) evaluated (by decide) contexts evaluatedRun).headers
  (Proofs.CppNoResizeRun.run_headers 8 command (project before ty) evaluated (by decide) contexts evaluatedRun).flags
  transferredCovered (by decide +kernel)

example := restore_materialize_allocation before.objects objects ty evaluated.state.frame objectsRun transferredCovered 0 (by decide)
example := restore_materialize_allocation before.objects objects ty evaluated.state.frame objectsRun transferredCovered 1 (by decide)
example := restore_bindings before.objects objects ty evaluated.state.frame objectsRun
#guard (Proofs.CppMoveFrame.materialize objects ty).frame == evaluated.state.frame
#guard project restored ty == evaluated.state
example := restore_generations before.objects objects ty evaluated.state.frame objectsRun
example := restore_frame before.objects objects ty evaluated.state.frame objectsRun transferredCovered (by decide +kernel)
example := restoreContext_project before restored ty evaluated.state restoredRun transferredCovered

def empty : Proofs.CppMoveContext.Context := ⟨⟨⟨[some ⟨none,0,true,8⟩],[],[],0,0,0⟩,[⟨0,true⟩]⟩,
  ⟨[⟨ty,7⟩],[⟨0,true⟩],0,0,0⟩,[.vector 0,.scalar 0],0,0⟩
def emptyCommand : Command := .primitive (.assign 1 ty (.size (.integer ty) (.local 0)))
def emptyEvaluated : NStep := match runFuel 2 emptyCommand (project empty ty) with
  | .finished step => step
  | _ => ⟨project empty ty,none,false⟩
theorem emptyEvaluatedRun : runFuel 2 emptyCommand (project empty ty) = .finished emptyEvaluated := by decide +kernel
#guard (restoreContext empty ty emptyEvaluated.state).isSome
def emptyRestored := (restoreContext empty ty emptyEvaluated.state).getD empty
#guard emptyRestored.scalars.memory.map (·.value) == [0]
#guard emptyRestored.objects.heap.allocations.isEmpty
#guard emptyRestored.objects.heap.header 0 == some ⟨none,0,true,8⟩
#guard project emptyRestored ty == emptyEvaluated.state
theorem emptyRun : restoreContext empty ty emptyEvaluated.state = some emptyRestored := by
  have live : (restoreContext empty ty emptyEvaluated.state).isSome = true := by decide +kernel
  have nonempty : restoreContext empty ty emptyEvaluated.state ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty empty).symm
theorem emptyCovered : Proofs.CppMoveHeaders.OwnsAll empty.objects.heap := by
  intro owner tracked found
  simp [empty,Proofs.CppMoveHeaders.Heap.allocation] at found
example := restoreContext_project empty emptyRestored ty emptyEvaluated.state emptyRun emptyCovered
end RestoreExamples
'''

NATIVE = r'''

#include <cassert>
#include <utility>
#include <vector>
void update(std::vector<long long>& data,long long& scalar){
  data[0]=42;data[1]=43;scalar=9;
}
int main(){
  std::vector<long long> source{10,11},target{99};source.reserve(4);
  long long& writable=source[1];const long long& readonly=source[0];
  auto& sourceObject=source;auto* storage=source.data();
  target=std::move(source);
  long long scalar=7;update(target,scalar);
  assert(sourceObject.empty() && sourceObject.capacity()==0 && target.data()==storage);
  assert(target[0]==42 && target[1]==43 && writable==43 && readonly==42 && scalar==9);
  writable=55;assert(target[1]==55);
  std::vector<long long> empty;scalar=static_cast<long long>(empty.size());
  assert(scalar==0 && empty.capacity()==0);
}
'''

class MoveRestoreTests(unittest.TestCase):
    def test_full_projection_payloads_invariants_and_resources(self):
        with tempfile.TemporaryDirectory(prefix='move-restore-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveRestore\n'+HEADER_CHECKS+FRAME_CHECKS+WRITE_CHECKS+CONTEXT_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_native_writes_after_move_and_scalar_reference(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='move-restore-native-') as directory:
            source=Path(directory)/'check.cpp';binary=Path(directory)/'check'
            source.write_text(NATIVE)
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=address,undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0:abort_on_error=1'
            subprocess.run([str(binary)],env=env,check=True)

if __name__=='__main__':
    disable_network()
    unittest.main()
