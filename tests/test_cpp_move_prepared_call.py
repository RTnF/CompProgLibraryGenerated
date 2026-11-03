"""Ghost-free call preparation, actual body/finish restoration and resource formulas."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_call_restore import UF_CHECKS
from offline import disable_network

CHECKS = r'''

namespace PreparedCallExamples
open Proofs.CppMovePreparedCall Proofs.CppMoveContext Proofs.CppNestedProgram
open Proofs.CppNestedCall Proofs.CppLoop Proofs.CppMoveHeaders
open UfMoveCallExamples
abbrev program := Proofs.UnionFindCandidateInstance.UnionFind_same
def initial := (prepareArguments moved.1 ty program.parameters args).getD moved.1
#guard initial.scalars.memory.length == 14
theorem preparedRun : prepareArguments moved.1 ty program.parameters args = some initial := by
  have live : (prepareArguments moved.1 ty program.parameters args).isSome = true := by decide +kernel
  have nonempty : prepareArguments moved.1 ty program.parameters args ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty moved.1).symm

def resolved := (resolveArguments moved.1 ty program.parameters args).getD (moved.1,[])
theorem resolvedRun : resolveArguments moved.1 ty program.parameters args = some resolved := by
  have live : (resolveArguments moved.1 ty program.parameters args).isSome = true := by decide +kernel
  have nonempty : resolveArguments moved.1 ty program.parameters args ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (moved.1,[])).symm
example := Proofs.CppMoveArgumentFacts.prepareArguments_resources moved.1 resolved.1 initial ty
  program.parameters args resolved.2 resolvedRun preparedRun (by decide +kernel)
def step : NStep := match runFuel 128 program.body (project initial ty) with
  | .finished step => step
  | _ => ⟨project initial ty,none,false⟩
theorem bodyRun : runFuel 128 program.body (project initial ty) = .finished step := by decide +kernel
def ended : NState × Ret := (Proofs.CppNestedCall.finish (project moved.1 ty) step.state program.result step.returned).getD (project moved.1 ty,.unit)
theorem finishRun : Proofs.CppNestedCall.finish (project moved.1 ty) step.state program.result step.returned = some ended := by decide +kernel
example := preparedCall_ready program 128 moved.1 initial ty Proofs.PrefixSumsCall.bT args step ended.1 ended.2
  rfl (by decide) contexts covered preparedRun bodyRun (by decide +kernel) finishRun


example := Proofs.CppNoResizeValid.run_valid 128 program.body (project initial ty) step
  (by decide) (by
    intro owner scope found
    have prep := prepareArguments_effects moved.1 initial ty program.parameters args preparedRun
    have state : (project initial ty).frame.state = (project moved.1 ty).frame.state := by
      simp only [project,Proofs.CppMoveFrame.materialize,prep.1]
    rw [state] at found
    change scope ≤ initial.scope
    rw [prep.2]
    exact Nat.le_trans (contexts owner scope found) (Nat.le_succ _)) (by decide +kernel) bodyRun
example := finish_ready (project moved.1 ty) step.state Proofs.PrefixSumsCall.bT 1
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
example := preparedCall_of_body program 128 moved.1 initial ty Proofs.PrefixSumsCall.bT args step.state 1
  rfl (by decide) contexts covered (by decide +kernel) preparedRun (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
example := finish_counters (project moved.1 ty) step.state ended.1 Proofs.PrefixSumsCall.bT step.returned ended.2 finishRun
def observation (r : Outcome (Context × Ret)) : Option (Ret × List Int × Option (List Int) × Nat × Nat × Nat × Nat) := match r with
  | .finished (out,result) => some (result,out.scalars.memory.map (·.value),
      (out.objects.heap.allocation 0).map (fun a => a.buffer.items),
      work out,out.peak,out.scalars.peak,out.objects.heap.peak)
  | _ => none
def originalCall := preparedCallFuel program 128 moved.1 ty args
#guard (observation originalCall).isSome
#guard (match originalCall with
  | .finished (out,result) => result == .scalar 1 &&
      Proofs.CppMoveHeaders.read out.objects.heap ty.valid 0 == some 0 &&
      (Proofs.CppMoveHeaders.read out.objects.heap ty.valid 1).isNone
  | _ => false)
def historical : Context := {moved.1 with objects := {moved.1.objects with heap :=
  {moved.1.objects.heap with grants := (List.replicate 100 moved.1.objects.heap.grants).flatten}}}
#guard historical.objects.heap.grants.length == 200
#guard (prepareArguments historical ty program.parameters args).map (fun s => s.scalars.memory.length) == some 14
#guard observation (preparedCallFuel program 128 historical ty args) == observation originalCall
#guard (match preparedCallFuel program 128 historical ty args with
  | .finished (out,_) => out.objects.heap.grants.length == 200
  | _ => false)
#guard (match preparedCallFuel program 0 moved.1 ty args with | .exhausted => true | _ => false)
end PreparedCallExamples
'''

class MovePreparedCallTests(unittest.TestCase):
    def test_uf_actual_call_normal_finish_and_ghost_history_resources(self):
        with tempfile.TemporaryDirectory(prefix='move-prepared-call-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMovePreparedCall\nimport Proofs.UfClassCopyBridge\n'
                'import Proofs.UfFieldsSame\nimport Proofs.UfFieldsSize\n'
                'import Proofs.UfFieldsUnite\nimport Proofs.UfFieldsCounter\n'+UF_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__=='__main__':
    disable_network()
    unittest.main()
