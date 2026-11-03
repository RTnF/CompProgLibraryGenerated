"""Exact write/retire peaks and storage bounds independent of UF trace length."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_dynamic_expr import fixture_checks
from test_cpp_no_resize import CHECKS as SCALAR_CHECKS
from test_cpp_call_metadata import CONTROL
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_union_find_constructed_receiver import CHECKS as RECEIVER_CHECKS
from test_union_find_receiver_trace import CHECKS as TRACE_CHECKS
from test_union_find_rank_doubling import CHECKS as RANK_CHECKS
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
NESTED = '''
 example := Proofs.CppWritePeak.stmt_write_peak state written (.row (.local 0) atom idx) i32 pos (.literal i32 42) (by decide +kernel)
 example := Proofs.CppStoragePeak.run_peak 128 flowBody state result (by decide +kernel) contexts (by decide +kernel)
 #guard result.state.frame.state.storage.peak == Proofs.CppStoragePeak.bound state
 example := Proofs.CppStoragePeak.run_peak 32 early state earlyResult (by decide +kernel) contexts (by decide +kernel)
 example := Proofs.CppStoragePeak.run_peak 16 broken state brokenResult rfl contexts (by decide +kernel)
 example := Proofs.CppCallStoragePeak.call_peak nestedProgram 8 state nestedOut nestedArgs (.scalar (-3)) i32
   rfl rfl contexts (by decide +kernel)
 def saturated : NState := {state with frame := {state.frame with state := {state.frame.state with storage :=
   {state.frame.state.storage with baseSpace := state.frame.state.liveSpace+100,peak := 0}}}}
 #guard saturated.frame.state.wellFormed
 def saturatedWrite : NStep := (write.run saturated).getD ⟨saturated,none,false⟩
 example := Proofs.CppWritePeak.stmt_write_peak saturated saturatedWrite (.row (.local 0) atom idx) i32 pos (.literal i32 42) (by decide +kernel)
 #guard Proofs.CppStoragePeak.bound saturated == 0
 #guard saturatedWrite.state.frame.state.storage.peak == 0
 def retired : Frame := (state.frame.retireScope (state.scope+1)).getD state.frame
 theorem fresh : ∀ owner, state.frame.state.forest.context owner ≠ some (state.scope+1) := by
   intro owner found
   have bound := contexts owner (state.scope+1) found
   omega
 example := Proofs.CppWritePeak.retire_peak state.frame retired (state.scope+1) fresh (by decide +kernel)
 #guard retired.state.storage.peak == max state.frame.state.storage.peak
   (state.frame.state.liveSpace-state.frame.state.storage.baseSpace)
 example (fuel : Nat) (command : Command) (s : NState) (out : NStep)
   (allowed : Proofs.CppNoResizeScope.Allowed command = true)
   (ctx : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
   (ran : Proofs.CppNestedProgram.runFuel fuel command s = .finished out) :=
   Proofs.CppStoragePeak.run_peak fuel command s out allowed ctx ran
'''
UF = '''
 theorem builtContexts : ∀ owner scope, built.frame.state.forest.context owner = some scope → scope ≤ built.scope := by
   obtain ⟨buf,cb,nb,inv⟩ := builtRep
   exact inv.ok.strict
 def twice := mixed++mixed
 theorem twiceAllowed : ∀ op ∈ twice, op.allowed 4 := by
   intro op member
   rcases List.mem_append.mp member with h|h <;> exact mixedAllowed op h
 def twiceRun := runCalls (List.replicate twice.length 128) twice built (layoutOf populated)
 def twiceOut : NState := match twiceRun with | .finished (out,_) => out | _ => built
 def twiceAnswers : List Int := match twiceRun with | .finished (_,answers) => answers | _ => []
 theorem twiceActual : runCalls (List.replicate twice.length 128) twice built (layoutOf populated) =
   .finished (twiceOut,twiceAnswers) := by decide +kernel
 theorem storageBound : twiceOut.frame.state.storage.peak ≤ Proofs.CppStoragePeak.bound built :=
   Proofs.UfUniformStoragePeak.actual_calls (List.replicate twice.length 128) twice built (layoutOf populated)
     twiceOut twiceAnswers builtContexts twiceActual
 #guard twiceAnswers.length == 24
 #guard twiceOut.frame.state.storage.peak <= Proofs.CppStoragePeak.bound built
 #guard twiceOut.frame.state.liveSpace == built.frame.state.liveSpace
 #guard twiceOut.frame.state.storage.baseSpace == built.frame.state.storage.baseSpace
 def onceOut : NState := match executed with | .finished (out,_) => out | _ => built
 #guard twiceOut.frame.state.storage.peak == onceOut.frame.state.storage.peak
 example := Proofs.UfUniformStoragePeak.calls_components twice built (layoutOf populated)
   (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong twiceAllowed
 example := Proofs.UfUniformStoragePeak.calls_components [] built (layoutOf populated)
   (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong (by simp)
 example (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
   (ctx : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
   (ran : call fuel s layout op = .finished (out,ret)) :=
   Proofs.UfUniformStoragePeak.call_peak fuel s out layout op ret ctx ran
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (strong : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   Proofs.UfUniformStoragePeak.calls_components ops s layout ps count rank strong allowed
'''

class StoragePeakTests(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory(prefix='uf-storage-peak-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text(source)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_nested_control_and_saturating_storage_baseline(self):
        self.check('import Proofs.CppCallStoragePeak\nimport Proofs.Generated.UnionFindCandidate\n'
                   +'\n'.join(fixture_checks())+SCALAR_CHECKS+CONTROL+NESTED)

    def test_actual_uf_history_and_joint_components(self):
        self.check('import Proofs.UfUniformStoragePeak\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+RECEIVER_CHECKS
                   +TRACE_CHECKS+RANK_CHECKS+UF)

if __name__ == '__main__':
    disable_network()
    unittest.main()
