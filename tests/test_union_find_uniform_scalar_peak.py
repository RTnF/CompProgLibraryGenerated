"""Prepare bounds and a scalar peak independent of UF history length."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_union_find_constructed_receiver import CHECKS as RECEIVER_CHECKS
from test_union_find_receiver_trace import CHECKS as TRACE_CHECKS
from test_union_find_rank_doubling import CHECKS as RANK_CHECKS
from test_union_find_method_scalar_peak import CHECKS as METHOD_CHECKS
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
 example (op : Operation) (member : op ∈ probes) := Proofs.UfUniformScalarPeak.prepare_peak
   hot (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) hotRep op (allowedProbes op member)
 def longOps := mixed++mixed++mixed
 theorem longAllowed : ∀ op ∈ longOps, op.allowed 4 := by
   intro op member
   simp only [longOps,List.mem_append] at member
   rcases member with (h|h)|h <;> exact mixedAllowed op h
 def longRun := runCalls (List.replicate longOps.length 128) longOps hot (layoutOf populated)
 def longOut : NState := match longRun with | .finished (out,_) => out | _ => hot
 def longAnswers : List Int := match longRun with | .finished (_,answers) => answers | _ => []
 theorem longActual : runCalls (List.replicate longOps.length 128) longOps hot (layoutOf populated) =
   .finished (longOut,longAnswers) := by decide +kernel
 theorem uniformPeak : longOut.scalars.peak ≤ max hot.scalars.peak (Proofs.UfUniformScalarPeak.budget hot) :=
   Proofs.UfUniformScalarPeak.actual_calls_peak (List.replicate longOps.length 128) longOps hot (layoutOf populated)
     longOut longAnswers (List.replicate 4 (-1)) 4 (fun _ => 0) hotStrong longAllowed longActual
 #guard longAnswers.length == 36
 #guard longOut.peak >= 100000000
 #guard longOut.scalars.peak <= max hot.scalars.peak (Proofs.UfUniformScalarPeak.budget hot)
 #guard longOut.scalars.peak < 1000
 #guard longOut.frame.state.liveSpace == hot.frame.state.liveSpace
 #guard longOut.scalars.memory.length == hot.scalars.memory.length
 #guard Proofs.UfUniformScalarPeak.budget longOut == Proofs.UfUniformScalarPeak.budget hot
 def singleRun := runCalls (List.replicate mixed.length 128) mixed hot (layoutOf populated)
 def singleOut : NState := match singleRun with | .finished (out,_) => out | _ => hot
 #guard singleOut.scalars.peak == longOut.scalars.peak
 theorem longEffects : Proofs.CppCallFrame.CallEffects hot longOut :=
   Proofs.UfReceiverMetadata.actual_calls (List.replicate longOps.length 128) longOps hot (layoutOf populated)
     longOut longAnswers (by obtain ⟨buf,cb,nb,inv⟩ := hotRep; exact inv.ok.strict) longActual
 example := Proofs.UfUniformScalarPeak.budget_kept longEffects
 example := Proofs.UfUniformScalarPeak.calls_peak longOps hot (layoutOf populated)
   (List.replicate 4 (-1)) 4 (fun _ => 0) hotStrong longAllowed
 example := Proofs.UfUniformScalarPeak.calls_peak [] hot (layoutOf populated)
   (List.replicate 4 (-1)) 4 (fun _ => 0) hotStrong (by simp)
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (strong : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   Proofs.UfUniformScalarPeak.calls_peak ops s layout ps count rank strong allowed
 example (ops : List Operation) (first second : List Nat) (s : NState) (layout : Layout)
   (a b : NState × List Int) (one : runCalls first ops s layout = .finished a)
   (two : runCalls second ops s layout = .finished b) :=
   Proofs.UfUniformScalarPeak.run_calls_unique ops first second s layout a b one two
'''

class UniformScalarPeakTests(unittest.TestCase):
    def test_prepare_and_long_history_uniform_scalar_peak(self):
        with tempfile.TemporaryDirectory(prefix='uf-uniform-scalar-peak-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfUniformScalarPeak\n'+HEADER+CALLER_HEADER+STAGE_CHECKS
                             +RECEIVER_CHECKS+TRACE_CHECKS+RANK_CHECKS+METHOD_CHECKS+CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
