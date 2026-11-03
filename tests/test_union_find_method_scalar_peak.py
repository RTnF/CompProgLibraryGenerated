"""All generated UF methods have scalar bounds independent of outer history."""
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
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.UfReceiverScalarPeak
 def hot : NState := {built with peak := 100000000}
 theorem hotRep : Represents hot (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) := by
   obtain ⟨buf,cb,nb,inv⟩ := builtRep
   refine ⟨buf,cb,nb,?_,inv.items,inv.bufferValid,inv.limit,inv.owner,inv.math,inv.countCell,inv.writable,inv.nCell,inv.different⟩
   exact ⟨inv.ok.valid,inv.ok.slot,inv.ok.binding,inv.ok.vtag,inv.ok.vfound,
     inv.ok.lengths,inv.ok.flag,inv.ok.strict,inv.ok.base⟩
 theorem hotStrong : Proofs.UfBalancedReceiver.Strong hot (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) :=
   ⟨hotRep,builtStrong.2⟩
 def probes : List Operation := [.root 3,.same 0 1,.size 3,.unite 0 1,.numGroups]
 theorem allowedProbes : ∀ op ∈ probes, op.allowed 4 := by
   intro op member
   simp [probes] at member
   rcases member with h|h|h|h|h <;> subst op <;> simp [Operation.allowed]
 def hotResult (op : Operation) : NState × Ret := match call 128 hot (layoutOf populated) op with
   | .finished result => result | _ => (hot,.unit)
 def coldResult (op : Operation) : NState × Ret := match call 128 built (layoutOf populated) op with
   | .finished result => result | _ => (built,.unit)
 def hotInit (op : Operation) : NState := (Proofs.CppNestedCall.prepare hot op.program.parameters
   (arguments (layoutOf populated)++op.extra)).getD hot
 theorem callsChecked : probes.all (fun op => decide (call 128 hot (layoutOf populated) op = .finished (hotResult op))) = true := by decide +kernel
 theorem preparesChecked : probes.all (fun op => decide (Proofs.CppNestedCall.prepare hot op.program.parameters
   (arguments (layoutOf populated)++op.extra) = some (hotInit op))) = true := by decide +kernel
 theorem boundsChecked : probes.all (fun op => decide (max (hotInit op).scalars.peak
   ((Proofs.DoublingCall.callerP hot).length+12-hot.scalars.baseMemory+100) ≤ 1000)) = true := by decide +kernel
 theorem eachPeak (op : Operation) (member : op ∈ probes) : (hotResult op).1.scalars.peak ≤ 1000 := by
   have ran : call 128 hot (layoutOf populated) op = .finished (hotResult op) := by
     simpa only [decide_eq_true_eq] using List.all_eq_true.mp callsChecked op member
   obtain ⟨init,prep,peak⟩ := call_peak 128 hot (hotResult op).1 (layoutOf populated)
     (List.replicate 4 (-1)) 4 (fun _ => 0) hotRep op (allowedProbes op member) (hotResult op).2 ran
   have prepared : Proofs.CppNestedCall.prepare hot op.program.parameters
     (arguments (layoutOf populated)++op.extra) = some (hotInit op) := by
     simpa only [decide_eq_true_eq] using List.all_eq_true.mp preparesChecked op member
   rw [prepared] at prep
   have eq := Option.some.inj prep
   subst init
   apply Nat.le_trans peak
   simpa only [decide_eq_true_eq] using List.all_eq_true.mp boundsChecked op member
 #guard probes.all (fun op => (hotResult op).1.scalars.peak == (coldResult op).1.scalars.peak)
 #guard probes.all (fun op => (hotResult op).1.peak >= 100000000)
 #guard probes.all (fun op => (hotResult op).1.scalars.memory == (coldResult op).1.scalars.memory)
 #guard probes.all (fun op => (hotResult op).1.frame.state == (coldResult op).1.frame.state)
 #guard probes.map (fun op => (hotResult op).2) == [.scalar 3,.scalar 0,.scalar 1,.scalar 0,.scalar 4]
 example := step_peak hot (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) hotStrong (.unite 0 1) (by constructor <;> decide)
 example (fuel : Nat) (s out : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (represented : Represents s layout ps count rank) (op : Operation) (allowed : op.allowed ps.length) (ret : Ret)
   (ran : call fuel s layout op = .finished (out,ret)) := call_peak fuel s out layout ps count rank represented op allowed ret ran
'''

class MethodScalarPeakTests(unittest.TestCase):
    def test_all_five_actual_methods_and_strong_work(self):
        with tempfile.TemporaryDirectory(prefix='uf-method-scalar-peak-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfReceiverScalarPeak\n'+HEADER+CALLER_HEADER+STAGE_CHECKS
                             +RECEIVER_CHECKS+TRACE_CHECKS+RANK_CHECKS+CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
