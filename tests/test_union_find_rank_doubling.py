"""Reachable rank doubling, all generated method histories and logarithmic root work."""
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
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
 example := Proofs.UfRankDoubling.initial_balanced 0
 example := Proofs.UfRankDoubling.initial_balanced 1
 example (n : Nat) := Proofs.UfRankDoubling.initial_balanced n
 example := Proofs.UfRankDoubling.unite_balanced (Proofs.UfClassInvariant.initial_valid 4 (by decide))
   (Proofs.UfRankDoubling.initial_balanced 4) 0 1 ⟨-1,rfl,by decide⟩ ⟨-1,rfl,by decide⟩
 example : ¬ Proofs.UfRankDoubling.Balanced [-1] (fun _ => 5) := by
   intro balanced
   have impossible := balanced.rootZero 0 (-1) rfl (by decide)
   contradiction
 theorem builtStrong : Proofs.UfBalancedReceiver.Strong built (layoutOf populated)
     (List.replicate 4 (-1)) 4 (fun _ => 0) := by
   obtain ⟨s,ran,rep⟩ := Proofs.UfBalancedReceiver.construct_sized populated noHeap (by decide +kernel)
     (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
     (.literal i32 4) 4 (by decide) rfl rfl rfl
   have execution : UnionFind_construct1.constructFuel 8 populated [.value (.literal i32 4)]
     (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
       .finished (s,Proofs.CppConstructorFinish.reference populated 2) := ran
   have same : built = s := by unfold built; rw [execution]
   rwa [same]
 example := Proofs.UfBalancedReceiver.root_work built (layoutOf populated) (List.replicate 4 (-1)) 4
   (fun _ => 0) builtStrong 3 (by decide)
 example := Proofs.UfBalancedReceiver.constructed_calls populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
   (.literal i32 4) 4 (by decide) rfl rfl rfl mixed mixedAllowed
 example := Proofs.UfBalancedReceiver.default_calls populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 #guard (match Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 128 built
     (arguments (layoutOf populated) ++ [.value (.literal i32 3)]) with
   | .finished (out,.scalar r) => r == 3 && out.work ≤ built.work + 91*Nat.log2 4 + 142
   | _ => false)
 example (ps : List Int) (count : Int) (rank : Nat → Nat)
   (valid : Proofs.UfClassInvariant.Valid ps count rank) (balanced : Proofs.UfRankDoubling.Balanced ps rank)
   (i : Nat) (inside : i < ps.length) : rank i ≤ Nat.log2 ps.length :=
   Proofs.UfRankDoubling.rank_bound valid balanced i inside
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (rep : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   Proofs.UfBalancedReceiver.strong_calls ops s layout ps count rank rep allowed
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (rep : Proofs.UfBalancedReceiver.Strong s layout ps count rank) (endpoint : ps.length = 2147483647)
   (i : Nat) (inside : i < ps.length) : rank i ≤ 30 := by
   have bound := Proofs.UfBalancedReceiver.strong_rank_bound rep i inside
   rw [endpoint] at bound
   have value : Nat.log2 2147483647 = 30 := by decide +kernel
   rwa [value] at bound
'''
class UnionFindRankDoublingTests(unittest.TestCase):
    def test_balanced_history_and_actual_root_cost(self):
        with tempfile.TemporaryDirectory(prefix='uf-rank-doubling-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfBalancedReceiver\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+RECEIVER_CHECKS+TRACE_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__ == '__main__':
    disable_network()
    unittest.main()
