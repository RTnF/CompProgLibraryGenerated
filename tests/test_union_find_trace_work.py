"""Generated calls preserve the strong receiver and accumulate logarithmic work bounds."""
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
 example := Proofs.UfTraceWork.constructed_calls_work populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
   (.literal i32 4) 4 (by decide) rfl rfl rfl mixed mixedAllowed
 example := Proofs.UfTraceWork.default_calls_work populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 #guard (match executed with
   | .finished (out,_) => out.work ≤ built.work + mixed.length * Proofs.UfTraceWork.budget 4
   | _ => false)
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (rep : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   Proofs.UfTraceWork.calls_work ops s layout ps count rank rep allowed
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (rep : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (endpoint : ps.length = 2147483647) (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
   ∃ fuels out vec nextCount nextRank answers,
     runCalls fuels ops s layout = .finished (out,answers) ∧
     Proofs.UfBalancedReceiver.Strong out layout vec nextCount nextRank ∧
     out.work ≤ s.work + ops.length * 5865 := by
   obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,represented,length,fl,al,work⟩ :=
     Proofs.UfTraceWork.calls_work ops s layout ps count rank rep allowed
   have fixed : Proofs.UfTraceWork.budget ps.length = 5865 := by rw [endpoint]; decide +kernel
   rw [fixed] at work
   exact ⟨fuels,out,vec,nextCount,nextRank,answers,ran,represented,work⟩
'''
class UnionFindTraceWorkTests(unittest.TestCase):
    def test_each_method_and_total_trace_work(self):
        with tempfile.TemporaryDirectory(prefix='uf-trace-work-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfTraceWork\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+RECEIVER_CHECKS+TRACE_CHECKS+RANK_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__ == '__main__':
    disable_network()
    unittest.main()
