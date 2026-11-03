"""Constructed receiver readiness and actual getter calls using stored _n."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
 theorem populatedStrict : ∀ owner scope, populated.frame.state.forest.context owner = some scope → scope ≤ populated.scope := by
   intro owner scope found
   have inside := Proofs.UfConstructedReceiver.context_inside populated.frame.state.forest owner scope found
   have len : populated.frame.state.forest.objects.length = 1 := by decide +kernel
   have eq : owner = 0 := by rw [len] at inside; omega
   subst owner
   have context : populated.frame.state.forest.context 0 = some 0 := by decide +kernel
   rw [context] at found
   cases found
   exact Nat.zero_le _
 example := Proofs.UfConstructedReceiver.sized_ready populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
   (.variable i32 2) 2 (by decide) rfl rfl (by decide +kernel)
 example := Proofs.UfConstructedReceiver.sized_getter populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
   (.variable i32 2) 2 (by decide) rfl rfl (by decide +kernel)
 example := Proofs.UfConstructedReceiver.default_getter populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
 def getter (s : NState) : Outcome (NState × Ret) :=
   Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel 64 s
     [.vectorReference populated.slots.length,.scalarReference (populated.slots.length+1),
      .value (.variable i32 (populated.slots.length+2))]
 def freshGetter (n : Nat) : Bool := match UnionFind_construct1.constructFuel 8 populated
     [.value (.literal i32 n)] (Proofs.UfConstructionExport.vectorField true) (.integer i32)
     (Proofs.UfConstructionExport.fields true) with
   | .finished (s,_) => match getter s with
     | .finished (out,.scalar count) => count == n && out.scalars.memory == s.scalars.memory &&
         out.frame.bindings == s.frame.bindings && out.frame.rootWritable == s.frame.rootWritable &&
         out.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0
     | _ => false
   | _ => false
 #guard freshGetter 0
 #guard freshGetter 1
 #guard freshGetter 2
 #guard freshGetter 17
 #guard (match UnionFind_construct0.constructFuel 8 populated [] (Proofs.UfConstructionExport.vectorField false)
     (.integer i32) (Proofs.UfConstructionExport.fields false) with
   | .finished (s,_) => match getter s with
     | .finished (out,.scalar count) => count == 0 && out.scalars.memory == s.scalars.memory &&
         out.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0
     | _ => false
   | _ => false)
 example (c : NState) (h : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state h) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (strict : ∀ owner scope, c.frame.state.forest.context owner = some scope → scope ≤ c.scope)
   (base : c.scalars.baseMemory ≤ c.scalars.memory.length)
   (e : NExpr) (n : Nat) (endpoint : n = 2147483647) (scalar : e.scalarOnly = true)
   (ty : e.resultType = i32) (value : e.denote (Proofs.CppNestedEval.envOf c) = some (n : Int)) :=
   Proofs.UfConstructedReceiver.sized_getter c h valid models lengths strict base e n (by omega) scalar ty value
'''
class UnionFindConstructedReceiverTests(unittest.TestCase):
    def test_receiver_preconditions_and_stored_field_getter(self):
        with tempfile.TemporaryDirectory(prefix='uf-constructed-receiver-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfConstructedReceiver\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__ == '__main__':
    disable_network()
    unittest.main()
