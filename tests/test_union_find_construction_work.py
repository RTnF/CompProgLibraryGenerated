"""Prepare/allocation/fields/finish work and constructor-to-finite-trace total work."""
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
 example := Proofs.UfConstructionWork.construct_sized_work populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
   (.variable i32 2) 2 (by decide) rfl rfl (by decide +kernel)
 example := Proofs.UfConstructionWork.construct_default_work populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
 example := Proofs.UfConstructionWork.constructed_trace_work populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
   (.literal i32 4) 4 (by decide) rfl rfl rfl mixed mixedAllowed
 example := Proofs.UfConstructionWork.default_trace_work populated noHeap (by decide +kernel)
   (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 def ctorBudget (n : Nat) : Bool := match UnionFind_construct1.constructFuel 8 populated [.value (.literal i32 n)]
     (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) with
   | .finished (out,_) => out.work ≤ populated.work + n + 31
   | _ => false
 #guard ctorBudget 0
 #guard ctorBudget 1
 #guard ctorBudget 2
 #guard ctorBudget 17
 #guard (match UnionFind_construct0.constructFuel 8 populated [] (Proofs.UfConstructionExport.vectorField false)
     (.integer i32) (Proofs.UfConstructionExport.fields false) with
   | .finished (out,_) => out.work ≤ populated.work+12
   | _ => false)
 #guard (match UnionFind_construct1.constructFuel 8 populated
     [.value (.binary i32 .add (.literal i32 2) (.literal i32 2))]
     (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) with
   | .finished (out,_) => out.work ≤ populated.work+3+4+30
   | _ => false)
 #guard (match executed with
   | .finished (out,_) => out.work ≤ populated.work+1+4+30+mixed.length*Proofs.UfTraceWork.budget 4
   | _ => false)
 example (caller : NState) (h : Proofs.CppRootModel.Heap) (valid : caller.frame.state.wellFormed = true)
   (models : Proofs.CppRootModel.HeapModels caller.frame.state h)
   (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
   (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
   (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (en : NExpr) (n : Nat)
   (endpoint : n = 2147483647) (scalar : en.scalarOnly = true) (ty : en.resultType = i32)
   (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int))
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed n) :=
   Proofs.UfConstructionWork.constructed_trace_work caller h valid models lengths strict base en n (by omega) scalar ty value ops allowed
'''
class UnionFindConstructionWorkTests(unittest.TestCase):
    def test_constructor_and_total_work(self):
        with tempfile.TemporaryDirectory(prefix='uf-construction-work-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfConstructionWork\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+RECEIVER_CHECKS+TRACE_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__ == '__main__':
    disable_network()
    unittest.main()
