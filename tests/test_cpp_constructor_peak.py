"""Allocation and field export peaks with existing caller storage and aliases."""
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
open Proofs.CppConstructorPeak Proofs.CppConstructorFinish Proofs.UfConstructionStage
open Proofs.DynamicOwnedState Proofs.DynamicContents Proofs.DynamicExpr
 def init : NState := (prepare populated UnionFind_construct1.parameters [.value (.literal i32 3)]).getD populated
 theorem initReal : Realizes
     (entry (Proofs.DoublingCall.callerP populated) (eraseHeap noHeap) []
       populated.frame.state.storage.objects.length 0 (populated.scope+1) 3) init := by
   apply Proofs.UfConstructionPrepare.sized_real populated init noHeap (by decide +kernel)
     (noModels populated) (by decide +kernel) 3 <;> decide +kernel
 def filled : NState := match (NStmt.fillVector i32 true countExpr valueExpr).run init with
   | some step => step.state
   | none => init
 example := fill_peak _ init filled initReal i32 true countExpr valueExpr 3 (-1)
   (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) rfl (by decide +kernel)
 def declared : NState := match (NStmt.declare i32 true argument).run filled with
   | some step => step.state
   | none => filled
 theorem filledReal : Realizes
     (vectorState (Proofs.DoublingCall.callerP populated) (eraseHeap noHeap) []
       populated.frame.state.storage.objects.length 0 (populated.scope+1) 3) filled := by
   obtain ⟨out,ran,real⟩ := Proofs.UfConstructionFootprint.execute _ _ init initReal
     (.fillVector i32 true countExpr valueExpr)
     (fill_step _ _ _ _ _ _ 3 (by decide))
   have same : filled = out := by simp [filled,ran]
   rwa [same]
 example := scalar_peak _ _ filled declared filledReal (.declare i32 true argument) (by trivial)
   (count_step _ _ _ _ _ _ 3 (by decide)) (by decide +kernel)
 def defaultInit : NState := (prepare populated UnionFind_construct0.parameters []).getD populated
 def allocated : NState := match (NStmt.declareVector i32 true).run defaultInit with
   | some step => step.state
   | none => defaultInit
 example := empty_peak defaultInit allocated i32 true (by decide +kernel)
 def callee : NState := match stageOn UnionFind_construct1 [.value (.literal i32 3)] with
   | .finished step => step.state
   | _ => populated
 def exported := (finish populated callee (Proofs.UfConstructionExport.vectorField true) (.integer i32)
   (Proofs.UfConstructionExport.fields true)).getD (populated,reference populated 2)
 example := finish_peak populated callee exported.1 (Proofs.UfConstructionExport.vectorField true) (.integer i32)
   (Proofs.UfConstructionExport.fields true) (Proofs.UfConstructionExport.payload 3 3) exported.2
   (by decide +kernel) (by decide +kernel) (by decide +kernel)
 #guard exported.1.scalars.memory.length == populated.scalars.memory.length+2
 #guard Proofs.CppNestedEval.liveS exported.1 == Proofs.CppNestedEval.liveS populated+4
 #guard exported.1.frame.state.storage.lookup 0 == some oldBuffer
 #guard exported.1.frame.state.storage.lookup 1 == some ⟨1,List.replicate 3 (.integer (-1)),3,
   Proofs.CppVectorBindings.sizeLimit i32,0⟩
 def high : NState := {populated with peak := 900,scalars := {populated.scalars with peak := 700}}
 def binding : Binding := ⟨1,.integer i32,true,.root 1⟩
 example := restored_peak high callee exported.1.frame binding [] (by decide +kernel) (by decide +kernel)
 example := restored_peak high callee exported.1.frame binding (Proofs.UfConstructionExport.payload 3 3)
   (by decide +kernel) (by decide +kernel)
 #guard (restored high callee exported.1.frame binding (Proofs.UfConstructionExport.payload 3 3)).peak ≥ 900
 def based : NState := {populated with scalars := {populated.scalars with baseMemory := populated.scalars.memory.length}}
 example := restored_live based callee exported.1.frame binding (Proofs.UfConstructionExport.payload 3 3)
   (by decide +kernel) (by decide +kernel)
 example (caller callee : NState) (frame : Frame) (binding : Binding) (values : List ScalarValue)
   (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
   (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :=
   restored_peak caller callee frame binding values fits base
'''

class ConstructorPeakTests(unittest.TestCase):
    def test_allocation_scalar_and_field_export(self):
        with tempfile.TemporaryDirectory(prefix='cpp-constructor-peak-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppConstructorPeak\nimport Proofs.UfConstructionWork\n'
                             + HEADER + CALLER_HEADER + STAGE_CHECKS + CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
