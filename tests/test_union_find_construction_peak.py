"""Actual constructor stages keep scalar peaks independent of vector length."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_cpp_constructor_peak import CHECKS as BASE_CHECKS
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.CppScalarComponents Proofs.UfConstructionPeak Proofs.CppNestedEval
 example := sized_stage_peak _ _ _ _ _ _ 3 (by decide) init initReal
 example := fill_components init filled i32 true countExpr valueExpr 3 (-1) rfl rfl
   (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
 example := declare_components filled declared i32 true argument 3 3 rfl
   (by decide +kernel) (by decide +kernel) (by decide +kernel)
 example := empty_components defaultInit allocated i32 true (by decide +kernel)
 theorem defaultReal : Realizes
     (defaultEntry (Proofs.DoublingCall.callerP populated) (eraseHeap noHeap) []
       populated.frame.state.storage.objects.length 0 (populated.scope+1)) defaultInit := by
   apply Proofs.UfConstructionPrepare.default_real populated defaultInit noHeap (by decide +kernel)
     (noModels populated) (by decide +kernel) <;> decide +kernel
 example := default_stage_peak _ _ _ _ _ _ defaultInit defaultReal
 def peakedStage (n : Nat) : Bool :=
   match prepare populated UnionFind_construct1.parameters [.value (.literal i32 n)] with
   | none => false
   | some s => match runFuel 8 UnionFind_construct1.body s with
     | .finished out =>
       out.state.scalars.memory.length == s.scalars.memory.length+2 &&
       out.state.scalars.bindings.length == s.scalars.bindings.length+2 &&
       out.state.scalars.peak ≤ max s.scalars.peak (liveS s+7) &&
       out.state.peak ≤ max s.peak (max s.scalars.peak (liveS s+10)+
         max s.frame.state.storage.peak (s.frame.state.liveSpace+(n+2)-s.frame.state.storage.baseSpace))
     | _ => false
 #guard peakedStage 0
 #guard peakedStage 1
 #guard peakedStage 3
 #guard peakedStage 17
 #guard callee.scalars.peak ≤ max init.scalars.peak (liveS init+7)
 #guard callee.scalars.memory.length == init.scalars.memory.length+2
 #guard (match runFuel 8 UnionFind_construct0.body defaultInit with
   | .finished out =>
     out.state.scalars.peak ≤ max defaultInit.scalars.peak (liveS defaultInit+5) &&
     out.state.peak ≤ max defaultInit.peak (max defaultInit.scalars.peak (liveS defaultInit+6)+
       max defaultInit.frame.state.storage.peak
         (defaultInit.frame.state.liveSpace+1-defaultInit.frame.state.storage.baseSpace))
   | _ => false)
 def highInit : NState := {init with peak := 900,scalars := {init.scalars with peak := 700}}
 example := sized_stage_peak _ _ _ _ _ _ 3 (by decide) highInit (show Realizes (entry (Proofs.DoublingCall.callerP populated) (eraseHeap noHeap) [] populated.frame.state.storage.objects.length 0 (populated.scope+1) 3) highInit from ⟨⟨initReal.data.locals,initReal.data.heap⟩,initReal.owner,initReal.binding,initReal.scopedState⟩)
 #guard (match runFuel 8 UnionFind_construct1.body highInit with
   | .finished out => out.state.peak == 900 && out.state.scalars.peak == 700
   | _ => false)
 def overBase : NState := {init with scalars := {init.scalars with baseMemory := 999}}
 example := sized_stage_peak _ _ _ _ _ _ 3 (by decide) overBase (show Realizes (entry (Proofs.DoublingCall.callerP populated) (eraseHeap noHeap) [] populated.frame.state.storage.objects.length 0 (populated.scope+1) 3) overBase from ⟨⟨initReal.data.locals,initReal.data.heap⟩,initReal.owner,initReal.binding,initReal.scopedState⟩)
 #guard (match runFuel 8 UnionFind_construct1.body overBase with
   | .finished out => out.state.scalars.peak ≤ max overBase.scalars.peak (liveS overBase+7)
   | _ => false)
 example (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Proofs.MultiVecDynamic.Parameter)
   (owner binding scope n : Nat) (endpoint : n = 2147483647) (s : NState)
   (real : Realizes (entry P h params owner binding scope n) s) :=
   sized_stage_peak P h params owner binding scope n (by omega) s real
 example (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Proofs.MultiVecDynamic.Parameter)
   (owner binding scope : Nat) (s : NState)
   (real : Realizes (defaultEntry P h params owner binding scope) s) :=
   default_stage_peak P h params owner binding scope s real
'''

class UnionFindConstructionPeakTests(unittest.TestCase):
    def test_stage_component_and_combined_peaks(self):
        with tempfile.TemporaryDirectory(prefix='uf-construction-peak-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfConstructionPeak\nimport Proofs.UfConstructionWork\n'
                             + HEADER + CALLER_HEADER + STAGE_CHECKS + BASE_CHECKS + CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
