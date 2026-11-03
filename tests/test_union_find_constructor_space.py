"""Caller argument evaluation, resident allocation and finish peaks compose."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_union_find_constructed_receiver import CHECKS as RECEIVER_CHECKS
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.UfConstructorSpace Proofs.CppNestedEval
 example := construct_sized populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.variable i32 2) 2
   (by decide) rfl rfl (by decide +kernel)
 example := construct_default populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel)
 example := Proofs.CppConstructionSpace.filled_live populated.frame.state i32 3 17 (-1) (by decide +kernel)
 example := Proofs.CppConstructionSpace.empty_live populated.frame.state i32 3 (by decide +kernel)
 def budget (s : NState) (n nodes : Nat) := max s.peak
   (max s.scalars.peak (liveS s+s.frame.bindings.length+nodes+12)+
     max s.frame.state.storage.peak (s.frame.state.liveSpace+(n+2)-s.frame.state.storage.baseSpace))
 def sizedBound (s : NState) (n : Nat) : Bool := match UnionFind_construct1.constructFuel 8 s
     [.value (.literal i32 n)] (Proofs.UfConstructionExport.vectorField true) (.integer i32)
     (Proofs.UfConstructionExport.fields true) with
   | .finished (out,_) =>
     out.peak ≤ budget s n 1 && liveS out == liveS s+4 &&
     out.frame.state.liveSpace == s.frame.state.liveSpace+n+1 &&
     out.work ≤ s.work+n+31 &&
     out.frame.state.storage.lookup 0 == s.frame.state.storage.lookup 0
   | _ => false
 #guard sizedBound populated 0
 #guard sizedBound populated 1
 #guard sizedBound populated 2
 #guard sizedBound populated 17
 #guard (match UnionFind_construct0.constructFuel 8 populated [] (Proofs.UfConstructionExport.vectorField false)
     (.integer i32) (Proofs.UfConstructionExport.fields false) with
   | .finished (out,_) => liveS out == liveS populated+4 &&
     out.frame.state.liveSpace == populated.frame.state.liveSpace+1 &&
     out.peak ≤ max populated.peak (max populated.scalars.peak
       (liveS populated+populated.frame.bindings.length+6)+max populated.frame.state.storage.peak
         (populated.frame.state.liveSpace+1-populated.frame.state.storage.baseSpace))
   | _ => false)
 def aliases : NState :=
   {populated with
     frame := {populated.frame with bindings := populated.frame.bindings++[⟨0,.integer i32,false,.root 0⟩]}
     slots := populated.slots++[.vector populated.frame.bindings.length]}
 example := construct_sized aliases noHeap (by decide +kernel) (noModels aliases)
   (by decide +kernel) populatedStrict (by decide +kernel) (.variable i32 2) 2
   (by decide) rfl rfl (by decide +kernel)
 #guard sizedBound aliases 17
 def based : NState :=
   {populated with
     scalars := {populated.scalars with baseMemory := 2}
     frame := {populated.frame with state := {populated.frame.state with
       storage := {populated.frame.state.storage with baseSpace := 30}}}}
 example := construct_sized based noHeap (by decide +kernel) (noModels based)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 17) 17
   (by decide) rfl rfl (by decide +kernel)
 #guard sizedBound based 17
 def high : NState := {populated with peak := 900,scalars := {populated.scalars with peak := 700}}
 example := construct_default high noHeap (by decide +kernel) (noModels high)
   (by decide +kernel) populatedStrict (by decide +kernel)
 #guard sizedBound high 17
 #guard (match UnionFind_construct1.constructFuel 8 high [.value (.literal i32 17)]
     (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) with
   | .finished (out,_) => out.peak ≥ 900
   | _ => false)
 example := construct_sized populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel)
   (.binary i32 .add (.literal i32 2) (.literal i32 2)) 4 (by decide) rfl rfl (by decide +kernel)
 example (c : NState) (h : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state h) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (strict : ∀ owner scope, c.frame.state.forest.context owner = some scope → scope ≤ c.scope)
   (base : c.scalars.baseMemory ≤ c.scalars.memory.length) (e : NExpr) (n : Nat)
   (endpoint : n = 2147483647) (scalar : e.scalarOnly = true) (ty : e.resultType = i32)
   (value : e.denote (envOf c) = some (n : Int)) :=
   construct_sized c h valid models lengths strict base e n (by omega) scalar ty value
 example (c : NState) (h : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state h) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (strict : ∀ owner scope, c.frame.state.forest.context owner = some scope → scope ≤ c.scope)
   (base : c.scalars.baseMemory ≤ c.scalars.memory.length) := construct_default c h valid models lengths strict base
'''

class UnionFindConstructorSpaceTests(unittest.TestCase):
    def test_full_constructor_work_and_space(self):
        with tempfile.TemporaryDirectory(prefix='uf-constructor-space-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfConstructorSpace\n' + HEADER + CALLER_HEADER
                             + STAGE_CHECKS + RECEIVER_CHECKS + CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
