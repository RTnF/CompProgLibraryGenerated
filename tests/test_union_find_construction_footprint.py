"""Exact allocation frames derived from actual default/sized constructor stages."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.CppConstructionFootprint Proofs.CppRootModel
 def noHeap : Heap := fun _ => none
 theorem noModels (s : NState) : HeapModels s.frame.state noHeap := by
   intro owner view found
   simp [noHeap] at found
 def oldBuffer : Proofs.CppVector.Buffer Value := ⟨0,[.integer (-1),.integer (-1)],29,64,7⟩
 def populated : NState :=
   let c := caller [-1,-1] 2
   {c with frame := {c.frame with state := {c.frame.state with
     storage := {c.frame.state.storage with objects := [some oldBuffer]}}}}
 example := Proofs.UfConstructionFootprint.default_from_caller populated noHeap
   (by decide +kernel) (noModels populated) (by decide +kernel)
 example := Proofs.UfConstructionFootprint.sized_from_caller populated noHeap
   (by decide +kernel) (noModels populated) (by decide +kernel)
   (.variable i32 2) 2 (by decide) rfl rfl (by decide +kernel)
 example (s : NState) (h : Heap) (ok : s.frame.state.wellFormed = true)
   (hm : HeapModels s.frame.state h)
   (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
   (e : NExpr) (n : Nat) (small : n < 2147483648) (scalar : e.scalarOnly = true)
   (ty : e.resultType = i32) (value : e.denote (Proofs.CppNestedEval.envOf s) = some (n : Int)) :=
   Proofs.UfConstructionFootprint.sized_from_caller s h ok hm lengths e n small scalar ty value
 example (s : NState) (h : Heap) (ok : s.frame.state.wellFormed = true)
   (hm : HeapModels s.frame.state h)
   (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
   (e : NExpr) (n : Nat) (endpoint : n = 2147483647) (scalar : e.scalarOnly = true)
   (ty : e.resultType = i32) (value : e.denote (Proofs.CppNestedEval.envOf s) = some (n : Int)) :=
   Proofs.UfConstructionFootprint.sized_from_caller s h ok hm lengths e n (by omega) scalar ty value
 def saved : Option Reference := populated.frame.elementRef 0 i32 1
 #guard saved.isSome
 def stageOn (p : NProgram) (args : List NArgument) : Outcome NStep := do
   let s ← liftChecked (prepare populated p.parameters args)
   runFuel 8 p.body s
 def exactFilled (n : Nat) : Bool := match stageOn UnionFind_construct1 [.value (.literal i32 n)] with
   | .finished out =>
     out.state.frame == installed (Proofs.UfConstructionFootprint.preparedFrame populated)
       (filledState populated.frame.state i32 1 n (-1)) i32 true 1 &&
     out.state.frame.state.storage.lookup 0 == some oldBuffer &&
     out.state.frame.state.storage.lookup 1 == some ⟨1,List.replicate n (.integer (-1)),n,
       Proofs.CppVectorBindings.sizeLimit i32,0⟩ &&
     (saved.bind ({out.state.frame with bindings := populated.frame.bindings}.read)) == some (-1)
   | _ => false
 #guard exactFilled 0
 #guard exactFilled 1
 #guard exactFilled 2
 #guard exactFilled 17
 #guard (match stageOn UnionFind_construct0 [] with
   | .finished out =>
     out.state.frame == installed (Proofs.UfConstructionFootprint.preparedFrame populated)
       (emptyState populated.frame.state i32 1) i32 true 1 &&
     out.state.frame.state.storage.lookup 0 == some oldBuffer &&
     out.state.frame.state.storage.lookup 1 == some (Proofs.CppNestedConstruct.flatBuffer i32 1) &&
     (saved.bind ({out.state.frame with bindings := populated.frame.bindings}.read)) == some (-1)
   | _ => false)
 example (s : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope count owner : Nat) (x : Int)
   (bound : owner < s.storage.objects.length) := filled_old s ty scope count x owner bound
 example (s : Proofs.CppNestedVectorStore.State) (ty : Ty) (scope count : Nat) (x : Int) :=
   filled_new s ty scope count x
'''
class UnionFindConstructionFootprintTests(unittest.TestCase):
    def test_general_allocation_frame_and_saved_reference(self):
        with tempfile.TemporaryDirectory(prefix='uf-construction-footprint-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfConstructionFootprint\n'+HEADER+CALLER_HEADER+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__ == '__main__':
    disable_network()
    unittest.main()
