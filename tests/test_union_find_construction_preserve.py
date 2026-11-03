"""Full constructor finish keeps old allocations and captured element references."""
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
 example : Proofs.UfConstructionPreserve.OldScopes populated := by
   intro owner inside
   have eq : owner = 0 := by simpa [populated,caller] using inside
   subst owner
   decide +kernel
 example := Proofs.UfConstructionPreserve.construct_sized populated noHeap
   (by decide +kernel) (noModels populated) (by decide +kernel) (by
     intro owner inside
     have eq : owner = 0 := by simpa [populated,caller] using inside
     subst owner
     decide +kernel)
   (.variable i32 2) 2 (by decide) rfl rfl (by decide +kernel)
 example := Proofs.UfConstructionPreserve.construct_default populated noHeap
   (by decide +kernel) (noModels populated) (by decide +kernel) (by
     intro owner inside
     have eq : owner = 0 := by simpa [populated,caller] using inside
     subst owner
     decide +kernel)
 def preserved (n : Nat) : Bool := match UnionFind_construct1.constructFuel 8 populated
     [.value (.literal i32 n)] (Proofs.UfConstructionExport.vectorField true) (.integer i32)
     (Proofs.UfConstructionExport.fields true) with
   | .finished (out,_) => out.frame.state.storage.lookup 0 == some oldBuffer &&
       out.frame.state.forest.lookup 0 == populated.frame.state.forest.lookup 0 &&
       out.frame.state.storage.lookup 1 == some ⟨1,List.replicate n (.integer (-1)),n,
         Proofs.CppVectorBindings.sizeLimit i32,0⟩ &&
       saved.bind out.frame.read == some (-1) && out.frame.rootWritable == [true,true]
   | _ => false
 #guard preserved 0
 #guard preserved 1
 #guard preserved 2
 #guard preserved 17
 #guard (match UnionFind_construct0.constructFuel 8 populated []
     (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) with
   | .finished (out,_) => out.frame.state.storage.lookup 0 == some oldBuffer &&
       saved.bind out.frame.read == some (-1) && out.frame.rootWritable == [true,true]
   | _ => false)
 def rowsState : Proofs.CppNestedVectorStore.State :=
   match empty.frame.state.constructRows i32 0 2 with
   | some s => {s with storage := {s.storage with objects := (s.storage.objects.set 1
       (some ⟨1,[.integer (-1),.integer (-1)],29,64,7⟩))}}
   | none => empty.frame.state
 def rowsFrame : Frame := ⟨rowsState,[true,false,false],[⟨0,.vector (.integer i32),true,.root 0⟩]⟩
 def rowsBound : Frame := match rowsFrame.bindChild 0 (.integer i32) 0 false with
   | some (f,_) => f
   | none => rowsFrame
 def nestedCaller : NState := {empty with frame := rowsBound,slots := [.vector 0,.vector 1]}
 def nestedSaved := nestedCaller.frame.elementRef 1 i32 1
 #guard nestedSaved.isSome
 #guard nestedSaved.bind nestedCaller.frame.read == some (-1)
 #guard (match UnionFind_construct1.constructFuel 8 nestedCaller [.value (.literal i32 2)]
     (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) with
   | .finished (out,_) => nestedSaved.bind out.frame.read == some (-1) &&
       out.frame.state.storage.lookup 0 == nestedCaller.frame.state.storage.lookup 0 &&
       out.frame.state.storage.lookup 1 == nestedCaller.frame.state.storage.lookup 1 &&
       out.frame.state.storage.lookup 2 == nestedCaller.frame.state.storage.lookup 2 &&
       out.frame.rootWritable == [true,false,false,true]
   | _ => false)
 example (c : NState) (h : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state h) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (scopes : Proofs.UfConstructionPreserve.OldScopes c)
   (e : NExpr) (n : Nat) (endpoint : n = 2147483647) (scalar : e.scalarOnly = true)
   (ty : e.resultType = i32) (value : e.denote (Proofs.CppNestedEval.envOf c) = some (n : Int)) :=
   Proofs.UfConstructionPreserve.construct_sized c h valid models lengths scopes e n (by omega) scalar ty value
'''
class UnionFindConstructionPreserveTests(unittest.TestCase):
    def test_full_finish_preserves_old_metadata_and_nested_references(self):
        with tempfile.TemporaryDirectory(prefix='uf-construction-preserve-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfConstructionPreserve\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__ == '__main__':
    disable_network()
    unittest.main()
