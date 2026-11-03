"""General captured-reference preservation and stale/unauthorized reference results."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_union_find_construction_preserve import CHECKS as PRESERVE_CHECKS
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.CppFrameExtension
 theorem nestedScopes : Proofs.UfConstructionPreserve.OldScopes nestedCaller := by
   intro owner inside
   have len : nestedCaller.frame.state.storage.objects.length = 3 := by decide +kernel
   have small : owner < 3 := by rwa [len] at inside
   have cases : owner = 0 ∨ owner = 1 ∨ owner = 2 := by omega
   rcases cases with rfl | rfl | rfl <;> decide +kernel
 def nestedBuilt : NState := match UnionFind_construct1.constructFuel 8 nestedCaller
     [.value (.literal i32 2)] (Proofs.UfConstructionExport.vectorField true) (.integer i32)
       (Proofs.UfConstructionExport.fields true) with
   | .finished (s,_) => s
   | _ => empty
 theorem extended : Extends nestedCaller.frame nestedBuilt.frame := by
   obtain ⟨out,ran,initialized,extension,reads⟩ := Proofs.UfConstructionReferences.construct_sized nestedCaller
     noHeap (by decide +kernel) (noModels nestedCaller) (by decide +kernel) nestedScopes
     (.literal i32 2) 2 (by decide +kernel) rfl rfl rfl
   have executed : UnionFind_construct1.constructFuel 8 nestedCaller [.value (.literal i32 2)]
       (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
       .finished (out,Proofs.CppConstructorFinish.reference nestedCaller 2) := ran
   have same : nestedBuilt = out := by unfold nestedBuilt; rw [executed]
   rw [same]
   exact extension
 def captured : Reference := ⟨1,i32,false,⟨1,7,1⟩⟩
 def stale : Reference := ⟨1,i32,false,⟨1,8,1⟩⟩
 def unauthorized : Reference := ⟨1,i32,true,⟨1,7,1⟩⟩
 #guard nestedSaved == some captured
 #guard nestedCaller.frame.read captured == some (-1)
 #guard nestedBuilt.frame.read captured == some (-1)
 #guard nestedCaller.frame.read stale == none
 #guard nestedBuilt.frame.read stale == none
 #guard nestedCaller.frame.grant unauthorized == none
 #guard nestedBuilt.frame.grant unauthorized == none
 #guard nestedCaller.frame.read unauthorized == none
 #guard nestedBuilt.frame.read unauthorized == none
 example : nestedBuilt.frame.read captured = some (-1) :=
   read_kept nestedCaller.frame nestedBuilt.frame extended captured (-1) (by decide +kernel)
 example : nestedBuilt.frame.read stale = nestedCaller.frame.read stale :=
   read_eq nestedCaller.frame nestedBuilt.frame extended stale
     ⟨1,.integer i32,false,.child ⟨0,0,0⟩⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
 example : nestedBuilt.frame.grant unauthorized = nestedCaller.frame.grant unauthorized :=
   grant_eq nestedCaller.frame nestedBuilt.frame extended unauthorized
     ⟨1,.integer i32,false,.child ⟨0,0,0⟩⟩ (by decide +kernel) (by decide +kernel)
 example (f g : Frame) (extension : Extends f g) (ref : Reference) (v : Int)
   (read : f.read ref = some v) : g.read ref = some v := read_kept f g extension ref v read
 example (c : NState) (h : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state h) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (scopes : Proofs.UfConstructionPreserve.OldScopes c) :=
   Proofs.UfConstructionReferences.construct_default c h valid models lengths scopes
 example (c : NState) (h : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state h) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (scopes : Proofs.UfConstructionPreserve.OldScopes c)
   (e : NExpr) (n : Nat) (endpoint : n = 2147483647) (scalar : e.scalarOnly = true)
   (ty : e.resultType = i32) (value : e.denote (Proofs.CppNestedEval.envOf c) = some (n : Int)) :=
   Proofs.UfConstructionReferences.construct_sized c h valid models lengths scopes e n (by omega) scalar ty value
'''
class UnionFindConstructionReferencesTests(unittest.TestCase):
    def test_all_reference_reads_and_permission_failures(self):
        with tempfile.TemporaryDirectory(prefix='uf-construction-references-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfConstructionReferences\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+PRESERVE_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__ == '__main__':
    disable_network()
    unittest.main()
