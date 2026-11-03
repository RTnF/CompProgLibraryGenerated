"""General caller -> prepare -> allocated constructor stages, including readonly aliases."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
CHECKS='''
open Proofs.UfConstructionPrepare Proofs.UfConstructionStage Proofs.DynamicContents Proofs.CppRootModel
 def noHeap : Heap := fun _ => none
 theorem noModels (s : NState) : HeapModels s.frame.state noHeap := by
   intro owner view found
   simp [noHeap] at found
 example := default_from_caller empty noHeap (by decide +kernel) (noModels empty) (by decide +kernel)
 example := sized_from_caller empty noHeap (by decide +kernel) (noModels empty) (by decide +kernel)
   (.literal i32 0) 0 (by decide) rfl rfl (by decide +kernel)
 def populated := caller [-1,-1] 2
 -- n is read from the caller's readonly alias, before the callee frame exists.
 def nAlias : NExpr := .variable i32 2
 example := sized_from_caller populated noHeap (by decide +kernel) (noModels populated) (by decide +kernel)
   nAlias 2 (by decide) rfl rfl (by decide +kernel)
 example := default_from_caller populated noHeap (by decide +kernel) (noModels populated) (by decide +kernel)
 def invokeStage (p : NProgram) (c : NState) (args : List NArgument) : Outcome NStep := do
   let init ← liftChecked (prepare c p.parameters args)
   runFuel 8 p.body init
 def actual := invokeStage UnionFind_construct1 populated [.value nAlias]
 #guard summary actual 1 2 3 == some ([-1,-1],2,2)
 #guard (match actual with
   | .finished out => out.state.scalars.memory.take 2 == populated.scalars.memory &&
       out.state.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0 &&
       out.state.frame.state.forest.lookup 0 == populated.frame.state.forest.lookup 0 &&
       out.state.frame.state.storage.objects.length == 2 && out.state.frame.state.storage.work == 3 &&
       out.state.frame.bindings == [⟨1,.integer i32,true,.root 1⟩] && out.state.scope == 1
   | _ => false)
 #guard summary (invokeStage UnionFind_construct0 populated []) 0 1 2 == some ([],0,0)
 #guard invokeStage UnionFind_construct1 populated [.value (.literal ⟨64,false,false⟩ 2)] == .fault
 example (c : NState) (heap : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state heap) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
   (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf c) = some (n : Int)) :=
   sized_from_caller c heap valid models lengths en n small scalar type value
 example (c : NState) (heap : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state heap) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (en : NExpr) (n : Nat) (endpoint : n = 2147483647) (scalar : en.scalarOnly = true)
   (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf c) = some (n : Int)) :=
   sized_from_caller c heap valid models lengths en n (by omega) scalar type value
'''
class UnionFindConstructionPrepareTests(unittest.TestCase):
    def test_prepare_and_stage_from_generic_caller_and_alias(self):
        with tempfile.TemporaryDirectory(prefix='uf-construction-prepare-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfConstructionPrepare\n'+HEADER+CALLER_HEADER+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__=='__main__':disable_network();unittest.main()
