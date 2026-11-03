"""General allocated constructor stages and concrete prepared-state certificates."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
CHECKS='''
open Proofs.UfConstructionStage Proofs.DynamicOwnedState
open Proofs.MultiVecDynamic Proofs.CppRootModel Proofs.DynamicExpr Proofs.DynamicContents
 def noHeap : Heap := fun _ => none
 def noContents : ContentsHeap := fun _ => none
 def sizedEntry : NState := (prepare empty UnionFind_construct1.parameters
   [.value (.literal i32 4)]).getD empty
 theorem sizedFamily : Family [] noHeap sizedEntry.frame (Proofs.CppRowsFrame.resources sizedEntry.frame) :=
   Proofs.DynamicFamilyInit.empty noHeap sizedEntry.frame (by decide +kernel)
     (by intro owner view found; simp [noHeap] at found) (by decide +kernel)
 theorem sizedReal : Realizes (entry [] noContents [] 0 0 1 4) sizedEntry :=
   ⟨⟨by decide +kernel,noHeap,_,sizedFamily,rfl⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩
 example := sized_stage [] noContents [] 0 0 1 4 (by decide) sizedEntry sizedReal
 example : ∃ out, Proofs.CppNestedProgram.runFuel 8 UnionFind_construct1.body sizedEntry = .finished out ∧
     Flat out.state.frame.state 0 i32 1 [-1,-1,-1,-1] ∧ out.returned = none ∧ out.breaking = false := by
   obtain ⟨out,ran,real,ret,br,valid⟩ := sized_stage [] noContents [] 0 0 1 4 (by decide) sizedEntry sizedReal
   exact ⟨out,ran,(final_fields [] noContents [] 0 0 1 4 out.state real).2.2.2,ret,br⟩
 def defaultPrepared : NState := (prepare empty UnionFind_construct0.parameters []).getD empty
 theorem defaultFamily : Family [] noHeap defaultPrepared.frame (Proofs.CppRowsFrame.resources defaultPrepared.frame) :=
   Proofs.DynamicFamilyInit.empty noHeap defaultPrepared.frame (by decide +kernel)
     (by intro owner view found; simp [noHeap] at found) (by decide +kernel)
 theorem defaultReal : Realizes (defaultEntry [] noContents [] 0 0 1) defaultPrepared :=
   ⟨⟨by decide +kernel,noHeap,_,defaultFamily,rfl⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩
 example := default_stage [] noContents [] 0 0 1 defaultPrepared defaultReal
 -- Arbitrary prefixes, tracked objects/references, and allocation/scope cursors.
 example (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Parameter)
   (owner binding scope n : Nat) (small : n < 2147483648) (s : NState)
   (real : Realizes (entry P h params owner binding scope n) s) :=
   sized_stage P h params owner binding scope n small s real
 example (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Parameter)
   (owner binding scope n : Nat) (endpoint : n = 2147483647) (s : NState)
   (real : Realizes (entry P h params owner binding scope n) s) :=
   sized_stage P h params owner binding scope n (by omega) s real
 example (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Parameter)
   (owner binding scope : Nat) (s : NState)
   (real : Realizes (defaultEntry P h params owner binding scope) s) :=
   default_stage P h params owner binding scope s real
'''
class UnionFindConstructionProofTests(unittest.TestCase):
    def test_general_stage_from_actual_prepared_states(self):
        with tempfile.TemporaryDirectory(prefix='uf-construction-proof-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfConstructionStage\n'+HEADER+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__=='__main__':disable_network();unittest.main()
