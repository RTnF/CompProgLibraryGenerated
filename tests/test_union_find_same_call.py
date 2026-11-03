"""Path-compressing same: source body, complete call, and inlined return capture."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_fields_call import FIXTURE
from test_union_find_original_api import HEADER, SOURCE
from nested_ir import lower_source,emit_lean
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
PROOF='''
open Proofs.UfFieldsSame Proofs.VecCapture Proofs.UfInlineRoot
open Proofs.DoublingNested Proofs.PrefixSumsCall
 def ne : NExpr := .binary intTy .add (.literal intTy 2) (.literal intTy 2)
 def ae : NExpr := .binary intTy .add (.literal intTy 1) (.literal intTy 2)
 def be : NExpr := .variable intTy 2
 example := same_call (cslot := 1) rootCaller ownerOK ⟨0,true⟩ 1 (by decide +kernel) rfl
   parents ranks parentForest (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl
   ne ae be 3 1 rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
   (by decide +kernel) (by decide +kernel)
 def args : List NArgument := [.vectorReference 0,.scalarReference 1,.value ne,.value ae,.value be]
 def sameCall := Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel 128 rootCaller args
 #guard observe sameCall == some (1,1,[-4,0,0,0])
 def entry := (prepare rootCaller Proofs.UnionFindCandidateInstance.UnionFind_same.parameters args).getD rootCaller
 #guard entry.scalars.bindings == [⟨0,true⟩,⟨6,true⟩,⟨7,true⟩,⟨8,true⟩]
 #guard entry.slots == [.vector 0,.scalar 0,.scalar 1,.scalar 2,.scalar 3]
 def separate : List Int := [-2,0,-2,2]
 def separateRanks (i : Nat) : Nat := if i=0 ∨ i=2 then 0 else 1
 theorem separateForest : Proofs.UfRootCall.Forest separate separateRanks := by
   refine ⟨?_,?_,?_⟩
   · intro x member; simp [separate] at member
     rcases member with rfl | rfl | rfl | rfl <;> decide +kernel
   · intro i p found nonneg
     have small : i<4 := (List.getElem?_eq_some_iff.mp found).1
     have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
     rcases choices with rfl | rfl | rfl | rfl <;> simp [separate] at found <;> subst p <;> first | omega | decide +kernel
   · intro i p found nonneg
     have small : i<4 := (List.getElem?_eq_some_iff.mp found).1
     have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
     rcases choices with rfl | rfl | rfl | rfl <;> simp [separate] at found <;> subst p <;> first | omega | decide +kernel
 def separateCaller := caller separate 2
 def separateCall := Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel 128 separateCaller
   [.vectorReference 0,.scalarReference 1,.value (.literal intTy 4),.value (.literal intTy 1),.value (.literal intTy 3)]
 #guard observe separateCall == some (0,2,separate)
 example := body_correct [] (⟨0,true⟩ : Proofs.CppState.Binding) separate separateRanks separateForest
   (by decide +kernel) 1 3 (by decide +kernel) (by decide +kernel) 4 (by decide +kernel) (by decide +kernel)

 def coreInput := stI [(⟨intTy,99⟩ : Proofs.CppState.Cell)] 3
 def before := pexecW intTy 8 Proofs.UfFindCall.bodyF coreInput parents
 def after := pexecW intTy 8 capturedF coreInput parents
 def observation (r : PRW) := (r.ps.mem,r.ps.bs,r.vec,r.ret,r.cost,r.need,r.wk)
 #guard before.map (·.ret) == some (some 0)
 #guard after.map (·.ret) == some none
 #guard after.map (·.cost) == before.map (·.cost)
 #guard after.map (·.wk) == before.map (·.wk)
 #guard after.map (fun r => r.ps.mem) == some [⟨intTy,99⟩,⟨intTy,0⟩,⟨intTy,0⟩,⟨intTy,0⟩]
 #guard (match before,after with | some a,some b => b.need ≤ a.need+2 | _,_ => false)
 def tail : Command := .sequence (.primitive (.declare intTy true (.binary intTy .add (.variable intTy 3) (.literal intTy 5))))
   (.sequence (.primitive (.ret (.variable intTy 4))) (.primitive .skip))
 def continued := pexecW intTy 8 (plug capturedF tail) coreInput parents
 #guard continued.map (fun r => (r.ret,r.vec)) == some (some 5,[-4,0,0,0])
 example : ¬ Silent intTy (.primitive (.ret (.literal intTy 0))) := by
   intro silent
   have invalid := silent 0 ⟨[],[]⟩ [] ⟨⟨[],[]⟩,[],some 0,2,3,0⟩ (by rw [pexecW,pstmtW]; rfl)
   contradiction
 def overflowReturn : Command := .sequence (.primitive (.ret (.literal ⟨64,true,false⟩ 1099511627776))) (.primitive .skip)
 def overflowCapture : Command := .sequence (.primitive (.declare intTy true (.literal ⟨64,true,false⟩ 1099511627776))) (.primitive .skip)
 #guard (pexecW intTy 2 overflowReturn ⟨[],[]⟩ []).isSome
 #guard (pexecW intTy 2 overflowCapture ⟨[],[]⟩ []).isNone
 def fuelEmpty := pexecW intTy 0 capturedF coreInput parents
 #guard fuelEmpty.isNone
'''

class UnionFindSameCallTests(unittest.TestCase):
    def test_same_source_call_and_capture_continuation(self):
        self.assertEqual((ROOT/'Proofs/Generated/UnionFindCandidate.lean').read_text(),
            emit_lean(lower_source(SOURCE,[SOURCE.parent]),'Proofs.UnionFindCandidateInstance'))
        header=HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
        with tempfile.TemporaryDirectory(prefix='union-find-same-call-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfFieldsSame\n'+header+FIXTURE+PROOF)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        print('same full source call: connected/separate roots, counter alias, compression, capture continuation, early-return exclusion, conversion/fuel failures')

if __name__=='__main__':disable_network();unittest.main()
