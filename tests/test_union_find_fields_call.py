"""General source-derived UnionFind root call with mixed fields and reference aliases."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_original_api import HEADER, SOURCE
from nested_ir import lower_source, emit_lean
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent

FIXTURE = '''
open Proofs.UfRootCall Proofs.UfFindCall Proofs.UfFieldsRoot
open Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
 def parents : List Int := [-4,0,0,2]
 def ranks (i : Nat) : Nat := if i=0 then 0 else if i=2 then 1 else 2
 theorem parentForest : Proofs.UfRootCall.Forest parents ranks := by
   refine ⟨?_,?_,?_⟩
   · intro x member; simp [parents] at member
     rcases member with rfl | rfl | rfl <;> decide +kernel
   · intro i p found nonneg
     have inside := (List.getElem?_eq_some_iff.mp found).1
     have small : i < 4 := inside
     have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
     rcases choices with rfl | rfl | rfl | rfl <;> simp [parents] at found <;> subst p <;> first | omega | decide +kernel
   · intro i p found nonneg
     have inside := (List.getElem?_eq_some_iff.mp found).1
     have small : i < 4 := inside
     have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
     rcases choices with rfl | rfl | rfl | rfl <;> simp [parents] at found <;> subst p <;> first | omega | decide +kernel
 def rootCaller := caller parents 1
 def rootBuffer : Proofs.CppVector.Buffer Value :=
   ⟨0,parents.map Value.integer,parents.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0⟩
 theorem strict : ∀ owner c, rootCaller.frame.state.forest.context owner = some c → c ≤ rootCaller.scope := by
   intro owner c found
   cases owner with
   | zero =>
     have same : rootCaller.frame.state.forest.context 0 = some 0 := by decide +kernel
     rw [same] at found
     cases found
     exact Nat.le_refl 0
   | succ owner =>
     have missing : rootCaller.frame.state.forest.lookup (owner+1) = none := by simp [rootCaller,caller,Forest.lookup]
     rw [Forest.context,Forest.rootOwner,missing] at found
     contradiction
 theorem ownerOK : VOKWF rootCaller 0 0 0 0 rootBuffer :=
   ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,strict,by decide +kernel⟩
'''

ROOT_CHECKS = '''
 def nExpr : NExpr := .binary intTy .add (.literal intTy 2) (.literal intTy 2)
 def aExpr : NExpr := .binary intTy .add (.literal intTy 1) (.literal intTy 2)
 example := root_call (cslot := 1) rootCaller ownerOK ⟨0,true⟩ 1 (by decide +kernel) rfl
   parents ranks parentForest (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl
   nExpr aExpr 3 rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
 def args : List NArgument := [.vectorReference 0,.scalarReference 1,.value nExpr,.value aExpr]
 def fullCall := Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 64 rootCaller args
 #guard observe fullCall == some (0,1,[-4,0,0,0])
 def entry := (prepare rootCaller Proofs.UnionFindCandidateInstance.UnionFind_root.parameters args).getD rootCaller
 #guard entry.scalars.bindings == [⟨0,true⟩,⟨6,true⟩,⟨7,true⟩]
 #guard entry.slots == [.vector 0,.scalar 0,.scalar 1,.scalar 2]
 def readonly := {rootCaller with scalars.bindings := [⟨0,false⟩,⟨0,false⟩,⟨1,true⟩]}
 #guard Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 64 readonly args == .fault

 def aliasCaller := {rootCaller with
   frame.bindings := rootCaller.frame.bindings ++ [(⟨0,.integer intTy,false,.root 0⟩ : Proofs.CppNestedVectorBindings.Binding)],
   slots := rootCaller.slots ++ [(.vector 1 : Proofs.CppMixedInvoke.Location)]}
 def aliasCall := Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 64 aliasCaller args
 #guard (match aliasCall with
 | .finished (s,.scalar x) =>
   x == 0 && s.frame.bindings == aliasCaller.frame.bindings && s.slots == aliasCaller.slots &&
   s.scalars.memory == aliasCaller.scalars.memory &&
   (s.frame.state.storage.lookup 0).map (·.items) == some ([-4,0,0,0].map Value.integer)
   | _ => false)

 -- No sentinel restriction is introduced by the bound proof.
 example (P : List Proofs.CppState.Cell) (b : Proofs.CppState.Binding) (ps : List Int)
   (size : ps.length = 2147483647) :
   vdenL intTy ps (penv1 (fields P b ps.length 2147483646)) guardExpr = some 1 :=
   guard_value P b ps (by omega) 2147483646 (by omega)

 -- Scalar slot 0 stays invalid; unused leading references may not repair it.
 def scalarState : PS := ⟨[⟨intTy,6⟩,⟨intTy,7⟩,⟨intTy,1⟩],[⟨2,true⟩]⟩
 def extra : List Proofs.CppState.Binding := [⟨0,true⟩,⟨1,true⟩]
 def invalid : Command := .primitive (.ret (.variable intTy 0))
 #guard (pexecW intTy 4 invalid scalarState [4,5,6]).isNone
 #guard (pexecW intTy 4 (Proofs.VecShift.command 2 invalid) (Proofs.VecShift.pad extra scalarState) [4,5,6]).isNone
 def index : NExpr := .cast ⟨64,false,false⟩ (.variable intTy 1)
 def readValue : NExpr := .read intTy (.local 0) index
 def writeRead : Command := .sequence
   (.primitive (.write (.local 0) intTy index (.binary intTy .add readValue (.literal intTy 3))))
   (.primitive (.ret readValue))
 def original := pexecW intTy 4 writeRead scalarState [4,5,6]
 def shifted := pexecW intTy 4 (Proofs.VecShift.command 2 writeRead) (Proofs.VecShift.pad extra scalarState) [4,5,6]
 #guard (original.map (fun r => (r.ret,r.vec))) == some (some 8,[4,8,6])
 def pureObservation (r : PRW) := (r.ret,r.vec,r.ps.mem,r.ps.bs,r.need,r.cost,r.wk)
 #guard shifted.map pureObservation == (original.map (Proofs.VecShift.result extra)).map pureObservation
 #guard shifted.map (·.need) == original.map (fun r => r.need+2)
 #guard shifted.map (·.cost) == original.map (·.cost)
 #guard shifted.map (·.wk) == original.map (·.wk)
 example (ty : Ty) (fuel : Nat) (cmd : Command) (s : PS) (vec : List Int) (B : List Proofs.CppState.Binding) :
   pexecW ty fuel (Proofs.VecShift.command B.length cmd) (Proofs.VecShift.pad B s) vec =
     (pexecW ty fuel cmd s vec).map (Proofs.VecShift.result B) := Proofs.VecShift.execution ty fuel cmd s vec B
'''


PROOF = FIXTURE + ROOT_CHECKS

class UnionFindFieldsCallTests(unittest.TestCase):
    def test_generated_model_and_general_call_certificate(self):
        model=ROOT/'Proofs/Generated/UnionFindCandidate.lean'
        expected=emit_lean(lower_source(SOURCE,[SOURCE.parent]),'Proofs.UnionFindCandidateInstance')
        self.assertEqual(model.read_text(),expected)
        header=HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
        with tempfile.TemporaryDirectory(prefix='union-find-fields-call-') as directory:
            proof=Path(directory)/'checks.lean';proof.write_text('import Proofs.UfFieldsRoot\n'+header+PROOF)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        print('source-derived mixed-field root call: general certificate, expression arguments, alias/state preservation, INT_MAX domain, vector index shifts')


if __name__=='__main__':disable_network();unittest.main()
