"""Complete generated unite call: compression, merge, counter aliases and finish."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_original_api import HEADER,SOURCE
from test_union_find_fields_call import FIXTURE as OWNER_FIXTURE
from test_union_find_class_invariant import PARENT_FIXTURE
from test_union_find_merge_invariant import FIXTURE as MERGE_FIXTURE
from nested_ir import lower_source,emit_lean
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
CALLER_STRICT=''' theorem callerStrict (ps : List Int) (groups : Int) :
     ∀ owner c, (caller ps groups).frame.state.forest.context owner = some c → c ≤ (caller ps groups).scope := by
   intro owner c found
   cases owner with
   | zero =>
     have same : (caller ps groups).frame.state.forest.context 0 = some 0 := by simp [caller,Forest.context,Forest.rootOwner,Forest.lookup]
     rw [same] at found
     cases found
     exact Nat.le_refl 0
   | succ owner =>
     have missing : (caller ps groups).frame.state.forest.lookup (owner+1) = none := by simp [caller,Forest.lookup]
     rw [Forest.context,Forest.rootOwner,missing] at found
     contradiction
'''
PROOF='''
open Proofs.UfFieldsUnite Proofs.UfClassInvariant Proofs.UfMergeInvariant
open Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.CppNestedFacts
 def ne : NExpr := .binary intTy .add (.literal intTy 2) (.literal intTy 2)
 def ae : NExpr := .binary intTy .add (.literal intTy 1) (.literal intTy 2)
 def be : NExpr := .variable intTy 2
 def args : List NArgument := [.vectorReference 0,.scalarReference 1,.value ne,.value ae,.value be]
 example := unite_call (cslot := 1) rootCaller ownerOK ⟨0,true⟩ 1 (by decide +kernel) rfl
   parents ranks parentValid (by decide +kernel) (by decide +kernel) rfl rfl
   ne ae be 3 1 rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
   (by decide +kernel) (by decide +kernel)
 -- Keep the endpoint abstract: no gigantic replicate term is elaborated.
 example (P : List Proofs.CppState.Cell) (counter : Nat) (groups : Int) (vec : List Int) (rank : Nat → Nat)
   (valid : Valid vec groups rank) (found : P[counter]? = some ⟨intTy,groups⟩) (endpoint : vec.length = 2147483647) :=
   body_correct P counter groups vec rank valid found 0 1 (by rw [endpoint]; decide) (by rw [endpoint]; decide)
     (max (rank 0) (rank 1)+2) (by omega) (by omega)
 def sameCall := Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel 128 rootCaller args
 #guard observe sameCall == some (0,1,[-4,0,0,0])
'''+CALLER_STRICT+''' def secondCaller := caller second 2
 def secondBuffer : Proofs.CppVector.Buffer Value :=
   ⟨0,second.map Value.integer,second.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0⟩
 theorem secondOK : VOKWF secondCaller 0 0 0 0 secondBuffer :=
   ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,callerStrict second 2,by decide +kernel⟩
 example : Proofs.UnionFindCandidateInstance.UnionFind_unite.Terminates secondCaller args := by
   obtain ⟨rank,valid⟩ := secondValid
   obtain ⟨Sinit,fuel,out,r1,r2,middle,two,final,prep,run,rest⟩ :=
     unite_call (cslot := 1) secondCaller secondOK ⟨0,true⟩ 2 (by decide +kernel) rfl second rank valid
       (by decide +kernel) (by decide +kernel) rfl rfl ne ae be 3 2
       rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
       (by decide +kernel) (by decide +kernel)
   exact ⟨fuel,(out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2)),run⟩
 def swapCall := Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel 128 secondCaller args
 #guard observe swapCall == some (0,1,finalParents)
 def entry := (prepare secondCaller Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters args).getD secondCaller
 #guard entry.scalars.memory == [⟨intTy,2⟩,⟨intTy,9876⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨1,false,true⟩,0⟩,⟨intTy,4⟩,⟨intTy,3⟩,⟨intTy,2⟩]
 #guard entry.scalars.bindings == [⟨0,true⟩,⟨6,true⟩,⟨7,true⟩,⟨8,true⟩]
 #guard (match swapCall with
   | .finished (s,_) => s.scalars.bindings == secondCaller.scalars.bindings &&
       s.scalars.baseMemory == secondCaller.scalars.baseMemory && s.scalars.memory == [⟨intTy,1⟩,⟨intTy,9876⟩] &&
       (s.scalarCell 2 intTy).map (fun (_,cell) => cell.value) == some (1 : Int)
   | _ => false)
 def firstCaller := caller first 3
 def ordinary := Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel 128 firstCaller
   [.vectorReference 0,.scalarReference 1,.value ne,.value (.literal intTy 0),.value (.literal intTy 2)]
 #guard observe ordinary == some (0,2,second)
 def readonly := {secondCaller with scalars.bindings := [⟨0,false⟩,⟨0,false⟩,⟨1,true⟩]}
 #guard Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel 128 readonly args == .fault
 #guard Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel 0 secondCaller args == .exhausted
 def aliasCaller := {secondCaller with
   frame.bindings := secondCaller.frame.bindings ++ [(⟨0,.integer intTy,false,.root 0⟩ : Proofs.CppNestedVectorBindings.Binding)],
   slots := secondCaller.slots ++ [(.vector 1 : Proofs.CppMixedInvoke.Location)]}
 def aliasCall := Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel 128 aliasCaller args
 #guard (match aliasCall with
   | .finished (s,.scalar root) => root == 0 && s.frame.bindings == aliasCaller.frame.bindings &&
       s.slots == aliasCaller.slots && s.scalars.bindings == aliasCaller.scalars.bindings &&
       s.scalars.memory == [⟨intTy,1⟩,⟨intTy,9876⟩] &&
       (s.frame.state.storage.lookup 0).map (·.items) == some (finalParents.map Value.integer)
   | _ => false)
'''
class UnionFindUniteCallTests(unittest.TestCase):
    def test_complete_source_call_and_reference_footprint(self):
        self.assertEqual((ROOT/'Proofs/Generated/UnionFindCandidate.lean').read_text(),
            emit_lean(lower_source(SOURCE,[SOURCE.parent]),'Proofs.UnionFindCandidateInstance'))
        with tempfile.TemporaryDirectory(prefix='union-find-unite-call-') as directory:
            proof=Path(directory)/'checks.lean'
            header=HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
            proof.write_text('import Proofs.UfFieldsUnite\n'+header+OWNER_FIXTURE+MERGE_FIXTURE+PARENT_FIXTURE+PROOF)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        print('unite full call: general same/swap proofs, compression/merge/count, readonly counter argument alias, prepared values, scalar/vector aliases, restored metadata and permission/fuel failure')
if __name__=='__main__':disable_network();unittest.main()
