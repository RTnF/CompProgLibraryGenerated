"""Complete num_groups call and unique roots representing the components."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_original_api import HEADER,SOURCE
from test_union_find_fields_call import FIXTURE as OWNER_FIXTURE
from test_union_find_class_invariant import PARENT_FIXTURE
from test_union_find_unite_call import CALLER_STRICT
from nested_ir import lower_source,emit_lean
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
PROOF='''
open Proofs.UfFieldsCounter Proofs.UfClassInvariant Proofs.DoublingNested Proofs.PrefixSumsCall
 def ne : NExpr := .binary intTy .add (.literal intTy 2) (.literal intTy 2)
 example := num_groups_call (cslot := 1) rootCaller ownerOK ⟨0,true⟩ 1 (by decide +kernel) rfl
   parents ranks parentValid (by decide +kernel) (by decide +kernel) rfl rfl ne rfl rfl (by decide +kernel)
 example := parentValid.root_representative 3 (by decide +kernel)
 example : ¬ Proofs.UfFieldsSame.Connected (initial 4) 0 1 := by
   rw [roots_distinct_components (initial 4) 0 1 (by rw [initial_roots]; decide) (by rw [initial_roots]; decide)]
   decide
 def parentCall := Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel 16 rootCaller
   [.vectorReference 0,.scalarReference 1,.value ne]
 -- Getter leaves the uncompressed path 3 -> 2 -> 0 in place.
 #guard observe parentCall == some (1,1,parents)
 def soloCaller := caller (initial 4) 4
 def soloBuffer : Proofs.CppVector.Buffer Value :=
   ⟨0,(initial 4).map Value.integer,5,Proofs.CppVectorBindings.sizeLimit intTy,0⟩
 theorem soloOK : VOKWF soloCaller 0 0 0 0 soloBuffer :=
   ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,callerStrict (initial 4) 4,by decide +kernel⟩
 def aliasN : NExpr := .variable intTy 2
 example := num_groups_call (cslot := 1) soloCaller soloOK ⟨0,true⟩ 4 (by decide +kernel) rfl
   (initial 4) (fun _ => 0) (initial_valid 4 (by decide)) (by decide +kernel) (by decide +kernel) rfl rfl
   aliasN rfl rfl (by decide +kernel)
 def soloArgs : List NArgument := [.vectorReference 0,.scalarReference 1,.value aliasN]
 def soloCall := Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel 16 soloCaller soloArgs
 #guard observe soloCall == some (4,4,initial 4)
 def entry := (prepare soloCaller Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters soloArgs).getD soloCaller
 #guard entry.scalars.bindings == [⟨0,true⟩,⟨6,true⟩]
 #guard entry.scalars.memory.drop 6 == [⟨intTy,4⟩]
 #guard (match soloCall with
   | .finished (s,_) => s.scalars.bindings == soloCaller.scalars.bindings &&
       s.scalars.memory == soloCaller.scalars.memory && s.scalars.baseMemory == soloCaller.scalars.baseMemory &&
       s.frame.bindings == soloCaller.frame.bindings && s.slots == soloCaller.slots &&
       s.frame.state.storage.work == soloCaller.frame.state.storage.work
   | _ => false)
 def emptyCaller := caller [] 0
 def emptyBuffer : Proofs.CppVector.Buffer Value :=
   ⟨0,[],1,Proofs.CppVectorBindings.sizeLimit intTy,0⟩
 theorem emptyOK : VOKWF emptyCaller 0 0 0 0 emptyBuffer :=
   ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,callerStrict [] 0,by decide +kernel⟩
 example := num_groups_call (cslot := 1) emptyCaller emptyOK ⟨0,true⟩ 0 (by decide +kernel) rfl
   [] (fun _ => 0) (initial_valid 0 (by decide)) (by decide +kernel) (by decide +kernel) rfl rfl
   (.literal intTy 0) rfl rfl (by decide +kernel)
 #guard observe (Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel 16 emptyCaller
   [.vectorReference 0,.scalarReference 1,.value (.literal intTy 0)]) == some (0,0,[])
 -- The typed raw getter proof also handles every i32 counter; Valid is used for the component interpretation.
 def rawCaller := caller [-1] (-2147483648)
 def rawBuffer : Proofs.CppVector.Buffer Value :=
   ⟨0,[.integer (-1)],2,Proofs.CppVectorBindings.sizeLimit intTy,0⟩
 theorem rawOK : VOKWF rawCaller 0 0 0 0 rawBuffer :=
   ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,callerStrict [-1] (-2147483648),by decide +kernel⟩
 example := counter_call (cslot := 1) rawCaller rawOK ⟨0,true⟩ (-2147483648) (by decide +kernel) rfl
   [-1] (by decide +kernel) (by decide) (by decide +kernel) rfl rfl
   (.literal intTy (-2147483648)) (-2147483648) rfl rfl (by decide +kernel) (by decide +kernel)
 #guard observe (Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel 16 rawCaller
   [.vectorReference 0,.scalarReference 1,.value (.literal intTy (-2147483648))]) == some (-2147483648,-2147483648,[-1])
 def readonly := {soloCaller with scalars.bindings := [⟨0,false⟩,⟨0,false⟩,⟨1,true⟩]}
 #guard Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel 16 readonly soloArgs == .fault
 #guard Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel 0 soloCaller soloArgs == .exhausted
 example (P : List Proofs.CppState.Cell) (counter : Nat) (n groups : Int) (vec : List Int)
   (found : P[counter]? = some ⟨intTy,groups⟩) (valid : intTy.valid groups = true) :=
   body_correct P counter n groups vec found valid 0
'''
class UnionFindNumGroupsCallTests(unittest.TestCase):
    def test_count_call_components_empty_and_counter_type_range(self):
        self.assertEqual((ROOT/'Proofs/Generated/UnionFindCandidate.lean').read_text(),
            emit_lean(lower_source(SOURCE,[SOURCE.parent]),'Proofs.UnionFindCandidateInstance'))
        with tempfile.TemporaryDirectory(prefix='union-find-num-groups-') as directory:
            proof=Path(directory)/'checks.lean'
            header=HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
            proof.write_text('import Proofs.UfFieldsCounter\n'+header+OWNER_FIXTURE+CALLER_STRICT+
                'open Proofs.UfClassInvariant\n'+PARENT_FIXTURE+PROOF)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        print('num_groups full call: empty/isolated/nontrivial components, unique root representatives, readonly argument alias, unchanged caller/vector/work, full i32 raw count and permission/fuel failures')
if __name__=='__main__':disable_network();unittest.main()
