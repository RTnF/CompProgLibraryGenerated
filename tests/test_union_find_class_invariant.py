"""Actual component cardinality, root count, initialization and compression."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_fields_call import FIXTURE
from test_union_find_original_api import HEADER
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
PARENT_FIXTURE=''' theorem parentMembers : members parents 0 = List.range 4 := by
   classical
   unfold members
   change (List.range 4).filter (fun i => decide (Reach parents i 0)) = List.range 4
   apply List.filter_eq_self.mpr
   intro i member
   have inside : i<4 := List.mem_range.mp member
   have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
   simp only [decide_eq_true_eq]
   rcases choices with rfl | rfl | rfl | rfl
   · exact Reach.refl 0
   · exact Reach.step 1 0 0 rfl (Reach.refl 0)
   · exact Reach.step 2 0 0 rfl (Reach.refl 0)
   · exact Reach.step 3 2 0 rfl (Reach.step 2 0 0 rfl (Reach.refl 0))
 theorem parentRoots : roots parents = [0] := by
   classical
   simp [roots,parents,List.range_succ]
 theorem parentValid : Valid parents 1 ranks := by
   refine ⟨parentForest,by decide,?_,?_⟩
   · intro r w found negative
     have inside : r<4 := (List.getElem?_eq_some_iff.mp found).1
     have choices : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
     rcases choices with rfl | rfl | rfl | rfl
     · have value : w = -4 := by simpa [parents] using found.symm
       rw [value,parentMembers]
       rfl
     · simp [parents] at found
       subst w
       omega
     · simp [parents] at found
       subst w
       omega
     · simp [parents] at found
       subst w
       omega
   · rw [parentRoots]
     rfl
'''
PROOF='''
open Proofs.UfClassInvariant
open Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.UfFieldsSize
 example := initial_valid 0 (by decide)
 example := initial_valid 1 (by decide)
 example := initial_valid 2147483647 (by decide)
 example (n r : Nat) (bound : r<n) : members (initial n) r = [r] := initial_members n r bound
 example (ps : List Int) (a : Nat) : (component ps a).Nodup := component_nodup ps a
 example (ps : List Int) : (roots ps).Nodup := roots_nodup ps
 example (ps : List Int) (a i : Nat) (outside : ps.length ≤ i) : i ∉ component ps a := by
   classical
   simp only [component,List.mem_filter,List.mem_range,decide_eq_true_eq]
   omega
'''+PARENT_FIXTURE+''' example : component parents 3 = List.range 4 := by
   rw [component_eq_members parents 3 0 (Reach.step 3 2 0 rfl (Reach.step 2 0 0 rfl (Reach.refl 0)))
     ⟨-4,rfl,by decide⟩,parentMembers]
 def ne : NExpr := .binary intTy .add (.literal intTy 2) (.literal intTy 2)
 def ae : NExpr := .binary intTy .add (.literal intTy 1) (.literal intTy 2)
 example := size_card_call (cslot := 1) rootCaller ownerOK ⟨0,true⟩ 1 (by decide +kernel) rfl
   parents ranks parentValid (by decide +kernel) (by decide +kernel) rfl rfl
   ne ae 3 rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
 example (next : List Int) (compressed : Proofs.UfCompression.Compressed parents next 3 0) :
     Valid next 1 ranks := parentValid.compressed compressed
 example : ¬ Valid [-2] 1 (fun _ => 0) := by
   intro valid
   have size := valid.sizes 0 (-2) rfl (by decide)
   have bound := members_card_le [-2] 0
   change (members [-2] 0).length ≤ 1 at bound
   omega
 example : ¬ Valid [-2147483648] 1 (fun _ => 0) := by
   intro valid
   have weight := valid.weights 0 (-2147483648) rfl (by decide)
   norm_num at weight
 example : ¬ Valid (initial 3) 4 (fun _ => 0) := by
   intro valid
   have bound := valid.count_range
   have length : (initial 3).length = 3 := rfl
   rw [length] at bound
   omega
'''
class UnionFindClassInvariantTests(unittest.TestCase):
    def test_class_sizes_count_and_full_size_call(self):
        with tempfile.TemporaryDirectory(prefix='union-find-class-invariant-') as directory:
            proof=Path(directory)/'checks.lean'
            header=HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
            proof.write_text('import Proofs.UfClassInvariant\n'+header+FIXTURE+PROOF)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        print('class invariant: initial n=0/1/INT_MAX, actual connected component cardinality, size full call, compression, duplicate exclusion and invalid size/count')
if __name__=='__main__':disable_network();unittest.main()
