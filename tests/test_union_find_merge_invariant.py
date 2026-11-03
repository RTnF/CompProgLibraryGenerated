"""Merge cardinalities, safe sums/decrements and source-derived unite states."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_original_api import HEADER,SOURCE
from nested_ir import lower_source,emit_lean
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
FIXTURE='''
open Proofs.UfMergeInvariant Proofs.UfClassInvariant Proofs.UfRootCall Proofs.UfFindCall
open Proofs.DoublingNested
 def first : List Int := [-2,0,-1,-1]
 def second : List Int := [-3,0,0,-1]
 def finalParents : List Int := [-4,0,0,0]
 theorem firstValid : ∃ rank, Valid first 3 rank :=
   (initial_valid 4 (by decide)).linked 0 1 (-1) (-1) rfl rfl (by decide) (by decide) (by decide)
 theorem secondValid : ∃ rank, Valid second 2 rank := by
   obtain ⟨r1,v1⟩ := firstValid
   exact v1.linked 0 2 (-2) (-1) rfl rfl (by decide) (by decide) (by decide)
'''
PROOF=FIXTURE+''' theorem successive : ∃ rank, Valid finalParents 1 rank := by
   obtain ⟨r2,v2⟩ := secondValid
   exact v2.unite_vec 3 0 ⟨-1,rfl,by decide⟩ ⟨-3,rfl,by decide⟩
 example : ∃ rank, Valid first 3 rank := by
   obtain ⟨rank,valid⟩ := firstValid
   exact valid.unite_vec 0 0 ⟨-2,rfl,by decide⟩ ⟨-2,rfl,by decide⟩
 example : ∃ rank, Valid [-1,-1,3,-2] 3 rank :=
   (initial_valid 4 (by decide)).linked 3 2 (-1) (-1) rfl rfl (by decide) (by decide) (by decide)
 example : roots (linked (initial 4) 0 1 (-2)) = (roots (initial 4)).filter (· != 1) :=
   roots_linked (initial 4) 0 1 (-2) ⟨-1,rfl,by decide⟩ ⟨-1,rfl,by decide⟩ (by decide) (by decide)
 example : members (linked (initial 4) 0 1 (-2)) 2 = members (initial 4) 2 :=
   members_linked_other (initial 4) 0 1 2 (-2) ⟨-1,rfl,by decide⟩ ⟨-1,rfl,by decide⟩
     (by decide) (by decide) (by decide)
 example (i z : Nat) : Reach first i z ↔ Reach (initial 4) i z ∨ (z=0 ∧ Reach (initial 4) i 1) :=
   reach_iff (initial 4) 0 1 (-2) ⟨-1,rfl,by decide⟩ ⟨-1,rfl,by decide⟩ (by decide) (by decide) i z
 -- Weights alone permits these individually bounded roots, but their sizes double-count the vector.
 example : Proofs.UfFieldsSize.Weights [-2,-2] := by
   intro i w found negative
   have member : w ∈ List.replicate 2 (-2) := List.mem_of_getElem? found
   have same : w = -2 := List.eq_of_mem_replicate member
   rw [same]
   decide
 example : ¬ ∃ rank, Valid [-2,-2] 2 rank := by
   rintro ⟨rank,valid⟩
   have safe := valid.sum_valid 0 1 (-2) (-2) rfl rfl (by decide) (by decide) (by decide)
   norm_num at safe
 -- Arithmetic bounds do not need the extra sentinel slot or n<INT_MAX.
 example (ps : List Int) (groups : Int) (rank : Nat → Nat) (valid : Valid ps groups rank)
   (nmax : ps.length = 2147483647) (X Y : Nat) (vx vy : Int)
   (fx : ps[X]? = some vx) (fy : ps[Y]? = some vy) (nx : vx<0) (ny : vy<0) (different : X≠Y) :
   -2147483647 ≤ vx+vy ∧ i32.valid (groups-1) = true := by
   have sum := valid.sum_valid X Y vx vy fx fy nx ny different
   have decrement := valid.decrement_valid X Y ⟨vx,fx,nx⟩ ⟨vy,fy,ny⟩ different
   rw [nmax] at sum
   exact ⟨sum.1,decrement.2⟩
 def unite (ps : List Int) (groups a b : Int) := Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel 128
   (caller ps groups) [.vectorReference 0,.scalarReference 1,.value (.literal intTy ps.length),
     .value (.literal intTy a),.value (.literal intTy b)]
 #guard observe (unite (initial 4) 4 0 1) == some (0,3,first)
 #guard observe (unite first 3 0 2) == some (0,2,second)
 -- Smaller first component triggers the original swap; the scalar counter still changes only once.
 #guard observe (unite second 2 3 2) == some (0,1,finalParents)
 -- Same-root early return preserves the counter and the entire represented class state.
 #guard observe (unite first 3 0 1) == some (0,3,first)
 #guard linked (initial 4) 0 1 (-2) == first
 #guard linked first 0 2 (-3) == second
 #guard linked second 0 3 (-4) == finalParents
'''
class UnionFindMergeInvariantTests(unittest.TestCase):
    def test_merge_invariant_and_source_unite_states(self):
        self.assertEqual((ROOT/'Proofs/Generated/UnionFindCandidate.lean').read_text(),
            emit_lean(lower_source(SOURCE,[SOURCE.parent]),'Proofs.UnionFindCandidateInstance'))
        with tempfile.TemporaryDirectory(prefix='union-find-merge-invariant-') as directory:
            proof=Path(directory)/'checks.lean'
            header=HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
            proof.write_text('import Proofs.UfMergeInvariant\n'+header+PROOF)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        print('merge invariant: disjoint component cardinalities, n=INT_MAX safe arithmetic, root removal, three successive links and source unite swap/early return')
if __name__=='__main__':disable_network();unittest.main()
