"""Generated unite suffix: swap, early return, mutable counter alias and exact state."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_original_api import HEADER,SOURCE
from test_union_find_merge_invariant import FIXTURE
from nested_ir import lower_source,emit_lean
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
PROOF='''
open Proofs.UfUniteTail Proofs.StraightLine Proofs.VecWrite Proofs.VecExpr Proofs.UfSameCall
open Proofs.CppState
 def localState (groups x y : Int) : PS :=
   ⟨[⟨intTy,groups⟩,⟨intTy,99⟩,⟨intTy,x⟩,⟨intTy,y⟩],(List.range 14).map fun j =>
     if j=0 then ⟨0,true⟩ else if j=1 then ⟨0,false⟩ else if j=8 then ⟨2,true⟩
     else if j=13 then ⟨3,true⟩ else ⟨1,false⟩⟩
 def observation (r : PRW) := (r.ret,r.vec,r.ps.mem,r.ps.bs,r.wk)
 example : ∃ rank out, pexecW intTy 0 Proofs.UfUniteTail.tail (localState 2 3 0) second = some out ∧
     Valid out.vec 1 rank := by
   obtain ⟨rank,valid⟩ := secondValid
   obtain ⟨out,run,ret,vec,memory,work,cost,need,newRank,newValid⟩ := tail_correct (localState 2 3 0) second 2 rank valid
     2 3 0 3 0 (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩) (by decide) (by decide) (by decide)
     (by decide +kernel) ⟨-1,rfl,by decide⟩ ⟨-3,rfl,by decide⟩ 0
   exact ⟨newRank,out,run,by simpa using newValid⟩
 def swapped := pexecW intTy 0 Proofs.UfUniteTail.tail (localState 2 3 0) second
 #guard swapped.map observation == some (some 0,finalParents,[⟨intTy,1⟩,⟨intTy,99⟩,⟨intTy,0⟩,⟨intTy,3⟩],(localState 2 3 0).bs,2)
 #guard swapped.map (fun r => penv1 r.ps 2 intTy) == some (some 1)
 #guard swapped.map (fun r => r.ps.mem.length) == some 4
 #guard swapped.map (fun r => r.ps.bs.length) == some 14
 #guard swapped.map (fun r => decide (r.cost ≤ 160 ∧ r.need ≤ 88)) == some true
 def ordered := pexecW intTy 0 Proofs.UfUniteTail.tail (localState 3 0 2) first
 #guard ordered.map observation == some (some 0,second,[⟨intTy,2⟩,⟨intTy,99⟩,⟨intTy,0⟩,⟨intTy,2⟩],(localState 3 0 2).bs,2)
 def equal := pexecW intTy 0 Proofs.UfUniteTail.tail (localState 3 0 0) first
 #guard equal.map observation == some (some 0,first,(localState 3 0 0).mem,(localState 3 0 0).bs,0)
 -- The swap scope removes its temporary cell and binding and preserves the vector/counter.
 def swapOnly := pexecW intTy 0 Proofs.UfUniteTail.swapBlock (localState 2 3 0) ([] : List Int)
 #guard swapOnly.map observation == some (none,[],[⟨intTy,2⟩,⟨intTy,99⟩,⟨intTy,0⟩,⟨intTy,3⟩],(localState 2 3 0).bs,0)
 -- The write suffix updates the referenced counter rather than a vector sentinel.
 def writesOnly := pexecW intTy 0 writes (localState 2 0 3) second
 #guard writesOnly.map observation == some (some 0,finalParents,[⟨intTy,1⟩,⟨intTy,99⟩,⟨intTy,0⟩,⟨intTy,3⟩],(localState 2 0 3).bs,2)
 def readonly := {localState 2 3 0 with bs := (localState 2 3 0).bs.set 0 ⟨0,false⟩}
 #guard (pexecW intTy 0 Proofs.UfUniteTail.tail readonly second).isNone
 example := Proofs.UfUniteTail.body_eq
'''
class UnionFindUniteTailTests(unittest.TestCase):
    def test_source_suffix_counter_swap_return_and_resources(self):
        self.assertEqual((ROOT/'Proofs/Generated/UnionFindCandidate.lean').read_text(),
            emit_lean(lower_source(SOURCE,[SOURCE.parent]),'Proofs.UnionFindCandidateInstance'))
        with tempfile.TemporaryDirectory(prefix='union-find-unite-tail-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfUniteTail\n'+HEADER+FIXTURE+PROOF)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        print('source unite suffix: actual slot9/14 swap/early return, counter readonly alias, whole scalar/vector state, scope cleanup, work/need and writable condition')
if __name__=='__main__':disable_network();unittest.main()
