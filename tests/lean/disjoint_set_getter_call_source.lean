namespace DisjointSetGetterSourceExamples
open Proofs.CppMoveContext UfMoveCallExamples
-- ObjectRef scalar slots follow the original DisjointSet declaration order.
example := Proofs.DisjointSetGetterCall.call_resources moved.1 ⟨3,[5,4]⟩ 5 4 1 ⟨some 0,0,true,limit⟩
  ⟨2,true⟩ ⟨3,true⟩ 1 4 rfl (by decide +kernel) (by decide +kernel) rfl
  (by decide +kernel) rfl (by decide +kernel) contexts covered ownerOK.valid
-- The moved-from source has _n=4, count=1 and an empty vector header.
example := Proofs.DisjointSetGetterCall.call_resources moved.1 ⟨0,[2,1]⟩ 2 1 0 ⟨none,0,true,limit⟩
  ⟨0,true⟩ ⟨1,true⟩ 1 4 rfl (by decide +kernel) (by decide +kernel) rfl
  (by decide +kernel) rfl (by decide +kernel) contexts covered ownerOK.valid
def readonlySize : Context := {moved.1 with scalars := {moved.1.scalars with
  bindings := [⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,false⟩]}}
example := Proofs.DisjointSetGetterCall.call_resources readonlySize ⟨3,[5,4]⟩ 5 4 1 ⟨some 0,0,true,limit⟩
  ⟨2,true⟩ ⟨3,false⟩ 1 4 rfl (by decide +kernel) (by decide +kernel) rfl
  (by decide +kernel) rfl (by decide +kernel) contexts covered ownerOK.valid

def readonlyCounter : Context := {moved.1 with scalars := {moved.1.scalars with
  bindings := [⟨0,true⟩,⟨1,true⟩,⟨2,false⟩,⟨3,true⟩]}}
#guard (match Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_callFuel 2 readonlyCounter ⟨3,[5,4]⟩ [] with
  | .fault => true | _ => false)
end DisjointSetGetterSourceExamples
