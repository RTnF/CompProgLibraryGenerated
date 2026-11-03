namespace DisjointSetGetterChecks
open Proofs.CppNestedCall Proofs.CppNestedProgram
example : Proofs.Generated.DisjointSetMethods.fieldNames = ["ps","_n","num_groups"] := rfl
example : Proofs.Generated.DisjointSetMethods.«DisjointSet_getNum_arguments» ⟨0,[2,1]⟩ [] =
    some [.vectorReference 0,.value (.variable ⟨32,true,false⟩ 2),.scalarReference 1] := rfl
abbrev ty : Proofs.CppScalar.Ty := ⟨32,true,false⟩
abbrev limit := Proofs.CppVectorBindings.sizeLimit ty
def initial (parents : List Int) (count n : Int) : Proofs.CppMoveContext.Context :=
  ⟨⟨⟨[some ⟨some 0,0,true,limit⟩],
    [some ⟨⟨0,parents,parents.length,limit,0⟩,fun _ => 0⟩],[],0,0,0⟩,[⟨0,true⟩]⟩,
    ⟨[⟨ty,n⟩,⟨ty,count⟩],[⟨0,true⟩,⟨1,true⟩],0,0,0⟩,
    [.vector 0,.scalar 0,.scalar 1],0,0⟩
#guard (match Proofs.Generated.DisjointSetMethods.«DisjointSet_getNum_callFuel» 16 (initial [-2,0,-1,-1] 3 4) ⟨0,[1,2]⟩ [] with
  | .finished (out,result) => result == .scalar 3 && out.scalars.memory.map (·.value) == [4,3]
  | _ => false)
#guard (match Proofs.Generated.DisjointSetMethods.«DisjointSet_getNum_callFuel» 16 (initial [] 0 0) ⟨0,[1,2]⟩ [] with
  | .finished (_,result) => result == .scalar 0 | _ => false)
#guard (match Proofs.Generated.DisjointSetMethods.«DisjointSet_getNum_callFuel» 16 (initial [] 1 4) ⟨0,[1,2]⟩ [] with
  | .finished (_,result) => result == .scalar 1 | _ => false)
end DisjointSetGetterChecks

example (P : List Proofs.CppState.Cell) (counter : Nat) (n groups : Int) (vec : List Int)
    (found : P[counter]? = some ⟨Proofs.DoublingNested.i32,groups⟩)
    (valid : Proofs.DoublingNested.i32.valid groups = true) (fuel : Nat) :
    Proofs.VecWrite.pexecW Proofs.DoublingNested.i32 fuel
      Proofs.Generated.DisjointSetMethods.Methods.DisjointSet_getNum.body
      (Proofs.DisjointSetGetter.fields P counter n) vec =
      some ⟨Proofs.DisjointSetGetter.fields P counter n,vec,some groups,2,P.length+6,0⟩ :=
  Proofs.DisjointSetGetter.body_correct P counter n groups vec found valid fuel
