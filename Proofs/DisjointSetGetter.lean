import Proofs.Generated.DisjointSetMethods
import Proofs.UfFieldsCounter

namespace Proofs.DisjointSetGetter
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.UfRootCall Proofs.UfFindCall
open Proofs.UfCompression Proofs.VectorFillCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedCall Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppNestedStmt
open Proofs.IntSim Proofs.CppNestedFacts
open Proofs.CppNestedRows
open Proofs.VecKit
open Proofs.QuotientFrame Proofs.DoublingCall Proofs.ScalarCall Proofs.ExtremaCall Proofs.VecWriteCall

open Proofs.VecKitW Proofs.PowModStep
open Proofs.UfClassInvariant Proofs.UfFieldsUnite

def fields (P : List Cell) (counter : Nat) (n : Int) : PS :=
  ⟨P++[⟨i32,n⟩],[⟨P.length,true⟩,⟨counter,true⟩]⟩

theorem body_eq : Proofs.Generated.DisjointSetMethods.Methods.DisjointSet_getNum.body =
    .sequence (.primitive (.ret (.variable i32 2))) Sk := rfl

theorem body_correct (P : List Cell) (counter : Nat) (n groups : Int) (vec : List Int)
    (found : P[counter]? = some ⟨i32,groups⟩) (valid : i32.valid groups = true) (fuel : Nat) :
    pexecW i32 fuel Proofs.Generated.DisjointSetMethods.Methods.DisjointSet_getNum.body (fields P counter n) vec =
      some ⟨fields P counter n,vec,some groups,2,P.length+6,0⟩ := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have env : penv1 (fields P counter n) 2 i32 = some groups := by
    simp [fields,penv1,penv,List.getElem?_append_left inside,found,valid]
  have value : vdenL i32 vec (penv1 (fields P counter n)) (.variable i32 2) = some groups := by
    rw [vdenL_scalar _ _ _ _ rfl]
    exact env
  have returned := seqW_ret (b := Sk) ((pexecW_prim i32 fuel _ _ _).trans
    (pstmtW_ret_ok i32 (fields P counter n) vec (.variable i32 2) groups value)) rfl
  rw [body_eq]
  simpa [fields,vwp,NExpr.nodes] using returned

end Proofs.DisjointSetGetter
