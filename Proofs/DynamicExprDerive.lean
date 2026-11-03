import Proofs.DynamicExprAtoms

namespace Proofs.DynamicExprDerive
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicExprCertified Proofs.DynamicExprLaws

-- Ready describes which atomic lookup proofs are available. Scalar composition
-- requires no user-supplied intermediate values or conversion proofs.
inductive Ready (params : List Parameter) (l : Locals) (h : ContentsHeap) : NExpr → Prop where
  | scalar (e : NExpr) (scalar : e.scalarOnly = true) : Ready params l h e
  | atom (e : NExpr) (proved : ∀ v, denote params l h e = some v → Atomic params l h e v) : Ready params l h e
  | cast (ty : Ty) (e : NExpr) (inner : Ready params l h e) : Ready params l h (.cast ty e)
  | targetCast (ty : Ty) (e : NExpr) (inner : Ready params l h e) : Ready params l h (.targetCast ty e)
  | unary (ty : Ty) (op : Unary) (e : NExpr) (inner : Ready params l h e) : Ready params l h (.unary ty op e)
  | binary (ty : Ty) (op : Binary) (left right : NExpr) (first : Ready params l h left)
      (second : Ready params l h right) : Ready params l h (.binary ty op left right)
  | divrem (ty : Ty) (rem : Bool) (left right : NExpr) (first : Ready params l h left)
      (second : Ready params l h right) : Ready params l h (.divrem ty rem left right)
  | logical (conj : Bool) (left right : NExpr) (first : Ready params l h left)
      (second : Ready params l h right) : Ready params l h (.logical conj left right)

theorem known {params : List Parameter} {l : Locals} {h : ContentsHeap} {e : NExpr} {v : Int}
    (pure : denote params l h e = some v) (atomic : Atomic params l h e v) : Ready params l h e := by
  apply Ready.atom e
  intro value run
  have equal : value = v := Option.some.inj (run.symm.trans pure)
  subst value
  exact atomic

theorem failed {params : List Parameter} {l : Locals} {h : ContentsHeap} {e : NExpr}
    (pure : denote params l h e = none) : Ready params l h e := by
  apply Ready.atom e
  intro value run
  rw [pure] at run
  contradiction

theorem derive {params : List Parameter} {l : Locals} {h : ContentsHeap} {e : NExpr}
    (ready : Ready params l h e) : ∀ v, denote params l h e = some v → Evaluation params l h e v := by
  induction ready with
  | scalar e scalar =>
    intro v run
    rw [denote_scalar _ _ _ _ scalar] at run
    exact Evaluation.scalar e v scalar run
  | atom e proved => exact fun v run => Evaluation.atom e v (proved v run)
  | cast ty e inner ih =>
    intro v run
    rw [DynamicExprLaws.cast_eq] at run
    cases value : denote params l h e with
    | none => simp [value] at run
    | some a =>
      simp only [value,Option.bind_some] at run
      exact Evaluation.cast ty e a v (ih a value) run
  | targetCast ty e inner ih =>
    intro v run
    rw [targetCast_eq] at run
    cases value : denote params l h e with
    | none => simp [value] at run
    | some a =>
      simp only [value,Option.bind_some] at run
      exact Evaluation.targetCast ty e a v (ih a value) run
  | unary ty op e inner ih =>
    intro v run
    rw [unary_eq] at run
    cases value : denote params l h e with
    | none => simp [value] at run
    | some a =>
      simp only [value,Option.bind_some] at run
      exact Evaluation.unary ty op e a v (ih a value) run
  | binary ty op left right first second ih1 ih2 =>
    intro v run
    rw [binary_eq] at run
    cases va : denote params l h left with
    | none => simp [va] at run
    | some a =>
      simp only [va,Option.bind_some] at run
      cases vb : denote params l h right with
      | none => simp [vb] at run
      | some b =>
        simp only [vb,Option.bind_some] at run
        exact Evaluation.binary ty op left right a b v (ih1 a va) (ih2 b vb) run
  | divrem ty rem left right first second ih1 ih2 =>
    intro v run
    rw [divrem_eq] at run
    cases va : denote params l h left with
    | none => simp [va] at run
    | some a =>
      simp only [va,Option.bind_some] at run
      cases vb : denote params l h right with
      | none => simp [vb] at run
      | some b =>
        simp only [vb,Option.bind_some] at run
        exact Evaluation.divrem ty rem left right a b v (ih1 a va) (ih2 b vb) run
  | logical conj left right first second ih1 ih2 =>
    intro v run
    rw [logical_eq] at run
    cases va : denote params l h left with
    | none => simp [va] at run
    | some a =>
      simp only [va,Option.bind_some] at run
      cases conj with
      | false =>
        by_cases zero : a = 0
        · cases vb : denote params l h right with
          | none => simp [zero,vb] at run
          | some b =>
            simp [zero,vb] at run
            subst v
            exact Evaluation.logicalNext false left right a b (ih1 a va) (ih2 b vb) zero
        · simp [zero] at run
          subst v
          exact Evaluation.logicalShort false left right a (ih1 a va) zero
      | true =>
        by_cases zero : a = 0
        · simp [zero] at run
          subst v
          exact Evaluation.logicalShort true left right a (ih1 a va) zero
        · cases vb : denote params l h right with
          | none => simp [zero,vb] at run
          | some b =>
            simp [zero,vb] at run
            subst v
            exact Evaluation.logicalNext true left right a b (ih1 a va) (ih2 b vb) zero

end Proofs.DynamicExprDerive
