import Proofs.DynamicExpr

namespace Proofs.DynamicExprLaws
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedEval
open Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicExpr

theorem cast_eq (params : List Parameter) (l : Locals) (h : ContentsHeap) (ty : Ty)  (operand : NExpr) :
    denote params l h (.cast ty operand) = (denote params l h operand).bind ty.convert := by
  by_cases scalar : operand.scalarOnly = true
  · rw [denote_scalar params l h (.cast ty operand) (by simpa [NExpr.scalarOnly] using scalar),denote_scalar params l h operand scalar]
    rfl
  · rw [denote.eq_def]
    simp [NExpr.scalarOnly,scalar]

theorem targetCast_eq (params : List Parameter) (l : Locals) (h : ContentsHeap) (ty : Ty)  (operand : NExpr) :
    denote params l h (.targetCast ty operand) = (denote params l h operand).bind ty.targetConvert := by
  by_cases scalar : operand.scalarOnly = true
  · rw [denote_scalar params l h (.targetCast ty operand) (by simpa [NExpr.scalarOnly] using scalar),denote_scalar params l h operand scalar]
    rfl
  · rw [denote.eq_def]
    simp [NExpr.scalarOnly,scalar]

theorem unary_eq (params : List Parameter) (l : Locals) (h : ContentsHeap) (ty : Ty) (op : Unary) (operand : NExpr) :
    denote params l h (.unary ty op operand) = (denote params l h operand).bind fun v => ty.convert (unaryValue op v) := by
  by_cases scalar : operand.scalarOnly = true
  · rw [denote_scalar params l h (.unary ty op operand) (by simpa [NExpr.scalarOnly] using scalar),denote_scalar params l h operand scalar]
    rfl
  · rw [denote.eq_def]
    simp [NExpr.scalarOnly,scalar]

theorem binary_eq (params : List Parameter) (l : Locals) (h : ContentsHeap) (ty : Ty) (op : Binary) (left right : NExpr) :
    denote params l h (.binary ty op left right) = (denote params l h left).bind fun a =>
      (denote params l h right).bind fun b => ty.convert (binaryValue op a b) := by
  by_cases scalar : (left.scalarOnly && right.scalarOnly) = true
  · obtain ⟨sl,sr⟩ := Bool.and_eq_true_iff.mp scalar
    rw [denote_scalar params l h (.binary ty op left right) (by simpa [NExpr.scalarOnly] using scalar),denote_scalar params l h left sl,denote_scalar params l h right sr]
    rfl
  · rw [denote.eq_def]
    simp [NExpr.scalarOnly,scalar]

theorem divrem_eq (params : List Parameter) (l : Locals) (h : ContentsHeap) (ty : Ty) (rem : Bool) (left right : NExpr) :
    denote params l h (.divrem ty rem left right) = (denote params l h left).bind fun a =>
      (denote params l h right).bind fun b => checkedDivRem ty rem a b := by
  by_cases scalar : (left.scalarOnly && right.scalarOnly) = true
  · obtain ⟨sl,sr⟩ := Bool.and_eq_true_iff.mp scalar
    rw [denote_scalar params l h (.divrem ty rem left right) (by simpa [NExpr.scalarOnly] using scalar),denote_scalar params l h left sl,denote_scalar params l h right sr]
    rfl
  · rw [denote.eq_def]
    simp [NExpr.scalarOnly,scalar]

theorem logical_eq (params : List Parameter) (l : Locals) (h : ContentsHeap) (conj : Bool) (left right : NExpr) :
    denote params l h (.logical conj left right) = (denote params l h left).bind fun a =>
      if conj then (if a = 0 then some 0 else (denote params l h right).map fun b => if b = 0 then 0 else 1)
      else (if a = 0 then (denote params l h right).map fun b => if b = 0 then 0 else 1 else some 1) := by
  by_cases scalar : (left.scalarOnly && right.scalarOnly) = true
  · obtain ⟨sl,sr⟩ := Bool.and_eq_true_iff.mp scalar
    rw [denote_scalar params l h (.logical conj left right) (by simpa [NExpr.scalarOnly] using scalar),denote_scalar params l h left sl,denote_scalar params l h right sr]
    cases conj <;> cases hl : left.denote (environment l) <;> cases hr : right.denote (environment l) <;>
      simp [NExpr.denote,hl,hr]
  · rw [denote.eq_def]
    simp [NExpr.scalarOnly,scalar]

end Proofs.DynamicExprLaws
