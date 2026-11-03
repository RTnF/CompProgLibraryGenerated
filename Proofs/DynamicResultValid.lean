import Proofs.DynamicCallPrepare
import Proofs.CppTargetCast

namespace Proofs.DynamicResultValid
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.DynamicExpr Proofs.DynamicExprLaws
open Proofs.MultiVecDynamic Proofs.DynamicContents

theorem convert_valid (ty : Ty) (x v : Int) (run : ty.convert x = some v) : ty.valid v = true := by
  cases hb : ty.boolean with
  | true =>
    cases zero : x == 0 <;> simp [Ty.convert,hb,zero] at run <;> subst v <;> simp [Ty.valid,hb]
  | false =>
    cases hs : ty.signed with
    | true =>
      by_cases valid : ty.valid x = true
      · simp [Ty.convert,hb,hs,valid] at run
        subst v; exact valid
      · simp [Ty.convert,hb,hs,valid] at run
    | false =>
      simp only [Ty.convert,hb,hs,Bool.false_eq_true,ite_false,Option.some.injEq] at run
      subst v
      have positive : 0 < (2^ty.width : Int) := Int.pow_pos (by decide)
      have low := Int.emod_nonneg x (by omega : (2^ty.width : Int) ≠ 0)
      have high := Int.emod_lt_of_pos x positive
      simp [Ty.valid,hb,hs]; omega

theorem target_valid (ty : Ty) (x v : Int) (run : ty.targetConvert x = some v) : ty.valid v = true := by
  by_cases signed : (ty.signed && !ty.boolean) = true
  · have hs := (Bool.and_eq_true_iff.mp signed).1
    have hb : ty.boolean = false := by simpa using (Bool.and_eq_true_iff.mp signed).2
    unfold Ty.targetConvert at run
    rw [if_pos signed] at run
    split at run
    · rename_i width
      have sizes : ty.width = 32 ∨ ty.width = 64 := by simpa using width
      have same := Option.some.inj run
      subst v
      have bounds := Proofs.CppTargetCast.decode_bounds ty.width x (by omega)
      simpa [Ty.valid,hs,hb] using bounds
    · contradiction
  · have converted : ty.convert x = some v := by simpa [Ty.targetConvert,signed] using run
    exact convert_valid ty x v converted

theorem division_valid (ty : Ty) (rem : Bool) (a b v : Int) (run : checkedDivRem ty rem a b = some v) : ty.valid v = true := by
  unfold checkedDivRem at run
  split at run
  · contradiction
  · split at run
    · contradiction
    · exact convert_valid ty _ v run

theorem bind_some {α β : Type} (o : Option α) (f : α → Option β) (v : β) (run : o.bind f = some v) :
    ∃ x, o = some x ∧ f x = some v := by
  cases o with
  | none => simp at run
  | some x => exact ⟨x,rfl,run⟩

theorem environment_valid (l : Locals) (slot : Nat) (ty : Ty) (v : Int) (run : environment l slot ty = some v) : ty.valid v = true := by
  unfold environment at run
  cases loc : l.slots[slot]? with
  | none => simp [loc] at run
  | some location =>
    cases location with
    | vector _ => simp [loc] at run
    | scalar index =>
      cases binding : l.bindings[index]? with
      | none => simp [loc,binding] at run
      | some b =>
        cases cell : l.memory[b.address]? with
        | none => simp [loc,binding,cell] at run
        | some c =>
          simp only [loc,binding,cell,Bind.bind,Option.bind] at run
          split at run
          · rename_i good
            have same := Option.some.inj run
            subst v; exact good.2
          · contradiction

theorem mapped_bool (o : Option Int) (v : Int)
    (run : o.map (fun b => if b = 0 then 0 else 1) = some v) : (⟨1,false,true⟩ : Ty).valid v = true := by
  cases o with
  | none => simp at run
  | some b =>
    simp only [Option.map_some,Option.some.injEq] at run
    subst v
    split <;> decide

-- The result's own checks suffice; no bounds on unrelated subexpressions are
-- introduced. This includes unsigned wrapping and target-compiler casts.
theorem expression (params : List Parameter) (l : Locals) (h : ContentsHeap) (e : NExpr) (v : Int)
    (run : denote params l h e = some v) : e.resultType.valid v = true := by
  cases e with
  | literal ty x =>
    rw [denote_scalar _ _ _ _ rfl] at run
    simp only [NExpr.denote] at run
    split at run
    · rename_i valid
      have same := Option.some.inj run
      subst v; exact valid
    · contradiction
  | «variable» ty slot =>
    rw [denote_scalar _ _ _ _ rfl] at run
    exact environment_valid l slot ty v run
  | cast ty e =>
    rw [DynamicExprLaws.cast_eq] at run
    obtain ⟨a,_,converted⟩ := bind_some _ _ _ run
    exact convert_valid ty a v converted
  | targetCast ty e =>
    rw [targetCast_eq] at run
    obtain ⟨a,_,converted⟩ := bind_some _ _ _ run
    exact target_valid ty a v converted
  | unary ty op e =>
    rw [unary_eq] at run
    obtain ⟨a,_,converted⟩ := bind_some _ _ _ run
    exact convert_valid ty _ v converted
  | binary ty op a b =>
    rw [binary_eq] at run
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ run
    obtain ⟨y,_,converted⟩ := bind_some _ _ _ rest
    exact convert_valid ty _ v converted
  | divrem ty rem a b =>
    rw [divrem_eq] at run
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ run
    obtain ⟨y,_,converted⟩ := bind_some _ _ _ rest
    exact division_valid ty rem x y v converted
  | logical conj a b =>
    rw [logical_eq] at run
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ run
    cases conj with
    | false =>
      by_cases zero : x = 0
      · exact mapped_bool _ v (by simpa [zero] using rest)
      · have same : (1 : Int) = v := by simpa [zero] using rest
        subst v; simp [NExpr.resultType,Ty.valid]
    | true =>
      by_cases zero : x = 0
      · have same : (0 : Int) = v := by simpa [zero] using rest
        subst v; simp [NExpr.resultType,Ty.valid]
      · exact mapped_bool _ v (by simpa [zero] using rest)
  | size element container =>
    obtain ⟨view,_,_,small,same⟩ := DynamicExprDecode.size params l h element container v run
    subst v
    simp [NExpr.resultType,Ty.valid]; omega
  | read ty container idx =>
    obtain ⟨_,_,_,_,_,_,valid⟩ := DynamicExprDecode.read params l h ty container idx v run
    exact valid

end Proofs.DynamicResultValid
