import Proofs.Cpp.Gen.Interval
import Proofs.Cpp.Lib.Basic

/-! # `Interval<T>` (library/interval/interval.hpp)

Half-open intervals `[s, e)` over a linear order `T`, with the emptiness flag `is_n` (`s == e`). The six comparisons
are the lexicographic order on `(s, e, is_n)` (`false < true`), as the original's defaulted `operator<=>`;
`intersection` is the common part (`[0, 0)` when they do not overlap). Every member is one step. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.Interval

variable {T : Type} [LinearOrder T]

/-- The lexicographic order on `(s, e, is_n)`. -/
def ILt (a b : cp.Interval T) : Prop :=
  a.s < b.s ∨ (a.s = b.s ∧ (a.e < b.e ∨ (a.e = b.e ∧ a.is_n = false ∧ b.is_n = true)))

instance (a b : cp.Interval T) : Decidable (ILt a b) := by unfold ILt; infer_instance

theorem ext_iff2 (a b : cp.Interval T) : a = b ↔ a.s = b.s ∧ a.e = b.e ∧ a.is_n = b.is_n := by
  cases a; cases b; simp

instance : DecidableEq (cp.Interval T) := fun a b => decidable_of_iff _ (ext_iff2 a b).symm

theorem init_spec (s e : T) (h : s ≤ e) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.init_T_T s e ⦃⇓ r c => ⌜r = ⟨s, e, decide (s = e)⟩ ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.init_T_T]
  all_goals simp_all +zetaDelta

theorem init_0_spec [Zero T] (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.Interval.init_0 : Cpp.M (cp.Interval T)) ⦃⇓ r c => ⌜r = ⟨0, 0, true⟩ ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.init_0]
  all_goals simp_all +zetaDelta

theorem start_spec (a : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.start a ⦃⇓ r c => ⌜r = a.s ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.start]; all_goals simp_all +zetaDelta

theorem end_spec (a : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.end_ a ⦃⇓ r c => ⌜r = a.e ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.end_]; all_goals simp_all +zetaDelta

theorem is_null_spec (a : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.is_null a ⦃⇓ r c => ⌜r = a.is_n ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.is_null]; all_goals simp_all +zetaDelta

theorem length_spec [Sub T] (a : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.length a ⦃⇓ r c => ⌜r = a.e - a.s ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.length]; all_goals simp_all +zetaDelta

theorem op_eq_spec (a b : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.op_eq a b ⦃⇓ r c => ⌜r = decide (a = b) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.op_eq]
  all_goals simp +zetaDelta at *
  refine ⟨?_, by assumption⟩
  rw [Bool.eq_iff_iff]; simp [ext_iff2]; tauto

theorem op_ne_spec (a b : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.op_ne a b ⦃⇓ r c => ⌜r = decide (a ≠ b) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.op_ne]
  all_goals simp +zetaDelta at *
  refine ⟨?_, by assumption⟩
  rw [Bool.eq_iff_iff]; simp [ext_iff2]; tauto

theorem op_lt_spec (a b : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.op_lt a b ⦃⇓ r c => ⌜r = decide (ILt a b) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.op_lt]
  all_goals simp +zetaDelta at *
  refine ⟨?_, by assumption⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]; simp [ILt, and_assoc]

theorem op_gt_spec (a b : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.op_gt a b ⦃⇓ r c => ⌜r = decide (ILt b a) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.op_gt]
  all_goals simp +zetaDelta at *
  refine ⟨?_, by assumption⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]; simp only [ILt, @eq_comm _ b.s a.s, @eq_comm _ b.e a.e]; simp [and_assoc]; tauto

theorem op_le_spec (a b : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.op_le a b ⦃⇓ r c => ⌜r = decide (ILt a b ∨ a = b) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.op_le]
  all_goals simp +zetaDelta at *
  refine ⟨?_, by assumption⟩
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_iff]
  rcases a with ⟨s, e, i⟩; rcases b with ⟨s', e', i'⟩
  cases i <;> cases i' <;> simp [ILt, ext_iff2] <;> tauto

theorem op_ge_spec (a b : cp.Interval T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.op_ge a b ⦃⇓ r c => ⌜r = decide (ILt b a ∨ a = b) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Interval.op_ge]
  all_goals simp +zetaDelta at *
  refine ⟨?_, by assumption⟩
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_iff]
  rcases a with ⟨s, e, i⟩; rcases b with ⟨s', e', i'⟩
  cases i <;> cases i' <;> simp [ILt, ext_iff2] <;> constructor <;> intro h <;>
    (try simp_all [eq_comm]) <;> (try tauto)

/-- `intersection(b)` of two valid intervals: `[max, min)` when they overlap, otherwise `[0, 0)`. -/
theorem intersection_spec [Zero T] (a b : cp.Interval T) (ha : a.s ≤ a.e) (hb : b.s ≤ b.e) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Interval.intersection a b
    ⦃⇓ r c => ⌜r = (if a.e ≤ b.s ∨ b.e ≤ a.s then ⟨0, 0, true⟩ else
                 ⟨max a.s b.s, min a.e b.e, decide (max a.s b.s = min a.e b.e)⟩) ∧ c = t0 + 2⌝⦄ := by
  mvcgen [cp.Interval.intersection, cp.Interval.init_0, cp.Interval.init_T_T]
  all_goals simp +zetaDelta at *
  · refine ⟨fun h1 h2 => ?_, by assumption⟩
    exfalso
    rcases ‹a.e ≤ b.s ∨ b.e ≤ a.s› with h | h
    · exact absurd h (not_le.mpr h1)
    · exact absurd h (not_le.mpr h2)
  · obtain ⟨o1, o2⟩ := ‹b.s < a.e ∧ a.s < b.e›
    refine ⟨fun h => ?_, by assumption⟩
    exfalso
    rcases h with h | h
    · exact absurd h (not_le.mpr o1)
    · exact absurd h (not_le.mpr o2)
  · obtain ⟨o1, o2⟩ := ‹b.s < a.e ∧ a.s < b.e›
    exact absurd (‹a.s ≤ a.e → b.s ≤ a.e → a.s ≤ b.e → b.e < b.s› ha (le_of_lt o1) (le_of_lt o2)) (not_lt.mpr hb)

end Proofs.Cpp.Interval
