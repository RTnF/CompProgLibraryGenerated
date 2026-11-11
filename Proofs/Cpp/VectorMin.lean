import Proofs.Cpp.Gen.VectorMin
import Proofs.Cpp.Lib.Basic

/-! # `vector_min` (library/array/vector_min.hpp)

For any linear order `T` and a nonempty vector, the result is an element of the vector and no element is
smaller; `x.size` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.VectorMin

theorem vector_min_spec {T : Type} [LinearOrder T] [Inhabited T] (x : Array T) (hx : 0 < x.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.vector_min x
    ⦃⇓ r c => ⌜(∃ i, i < x.size ∧ r = x[i]!) ∧ (∀ i, i < x.size → r ≤ x[i]!) ∧ c = t0 + x.size⌝⦄ := by
  mvcgen [cp.vector_min]
  case inv1 =>
    exact ⇓⟨xs, m⟩ c => ⌜(∃ i, i ≤ xs.prefix.length ∧ m = x[i]!) ∧ (∀ i, i ≤ xs.prefix.length → m ≤ x[i]!) ∧
                         c = t0 + 1 + xs.prefix.length⌝
  all_goals simp_all +zetaDelta [size, get_eq]
  · -- a smaller element
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    simp only [size] at hl
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    subst e
    obtain ⟨⟨j, hj, hm⟩, hle, hc⟩ := ‹(∃ i, _) ∧ _ ∧ _›
    have hgt : (_ : T) < _ := of_decide_eq_true ‹decide ((_ : T) < _) = true›
    refine ⟨⟨_, ?_, rfl⟩, fun i hi => ?_, by omega⟩
    · omega
    · rcases Nat.lt_or_eq_of_le hi with h | h
      · exact le_trans (le_of_lt hgt) (hle i (by omega))
      · subst h; simp only [toNat_one_add]; exact le_refl _
  · -- not smaller
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    simp only [size] at hl
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    subst e
    obtain ⟨⟨j, hj, hm⟩, hle, hc⟩ := ‹(∃ i, _) ∧ _ ∧ _›
    have hge : (_ : T) ≤ _ := not_lt.mp (of_decide_eq_false ‹decide ((_ : T) < _) = false›)
    refine ⟨⟨j, by omega, hm⟩, fun i hi => ?_, by omega⟩
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact hle i (by omega)
    · subst h; simp only [toNat_one_add] at hge; exact hge
  · obtain ⟨⟨j, hj, hm⟩, hle, hc⟩ := ‹(∃ i, _) ∧ _ ∧ _›
    simp [range] at hj hle hc ⊢
    refine ⟨⟨j, by omega, hm⟩, fun i hi => ?_, by omega⟩
    have := hle i (by omega)
    simpa [getElem!_pos, hi] using this
  all_goals omega

end Proofs.Cpp.VectorMin
