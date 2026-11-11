import Proofs.Cpp.Gen.VectorMax
import Proofs.Cpp.Lib.Basic

/-! # `vector_max` (library/array/vector_max.hpp)

For any linear order `T` and a nonempty vector, the result is an element of the vector and no element is
larger; `x.size` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.VectorMax

theorem vector_max_spec {T : Type} [LinearOrder T] [Inhabited T] (x : Array T) (hx : 0 < x.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.vector_max x
    ⦃⇓ r c => ⌜(∃ i, i < x.size ∧ r = x[i]!) ∧ (∀ i, i < x.size → x[i]! ≤ r) ∧ c = t0 + x.size⌝⦄ := by
  mvcgen [cp.vector_max]
  case inv1 =>
    exact ⇓⟨xs, m⟩ c => ⌜(∃ i, i ≤ xs.prefix.length ∧ m = x[i]!) ∧ (∀ i, i ≤ xs.prefix.length → x[i]! ≤ m) ∧
                         c = t0 + 1 + xs.prefix.length⌝
  all_goals simp_all +zetaDelta [size, get_eq]
  · -- a larger element
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    simp only [size] at hl
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    subst e
    obtain ⟨⟨j, hj, hm⟩, hle, hc⟩ := ‹(∃ i, _) ∧ _ ∧ _›
    have hgt : (_ : T) < _ := ‹(_ : T) < _›
    refine ⟨⟨_, ?_, rfl⟩, fun i hi => ?_, by omega⟩
    · omega
    · rcases Nat.lt_or_eq_of_le hi with h | h
      · exact le_trans (hle i (by omega)) (le_of_lt hgt)
      · subst h; simp only [toNat_one_add]; exact le_refl _
  · -- not larger
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    simp only [size] at hl
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    subst e
    obtain ⟨⟨j, hj, hm⟩, hle, hc⟩ := ‹(∃ i, _) ∧ _ ∧ _›
    have hge : (_ : T) ≤ _ := ‹x[_]! ≤ (_ : T)›
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

end Proofs.Cpp.VectorMax
