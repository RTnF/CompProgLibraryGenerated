import Proofs.Cpp.Gen.ElementCount
import Proofs.Cpp.Lib.Rle

/-! # `element_count` (library/array/element_count.hpp)

The runs of equal consecutive elements with their lengths (`rle`), for any element type with decidable
equality; at most `2 n + 2` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ElementCount

theorem element_count_spec {T : Type} [Inhabited T] [DecidableEq T] (v : Array T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.element_count v
    ⦃⇓ r c => ⌜r.toList = rle v.toList ∧ c ≤ t0 + 2 + 2 * v.size⌝⦄ := by
  mvcgen [cp.element_count]
  case inv1 =>
    exact ⇓⟨xs, ret, pre, cnt⟩ c =>
      ⌜((xs.prefix = [] ∧ ret.toList = [] ∧ cnt = 0 ∧ pre = get v 0) ∨
        (ret.toList ++ [(pre, cnt)] = rle (xs.prefix.map (get v)))) ∧ c ≤ t0 + 1 + 2 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · have : v = #[] := Array.eq_empty_of_size_eq_zero (by simp [size] at *; omega)
    subst this
    exact ⟨by simp [rle, rrle], by omega⟩
  · obtain ⟨hinv, hc⟩ := ‹(_ ∨ _) ∧ _›
    refine ⟨?_, by omega⟩
    rcases hinv with ⟨hp, hr, h0, hpre⟩ | hrle
    · have e := range_cursor ‹range _ _ = _ ++ _ :: _›
      subst hp
      simp at e
      subst e
      simp [hr, h0, hpre, rle, rrle, rrStep]
    · rw [rle_snoc_last _ _ _ _ hrle.symm]
      have heq : _ = get v _ := ‹(_ : T) = get v _›
      simp [heq]
  · obtain ⟨hinv, hc⟩ := ‹(_ ∨ _) ∧ _›
    refine ⟨?_, by omega⟩
    rcases hinv with ⟨hp, hr, h0, hpre⟩ | hrle
    · have e := range_cursor ‹range _ _ = _ ++ _ :: _›
      subst hp
      simp at e
      have hneq : ¬ (_ : T) = get v _ := ‹¬ _ = get v _›
      rw [e] at hneq
      exact absurd hpre hneq
    · rw [rle_snoc_last _ _ _ _ hrle.symm, if_neg ‹¬ _ = get v _›]
  · omega
  · obtain ⟨hinv, hc⟩ := ‹(_ ∨ _) ∧ _›
    simp [size] at hinv hc ⊢
    have hne : v.size ≠ 0 := by simpa [size] using ‹¬ size v = 0›
    rcases hinv with ⟨hp, _⟩ | hrle
    · exfalso
      have := congrArg List.length hp
      simp +zetaDelta [range, Proofs.Cpp.size] at this
      subst this
      simp at hne
    · exact ⟨hrle, by omega⟩

end Proofs.Cpp.ElementCount
