import Proofs.Cpp.Gen.CharCount
import Proofs.Cpp.Lib.Rle

/-! # `char_count` (library/string/char_count.hpp)

The runs of equal consecutive characters with their lengths (`rle`); the characters are the `char` values of the
string. At most `3 n + 2` steps for a string of length `n < 2^31`. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.CharCount

theorem signed_size (s : Array Int) (h : s.size < 2 ^ 31) :
    toSigned 32 (UInt64.ofInt (size s)).toNat = s.size := by
  rw [size, UInt64.ofInt, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have h64 : s.size < UInt64.size := by
    change s.size < 2 ^ 64
    omega
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h64]
  rw [toSigned, Nat.mod_eq_of_lt (by omega : s.size < 2 ^ 32)]
  simp only [show s.size < 2 ^ (32 - 1) from h, ↓reduceIte]

theorem foldl_rrStep_length {T : Type} [DecidableEq T] (xs : List T) (acc : List (T × Int)) :
    (xs.foldl rrStep acc).length ≤ acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (rrStep acc y)
    have h2 : (rrStep acc y).length ≤ acc.length + 1 := by
      unfold rrStep
      split
      · split <;> simp
      · simp
    omega

theorem rle_length_le {T : Type} [DecidableEq T] (xs : List T) : (rle xs).length ≤ xs.length := by
  have := foldl_rrStep_length xs []
  simpa [rle, rrle] using this

theorem char_count_spec (s : Array Int) (hs : s.size < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.char_count s
    ⦃⇓ r c => ⌜r.toList = rle s.toList ∧ c ≤ t0 + 2 + 3 * s.size⌝⦄ := by
  mvcgen [cp.char_count]
  case inv1 =>
    exact ⇓⟨xs, ret, pre, cnt⟩ c =>
      ⌜((xs.prefix = [] ∧ ret.toList = [] ∧ cnt = 0 ∧ pre = get s 0) ∨
        (ret.toList ++ [(pre, cnt)] = rle (xs.prefix.map (get s)))) ∧ c ≤ t0 + 1 + 2 * xs.prefix.length⌝
  all_goals simp +zetaDelta [signed_size s hs] at *
  · have : s = ([] : List Int).toArray := Array.eq_empty_of_size_eq_zero (by simp at *; omega)
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
      have heq : _ = get s _ := ‹(_ : Int) = get s _›
      simp [heq]
  · obtain ⟨hinv, hc⟩ := ‹(_ ∨ _) ∧ _›
    refine ⟨?_, by omega⟩
    rcases hinv with ⟨hp, hr, h0, hpre⟩ | hrle
    · have e := range_cursor ‹range _ _ = _ ++ _ :: _›
      subst hp
      simp at e
      have hneq : ¬ (_ : Int) = get s _ := ‹¬ _ = get s _›
      rw [e] at hneq
      exact absurd hpre hneq
    · rw [rle_snoc_last _ _ _ _ hrle.symm, if_neg ‹¬ _ = get s _›]
  · omega
  · obtain ⟨hinv, hc⟩ := ‹(_ ∨ _) ∧ _›
    have hne : s.size ≠ 0 := fun h => ‹¬ s = ([] : List Int).toArray› (Array.eq_empty_of_size_eq_zero h)
    rcases hinv with ⟨hp, _⟩ | hrle
    · exfalso
      have := congrArg List.length hp
      rw [range_length] at this
      simp at this
      first | omega | exact ‹¬ s = ([] : List Int).toArray› this
    · have hl := congrArg List.length hrle
      have hle := rle_length_le s.toList
      simp only [List.length_append, List.length_cons, List.length_nil, Array.length_toList] at hl hle
      exact ⟨hrle, by omega⟩

end Proofs.Cpp.CharCount
