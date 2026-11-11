import Proofs.Cpp.Gen.PowMod
import Proofs.Cpp.Lib.Basic

/-! # `pow_mod` (library/number_theory/pow_mod.hpp)

Binary exponentiation: for `1 ≤ m ≤ 2^32`, `base^exp mod m` in `bitWidth exp + 2` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.PowMod

/-- `x * y % m` on 64 bit values is the exact product modulo `m` when `x, y < m ≤ 2^32`. -/
theorem mulmod_toNat (x y m : UInt64) (hm : m.toNat ≤ 2 ^ 32) (hx : x.toNat < m.toNat) (hy : y.toNat < m.toNat) :
    (x * y % m).toNat = x.toNat * y.toNat % m.toNat := by
  have hlt : x.toNat * y.toNat < 2 ^ 64 := by
    calc x.toNat * y.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' (by omega) (by omega)
      _ = 2 ^ 64 := by norm_num
  rw [UInt64.toNat_mod, UInt64.toNat_mul, Nat.mod_eq_of_lt hlt]

theorem pow_split (b e : Nat) : b ^ e = (if e % 2 = 1 then b else 1) * (b * b) ^ (e / 2) := by
  have h : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
  conv_lhs => rw [h, pow_add, pow_mul, sq]
  rcases Nat.mod_two_eq_zero_or_one e with h0 | h1
  · rw [h0]; simp
  · rw [h1, pow_one, if_pos rfl, mul_comm]

theorem mul_pow_mod (x b k m : Nat) : x * (b % m) ^ k % m = x * b ^ k % m := by
  rw [← Nat.mul_mod_mod, ← Nat.pow_mod, Nat.mul_mod_mod]

theorem step_eq (r b e m : Nat) :
    (if e % 2 = 1 then r * b % m else r) * (b * b % m) ^ (e / 2) % m = r * b ^ e % m := by
  rw [pow_split b e, mul_pow_mod]
  split
  · rw [Nat.mod_mul_mod, mul_assoc]
  · simp

theorem pow_mod_spec (base exp m : UInt64) (hm1 : 1 ≤ m.toNat) (hm : m.toNat ≤ 2 ^ 32) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.pow_mod base exp m
    ⦃⇓ r c => ⌜r.toNat = base.toNat ^ exp.toNat % m.toNat ∧ c = t0 + 2 + bitWidth exp.toNat⌝⦄ := by
  mvcgen [cp.pow_mod]
  case inv =>
    exact ⟨fun ⟨res, b, e⟩ c => ⌜res.toNat < m.toNat ∧ b.toNat < m.toNat ∧
                                  res.toNat * b.toNat ^ e.toNat % m.toNat = base.toNat ^ exp.toNat % m.toNat ∧
                                  c + bitWidth e.toNat = t0 + 1 + bitWidth exp.toNat⌝,
           fun ⟨res, _, _⟩ c => ⌜res.toNat = base.toNat ^ exp.toNat % m.toNat ∧ c = t0 + 2 + bitWidth exp.toNat⌝,
           fun ⟨_, _, e⟩ => e.toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  · obtain ⟨hr, hb, he, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have hz : _ = (0 : UInt64) := ‹(_ : UInt64) = 0›
    simp [hz] at he hc
    exact ⟨by rw [← he, Nat.mod_eq_of_lt hr], by omega⟩
  · obtain ⟨hr, hb, he, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have hpar : (‹UInt64 × UInt64 × UInt64›.2.2 &&& 1).toNat = (‹UInt64 × UInt64 × UInt64›).2.2.toNat % 2 := by
      simp [UInt64.toNat_and, Nat.and_one_is_mod]
    have hp : (‹UInt64 × UInt64 × UInt64›).2.2.toNat % 2 = 1 := by
      have h := ‹¬ (_ &&& 1 : UInt64) = 0›
      rcases Nat.mod_two_eq_zero_or_one (‹UInt64 × UInt64 × UInt64›).2.2.toNat with h0 | h1
      · exact absurd (UInt64.toNat_inj.mp (by rw [hpar, h0]; rfl)) h
      · exact h1
    set R := (‹UInt64 × UInt64 × UInt64›).1.toNat with hR
    set B := (‹UInt64 × UInt64 × UInt64›).2.1.toNat with hB
    set E := (‹UInt64 × UInt64 × UInt64›).2.2.toNat with hE
    have hE0 : 0 < E := by
      omega
    have hsh : E >>> 1 = E / 2 := by simp [Nat.shiftRight_eq_div_pow]
    have hbw := bitWidth_div_two E hE0
    have hRB : R * B < 18446744073709551616 := by nlinarith
    have hBB : B * B < 18446744073709551616 := by nlinarith
    have key := step_eq R B E m.toNat
    simp only [hp, ↓reduceIte, Nat.zero_ne_one, ite_false] at key
    simp only [hsh, Nat.mod_eq_of_lt hRB, Nat.mod_eq_of_lt hBB]
    refine ⟨⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega), ?_, by omega⟩, by omega⟩
    · rw [Nat.mod_mul_mod] at key; rw [key, he]
  · obtain ⟨hr, hb, he, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have hpar : (‹UInt64 × UInt64 × UInt64›.2.2 &&& 1).toNat = (‹UInt64 × UInt64 × UInt64›).2.2.toNat % 2 := by
      simp [UInt64.toNat_and, Nat.and_one_is_mod]
    have hp : (‹UInt64 × UInt64 × UInt64›).2.2.toNat % 2 = 0 := by
      have h := congrArg UInt64.toNat ‹(_ &&& 1 : UInt64) = 0›
      rw [hpar] at h; simpa using h
    set R := (‹UInt64 × UInt64 × UInt64›).1.toNat with hR
    set B := (‹UInt64 × UInt64 × UInt64›).2.1.toNat with hB
    set E := (‹UInt64 × UInt64 × UInt64›).2.2.toNat with hE
    have hE0 : 0 < E := by
      have hne := ‹¬ (_ : UInt64) = 0›
      rcases Nat.eq_zero_or_pos E with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa [hE] using h)) hne
      · exact h
    have hsh : E >>> 1 = E / 2 := by simp [Nat.shiftRight_eq_div_pow]
    have hbw := bitWidth_div_two E hE0
    have hRB : R * B < 18446744073709551616 := by nlinarith
    have hBB : B * B < 18446744073709551616 := by nlinarith
    have key := step_eq R B E m.toNat
    simp only [hp, ↓reduceIte, Nat.zero_ne_one, ite_false] at key
    simp only [hsh, Nat.mod_eq_of_lt hRB, Nat.mod_eq_of_lt hBB]
    refine ⟨⟨hr, Nat.mod_lt _ (by omega), ?_, by omega⟩, by omega⟩
    · rw [key, he]
  · refine ⟨⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega), (Nat.pow_mod _ _ _).symm, ‹_›⟩, UInt64.toNat_lt _⟩
  · exact ‹_›

end Proofs.Cpp.PowMod
