import Proofs.Cpp.Gen.CountrZero
import Proofs.Cpp.Lib.Basic

/-! # `countr_zero_u64` (library/number_theory/countr_zero.hpp)

The number of trailing zero bits of `n` (`64` for `0`): the result `r ≤ 64` has `2^r ∣ n` and, when
`r < 64`, not `2^(r+1) ∣ n`; `r + 2` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.CountrZero

theorem countr_zero_u64_spec (n : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.countr_zero_u64 n
    ⦃⇓ r c => ⌜0 ≤ r ∧ r ≤ 64 ∧ 2 ^ r.toNat ∣ n.toNat ∧ (r < 64 → ¬ 2 ^ (r.toNat + 1) ∣ n.toNat) ∧
               c = t0 + 2 + r.toNat⌝⦄ := by
  mvcgen [cp.countr_zero_u64]
  case inv =>
    exact ⟨fun ⟨m, x⟩ c => ⌜0 ≤ x ∧ x ≤ 64 ∧ m.toNat * 2 ^ x.toNat = n.toNat ∧ c = t0 + 1 + x.toNat⌝,
           fun ⟨_, x⟩ c => ⌜0 ≤ x ∧ x ≤ 64 ∧ 2 ^ x.toNat ∣ n.toNat ∧ (x < 64 → ¬ 2 ^ (x.toNat + 1) ∣ n.toNat) ∧
                            c = t0 + 2 + x.toNat⌝,
           fun ⟨_, x⟩ => (64 - x).toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  · -- the loop stops
    obtain ⟨h0, h64, hm, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have hstop : 64 ≤ (‹UInt64 × Int›).2 ∨ ¬(‹UInt64 × Int›).1 % 2 = 0 := ‹_›
    refine ⟨h0, h64, Dvd.intro_left _ hm, fun hlt hd => ?_, ?_⟩
    rotate_left
    · rw [hc]; omega
    have hodd : ¬(‹UInt64 × Int›).1 % 2 = 0 := hstop.resolve_left (by omega)
    have hodd' : (‹UInt64 × Int›).1.toNat % 2 ≠ 0 := fun h => hodd (UInt64.toNat_inj.mp (by simpa using h))
    rw [← hm, Nat.pow_succ, Nat.mul_comm _ (2 ^ _)] at hd
    have := Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos _) hd
    omega
  · -- one more zero bit
    obtain ⟨h0, h64, hm, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    obtain ⟨hlt, heven⟩ : (‹UInt64 × Int›).2 < 64 ∧ (‹UInt64 × Int›).1 % 2 = 0 := ‹_›
    have he : (‹UInt64 × Int›).1.toNat % 2 = 0 := by
      have := congrArg UInt64.toNat heven; simpa using this
    have e1 : ((‹UInt64 × Int›).2 + 1).toNat = (‹UInt64 × Int›).2.toNat + 1 := by omega
    refine ⟨⟨by omega, by omega, ?_, by omega⟩, by omega⟩
    rw [e1, Nat.pow_succ, ← hm]
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero he)
    calc (‹UInt64 × Int›).1.toNat / 2 * (2 ^ (‹UInt64 × Int›).2.toNat * 2)
        = (‹UInt64 × Int›).1.toNat / 2 * 2 * 2 ^ (‹UInt64 × Int›).2.toNat := by
          rw [Nat.mul_comm (2 ^ _) 2, Nat.mul_assoc]
      _ = _ := by rw [this]
  all_goals first | assumption | simp_all

end Proofs.Cpp.CountrZero
