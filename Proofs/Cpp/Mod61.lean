import Proofs.Cpp.Gen.Mod61
import Proofs.Cpp.Lib.Basic
import Proofs.Mod61Math

/-! # `mod61` (library/string/mod61.hpp)

Arithmetic modulo `2^61 - 1` on `UInt64`: `mod61` reduces any 64 bit value, `mul61` multiplies two values below
`2^61` without overflow into a value congruent to the product (`Proofs.Mod61Math.mul61_math`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Mod61Math

namespace Proofs.Cpp.Mod61

theorem shr_toNat (a : UInt64) (k : Nat) (hk : k < 64) : (a >>> (k.toUInt64)).toNat = a.toNat / 2 ^ k := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  congr 2
  simp; omega

theorem and_mask_toNat (a : UInt64) (k : Nat) (hk : k < 64) :
    (a &&& ((1 : UInt64) <<< k.toUInt64 - 1)).toNat = a.toNat % 2 ^ k := by
  have hp : 2 ^ k < 18446744073709551616 := by
    have := Nat.pow_lt_pow_right (a := 2) (by omega) hk; simpa using this
  have hm : ((1 : UInt64) <<< k.toUInt64 - 1).toNat = 2 ^ k - 1 := by
    rw [UInt64.toNat_sub_of_le]
    · rw [UInt64.toNat_shiftLeft]; simp
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hp]
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_shiftLeft]; simp
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hp]
      exact Nat.one_le_two_pow
  rw [UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

/-- `mod61(x) = x mod (2^61 - 1)` for every 64 bit `x`; one step. -/
theorem mod61_spec (x : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mod61 x ⦃⇓ r c => ⌜r.toNat = x.toNat % M61 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.mod61]
  all_goals simp +zetaDelta only at *
  all_goals
    have h1 : (x >>> 61).toNat = x.toNat / 2 ^ 61 := shr_toNat x 61 (by omega)
    have h2 : (x &&& ((1 : UInt64) <<< 61 - 1)).toNat = x.toNat % 2 ^ 61 := and_mask_toNat x 61 (by omega)
    have h3 : ((1 : UInt64) <<< 61 - 1).toNat = 2 ^ 61 - 1 := by decide
    have hx := x.toNat_lt
    have hs : ((x >>> 61) + (x &&& ((1 : UInt64) <<< 61 - 1))).toNat = x.toNat / 2 ^ 61 + x.toNat % 2 ^ 61 := by
      rw [UInt64.toNat_add, h1, h2]; simp; omega
    refine ⟨?_, by omega⟩
  · have hge := ‹decide _ = true›
    simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, hs, h3] at hge
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hs, h3]; exact hge), hs, h3]
    unfold M61; omega
  · have hlt := ‹¬decide _ = true›
    simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, hs, h3, Nat.not_le] at hlt
    rw [hs]; unfold M61; omega

/-- `mul61(a, b)` for `a, b < 2^61`: a value congruent to `a * b` modulo `2^61 - 1`, computed without overflow
(`mul61_math`); one step. -/
theorem mul61_spec (a b : UInt64) (ha : a.toNat < 2 ^ 61) (hb : b.toNat < 2 ^ 61) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mul61 a b ⦃⇓ r c => ⌜r.toNat % M61 = (a.toNat * b.toNat) % M61 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.mul61]
  simp +zetaDelta only at *
  have hau : (a >>> 31).toNat = a.toNat / 2 ^ 31 := shr_toNat a 31 (by omega)
  have had : (a &&& ((1 : UInt64) <<< 31 - 1)).toNat = a.toNat % 2 ^ 31 := and_mask_toNat a 31 (by omega)
  have hbu : (b >>> 31).toNat = b.toNat / 2 ^ 31 := shr_toNat b 31 (by omega)
  have hbd : (b &&& ((1 : UInt64) <<< 31 - 1)).toNat = b.toNat % 2 ^ 31 := and_mask_toNat b 31 (by omega)
  set au := a >>> 31
  set ad := a &&& ((1 : UInt64) <<< 31 - 1)
  set bu := b >>> 31
  set bd := b &&& ((1 : UInt64) <<< 31 - 1)
  have p1 : au.toNat * bu.toNat ≤ (2 ^ 30 - 1) * (2 ^ 30 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have p2 : ad.toNat * bu.toNat ≤ (2 ^ 31 - 1) * (2 ^ 30 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have p3 : au.toNat * bd.toNat ≤ (2 ^ 30 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have p4 : ad.toNat * bd.toNat ≤ (2 ^ 31 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hmid : (ad * bu + au * bd).toNat = ad.toNat * bu.toNat + au.toNat * bd.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul]; simp; omega
  set mid := ad * bu + au * bd
  have hmu : (mid >>> 30).toNat = mid.toNat / 2 ^ 30 := shr_toNat mid 30 (by omega)
  have hmd : (mid &&& ((1 : UInt64) <<< 30 - 1)).toNat = mid.toNat % 2 ^ 30 := and_mask_toNat mid 30 (by omega)
  set midu := mid >>> 30
  set midd := mid &&& ((1 : UInt64) <<< 30 - 1)
  have hsh : (midd <<< 31).toNat = midd.toNat * 2 ^ 31 := by
    rw [UInt64.toNat_shiftLeft]; simp; rw [Nat.shiftLeft_eq]; omega
  obtain ⟨hlt, hcong⟩ := mul61_math a.toNat b.toNat au.toNat ad.toNat bu.toNat bd.toNat mid.toNat midu.toNat midd.toNat
    ha hb hau had hbu hbd hmid hmu hmd
  have hres : (au * bu * (2 : UInt64) + midu + midd <<< (31 : UInt64) + ad * bd).toNat =
      au.toNat * bu.toNat * 2 + midu.toNat + midd.toNat * 2 ^ 31 + ad.toNat * bd.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul, UInt64.toNat_mul, hsh]
    simp; omega
  exact ⟨by rw [hres]; exact hcong, by omega⟩

end Proofs.Cpp.Mod61
