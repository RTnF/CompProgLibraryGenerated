import Proofs.Cpp.Gen.FloorSum
import Proofs.Cpp.SafeMod
import Proofs.Cpp.FloorSumUnsigned
import Proofs.Math.FloorSumSignedArithmetic

/-! # `floor_sum` (library/number_theory/floor_sum.hpp)

The signed floor sum `Σ_{i<n} ⌊(a i + b) / m⌋` (`signedSum`). A negative `a` (or `b`) is replaced by `a mod m`, and
the correction `triangle n * (a / m)` (or `n * (b / m)`) is accumulated modulo `2^64` (`ansA_eq`, `ansB_eq`); the
rest is `floor_sum_unsigned`. The returned `int64_t` is the two's complement value of the sum modulo `2^64`
(`signedDecode64`, equal to the sum when it fits: `signedDecode64_exact`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.FloorSumArithmetic Proofs.FloorSumSignedArithmetic

namespace Proofs.Cpp.FloorSum

theorem W64 : ((2 : Int) ^ 64) = 18446744073709551616 := by norm_num

theorem ofInt_toNat (x : Int) : (UInt64.ofInt x).toNat = (x % 2 ^ 64).toNat := by
  unfold UInt64.ofInt
  rw [UInt64.toNat_ofNat']
  have h0 := Int.emod_nonneg x (by decide : (2:Int) ^ 64 ≠ 0)
  have h1 := Int.emod_lt_of_pos x (by decide : (0:Int) < 2 ^ 64)
  exact Nat.mod_eq_of_lt (by omega)

theorem ofInt_toNat_small (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) : (UInt64.ofInt x).toNat = x.toNat := by
  rw [ofInt_toNat, Int.emod_eq_of_lt h0 (by omega)]

theorem toSigned_small (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 63) : toSigned 64 (UInt64.ofInt x).toNat = x := by
  rw [ofInt_toNat_small x h0 (by omega)]
  unfold toSigned
  have : x.toNat < 2 ^ 63 := by omega
  rw [Nat.mod_eq_of_lt (by omega), if_pos (by simpa using this)]
  omega

theorem toSigned_ofInt (x : Int) : toSigned 64 (UInt64.ofInt x).toNat = signedDecode64 x := by
  rw [ofInt_toNat]
  have h0 := Int.emod_nonneg x (by decide : (2:Int) ^ 64 ≠ 0)
  have h1 := Int.emod_lt_of_pos x (by decide : (0:Int) < 2 ^ 64)
  unfold toSigned signedDecode64
  simp only [wordLimit]
  rw [W64] at h0 h1 ⊢
  rw [Nat.mod_eq_of_lt (by omega)]
  split_ifs <;> omega

theorem tri_eq (n : Int) (hn0 : 0 ≤ n) (hn : n < 2 ^ 32) :
    UInt64.ofInt n * UInt64.ofInt (n - 1) / 2 = UInt64.ofInt (triangle n.toNat : Int) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, UInt64.toNat_mul, ofInt_toNat, ofInt_toNat, ofInt_toNat]
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
  unfold triangle
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have hN : N < 2 ^ 32 := by omega
    have hp : N * (N - 1) < 2 ^ 64 :=
      calc N * (N - 1) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_le hN (by omega) (by omega)
        _ = 2 ^ 64 := by norm_num
    have e1 : ((N : Int) - 1) % 2 ^ 64 = ((N - 1 : Nat) : Int) := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
    have e2 : (N : Int) % 2 ^ 64 = N := Int.emod_eq_of_lt (Int.natCast_nonneg N) (by norm_num; omega)
    have e3 : ((N * (N - 1) / 2 : Nat) : Int) % 2 ^ 64 = ((N * (N - 1) / 2 : Nat) : Int) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [e1, e2, Int.toNat_natCast, Int.toNat_natCast, e3, Int.toNat_natCast, Nat.mod_eq_of_lt hp]
    rfl

theorem coef_eq (x m : Int) (hm0 : 1 ≤ m) (hm : m < 2 ^ 32) (hx0 : -2 ^ 63 ≤ x) (hx : x < 0) :
    (UInt64.ofInt (x % m) - UInt64.ofInt x) / UInt64.ofInt m = UInt64.ofInt (-(x / m)) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, UInt64.toNat_sub, ofInt_toNat, ofInt_toNat, ofInt_toNat, ofInt_toNat]
  have r0 := Int.emod_nonneg x (by omega : m ≠ 0)
  have r1 := Int.emod_lt_of_pos x (by omega : 0 < m)
  have ex : x % 2 ^ 64 = x + 2 ^ 64 := by
    rw [show x = (x + 2 ^ 64) + (-1) * 2 ^ 64 by ring, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (by omega) (by omega)]; ring
  have er : x % m % 2 ^ 64 = x % m := Int.emod_eq_of_lt r0 (by omega)
  have em : m % 2 ^ 64 = m := Int.emod_eq_of_lt (by omega) (by omega)
  have hc := coefficient_correction m x (by omega)
  -- -(x / m) = (x % m - x) / m ≥ 0
  have hq0 : 0 ≤ (x % m - x) / m := Int.ediv_nonneg (by omega) (by omega)
  have hq1 : (x % m - x) / m < 2 ^ 64 :=
    Int.lt_of_le_of_lt (Int.ediv_le_self _ (by omega)) (by omega)
  have eq : -(x / m) % 2 ^ 64 = -(x / m) := by rw [← hc]; exact Int.emod_eq_of_lt hq0 hq1
  rw [ex, er, em, eq, ← hc]
  have hs : (2 ^ 64 - (x + 2 ^ 64).toNat + (x % m).toNat) % 2 ^ 64 = (x % m - x).toNat := by omega
  rw [hs]
  have := Int.toNat_of_nonneg hq0
  have hd : ((x % m - x).toNat / m.toNat : Nat) = ((x % m - x) / m) := by
    rw [Int.natCast_ediv, Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  omega

theorem ansA_eq (n m a : Int) (hn0 : 0 ≤ n) (hn : n < 2 ^ 32) (hm0 : 1 ≤ m) (hm : m < 2 ^ 32)
    (ha0 : -2 ^ 63 ≤ a) (ha : a < 0) :
    0 - UInt64.ofInt n * UInt64.ofInt (n - 1) / 2 * ((UInt64.ofInt (a % m) - UInt64.ofInt a) / UInt64.ofInt m) =
      UInt64.ofInt ((triangle n.toNat : Int) * (a / m)) := by
  rw [tri_eq n hn0 hn, coef_eq a m hm0 hm ha0 ha, ← UInt64.ofInt_mul, UInt64.zero_sub, ← UInt64.ofInt_neg]
  congr 1; ring

theorem ansB_eq (ans : UInt64) (n m b : Int) (hm0 : 1 ≤ m) (hm : m < 2 ^ 32) (hb0 : -2 ^ 63 ≤ b) (hb : b < 0) :
    ans - UInt64.ofInt n * ((UInt64.ofInt (b % m) - UInt64.ofInt b) / UInt64.ofInt m) =
      ans + UInt64.ofInt (n * (b / m)) := by
  rw [coef_eq b m hm0 hm hb0 hb, ← UInt64.ofInt_mul, UInt64.sub_eq_add_neg, ← UInt64.ofInt_neg]
  congr 2; ring

theorem final_eq (C D S : Int) (r : UInt64) (hr : (r.toNat : Int) = D % 2 ^ 64) (hS : S = C + D) :
    toSigned 64 (UInt64.ofInt C + r).toNat = signedDecode64 S := by
  have er : r = UInt64.ofInt D := by
    apply UInt64.toNat_inj.mp
    rw [ofInt_toNat]; omega
  rw [er, ← UInt64.ofInt_add, toSigned_ofInt, hS]

theorem quot_zero (x m : Int) (positive : 0 < m) : (x % m) / m = 0 :=
  Int.ediv_eq_zero_of_lt (Int.emod_nonneg x (by omega)) (Int.emod_lt_of_pos x positive)

theorem sum_norm_a (n : Nat) (m a b : Int) (positive : 0 < m) :
    signedSum m a b n = (triangle n : Int) * (a / m) + signedSum m (a % m) b n := by
  have original := signedSum_normalization n m a b (by omega)
  have normalized := signedSum_normalization n m (a % m) b (by omega)
  simp only [quot_zero a m positive, Int.emod_emod, indexSum_eq_triangle, Int.mul_zero, Int.zero_add] at normalized
  rw [indexSum_eq_triangle] at original
  omega

theorem sum_norm_b (n : Nat) (m a b : Int) (positive : 0 < m) :
    signedSum m a b n = (n : Int) * (b / m) + signedSum m a (b % m) n := by
  have original := signedSum_normalization n m a b (by omega)
  have normalized := signedSum_normalization n m a (b % m) (by omega)
  simp only [quot_zero b m positive, Int.emod_emod, indexSum_eq_triangle, Int.mul_zero, Int.add_zero] at normalized
  rw [indexSum_eq_triangle] at original
  omega

theorem nat_sum (N M : Nat) (A B : Int) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    signedSum M A B N = (directSum M A.toNat B.toNat N : Int) := by
  have e := signedSum_of_nat N M A.toNat B.toNat
  rwa [Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB] at e

theorem nat_toNat (N : Nat) (h : N < 2 ^ 64) : (UInt64.ofInt (N : Int)).toNat = N := by
  rw [ofInt_toNat_small _ (Int.natCast_nonneg N) (by omega)]; simp

theorem gcd_bound (M x : Nat) (hx : x < M) : gcdCost M x ≤ 3 + 2 * Nat.log2 M := by
  unfold gcdCost
  split
  · omega
  · have h1 : Nat.log2 (M * x) ≤ Nat.log2 (M * M) := log2_mono2 _ _ (Nat.mul_le_mul_left _ (by omega))
    have h2 : Nat.log2 (M * M) < 2 * Nat.log2 M + 2 := by
      rw [Nat.log2_lt (Nat.mul_ne_zero (by omega) (by omega))]
      have := Nat.lt_log2_self (n := M)
      calc M * M < 2 ^ (Nat.log2 M + 1) * 2 ^ (Nat.log2 M + 1) := Nat.mul_lt_mul_of_lt_of_le this this.le (by positivity)
        _ = 2 ^ (2 * Nat.log2 M + 2) := by rw [← Nat.pow_add]; congr 1; omega
    split <;> omega

theorem close (n m C A B S : Int) (r : UInt64) (c s t0 k : Nat) (hn0 : 0 ≤ n) (hn : n < 2 ^ 32)
    (hm0 : 1 ≤ m) (hm : m < 2 ^ 32) (hA0 : 0 ≤ A) (hA1 : A < 2 ^ 63) (hB0 : 0 ≤ B) (hB1 : B < 2 ^ 63)
    (hr : r.toNat = directSum (UInt64.ofInt m).toNat (UInt64.ofInt A).toNat (UInt64.ofInt B).toNat
      (UInt64.ofInt n).toNat % wordLimit)
    (hc : c ≤ s + k + gcdCost (UInt64.ofInt m).toNat ((UInt64.ofInt A).toNat % (UInt64.ofInt m).toNat))
    (hS : S = C + signedSum m A B n.toNat) (hs : s = t0) (hk : k ≤ 7) :
    toSigned 64 (UInt64.ofInt C + r).toNat = signedDecode64 S ∧ c ≤ t0 + 10 + 2 * Nat.log2 m.toNat := by
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
  obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0:Int) ≤ m)
  simp only [nat_toNat N (by omega), nat_toNat M (by omega), ofInt_toNat_small A hA0 (by omega),
    ofInt_toNat_small B hB0 (by omega)] at hr hc
  have hg := gcd_bound M (A.toNat % M) (Nat.mod_lt _ (by omega))
  refine ⟨final_eq C (directSum M A.toNat B.toNat N) S r ?_ ?_, ?_⟩
  · rw [hr, wordLimit]; push_cast; rfl
  · rw [hS, Int.toNat_natCast, nat_sum N M A B hA0 hB0]
  · simp only [Int.toNat_natCast]; omega

/-- `floor_sum n m a b` for `0 ≤ n < 2^32`, `1 ≤ m < 2^32` and 64-bit `a`, `b`: the floor sum decoded as a
signed 64-bit value, in `O(log m)` ticks. -/
theorem floor_sum_spec (n m a b : Int) (hn0 : 0 ≤ n) (hn : n < 2 ^ 32) (hm0 : 1 ≤ m) (hm : m < 2 ^ 32)
    (ha : -2 ^ 63 ≤ a ∧ a < 2 ^ 63) (hb : -2 ^ 63 ≤ b ∧ b < 2 ^ 63) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.floor_sum n m a b
    ⦃⇓ r c => ⌜r = signedDecode64 (signedSum m a b n.toNat) ∧ c ≤ t0 + 10 + 2 * Nat.log2 m.toNat⌝⦄ := by
  mvcgen [cp.floor_sum]
  case vc6.isTrue.isTrue.isTrue.isTrue =>
    intro r c hr hc
    have hA : a < 0 := by simpa using ‹decide (a < 0) = true›
    have hB : b < 0 := by simpa using ‹decide (b < 0) = true›
    have ra0 := Int.emod_nonneg a (by omega : m ≠ 0)
    have ra1 := Int.emod_lt_of_pos a (by omega : 0 < m)
    have rb0 := Int.emod_nonneg b (by omega : m ≠ 0)
    have rb1 := Int.emod_lt_of_pos b (by omega : 0 < m)
    simp +zetaDelta only [WP.pure, ansA_eq n m a hn0 hn hm0 hm ha.1 hA, ansB_eq _ n m b hm0 hm hb.1 hB,
      toSigned_small (a % m) ra0 (by omega), toSigned_small (b % m) rb0 (by omega), ← UInt64.ofInt_add] at hr hc ⊢
    refine close n m _ (a % m) (b % m) _ r c _ t0 5 hn0 hn hm0 hm ra0 (by omega) rb0 (by omega) hr hc ?_
      ‹_› (by omega)
    rw [sum_norm_a _ m a b (by omega), sum_norm_b _ m (a % m) b (by omega), Int.toNat_of_nonneg hn0]; ring
  case vc10.isTrue.isTrue.isTrue.isFalse =>
    intro r c hr hc
    have hA : a < 0 := by simpa using ‹decide (a < 0) = true›
    have hB : 0 ≤ b := by simpa using ‹¬decide (b < 0) = true›
    have ra0 := Int.emod_nonneg a (by omega : m ≠ 0)
    have ra1 := Int.emod_lt_of_pos a (by omega : 0 < m)
    simp +zetaDelta only [WP.pure, ansA_eq n m a hn0 hn hm0 hm ha.1 hA,
      toSigned_small (a % m) ra0 (by omega)] at hr hc ⊢
    refine close n m _ (a % m) b _ r c _ t0 4 hn0 hn hm0 hm ra0 (by omega) hB hb.2 hr hc ?_ ‹_› (by omega)
    rw [sum_norm_a _ m a b (by omega)]
  case vc15.isTrue.isTrue.isFalse.isTrue =>
    intro r c hr hc
    have hA : 0 ≤ a := by simpa using ‹¬decide (a < 0) = true›
    have hB : b < 0 := by simpa using ‹decide (b < 0) = true›
    have rb0 := Int.emod_nonneg b (by omega : m ≠ 0)
    have rb1 := Int.emod_lt_of_pos b (by omega : 0 < m)
    simp +zetaDelta only [WP.pure, ansB_eq _ n m b hm0 hm hb.1 hB, toSigned_small (b % m) rb0 (by omega),
      UInt64.zero_add] at hr hc ⊢
    refine close n m _ a (b % m) _ r c _ t0 4 hn0 hn hm0 hm hA ha.2 rb0 (by omega) hr hc ?_ ‹_› (by omega)
    rw [sum_norm_b _ m a b (by omega), Int.toNat_of_nonneg hn0]
  case vc19.isTrue.isTrue.isFalse.isFalse =>
    intro r c hr hc
    have hA : 0 ≤ a := by simpa using ‹¬decide (a < 0) = true›
    have hB : 0 ≤ b := by simpa using ‹¬decide (b < 0) = true›
    simp +zetaDelta only [WP.pure] at hr hc ⊢
    have := close n m 0 a b _ r c _ t0 3 hn0 hn hm0 hm hA ha.2 hB hb.2 hr hc (by ring) ‹_› (by omega)
    rw [show UInt64.ofInt 0 = 0 from rfl] at this
    exact this
  all_goals try (rw [ofInt_toNat_small _ (by omega) (by omega)]; (try simp only [inputLimit]); omega)
  all_goals (simp [shl] at *; omega)

end Proofs.Cpp.FloorSum
