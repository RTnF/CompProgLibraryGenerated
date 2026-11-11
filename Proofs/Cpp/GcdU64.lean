import Proofs.Cpp.Gen.GcdU64
import Proofs.Cpp.Lib.Basic

/-! # `gcd_u64` (library/number_theory/gcd_u64.hpp)

Euclid's algorithm on 64 bit unsigned integers: the result is `Nat.gcd a b`, in at most
`log2 (a b) + 4` steps (`gcdCost`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.GcdU64

/-- A bound on the remaining iterations: the product of the pair halves on each step with `b ≤ a`. -/
def gcdCost (a b : Nat) : Nat := if b = 0 then 0 else (if b ≤ a then 1 else 2) + Nat.log2 (a * b)

theorem log2_mono' (a b : Nat) (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp [Nat.log2_zero]
  · rw [Nat.le_log2 (by omega)]; exact Nat.le_trans (Nat.log2_self_le (by omega)) h

theorem gcdCost_step (a b : Nat) (hb : 0 < b) : 1 + gcdCost b (a % b) ≤ gcdCost a b := by
  have hr : a % b < b := Nat.mod_lt _ hb
  by_cases hba : b ≤ a
  · by_cases hr0 : a % b = 0
    · simp [gcdCost, hr0, show b ≠ 0 by omega, hba]
    · have hq : 1 ≤ a / b := Nat.div_pos hba hb
      have hdm := Nat.mod_add_div a b
      have hbq : b ≤ b * (a / b) := Nat.le_mul_of_pos_right b hq
      have h2 : 2 * (a % b) ≤ a := by omega
      have hpos : 0 < b * (a % b) := Nat.mul_pos hb (by omega)
      have hl : Nat.log2 (2 * (b * (a % b))) = Nat.log2 (b * (a % b)) + 1 := Nat.log2_two_mul (by omega)
      have hm : 2 * (b * (a % b)) ≤ a * b := by
        have := Nat.mul_le_mul_left b h2
        rw [Nat.mul_comm a b]
        calc 2 * (b * (a % b)) = b * (2 * (a % b)) := by rw [← Nat.mul_assoc, Nat.mul_comm 2 b, Nat.mul_assoc]
          _ ≤ b * a := this
      have := log2_mono' _ _ hm
      simp [gcdCost, hr0, show b ≠ 0 by omega, hba, show a % b ≤ b by omega]
      omega
  · have e : a % b = a := Nat.mod_eq_of_lt (by omega)
    by_cases ha : a = 0
    · simp [gcdCost, e, ha, show b ≠ 0 by omega]
    · simp [gcdCost, e, ha, show b ≠ 0 by omega, hba, show a ≤ b by omega, Nat.mul_comm b a]
      omega

theorem gcd_u64_spec (a b : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.gcd_u64 a b
    ⦃⇓ r c => ⌜r.toNat = Nat.gcd a.toNat b.toNat ∧ c ≤ t0 + 2 + gcdCost a.toNat b.toNat⌝⦄ := by
  mvcgen [cp.gcd_u64]
  case inv =>
    exact ⟨fun ⟨x, y⟩ c => ⌜Nat.gcd x.toNat y.toNat = Nat.gcd a.toNat b.toNat ∧
                             c + gcdCost x.toNat y.toNat ≤ t0 + 1 + gcdCost a.toNat b.toNat⌝,
           fun ⟨x, _⟩ c => ⌜x.toNat = Nat.gcd a.toNat b.toNat ∧ c ≤ t0 + 2 + gcdCost a.toNat b.toNat⌝,
           fun ⟨_, y⟩ => y.toNat⟩
  all_goals simp_all +zetaDelta [fuel]
  · obtain ⟨hg, hc⟩ := ‹_ ∧ _›
    simp [gcdCost] at hc
    omega
  · obtain ⟨hg, hc⟩ := ‹_ ∧ _›
    have hy : (‹UInt64 × UInt64›).2 ≠ 0 := ‹_›
    have hy' : 0 < (‹UInt64 × UInt64›).2.toNat := by
      rcases Nat.eq_zero_or_pos (‹UInt64 × UInt64›).2.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hy
      · exact h
    have := gcdCost_step (‹UInt64 × UInt64›).1.toNat _ hy'
    refine ⟨⟨?_, ?_⟩, Nat.mod_lt _ hy'⟩
    · rw [← hg, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
    · omega
  · exact UInt64.toNat_lt _

end Proofs.Cpp.GcdU64
