import Proofs.LazySegMath

namespace Proofs.LazySegAncLeaf
open Proofs.SegTreeMath

/-- The leaf `x` lies under the node `k` of height `j` exactly when `x` is in the block `[k * 2^j, (k + 1) * 2^j)`. -/
theorem anc_leaf_iff (N h k j x : Nat) (hN : N = 2 ^ h) (hk1 : N ≤ k * 2 ^ j) (hk2 : k * 2 ^ j < 2 * N)
    (hx1 : N ≤ x) (hx2 : x < 2 * N) :
    Anc x k ↔ k * 2 ^ j ≤ x ∧ x < (k + 1) * 2 ^ j := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hNpos : 0 < N := by rw [hN]; exact Nat.two_pow_pos h
  have hk0 : 1 ≤ k := by
    apply Classical.byContradiction
    intro hc
    have : k = 0 := by omega
    subst this
    simp at hk1
    omega
  constructor
  · rintro ⟨t, ht⟩
    have hlow : k * 2 ^ t ≤ x := by rw [ht]; exact Nat.div_mul_le_self x (2 ^ t)
    have hup : x < (k + 1) * 2 ^ t := by
      rw [ht]
      have := Nat.lt_div_mul_add (a := x) (b := 2 ^ t) (Nat.two_pow_pos t)
      rw [Nat.add_mul, Nat.one_mul]
      omega
    by_cases htj : t = j
    · subst htj; exact ⟨hlow, hup⟩
    · exfalso
      rcases Nat.lt_or_gt_of_ne htj with hlt | hgt
      · -- t < j
        have hjh : j ≤ h := by
          apply Classical.byContradiction
          intro hc
          have : 2 ^ (h + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          have h2 : 2 ^ j ≤ k * 2 ^ j := Nat.le_mul_of_pos_left _ hk0
          rw [Nat.pow_succ'] at this
          omega
        have hth : t ≤ h := by omega
        -- k * 2^t < N
        have h2t : 2 ^ (t + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hlt
        have e1 : k * 2 ^ (t + 1) ≤ k * 2 ^ j := Nat.mul_le_mul_left k h2t
        have e2 : k * 2 ^ (t + 1) = 2 * (k * 2 ^ t) := by rw [Nat.pow_succ, Nat.mul_comm (2 ^ t) 2, Nat.mul_left_comm]
        have e3 : k * 2 ^ t < N := by omega
        have e4 : N = 2 ^ (h - t) * 2 ^ t := by rw [← Nat.pow_add, hN]; congr 1; omega
        have e5 : k < 2 ^ (h - t) := by
          apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ t)
          rw [e4] at e3
          exact e3
        have e6 : (k + 1) * 2 ^ t ≤ 2 ^ (h - t) * 2 ^ t := Nat.mul_le_mul_right _ e5
        omega
      · -- t > j
        have h2 : 2 ^ (j + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) hgt
        have e1 : k * 2 ^ (j + 1) ≤ k * 2 ^ t := Nat.mul_le_mul_left k h2
        have e2 : k * 2 ^ (j + 1) = 2 * (k * 2 ^ j) := by rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_left_comm]
        omega
  · rintro ⟨h1, h2⟩
    refine ⟨j, ?_⟩
    symm
    exact Nat.div_eq_of_lt_le h1 h2

end Proofs.LazySegAncLeaf
