import Proofs.Cpp.Gen.FloorSumUnsigned
import Proofs.Cpp.Lib.Basic
import Proofs.Math.FloorSumReciprocity

/-! # `floor_sum_unsigned` (library/number_theory/floor_sum_unsigned.hpp)

ACL's floor sum on `UInt64`. One loop round reduces `a`, `b` modulo `m` (`normalize`) and then stops or swaps to the
reciprocal sum (`round`, from `Proofs.FloorSumReciprocity.directSum_reciprocity`). The pair `(m, a mod m)` follows
Euclid's algorithm, so `gcdCost` bounds the rounds. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.FloorSumArithmetic Proofs.FloorSumReciprocity

namespace Proofs.Cpp.FloorSumUnsigned

/-- The loop invariant: the accumulated answer plus the remaining sum is the target, modulo `2^64`. -/
def Inv (n0 m0 a0 b0 : Nat) (n m a b ans : UInt64) : Prop :=
  n.toNat < inputLimit ∧ 0 < m.toNat ∧ m.toNat < inputLimit ∧
    (ans.toNat + directSum m.toNat a.toNat b.toNat n.toNat) % wordLimit = directSum m0 a0 b0 n0 % wordLimit

theorem W_eq : wordLimit = 18446744073709551616 := rfl

theorem two64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num

/-- The first half of a round: `a` and `b` reduced modulo `m`, the answer advanced (`normalizedAns`). -/
theorem normalize (n m a b ans : UInt64) (hm0 : 0 < m.toNat) (hn : n.toNat < inputLimit) :
    (if m ≤ a then a % m else a).toNat = a.toNat % m.toNat ∧
    (if m ≤ b then b % m else b).toNat = b.toNat % m.toNat ∧
    (if m ≤ b then (if m ≤ a then ans + n * (n - 1) / 2 * (a / m) else ans) + n * (b / m)
      else (if m ≤ a then ans + n * (n - 1) / 2 * (a / m) else ans)).toNat =
      normalizedAns n.toNat m.toNat a.toNat b.toNat ans.toNat := by
  have tri := triangle_intermediate_exact n.toNat hn
  rw [W_eq] at tri
  have hsub : (n - 1).toNat = (n.toNat + 18446744073709551616 - 1) % 18446744073709551616 := by
    rw [UInt64.toNat_sub, UInt64.toNat_one, two64]
    have := n.toNat_lt
    omega
  have htri : (n * (n - 1) / 2).toNat = triangle n.toNat := by
    rw [UInt64.toNat_div, UInt64.toNat_mul, hsub, two64, show (2 : UInt64).toNat = 2 from rfl]; exact tri
  have hA : (if m ≤ a then ans + n * (n - 1) / 2 * (a / m) else ans).toNat =
      (ans.toNat + triangle n.toNat * (a.toNat / m.toNat)) % 18446744073709551616 := by
    by_cases h : m ≤ a
    · rw [if_pos h, UInt64.toNat_add, UInt64.toNat_mul, htri, UInt64.toNat_div, two64]
      exact Nat.add_mod_mod _ _ _
    · rw [if_neg h]
      rw [UInt64.le_iff_toNat_le] at h
      rw [Nat.div_eq_of_lt (by omega), Nat.mul_zero, Nat.add_zero]
      exact (Nat.mod_eq_of_lt (by have := ans.toNat_lt; rw [two64] at this; exact this)).symm
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : m ≤ a
    · rw [if_pos h, UInt64.toNat_mod]
    · rw [if_neg h]; rw [UInt64.le_iff_toNat_le] at h; rw [Nat.mod_eq_of_lt (by omega)]
  · by_cases h : m ≤ b
    · rw [if_pos h, UInt64.toNat_mod]
    · rw [if_neg h]; rw [UInt64.le_iff_toNat_le] at h; rw [Nat.mod_eq_of_lt (by omega)]
  · unfold normalizedAns
    rw [W_eq]
    by_cases h : m ≤ b
    · rw [if_pos h, UInt64.toNat_add, hA, UInt64.toNat_mul, UInt64.toNat_div, two64, Nat.add_mod_mod, Nat.mod_add_mod]
    · rw [if_neg h, hA]
      rw [UInt64.le_iff_toNat_le] at h
      rw [Nat.div_eq_of_lt (show b.toNat < m.toNat by omega), Nat.mul_zero, Nat.add_zero]

/-- One round of the loop: it stops with the target, or continues in the reduced state with a smaller measure. -/
theorem round (n0 m0 a0 b0 : Nat) (n m a b ans : UInt64) (I : Inv n0 m0 a0 b0 n m a b ans) :
    ((if m ≤ a then a % m else a) * n + (if m ≤ b then b % m else b) < m →
      (if m ≤ b then (if m ≤ a then ans + n * (n - 1) / 2 * (a / m) else ans) + n * (b / m)
        else (if m ≤ a then ans + n * (n - 1) / 2 * (a / m) else ans)).toNat = directSum m0 a0 b0 n0 % wordLimit) ∧
    (¬(if m ≤ a then a % m else a) * n + (if m ≤ b then b % m else b) < m →
      Inv n0 m0 a0 b0 (((if m ≤ a then a % m else a) * n + (if m ≤ b then b % m else b)) / m)
        (if m ≤ a then a % m else a) m (((if m ≤ a then a % m else a) * n + (if m ≤ b then b % m else b)) % m)
        (if m ≤ b then (if m ≤ a then ans + n * (n - 1) / 2 * (a / m) else ans) + n * (b / m)
          else (if m ≤ a then ans + n * (n - 1) / 2 * (a / m) else ans)) ∧
      gcdCost (if m ≤ a then a % m else a).toNat (m.toNat % (if m ≤ a then a % m else a).toNat) + 1 ≤
        gcdCost m.toNat (a.toNat % m.toNat)) := by
  obtain ⟨hn, hm0, hm, hinv⟩ := I
  obtain ⟨ha, hb, hans⟩ := normalize n m a b ans hm0 hn
  generalize (if m ≤ a then a % m else a) = aN at ha ⊢
  generalize (if m ≤ b then b % m else b) = bN at hb ⊢
  generalize (if m ≤ b then (if m ≤ a then ans + n * (n - 1) / 2 * (a / m) else ans) + n * (b / m)
    else (if m ≤ a then ans + n * (n - 1) / 2 * (a / m) else ans)) = ans2 at hans ⊢
  have haM := Nat.mod_lt a.toNat hm0
  have hbM := Nat.mod_lt b.toNat hm0
  have hyb := normalized_y_bound n.toNat m.toNat (a.toNat % m.toNat) (b.toNat % m.toNat) hn hm haM hbM
  rw [W_eq] at hyb
  have hy : (aN * n + bN).toNat = a.toNat % m.toNat * n.toNat + b.toNat % m.toNat := by
    have hp : (aN * n).toNat = a.toNat % m.toNat * n.toNat := by
      rw [UInt64.toNat_mul, ha, two64]; exact Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_add, hp, hb, two64]; exact Nat.mod_eq_of_lt hyb
  have pres := normalization_preserves_accumulated_sum n.toNat m.toNat a.toNat b.toNat ans.toNat hm0
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · rw [UInt64.lt_iff_toNat_lt, hy] at hlt
    rw [directSum_stop _ _ _ _ hlt, Nat.add_zero] at pres
    rw [hans, ← hinv, pres]
    exact (Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))).symm.trans (by unfold normalizedAns; rw [Nat.mod_mod])
  · rw [UInt64.lt_iff_toNat_lt, hy] at hge
    have hcont : m.toNat ≤ a.toNat % m.toNat * n.toNat + b.toNat % m.toNat := by omega
    obtain ⟨hpos, -, hlt, hq, -⟩ := reduction_preserves_domain n.toNat m.toNat a.toNat b.toNat hn hm hm0 hcont
    have hrec := directSum_reciprocity n.toNat m.toNat (a.toNat % m.toNat) (b.toNat % m.toNat) hm0 hpos hbM
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [UInt64.toNat_div, hy]; exact hq
    · rw [ha]; exact hpos
    · rw [ha]; exact hlt
    · rw [UInt64.toNat_div, UInt64.toNat_mod, hy, ha, hans, ← hrec, ← hinv, pres]
    · rw [ha]; have := gcdCost_step m.toNat (a.toNat % m.toNat) hpos; omega

theorem tick_step {s t G g g' : Nat} (hc : s + g ≤ t + 1 + G) (h : g' + 1 ≤ g) :
    s + 1 + g' ≤ t + 1 + G ∧ g' < g := ⟨by omega, by omega⟩

/-- `floor_sum_unsigned(n, m, a, b)` for `n < 2^32`, `0 < m < 2^32` (any 64 bit `a`, `b`): the sum
`Σ_{i<n} ⌊(a i + b) / m⌋` modulo `2^64` (`directSum`), in at most `gcdCost m (a mod m) + 2 = O(log m)` steps. -/
theorem floor_sum_unsigned_spec (n m a b : UInt64) (hn : n.toNat < inputLimit) (hm0 : 0 < m.toNat)
    (hm : m.toNat < inputLimit) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.floor_sum_unsigned n m a b
    ⦃⇓ r c => ⌜r.toNat = directSum m.toNat a.toNat b.toNat n.toNat % wordLimit ∧
               c ≤ t0 + 2 + gcdCost m.toNat (a.toNat % m.toNat)⌝⦄ := by
  mvcgen [cp.floor_sum_unsigned]
  case inv =>
    exact ⟨fun ⟨n', m', a', b', ans⟩ c => ⌜Inv n.toNat m.toNat a.toNat b.toNat n' m' a' b' ans ∧
             c + gcdCost m'.toNat (a'.toNat % m'.toNat) ≤ t0 + 1 + gcdCost m.toNat (a.toNat % m.toNat)⌝,
           fun ⟨_, _, _, _, ans⟩ c => ⌜ans.toNat = directSum m.toNat a.toNat b.toNat n.toNat % wordLimit ∧
             c ≤ t0 + 2 + gcdCost m.toNat (a.toNat % m.toNat)⌝,
           fun ⟨_, m', a', _, _⟩ => gcdCost m'.toNat (a'.toNat % m'.toNat)⟩
  all_goals simp +zetaDelta only [fuel, SPred.down_pure, SPred.and_nil, SPred.and_cons, Prod.mk.eta] at *
  all_goals (try (obtain ⟨I, hc⟩ := ‹Inv _ _ _ _ _ _ _ _ _ ∧ _›
                  have R := round _ _ _ _ _ _ _ _ _ I
                  simp only [decide_eq_true_eq, ge_iff_le, Bool.not_eq_true, decide_eq_false_iff_not] at *
                  simp only [*, ite_true, ite_false, true_implies, not_true_eq_false, not_false_eq_true, false_implies,
                    and_true, true_and] at R
                  first
                  | exact ⟨R, by omega⟩
                  | exact ⟨⟨R.1, (tick_step hc R.2).1⟩, (tick_step hc R.2).2⟩))
  · refine ⟨⟨⟨hn, hm0, hm, by simp⟩, by omega⟩, ?_⟩
    have : gcdCost m.toNat (a.toNat % m.toNat) ≤ 2 + Nat.log2 (m.toNat * (a.toNat % m.toNat)) := by
      unfold gcdCost; split <;> [omega; split <;> omega]
    have := Nat.log2_le_self (m.toNat * (a.toNat % m.toNat))
    have := Nat.mul_le_mul (Nat.le_of_lt hm) (Nat.le_of_lt (Nat.mod_lt a.toNat hm0))
    simp only [inputLimit] at *
    omega
  · exact ‹_ ∧ _›

/-- `floor_sum_unsigned_spec` as a step `mvcgen` can use in a caller. -/
@[spec] theorem floor_sum_unsigned_wp (n m a b : UInt64) (hn : n.toNat < inputLimit) (hm0 : 0 < m.toNat)
    (hm : m.toNat < inputLimit) {Q : PostCond UInt64 PS} :
    ⦃fun t => ⌜∀ r c, r.toNat = directSum m.toNat a.toNat b.toNat n.toNat % wordLimit ∧
      c ≤ t + 2 + gcdCost m.toNat (a.toNat % m.toNat) → (Q.1 r c).down⌝⦄ cp.floor_sum_unsigned n m a b ⦃Q⦄ :=
  wp_of_triple (fun t0 => floor_sum_unsigned_spec n m a b hn hm0 hm t0)

end Proofs.Cpp.FloorSumUnsigned
