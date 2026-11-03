import Proofs.BeatsRepInv
namespace Proofs.BeatsRep
open Proofs.BeatsModel
set_option maxRecDepth 100000

/-- The range `[lo, hi)` of heap index `k` in the midpoint-split tree over `[0, n)`; `(0, 0)` outside the tree. -/
def rngOf (n : Nat) : Nat → Nat × Nat
  | 0 => (0, n)
  | k + 1 =>
    if (rngOf n (k / 2)).1 + 1 < (rngOf n (k / 2)).2 then
      (if k % 2 = 0 then ((rngOf n (k / 2)).1, ((rngOf n (k / 2)).1 + (rngOf n (k / 2)).2) / 2)
       else (((rngOf n (k / 2)).1 + (rngOf n (k / 2)).2) / 2, (rngOf n (k / 2)).2))
    else (0, 0)
termination_by k => k
decreasing_by all_goals omega

theorem rngOf_left (n k : Nat) :
    rngOf n (2 * k + 1) = if (rngOf n k).1 + 1 < (rngOf n k).2 then ((rngOf n k).1, ((rngOf n k).1 + (rngOf n k).2) / 2) else (0, 0) := by
  have e1 : (2 * k) / 2 = k := by omega
  have e2 : (2 * k) % 2 = 0 := by omega
  rw [rngOf, e1, e2]
  simp

theorem rngOf_right (n k : Nat) :
    rngOf n (2 * k + 2) = if (rngOf n k).1 + 1 < (rngOf n k).2 then (((rngOf n k).1 + (rngOf n k).2) / 2, (rngOf n k).2) else (0, 0) := by
  have e0 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
  have e1 : (2 * k + 1) / 2 = k := by omega
  have e2 : (2 * k + 1) % 2 = 1 := by omega
  rw [e0, rngOf, e1, e2]
  simp

theorem rngOf_zero_desc (n : Nat) : ∀ (p j : Nat), rngOf n p = (0, 0) → descN p j → rngOf n j = (0, 0) := by
  intro p j hp hd
  induction hd with
  | self => exact hp
  | step j h1 h2 ih =>
    have hj : j = 2 * ((j - 1) / 2) + 1 ∨ j = 2 * ((j - 1) / 2) + 2 := by omega
    rcases hj with h | h
    · rw [h, rngOf_left, ih]; simp
    · rw [h, rngOf_right, ih]; simp


/-- Inner nodes have small indices: `(k + 2) * (size - 1) ≤ 2 n`. -/
theorem rngOf_index (n : Nat) : ∀ (k : Nat), (rngOf n k).1 < (rngOf n k).2 → (k + 2) * ((rngOf n k).2 - (rngOf n k).1 - 1) ≤ 2 * n := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases h0 : k = 0
    · subst h0; simp [rngOf]
    · have hp : (k - 1) / 2 < k := by omega
      have hpar : k = 2 * ((k - 1) / 2) + 1 ∨ k = 2 * ((k - 1) / 2) + 2 := by omega
      have hih := ih ((k - 1) / 2) hp
      set p := (k - 1) / 2 with hpdef
      rcases hpar with h | h
      · rw [h, rngOf_left] at hk ⊢
        by_cases hin : (rngOf n p).1 + 1 < (rngOf n p).2
        · rw [if_pos hin] at hk ⊢
          have := hih (by omega)
          simp only at hk ⊢
          have e1 : ((rngOf n p).1 + (rngOf n p).2) / 2 - (rngOf n p).1 - 1 + 1 + 1 ≥ 0 := by omega
          have : (2 * p + 1 + 2) * (((rngOf n p).1 + (rngOf n p).2) / 2 - (rngOf n p).1 - 1) ≤ (p + 2) * ((rngOf n p).2 - (rngOf n p).1 - 1) := by
            have h2 : 2 * (((rngOf n p).1 + (rngOf n p).2) / 2 - (rngOf n p).1 - 1) ≤ (rngOf n p).2 - (rngOf n p).1 - 1 := by omega
            calc (2 * p + 1 + 2) * (((rngOf n p).1 + (rngOf n p).2) / 2 - (rngOf n p).1 - 1)
                ≤ (2 * (p + 2)) * (((rngOf n p).1 + (rngOf n p).2) / 2 - (rngOf n p).1 - 1) := Nat.mul_le_mul_right _ (by omega)
              _ = (p + 2) * (2 * (((rngOf n p).1 + (rngOf n p).2) / 2 - (rngOf n p).1 - 1)) := by ring
              _ ≤ (p + 2) * ((rngOf n p).2 - (rngOf n p).1 - 1) := Nat.mul_le_mul_left _ h2
          omega
        · rw [if_neg hin] at hk; simp at hk
      · rw [h, rngOf_right] at hk ⊢
        by_cases hin : (rngOf n p).1 + 1 < (rngOf n p).2
        · rw [if_pos hin] at hk ⊢
          have := hih (by omega)
          simp only at hk ⊢
          have : (2 * p + 2 + 2) * ((rngOf n p).2 - ((rngOf n p).1 + (rngOf n p).2) / 2 - 1) ≤ (p + 2) * ((rngOf n p).2 - (rngOf n p).1 - 1) := by
            have h2 : 2 * ((rngOf n p).2 - ((rngOf n p).1 + (rngOf n p).2) / 2 - 1) ≤ (rngOf n p).2 - (rngOf n p).1 - 1 := by omega
            calc (2 * p + 2 + 2) * ((rngOf n p).2 - ((rngOf n p).1 + (rngOf n p).2) / 2 - 1)
                = (p + 2) * (2 * ((rngOf n p).2 - ((rngOf n p).1 + (rngOf n p).2) / 2 - 1)) := by ring
              _ ≤ (p + 2) * ((rngOf n p).2 - (rngOf n p).1 - 1) := Nat.mul_le_mul_left _ h2
          omega
        · rw [if_neg hin] at hk; simp at hk


/-- The summary stored at heap index `j` in the finished tree. -/
def nodeAt (a : List Int) (n j : Nat) : Nd := (buildBT a (rngOf n j).1 (rngOf n j).2).nd

theorem sub2_build (a : List Int) (n : Nat) : ∀ (d lo hi k : Nat), hi - lo = d → lo < hi → rngOf n k = (lo, hi) →
    ∀ j nd otg, sub2 (buildBT a lo hi) k j = some (nd, otg) →
      (rngOf n j).1 < (rngOf n j).2 ∧ nd = nodeAt a n j ∧
        otg = (if (rngOf n j).1 + 1 < (rngOf n j).2 then some noTag else none) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro lo hi k hd hlo hk j nd otg h
    by_cases hc : lo + 1 < hi
    · have hb : buildBT a lo hi = .node (mergeNd (buildBT a lo ((lo + hi) / 2)).nd (buildBT a ((lo + hi) / 2) hi).nd) noTag
          (buildBT a lo ((lo + hi) / 2)) (buildBT a ((lo + hi) / 2) hi) := by
        rw [buildBT, if_pos hc]
      rw [hb] at h
      by_cases hjk : j = k
      · subst hjk
        simp only [sub2, if_true] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨by rw [hk]; exact hlo, ?_, ?_⟩
        · rw [← h1]; unfold nodeAt; rw [hk]; simp only; rw [hb]; rfl
        · rw [hk]; simp only; rw [if_pos hc]; exact h2.symm
      · simp only [sub2, if_neg hjk] at h
        have hl := rngOf_left n k
        have hr := rngOf_right n k
        rw [hk] at hl hr
        simp only [if_pos hc] at hl hr
        cases hsl : sub2 (buildBT a lo ((lo + hi) / 2)) (2 * k + 1) j with
        | some v =>
          rw [hsl] at h
          obtain ⟨v1, v2⟩ := v
          have hh := Prod.mk.inj (Option.some.inj h)
          rw [← hh.1, ← hh.2]
          exact ih _ (by omega) lo ((lo + hi) / 2) (2 * k + 1) rfl (by omega) hl j v1 v2 hsl
        | none =>
          rw [hsl] at h
          simp only at h
          exact ih _ (by omega) ((lo + hi) / 2) hi (2 * k + 2) rfl (by omega) hr j nd otg h
    · have hb : buildBT a lo hi = .leaf (leafNd (a.getD lo 0)) := by rw [buildBT, if_neg hc]
      rw [hb] at h
      by_cases hjk : j = k
      · subst hjk
        simp only [sub2, if_true] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨by rw [hk]; exact hlo, ?_, ?_⟩
        · rw [← h1]; unfold nodeAt; rw [hk]; simp only; rw [hb]; rfl
        · rw [hk]; simp only; rw [if_neg hc]; exact h2.symm
      · simp only [sub2, if_neg hjk] at h
        cases h


theorem rngOf_le (n : Nat) : ∀ j, (rngOf n j).1 ≤ (rngOf n j).2 ∧ (rngOf n j).2 ≤ n := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    by_cases h0 : j = 0
    · subst h0; simp [rngOf]
    · have hp : (j - 1) / 2 < j := by omega
      have hpar : j = 2 * ((j - 1) / 2) + 1 ∨ j = 2 * ((j - 1) / 2) + 2 := by omega
      have hih := ih ((j - 1) / 2) hp
      set p := (j - 1) / 2
      rcases hpar with h | h
      · rw [h, rngOf_left]
        by_cases hin : (rngOf n p).1 + 1 < (rngOf n p).2
        · rw [if_pos hin]; simp only; omega
        · rw [if_neg hin]; simp only; omega
      · rw [h, rngOf_right]
        by_cases hin : (rngOf n p).1 + 1 < (rngOf n p).2
        · rw [if_pos hin]; simp only; omega
        · rw [if_neg hin]; simp only; omega


theorem rngOf_cases (n k : Nat) : (rngOf n k).1 < (rngOf n k).2 ∨ rngOf n k = (0, 0) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases h0 : k = 0
    · subst h0; by_cases hn : n = 0
      · right; simp [rngOf, hn]
      · left; simp [rngOf]; omega
    · have hp : (k - 1) / 2 < k := by omega
      have hpar : k = 2 * ((k - 1) / 2) + 1 ∨ k = 2 * ((k - 1) / 2) + 2 := by omega
      set p := (k - 1) / 2
      rcases hpar with h | h
      · rw [h, rngOf_left]
        by_cases hin : (rngOf n p).1 + 1 < (rngOf n p).2
        · rw [if_pos hin]; left; simp only; omega
        · rw [if_neg hin]; right; rfl
      · rw [h, rngOf_right]
        by_cases hin : (rngOf n p).1 + 1 < (rngOf n p).2
        · rw [if_pos hin]; left; simp only; omega
        · rw [if_neg hin]; right; rfl



end Proofs.BeatsRep
