import Proofs.Math.EnumerateQuotientsMath
import Proofs.Math.FenwickMath
import Proofs.Math.FenwickBuildMath

namespace Proofs.FloydWarshallCall

/-- The Floyd-Warshall recurrence on a weight matrix `W`: shortest distances through the vertices `< k`. -/
def Dm (W : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0 => W
  | k + 1 => fun i j => min (Dm W k i j) (Dm W k i k + Dm W k k j)

theorem Dm_stable_col (W : Nat → Nat → Nat) (k i : Nat) : Dm W (k + 1) i k = Dm W k i k := by
  simp only [Dm]
  omega

theorem Dm_stable_row (W : Nat → Nat → Nat) (k j : Nat) : Dm W (k + 1) k j = Dm W k k j := by
  simp only [Dm]
  omega

/-- Matrix after the rows `< i` and the first `j` entries of row `i` were processed in round `k`. -/
def Em (W : Nat → Nat → Nat) (k i j p q : Nat) : Nat :=
  if p < i ∨ (p = i ∧ q < j) then Dm W (k + 1) p q else Dm W k p q

theorem Em_col (W : Nat → Nat → Nat) (k i j p : Nat) : Em W k i j p k = Dm W k p k := by
  unfold Em
  split
  · exact Dm_stable_col W k p
  · rfl

theorem Em_row (W : Nat → Nat → Nat) (k i j q : Nat) : Em W k i j k q = Dm W k k q := by
  unfold Em
  split
  · exact Dm_stable_row W k q
  · rfl

theorem Em_here (W : Nat → Nat → Nat) (k i j : Nat) : Em W k i j i j = Dm W k i j := by
  unfold Em
  split
  · omega
  · rfl

theorem Em_next (W : Nat → Nat → Nat) (k i j : Nat) : Em W k i (j + 1) i j = Dm W (k + 1) i j := by
  unfold Em
  rw [if_pos (by omega)]

theorem Em_other (W : Nat → Nat → Nat) (k i j p q : Nat) (h : ¬ (p = i ∧ q = j)) :
    Em W k i (j + 1) p q = Em W k i j p q := by
  unfold Em
  by_cases h1 : p < i ∨ (p = i ∧ q < j)
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

theorem Em_row_end (W : Nat → Nat → Nat) (k i n p q : Nat) (hq : q < n) : Em W k i n p q = Em W k (i + 1) 0 p q := by
  unfold Em
  by_cases h : p < i ∨ (p = i ∧ q < n)
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem Em_start (W : Nat → Nat → Nat) (k p q : Nat) : Em W k 0 0 p q = Dm W k p q := by
  unfold Em
  rw [if_neg (by omega)]

theorem Em_end (W : Nat → Nat → Nat) (k n p q : Nat) (hp : p < n) : Em W k n 0 p q = Dm W (k + 1) p q := by
  unfold Em
  rw [if_pos (by omega)]

theorem idx_inj (n p q p' q' : Nat) (hq : q < n) (hq' : q' < n) (h : p * n + q = p' * n + q') : p = p' ∧ q = q' := by
  have h1 : (p * n + q) / n = p := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hq]; omega
  have h2 : (p' * n + q') / n = p' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hq']; omega
  have h3 : (p * n + q) % n = q := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  have h4 : (p' * n + q') % n = q' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq']
  rw [h] at h1 h3
  exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

section Program

theorem idx_lt (n i k : Nat) (hi : i < n) (hk : k < n) : i * n + k < n * n := by
  have : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
  rw [Nat.add_mul] at this
  omega

end Program

end Proofs.FloydWarshallCall
