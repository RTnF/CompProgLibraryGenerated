import Init

/-! The table of `CumulativeSum2D`: `P2 V a b` is the sum of the first `a` rows of `V` restricted to their first `b`
columns, and the states of the one-pass construction. -/

namespace Proofs.CumulativeSum2DMath

/-- The sum of the block `[0, a) x [0, b)` of the matrix `V` (a list of rows). -/
def P2 (V : List (List Int)) (a b : Nat) : Int := ((V.take a).map (fun row => (row.take b).sum)).sum

theorem P2_zero_a (V : List (List Int)) (b : Nat) : P2 V 0 b = 0 := by simp [P2]
theorem P2_zero_b (V : List (List Int)) (a : Nat) : P2 V a 0 = 0 := by
  unfold P2
  have : (V.take a).map (fun row => (row.take 0).sum) = (V.take a).map (fun _ => (0 : Int)) := by simp
  rw [this]
  induction (V.take a) with
  | nil => simp
  | cons x xs ih => simpa using ih

theorem P2_succ_row (V : List (List Int)) (r : Nat) (row : List Int) (h : V[r]? = some row) (b : Nat) :
    P2 V (r + 1) b = P2 V r b + (row.take b).sum := by
  unfold P2
  rw [List.take_succ, h]
  simp [List.sum_append]

/-- The entry `(a, b)` of the table while the row `t` is being processed (columns `< j` of the row `t + 1` are done). -/
def csCell (V : List (List Int)) (t j a b : Nat) : Int :=
  if a ≤ t then P2 V a b else if a = t + 1 then (if b ≤ j then P2 V a b else 0) else 0

def csRow (V : List (List Int)) (m t j a : Nat) : List Int := (List.range (m + 1)).map (csCell V t j a)

/-- The contents family: rows of the table under the key of slot 0, rows of `V` under the key of slot 1. -/
def VCS (V : List (List Int)) (m t j : Nat) : Nat → List Int := fun key =>
  if key / 4294967296 = 1 then csRow V m t j (key % 4294967296)
  else if key / 4294967296 = 2 then (V[key % 4294967296]?).getD []
  else []

theorem csCell_zero_a (V : List (List Int)) (j b : Nat) : csCell V 0 j 0 b = 0 := by
  simp [csCell, P2_zero_a]


/-- The key of row `i` of the nested parameter `k` (see `MultiVecN.rowKey`). -/
def rk (k i : Nat) : Nat := 4294967296 * (k + 1) + i

theorem VCS_cs (V : List (List Int)) (m t j a : Nat) (h : a < 4294967296) :
    VCS V m t j (rk 0 a) = csRow V m t j a := by
  unfold VCS rk
  have e1 : (4294967296 * (0 + 1) + a) / 4294967296 = 1 := by omega
  have e2 : (4294967296 * (0 + 1) + a) % 4294967296 = a := by omega
  simp [e1, e2]

theorem VCS_v (V : List (List Int)) (m t j a : Nat) (h : a < 4294967296) :
    VCS V m t j (rk 1 a) = (V[a]?).getD [] := by
  unfold VCS rk
  have e1 : (4294967296 * (1 + 1) + a) / 4294967296 = 2 := by omega
  have e2 : (4294967296 * (1 + 1) + a) % 4294967296 = a := by omega
  simp [e1, e2]

theorem csRow_length (V : List (List Int)) (m t j a : Nat) : (csRow V m t j a).length = m + 1 := by
  simp [csRow]

theorem csRow_zero (V : List (List Int)) (m a : Nat) : csRow V m 0 0 a = List.replicate (m + 1) 0 := by
  unfold csRow
  apply List.ext_getElem
  · simp
  · intro b h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    unfold csCell
    by_cases h0 : a ≤ 0
    · have : a = 0 := by omega
      subst this; simp [P2_zero_a]
    · by_cases h1' : a = 0 + 1
      · subst h1'
        by_cases hb : b ≤ 0
        · have : b = 0 := by omega
          subst this; simp [P2_zero_b]
        · simp [hb]
      · simp [h0, h1']

theorem csRow_final (V : List (List Int)) (m n a : Nat) (ha : a ≤ n) :
    csRow V m n 0 a = (List.range (m + 1)).map (P2 V a) := by
  unfold csRow
  apply List.map_congr_left
  intro b _
  simp [csCell, ha]

theorem csRow_next (V : List (List Int)) (m t a : Nat) : csRow V m t m a = csRow V m (t + 1) 0 a := by
  unfold csRow
  apply List.map_congr_left
  intro b hb
  have hbm : b ≤ m := by have := List.mem_range.mp hb; omega
  unfold csCell
  by_cases h1 : a ≤ t
  · have : a ≤ t + 1 := by omega
    simp [h1, this]
  · by_cases h2 : a = t + 1
    · subst h2; simp [hbm]
    · by_cases h3 : a = t + 1 + 1
      · subst h3
        by_cases hb0 : b ≤ 0
        · have : b = 0 := by omega
          subst this
          simp [P2_zero_b]
        · have h4 : ¬ (t + 1 + 1 ≤ t) := by omega
          have h5 : ¬ (t + 1 ≤ t) := by omega
          simp [hb0, h4, h5]
      · have : ¬ a ≤ t + 1 := by omega
        simp [h1, h2, h3, this]

theorem csRow_step (V : List (List Int)) (m t j : Nat) (hj : j < m) :
    (csRow V m t j (t + 1)).set (j + 1) (P2 V (t + 1) (j + 1)) = csRow V m t (j + 1) (t + 1) := by
  unfold csRow
  apply List.ext_getElem
  · simp
  · intro b h1 h2
    simp only [List.length_set, List.length_map, List.length_range] at h1 h2
    by_cases hb : b = j + 1
    · subst hb
      simp [csCell]
    · simp only [List.getElem_set, List.getElem_map, List.getElem_range]
      rw [if_neg (Ne.symm hb)]
      simp only [csCell]
      by_cases hbj : b ≤ j
      · have : b ≤ j + 1 := by omega
        simp [hbj, this]
      · have : ¬ b ≤ j + 1 := by omega
        simp [hbj, this]

theorem VCS_step (V : List (List Int)) (m t j : Nat) (hj : j < m) (ht : t + 1 < 4294967296) :
    (fun key => if key = rk 0 (t + 1) then (VCS V m t j key).set (j + 1) (P2 V (t + 1) (j + 1)) else VCS V m t j key) =
      VCS V m t (j + 1) := by
  funext key
  by_cases hk : key = rk 0 (t + 1)
  · subst hk
    rw [if_pos rfl, VCS_cs V m t j (t + 1) ht, VCS_cs V m t (j + 1) (t + 1) ht]
    exact csRow_step V m t j hj
  · rw [if_neg hk]
    unfold VCS
    by_cases h1 : key / 4294967296 = 1
    · have hne : key % 4294967296 ≠ t + 1 := by
        intro h; apply hk; unfold rk; omega
      simp only [h1, if_true]
      unfold csRow
      apply List.map_congr_left
      intro b _
      simp [csCell, hne]
    · simp [h1]

end Proofs.CumulativeSum2DMath
