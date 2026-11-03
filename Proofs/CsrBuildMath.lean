namespace Proofs.CsrBuildMath

/-- The number of `j < i` with `F j = v`. -/
def cnt (F : Nat → Nat) (v i : Nat) : Nat := ((List.range i).filter (fun j => decide (F j = v))).length

/-- The number of `j < i` with `F j < k`. -/
def ocnt (F : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => ocnt F i k + cnt F k i

theorem cnt_zero (F : Nat → Nat) (v : Nat) : cnt F v 0 = 0 := by simp [cnt]

theorem cnt_succ (F : Nat → Nat) (v i : Nat) : cnt F v (i + 1) = cnt F v i + (if F i = v then 1 else 0) := by
  unfold cnt
  rw [List.range_succ, List.filter_append]
  by_cases h : F i = v <;> simp [h]

theorem cnt_mono (F : Nat → Nat) (v : Nat) {i j : Nat} (h : i ≤ j) : cnt F v i ≤ cnt F v j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    by_cases hij : i = j + 1
    · subst hij; exact Nat.le_refl _
    · have := ih (by omega)
      rw [cnt_succ]; omega

theorem cnt_le (F : Nat → Nat) (v i : Nat) : cnt F v i ≤ i := by
  induction i with
  | zero => simp [cnt_zero]
  | succ i ih => rw [cnt_succ]; split <;> omega

theorem ocnt_le (F : Nat → Nat) (i k : Nat) : ocnt F i k ≤ k * i := by
  induction k with
  | zero => simp [ocnt]
  | succ k ih =>
    simp only [ocnt]
    have := cnt_le F k i
    have : (k + 1) * i = k * i + i := by rw [Nat.succ_mul]
    omega

theorem cnt_lt (F : Nat → Nat) {j m : Nat} (hj : j < m) : cnt F (F j) j < cnt F (F j) m := by
  have h1 := cnt_succ F (F j) j
  rw [if_pos rfl] at h1
  have := cnt_mono F (F j) (show j + 1 ≤ m by omega)
  omega

theorem ocnt_succ (F : Nat → Nat) (i k : Nat) : ocnt F (i + 1) k = ocnt F i k + (if F i < k then 1 else 0) := by
  induction k with
  | zero => simp [ocnt]
  | succ k ih =>
    simp only [ocnt, ih, cnt_succ]
    by_cases h1 : F i < k
    · have : F i ≠ k := by omega
      simp [h1, this, show F i < k + 1 by omega]
      omega
    · by_cases h2 : F i = k
      · simp [h1, h2]
        omega
      · have : ¬ F i < k + 1 := by omega
        simp [h1, h2, this]

theorem ocnt_total (F : Nat → Nat) (n : Nat) : ∀ i, (∀ j, j < i → F j < n) → ocnt F i n = i := by
  intro i
  induction i with
  | zero =>
    intro _
    have : ∀ k, ocnt F 0 k = 0 := by
      intro k
      induction k with
      | zero => simp [ocnt]
      | succ k ih => simp only [ocnt, cnt_zero]; rw [ih]
    exact this n
  | succ i ih =>
    intro h
    rw [ocnt_succ, ih (fun j hj => h j (by omega)), if_pos (h i (by omega))]

theorem ocnt_mono (F : Nat → Nat) (i : Nat) {k l : Nat} (h : k ≤ l) : ocnt F i k ≤ ocnt F i l := by
  induction l with
  | zero => have : k = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ l ih =>
    by_cases hk : k = l + 1
    · subst hk; exact Nat.le_refl _
    · have := ih (by omega)
      simp only [ocnt]; omega

/-- The `k`-th occurrence of `u`. -/
theorem kth (F : Nat → Nat) (u : Nat) : ∀ m k, k < cnt F u m → ∃ j, j < m ∧ F j = u ∧ cnt F u j = k := by
  intro m
  induction m with
  | zero => intro k h; simp [cnt_zero] at h
  | succ m ih =>
    intro k h
    rw [cnt_succ] at h
    by_cases hf : F m = u
    · rw [if_pos hf] at h
      by_cases hk : k < cnt F u m
      · obtain ⟨j, hj, e1, e2⟩ := ih k hk
        exact ⟨j, by omega, e1, e2⟩
      · refine ⟨m, by omega, hf, by omega⟩
    · rw [if_neg hf] at h
      obtain ⟨j, hj, e1, e2⟩ := ih k (by omega)
      exact ⟨j, by omega, e1, e2⟩

end Proofs.CsrBuildMath
