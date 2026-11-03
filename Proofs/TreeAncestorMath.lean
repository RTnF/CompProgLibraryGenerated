namespace Proofs.TreeAncestorMath

/-- The `n`-fold iterate of `f`. -/
def itr (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => itr f n (f x)

theorem itr_add (f : Nat → Nat) (m n x : Nat) : itr f (m + n) x = itr f m (itr f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    show itr f (m + n + 1) x = itr f m (itr f (n + 1) x)
    show itr f (m + n) (f x) = itr f m (itr f n (f x))
    exact ih (f x)

/-- The table `T`: `T[k][x]` is meant to be the `2^k`-th ancestor of `x`. -/
def tab (T : List (List Nat)) (k x : Nat) : Nat := ((T.getD k []).getD x 0)

/-- The loop of `tree_ancestor` on the remaining quotient `q = i / 2^k`: the low bit of `q` selects the table entry. -/
def ancQ (T : List (List Nat)) : Nat → Nat → Nat → Nat
  | 0, _, v => v
  | q + 1, k, v => ancQ T ((q + 1) / 2) (k + 1) (if (q + 1) % 2 = 1 then tab T k v else v)
termination_by q => q
decreasing_by omega

theorem ancQ_zero (T : List (List Nat)) (k v : Nat) : ancQ T 0 k v = v := by
  unfold ancQ; rfl

theorem ancQ_succ (T : List (List Nat)) (q k v : Nat) :
    ancQ T (q + 1) k v = ancQ T ((q + 1) / 2) (k + 1) (if (q + 1) % 2 = 1 then tab T k v else v) := by
  rw [ancQ]

/-- The table is correct for `f`: entry `k` is the `2^k`-fold iterate. -/
def TabOK (T : List (List Nat)) (f : Nat → Nat) (N i : Nat) : Prop :=
  ∀ k, 2 ^ k ≤ i → ∀ x, x < N → tab T k x = itr f (2 ^ k) x ∧ tab T k x < N ∧ x < (T.getD k []).length

theorem ancQ_eq (T : List (List Nat)) (f : Nat → Nat) (N i : Nat) (H : TabOK T f N i) :
    ∀ q k v, q * 2 ^ k ≤ i → v < N → ancQ T q k v = itr f (q * 2 ^ k) v ∧ ancQ T q k v < N := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro k v hq hv
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0
      rw [ancQ_zero]
      simp [itr, hv]
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [ancQ_succ]
      have hk : 2 ^ k ≤ i := by
        have : 1 * 2 ^ k ≤ (q' + 1) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
        omega
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      have hq2 : (q' + 1) / 2 * 2 ^ (k + 1) ≤ i := by
        have : (q' + 1) / 2 * 2 ^ (k + 1) ≤ (q' + 1) * 2 ^ k := by
          rw [hpow, ← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (by omega)
        omega
      by_cases hbit : (q' + 1) % 2 = 1
      · rw [if_pos hbit]
        obtain ⟨h1, h2, _⟩ := H k hk v hv
        obtain ⟨e1, e2⟩ := ih ((q' + 1) / 2) (by omega) (k + 1) (tab T k v) hq2 h2
        refine ⟨?_, e2⟩
        rw [e1, h1, ← itr_add]
        congr 1
        rw [hpow]
        have : q' + 1 = 2 * ((q' + 1) / 2) + 1 := by omega
        calc (q' + 1) / 2 * (2 * 2 ^ k) + 2 ^ k = (2 * ((q' + 1) / 2) + 1) * 2 ^ k := by
              rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm 2 ((q' + 1) / 2), Nat.mul_assoc]
          _ = (q' + 1) * 2 ^ k := by rw [← this]
      · rw [if_neg hbit]
        obtain ⟨e1, e2⟩ := ih ((q' + 1) / 2) (by omega) (k + 1) v hq2 hv
        refine ⟨?_, e2⟩
        rw [e1]
        congr 1
        rw [hpow]
        have : q' + 1 = 2 * ((q' + 1) / 2) := by omega
        calc (q' + 1) / 2 * (2 * 2 ^ k) = (2 * ((q' + 1) / 2)) * 2 ^ k := by
              rw [Nat.mul_comm 2 ((q' + 1) / 2), Nat.mul_assoc]
          _ = (q' + 1) * 2 ^ k := by rw [← this]

/-- `tree_ancestor(anc, v, i)` is the `i`-th ancestor `itr f i v`. -/
theorem anc_spec (T : List (List Nat)) (f : Nat → Nat) (N i v : Nat) (H : TabOK T f N i) (hv : v < N) :
    ancQ T i 0 v = itr f i v ∧ ancQ T i 0 v < N := by
  have := ancQ_eq T f N i H i 0 v (by simp) hv
  simpa using this

/-- The number of loop iterations for the remaining quotient `q`. -/
def bits : Nat → Nat
  | 0 => 0
  | q + 1 => 1 + bits ((q + 1) / 2)
termination_by q => q
decreasing_by omega

theorem bits_zero : bits 0 = 0 := by unfold bits; rfl

theorem bits_succ (q : Nat) : bits (q + 1) = 1 + bits ((q + 1) / 2) := by rw [bits]

theorem bits_le (m : Nat) : ∀ q, q < 2 ^ m → bits q ≤ m := by
  induction m with
  | zero => intro q hq; have : q = 0 := by simpa using hq
            subst this; rw [bits_zero]; omega
  | succ m ih =>
    intro q hq
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0; rw [bits_zero]; omega
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [bits_succ]
      have : (q' + 1) / 2 < 2 ^ m := by rw [Nat.pow_succ] at hq; omega
      have := ih _ this
      omega

end Proofs.TreeAncestorMath
