import Proofs.Generated.MergeSort

namespace Proofs.MergeSort

theorem split_bounds (n : Nat) (hn : 2 ≤ n) :
    0 < n / 2 + n % 2 ∧ n / 2 + n % 2 < n ∧
    0 < n / 2 ∧ n / 2 < n ∧ n / 2 + n % 2 + n / 2 = n := by
  omega

theorem merge_index_bounds (left right i j : Nat)
    (hi : i ≤ left) (hj : j ≤ right) : i + j ≤ left + right := by
  omega

theorem merge_left_step (left right i j : Nat)
    (hi : i < left) (hj : j ≤ right) :
    i + 1 ≤ left ∧ (left + right - (i + 1 + j)) < left + right - (i + j) := by
  omega

theorem merge_right_step (left right i j : Nat)
    (hi : i ≤ left) (hj : j < right) :
    j + 1 ≤ right ∧ (left + right - (i + (j + 1))) < left + right - (i + j) := by
  omega

theorem model_perm (xs : List Int) : (model xs).Perm xs := by
  induction xs using model.induct with
  | case1 => simp [model]
  | case2 x => simp [model]
  | case3 x y rest xs mid ihl ihr =>
      rw [model]
      exact (List.merge_perm_append intLe).trans
        ((ihl.append ihr).trans (List.Perm.of_eq (List.take_append_drop mid xs)))

theorem model_sorted (xs : List Int) : (model xs).Pairwise (fun a b => a ≤ b) := by
  have htrans : ∀ a b c : Int, intLe a b → intLe b c → intLe a c := by
    intro a b c hab hbc
    simp only [intLe, decide_eq_true_eq] at *
    omega
  have htotal : ∀ a b : Int, intLe a b || intLe b a := by
    intro a b
    by_cases h : a ≤ b
    · simp [intLe, h]
    · have h' : b ≤ a := by omega
      simp [intLe, h']
  induction xs using model.induct with
  | case1 => simp [model]
  | case2 x => simp [model]
  | case3 x y rest xs mid ihl ihr =>
      rw [model]
      have hl : (model (xs.take mid)).Pairwise (fun a b => intLe a b = true) := by
        simpa only [intLe, decide_eq_true_eq] using ihl
      have hr : (model (xs.drop mid)).Pairwise (fun a b => intLe a b = true) := by
        simpa only [intLe, decide_eq_true_eq] using ihr
      simpa only [intLe, decide_eq_true_eq] using
        (List.pairwise_merge htrans htotal _ _ hl hr)

theorem work_bound_pow (k : Nat) : ∀ n : Nat, n ≤ 2 ^ k → work n ≤ n * k := by
  induction k with
  | zero =>
      intro n hn
      have h : n ≤ 1 := by simpa using hn
      cases n with
      | zero => simp [work]
      | succ n =>
          have : n = 0 := by omega
          subst n
          simp [work]
  | succ k ih =>
      intro n hn
      match n with
      | 0 => simp [work]
      | 1 => simp [work]
      | m + 2 =>
          let size := m + 2
          have hsize : size ≤ 2 * 2 ^ k := by
            simpa [size, Nat.pow_succ, Nat.mul_comm] using hn
          have hleft : size / 2 + size % 2 ≤ 2 ^ k := by omega
          have hright : size / 2 ≤ 2 ^ k := by omega
          have hl := ih _ hleft
          have hr := ih _ hright
          have hsum : size / 2 + size % 2 + size / 2 = size := by omega
          have hmul : (size / 2 + size % 2) * k + (size / 2) * k = size * k := by
            rw [← Nat.add_mul, hsum]
          rw [work]
          change work (size / 2 + size % 2) + work (size / 2) + size ≤
            size * (k + 1)
          calc
            work (size / 2 + size % 2) + work (size / 2) + size ≤
                (size / 2 + size % 2) * k + (size / 2) * k + size := by omega
            _ = size * (k + 1) := by rw [hmul, Nat.mul_succ]

theorem work_bound_log (n : Nat) : work n ≤ n * (Nat.log2 (n - 1) + 1) := by
  cases n with
  | zero => simp [work]
  | succ m =>
      have hpow : m + 1 ≤ 2 ^ (Nat.log2 m + 1) := by
        have h := Nat.lt_log2_self (n := m)
        omega
      simpa using work_bound_pow (Nat.log2 m + 1) (m + 1) hpow

theorem calls_exact (n : Nat) (hn : 0 < n) : calls n + 1 = 2 * n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      match n with
      | 0 => omega
      | 1 => simp [calls]
      | m + 2 =>
          let size := m + 2
          let left := size / 2 + size % 2
          let right := size / 2
          have hl_pos : 0 < left := by omega
          have hr_pos : 0 < right := by omega
          have hl_lt : left < size := by omega
          have hr_lt : right < size := Nat.div_lt_self (by omega) (by decide)
          have hl := ih left hl_lt hl_pos
          have hr := ih right hr_lt hr_pos
          have hsum : left + right = size := by omega
          rw [calls]
          change 1 + calls left + calls right + 1 = 2 * size
          omega

theorem total_work_bound (n : Nat) (hn : 0 < n) :
    work n + calls n ≤ n * (Nat.log2 (n - 1) + 3) := by
  have hw := work_bound_log n
  have hc := calls_exact n hn
  simp only [Nat.mul_add, Nat.mul_one] at *
  omega

theorem slots_linear (n : Nat) : slots n ≤ 4 * n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      match n with
      | 0 => simp [slots]
      | 1 => simp [slots]
      | m + 2 =>
          let size := m + 2
          let left := size / 2 + size % 2
          let right := size / 2
          have hl_lt : left < size := by omega
          have hr_lt : right < size := Nat.div_lt_self (by omega) (by decide)
          have hl := ih left hl_lt
          have hr := ih right hr_lt
          have hleft : size + 4 * left ≤ 4 * size := by omega
          have hright : size + left + 4 * right ≤ 4 * size := by omega
          have hmerge : 3 * size ≤ 4 * size := by omega
          rw [slots]
          change max (size + slots left)
              (max (size + left + slots right) (3 * size)) ≤ 4 * size
          exact Nat.max_le_of_le_of_le (by omega)
            (Nat.max_le_of_le_of_le (by omega) hmerge)

end Proofs.MergeSort
