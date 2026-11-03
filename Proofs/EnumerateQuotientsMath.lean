namespace Proofs.EnumerateQuotientsMath
def firstPart (p : Nat) : List Nat := (List.range p).map (·+1)
def secondPart (n K : Nat) : List Nat := (List.range (K-1)).map fun j => n / (K-1-j)
def qlist (n K : Nat) : List Nat := firstPart (n/K) ++ secondPart n K

theorem firstPart_succ (m : Nat) : firstPart (m+1) = firstPart m ++ [m+1] := by
  simp [firstPart,List.range_succ]

theorem firstPart_length (m : Nat) : (firstPart m).length = m := by simp [firstPart]

theorem secondPart_take_succ (n K t : Nat) (h : t < K-1) :
    (secondPart n K).take (t+1) = (secondPart n K).take t ++ [n / (K-1-t)] := by
  simp [secondPart,List.take_succ,List.getElem?_map,List.getElem?_range h]

theorem secondPart_take_all (n K : Nat) : (secondPart n K).take (K-1) = secondPart n K := by
  apply List.take_of_length_le
  simp [secondPart]

theorem mem_firstPart (p q : Nat) : q ∈ firstPart p ↔ 1 ≤ q ∧ q ≤ p := by
  simp only [firstPart, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; omega
  · intro ⟨h1, h2⟩; exact ⟨q-1, by omega, by omega⟩

theorem mem_secondPart (n K q : Nat) : q ∈ secondPart n K ↔ ∃ i, 1 ≤ i ∧ i ≤ K-1 ∧ n / i = q := by
  simp only [secondPart, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨K-1-j, by omega, by omega, rfl⟩
  · rintro ⟨i, h1, h2, rfl⟩; exact ⟨K-1-i, by omega, by congr 1; omega⟩

-- consecutive quotients strictly decrease while i * (i+1) < n
theorem quotient_gap (n i : Nat) (hi : 1 ≤ i) (h : i * (i+1) < n) : n / (i+1) < n / i := by
  have hi1 : 0 < i := hi
  have hi2 : 0 < i+1 := by omega
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hi1]
  have hn := Nat.div_add_mod n (i+1)
  have hr := Nat.mod_lt n hi2
  have hq : i ≤ n / (i+1) := by
    rw [Nat.le_div_iff_mul_le hi2]; omega
  have e : (n / (i+1) + 1) * i = i * (n / (i+1)) + i := by
    rw [Nat.add_mul, Nat.mul_comm (n / (i+1)) i, Nat.one_mul]
  have e2 : (i+1) * (n / (i+1)) = i * (n / (i+1)) + n / (i+1) := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem quotient_anti (n K : Nat) (hm : (K-1)*K < n) (i d : Nat) (hi : 1 ≤ i) (hj : i+d+1 ≤ K-1) :
    n / (i+d+1) < n / i := by
  induction d with
  | zero =>
    have : i * (i+1) < n := by
      have : i*(i+1) ≤ (K-1)*K := Nat.mul_le_mul (by omega) (by omega)
      omega
    exact quotient_gap n i hi this
  | succ d ih =>
    have h1 : (i+d+1) * (i+d+1+1) < n := by
      have : (i+d+1)*(i+d+1+1) ≤ (K-1)*K := Nat.mul_le_mul (by omega) (by omega)
      omega
    have := quotient_gap n (i+d+1) (by omega) h1
    have ih' := ih (by omega)
    have e : i + (d+1) + 1 = i+d+1+1 := by omega
    rw [e]
    omega

theorem firstPart_lt_second (n K : Nat) (hK : 2 ≤ K) (hm : (K-1)*K < n) :
    n / K < n / (K-1) := by
  have := quotient_gap n (K-1) (by omega) (by
    have e : K - 1 + 1 = K := by omega
    rw [e]; exact hm)
  have e : K - 1 + 1 = K := by omega
  rwa [e] at this

theorem qlist_sorted (n K : Nat) (hK1 : 1 ≤ K) (hKm : K = 1 ∨ (K-1)*K < n) :
    (qlist n K).Pairwise (· < ·) := by
  unfold qlist
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · unfold firstPart
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range (n := n / K)).imp (by intro a b h; omega)
  · unfold secondPart
    rw [List.pairwise_map]
    have : K = 1 ∨ 2 ≤ K := by omega
    rcases this with rfl | h2
    · simp
    · have hm : (K-1)*K < n := by omega
      refine (List.pairwise_lt_range (n := K-1)).imp_of_mem ?_
      intro a b ha hb hab
      have ha := List.mem_range.mp ha
      have hb := List.mem_range.mp hb
      have := quotient_anti n K hm (K-1-b) (b-a-1) (by omega) (by omega)
      have e : K-1-b + (b-a-1) + 1 = K-1-a := by omega
      rw [e] at this
      exact this
  · intro a ha b hb
    rw [mem_firstPart] at ha
    rw [mem_secondPart] at hb
    obtain ⟨i, h1, h2, rfl⟩ := hb
    have hm : (K-1)*K < n := by omega
    have hK2 : 2 ≤ K := by omega
    have := firstPart_lt_second n K hK2 hm
    have : n / (K-1) ≤ n / i := Nat.div_le_div_left h2 (by omega)
    omega

theorem first_attained (n K q : Nat) (hK1 : 1 ≤ K) (hKn : n ≤ K*(K+1)) (hq1 : 1 ≤ q) (hq : q ≤ n / K) :
    ∃ x, 1 ≤ x ∧ n / x = q := by
  have hqK : q * K ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hq
  by_cases small : q ≤ K
  · have hq0 : 0 < q := hq1
    have hsq : q * q ≤ n := Nat.le_trans (Nat.mul_le_mul_left q small) hqK
    have hx : q ≤ n / q := (Nat.le_div_iff_mul_le hq0).mpr hsq
    refine ⟨n / q, by omega, ?_⟩
    have h1 := Nat.div_add_mod n q
    have h2 := Nat.mod_lt n hq0
    have e1 : q * (n / q) = (n / q) * q := Nat.mul_comm _ _
    apply Nat.le_antisymm
    · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega)]
      show n < (q+1) * (n / q)
      have e2 : (q+1) * (n / q) = q * (n / q) + n / q := by rw [Nat.add_mul, Nat.one_mul]
      omega
    · rw [Nat.le_div_iff_mul_le (by omega)]
      omega
  · have hKq : K + 1 ≤ q := by omega
    have hp : q ≤ K + 1 := by
      have : n / K < K + 2 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        have : K * (K+1) < (K+2) * K := by
          rw [Nat.mul_comm (K+2) K]; exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        omega
      omega
    have hq' : q = K + 1 := by omega
    subst hq'
    refine ⟨K, hK1, ?_⟩
    have : K * (K+1) ≤ n := by rw [Nat.mul_comm]; exact hqK
    have : n = K * (K+1) := by omega
    rw [this, Nat.mul_comm, Nat.mul_div_cancel _ (by omega : 0 < K)]

theorem mem_qlist (n K q : Nat) (hK1 : 1 ≤ K) (hKn : n ≤ K*(K+1)) (hKm : K = 1 ∨ (K-1)*K < n) :
    q ∈ qlist n K ↔ 1 ≤ q ∧ ∃ x, 1 ≤ x ∧ n / x = q := by
  unfold qlist
  rw [List.mem_append, mem_firstPart, mem_secondPart]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨i, h1, h2, rfl⟩)
    · exact ⟨h1, first_attained n K q hK1 hKn h1 h2⟩
    · have hm : (K-1)*K < n := by
        rcases hKm with rfl | h
        · omega
        · exact h
      have : i ≤ n := by
        have : i ≤ (K-1)*K := by
          have : i * 1 ≤ (K-1) * K := Nat.mul_le_mul h2 hK1
          omega
        omega
      refine ⟨(Nat.le_div_iff_mul_le (by omega)).mpr (by omega), i, h1, rfl⟩
  · rintro ⟨hq, x, hx, rfl⟩
    by_cases small : x ≤ K - 1
    · right; exact ⟨x, hx, small, rfl⟩
    · left
      exact ⟨hq, Nat.div_le_div_left (by omega) (by omega)⟩

-- The result of `enumerate_quotients` is exactly the ascending list of the positive quotients.
theorem qlist_spec (n K : Nat) (hK1 : 1 ≤ K) (hKn : n ≤ K*(K+1)) (hKm : K = 1 ∨ (K-1)*K < n) :
    (qlist n K).Pairwise (· < ·) ∧ ∀ q, q ∈ qlist n K ↔ 1 ≤ q ∧ ∃ x, 1 ≤ x ∧ n / x = q :=
  ⟨qlist_sorted n K hK1 hKm,fun q => mem_qlist n K q hK1 hKn hKm⟩

theorem qlist_length (n K : Nat) : (qlist n K).length = n/K + (K-1) := by
  simp [qlist,firstPart,secondPart]

end Proofs.EnumerateQuotientsMath
