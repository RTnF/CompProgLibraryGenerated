namespace Proofs.LazySegArith

/-- `l = ceil(l0 / q)`. -/
def ceilDiv (l0 q : Nat) : Nat := (l0 + q - 1) / q

theorem floor_decomp (q u v : Nat) (hq : 0 < q) (hv : v < q) : (q * u + v) / q = u := by
  rw [Nat.mul_add_div hq u v, Nat.div_eq_of_lt hv]; simp

theorem ceilDiv_decomp (q u v : Nat) (hq : 0 < q) (hv : v < q) :
    ceilDiv (q * u + v) q = u + (if v = 0 then 0 else 1) := by
  unfold ceilDiv
  by_cases h0 : v = 0
  · subst h0
    have : q * u + 0 + q - 1 = q * u + (q - 1) := by omega
    rw [this, Nat.mul_add_div hq u (q - 1), Nat.div_eq_of_lt (by omega)]
    simp
  · simp only [h0, if_false]
    have : q * u + v + q - 1 = q * (u + 1) + (v - 1) := by rw [Nat.mul_add]; omega
    rw [this, Nat.mul_add_div hq (u + 1) (v - 1), Nat.div_eq_of_lt (by omega)]

theorem mod_mul_decomp (q m u v : Nat) (hq : 0 < q) (hm : 0 < m) (hv : v < q) :
    (q * u + v) % (q * m) = q * (u % m) + v := by
  have h1 : q * u + v = q * m * (u / m) + (q * (u % m) + v) := by
    have hu := Nat.div_add_mod u m
    calc q * u + v = q * (m * (u / m) + u % m) + v := by rw [hu]
      _ = q * m * (u / m) + (q * (u % m) + v) := by rw [Nat.mul_add, ← Nat.mul_assoc]; omega
  have h2 : q * (u % m) + v < q * m := by
    have : u % m + 1 ≤ m := Nat.mod_lt u hm
    have h3 : q * (u % m + 1) ≤ q * m := Nat.mul_le_mul_left q this
    rw [Nat.mul_add] at h3
    omega
  rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt h2]

theorem div_mul_decomp (q m u v : Nat) (hq : 0 < q) (hm : 0 < m) (hv : v < q) :
    (q * u + v) / (q * m) = u / m := by
  rw [← Nat.div_div_eq_div_mul, floor_decomp q u v hq hv]

theorem pow2_even (s : Nat) (hs : 1 ≤ s) : ∃ m', 2 ^ s = 2 * m' ∧ 0 < m' := by
  refine ⟨2 ^ (s - 1), ?_, Nat.two_pow_pos _⟩
  rw [← Nat.pow_succ']; congr 1; omega

/-- `(u + 1) / m = u / m` for an even `u` and an even `m >= 2`. -/
theorem succ_div_even (u m' : Nat) (hm : 0 < m') (hu : u % 2 = 0) : (u + 1) / (2 * m') = u / (2 * m') := by
  have h2 : 0 < 2 * m' := by omega
  have hr := Nat.mod_lt u h2
  have hd := Nat.div_add_mod u (2 * m')
  apply Nat.div_eq_of_lt_le
  · have := Nat.div_mul_le_self u (2 * m')
    omega
  · have hw : (2 * m') * (u / (2 * m')) = 2 * (m' * (u / (2 * m'))) := by rw [Nat.mul_assoc]
    have : u % (2 * m') ≠ 2 * m' - 1 := by omega
    have e : (u / (2 * m') + 1) * (2 * m') = (2 * m') * (u / (2 * m')) + 2 * m' := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (u / (2 * m'))]
    omega

theorem left_anc (l0 j s : Nat) (hs : 1 ≤ s) (hodd : ceilDiv l0 (2 ^ j) % 2 = 1) :
    l0 % 2 ^ (j + s) ≠ 0 ∧ ceilDiv l0 (2 ^ j) / 2 ^ s = l0 / 2 ^ (j + s) := by
  have hq : 0 < 2 ^ j := Nat.two_pow_pos j
  obtain ⟨m', hm', hm'pos⟩ := pow2_even s hs
  have hmpos : 0 < 2 ^ s := Nat.two_pow_pos s
  obtain ⟨u, v, hv, rfl⟩ : ∃ u v, v < 2 ^ j ∧ l0 = 2 ^ j * u + v :=
    ⟨l0 / 2 ^ j, l0 % 2 ^ j, Nat.mod_lt _ hq, (Nat.div_add_mod l0 (2 ^ j)).symm⟩
  rw [ceilDiv_decomp _ _ _ hq hv] at hodd ⊢
  have e1 : 2 ^ (j + s) = 2 ^ j * 2 ^ s := Nat.pow_add _ _ _
  rw [e1, mod_mul_decomp _ _ _ _ hq hmpos hv, div_mul_decomp _ _ _ _ hq hmpos hv]
  by_cases h0 : v = 0
  · subst h0
    simp only [if_true, Nat.add_zero] at hodd ⊢
    refine ⟨?_, trivial⟩
    have hu : u % 2 ^ s ≠ 0 := by
      intro hz
      have : 2 ^ s ∣ u := Nat.dvd_of_mod_eq_zero hz
      rw [hm'] at this
      obtain ⟨c, hc⟩ := this
      have : u % 2 = 0 := by rw [hc, Nat.mul_assoc]; exact Nat.mul_mod_right 2 (m' * c)
      omega
    intro hz
    rcases Nat.mul_eq_zero.mp hz with h | h
    · omega
    · exact hu h
  · simp only [h0, if_false] at hodd ⊢
    refine ⟨by omega, ?_⟩
    have hu : u % 2 = 0 := by omega
    rw [hm', succ_div_even u m' hm'pos hu]

theorem right_anc (r0 j s : Nat) (hs : 1 ≤ s) (hodd : (r0 / 2 ^ j) % 2 = 1) :
    r0 % 2 ^ (j + s) ≠ 0 ∧ (r0 / 2 ^ j - 1) / 2 ^ s = (r0 - 1) / 2 ^ (j + s) := by
  have hq : 0 < 2 ^ j := Nat.two_pow_pos j
  obtain ⟨m', hm', hm'pos⟩ := pow2_even s hs
  have hmpos : 0 < 2 ^ s := Nat.two_pow_pos s
  obtain ⟨u, v, hv, rfl⟩ : ∃ u v, v < 2 ^ j ∧ r0 = 2 ^ j * u + v :=
    ⟨r0 / 2 ^ j, r0 % 2 ^ j, Nat.mod_lt _ hq, (Nat.div_add_mod r0 (2 ^ j)).symm⟩
  rw [floor_decomp _ _ _ hq hv] at hodd ⊢
  have e1 : 2 ^ (j + s) = 2 ^ j * 2 ^ s := Nat.pow_add _ _ _
  rw [e1, mod_mul_decomp _ _ _ _ hq hmpos hv]
  have hum : u % 2 ^ s ≠ 0 := by
    intro hz
    have : 2 ^ s ∣ u := Nat.dvd_of_mod_eq_zero hz
    rw [hm'] at this
    obtain ⟨c, hc⟩ := this
    have : u % 2 = 0 := by rw [hc, Nat.mul_assoc]; exact Nat.mul_mod_right 2 (m' * c)
    omega
  by_cases h0 : v = 0
  · subst h0
    refine ⟨?_, ?_⟩
    · intro hz
      have : 2 ^ j * (u % 2 ^ s) = 0 := by omega
      rcases Nat.mul_eq_zero.mp this with h | h
      · omega
      · exact hum h
    · have hu1 : 1 ≤ u := by omega
      have : 2 ^ j * u + 0 - 1 = 2 ^ j * (u - 1) + (2 ^ j - 1) := by
        have : 2 ^ j * u = 2 ^ j * (u - 1) + 2 ^ j := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega
      rw [this, div_mul_decomp _ _ _ _ hq hmpos (by omega)]
  · refine ⟨by omega, ?_⟩
    have : 2 ^ j * u + v - 1 = 2 ^ j * u + (v - 1) := by omega
    rw [this, div_mul_decomp _ _ _ _ hq hmpos (by omega), hm']
    have hu : (u - 1) % 2 = 0 := by omega
    have := succ_div_even (u - 1) m' hm'pos hu
    rw [show u - 1 + 1 = u by omega] at this
    exact this.symm

theorem ceil_step (l0 j : Nat) : ceilDiv l0 (2 ^ (j + 1)) = (ceilDiv l0 (2 ^ j) + ceilDiv l0 (2 ^ j) % 2) / 2 := by
  unfold ceilDiv
  have hq : 0 < 2 ^ j := Nat.two_pow_pos j
  have e1 : (l0 + 2 ^ j - 1) / 2 ^ j + 1 = (l0 + 2 ^ j - 1 + 2 ^ j) / 2 ^ j := by
    rw [Nat.add_div_right _ hq]
  have e2 : (l0 + 2 ^ (j + 1) - 1) = (l0 + 2 ^ j - 1 + 2 ^ j) := by
    rw [Nat.pow_succ]; omega
  have e3 : (l0 + 2 ^ j - 1 + 2 ^ j) / 2 ^ j / 2 = (l0 + 2 ^ j - 1 + 2 ^ j) / (2 ^ j * 2) := by
    rw [Nat.div_div_eq_div_mul]
  rw [e2, Nat.pow_succ, ← e3, ← e1]
  omega

theorem floor_step (r0 j : Nat) : r0 / 2 ^ (j + 1) = (r0 / 2 ^ j - (r0 / 2 ^ j) % 2) / 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  generalize r0 / 2 ^ j = x
  omega

theorem ceil_pos (l0 q : Nat) (hl : 1 ≤ l0) (hq : 0 < q) : 1 ≤ ceilDiv l0 q := by
  unfold ceilDiv
  rw [Nat.le_div_iff_mul_le hq]
  omega

end Proofs.LazySegArith
