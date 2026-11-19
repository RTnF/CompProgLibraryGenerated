namespace Proofs.Fermat

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem coprime_of_lt (p a : Nat) (hp : IsPrime p) (h0 : 0 < a) (h1 : a < p) : Nat.Coprime a p := by
  have hd : Nat.gcd a p ∣ p := Nat.gcd_dvd_right a p
  rcases hp.2 _ hd with h | h
  · exact h
  · have : Nat.gcd a p ≤ a := Nat.le_of_dvd h0 (Nat.gcd_dvd_left a p)
    omega

theorem not_dvd_of_lt (p x : Nat) (h0 : 0 < x) (h1 : x < p) : ¬ p ∣ x := by
  intro h
  have := Nat.le_of_dvd h0 h
  omega

-- multiplication by a unit is injective on [1, p)
theorem mul_inj (p a x y : Nat) (hp : IsPrime p) (ha0 : 0 < a) (ha1 : a < p) (hx0 : 0 < x) (hx1 : x < p)
    (hy0 : 0 < y) (hy1 : y < p) (h : a * x % p = a * y % p) : x = y := by
  have cop : Nat.Coprime p a := (coprime_of_lt p a hp ha0 ha1).symm
  have key : ∀ u v, 0 < u → u < p → v < u → a * u % p = a * v % p → False := by
    intro u v hu0 hu1 hvu hh
    have h1 := Nat.sub_mod_eq_zero_of_mod_eq hh
    have h2 : p ∣ a * u - a * v := Nat.dvd_of_mod_eq_zero h1
    rw [← Nat.mul_sub] at h2
    have h3 : p ∣ u - v := cop.dvd_of_dvd_mul_left h2
    have := Nat.le_of_dvd (by omega) h3
    omega
  by_cases c : x < y
  · exact (key y x hy0 hy1 c h.symm).elim
  · by_cases c2 : y < x
    · exact (key x y hx0 hx1 c2 h).elim
    · omega

theorem nodup_map_inj (f : Nat → Nat) : ∀ (l : List Nat), l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
    (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
    intro hn hinj
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hn.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    intro hmem
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
    have := hinj y (List.mem_cons_of_mem _ hy) a (List.mem_cons_self ..) hfy
    exact hn.1 (this ▸ hy)

theorem prod_map_mod (p a : Nat) : ∀ (l : List Nat), ((l.map fun x => a * x % p).prod) % p = (a ^ l.length * l.prod) % p := by
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Nat.mul_mod, Nat.mod_mod, ih, ← Nat.mul_mod]
    have : a ^ (t.length + 1) * (x * t.prod) = (a * x) * (a ^ t.length * t.prod) := by
      rw [Nat.pow_succ]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [this]

theorem coprime_prod (p : Nat) (hp : IsPrime p) : ∀ (l : List Nat), (∀ x ∈ l, 0 < x ∧ x < p) → Nat.Coprime l.prod p := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x t ih =>
    intro h
    simp only [List.prod_cons]
    exact Nat.Coprime.mul_left (coprime_of_lt p x hp (h x (List.mem_cons_self ..)).1 (h x (List.mem_cons_self ..)).2)
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

-- Fermat's little theorem
theorem fermat (p a : Nat) (hp : IsPrime p) (ha0 : 0 < a) (ha1 : a < p) : a ^ (p - 1) % p = 1 := by
  have p2 := hp.1
  let S : List Nat := List.range' 1 (p - 1)
  let f : Nat → Nat := fun x => a * x % p
  have memS : ∀ z, z ∈ S ↔ 0 < z ∧ z < p := by
    intro z
    simp only [S, List.mem_range'_1]
    omega
  have hnodupS : S.Nodup := List.nodup_range'
  have hfS : ∀ x ∈ S, f x ∈ S := by
    intro x hx
    rw [memS] at hx ⊢
    refine ⟨?_, Nat.mod_lt _ (by omega)⟩
    apply Nat.pos_of_ne_zero
    intro h0
    have hd : p ∣ a * x := Nat.dvd_of_mod_eq_zero h0
    have cop : Nat.Coprime p a := (coprime_of_lt p a hp ha0 ha1).symm
    exact not_dvd_of_lt p x hx.1 hx.2 (cop.dvd_of_dvd_mul_left hd)
  have hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    intro x hx y hy h
    rw [memS] at hx hy
    exact mul_inj p a x y hp ha0 ha1 hx.1 hx.2 hy.1 hy.2 h
  have hnodupM : (S.map f).Nodup := nodup_map_inj f S hnodupS hinj
  have hperm : (S.map f).Perm S := by
    rw [List.perm_ext_iff_of_nodup hnodupM hnodupS]
    intro z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact hfS x hx
    · intro hz
      refine Classical.byContradiction fun hnot => ?_
      have hcons : (z :: S.map f).Nodup := List.nodup_cons.mpr ⟨hnot, hnodupM⟩
      have hsub : (z :: S.map f) ⊆ S := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact hz
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw'
          exact hfS x hx
      have := hcons.length_le_of_subset hsub
      simp [S] at this
      omega
  have hprod : (S.map f).prod = S.prod := List.Perm.prod_nat hperm
  have hlen : S.length = p - 1 := by simp [S]
  have hmod := prod_map_mod p a S
  rw [hprod, hlen] at hmod
  have hcop : Nat.Coprime S.prod p := coprime_prod p hp S (fun x hx => (memS x).mp hx)
  -- cancel S.prod
  have hge : S.prod ≤ a ^ (p - 1) * S.prod := by
    have : 1 ≤ a ^ (p - 1) := Nat.one_le_pow _ _ ha0
    calc S.prod = 1 * S.prod := (Nat.one_mul _).symm
      _ ≤ a ^ (p - 1) * S.prod := Nat.mul_le_mul_right _ this
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq hmod.symm
  have h2 : p ∣ a ^ (p - 1) * S.prod - S.prod := Nat.dvd_of_mod_eq_zero h1
  have h3 : a ^ (p - 1) * S.prod - S.prod = (a ^ (p - 1) - 1) * S.prod := by
    rw [Nat.sub_mul, Nat.one_mul]
  rw [h3] at h2
  have h4 : p ∣ a ^ (p - 1) - 1 := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right h2
  have h5 : 1 ≤ a ^ (p - 1) := Nat.one_le_pow _ _ ha0
  have h6 : a ^ (p - 1) = (a ^ (p - 1) - 1) + 1 := by omega
  rw [h6, Nat.add_mod, Nat.mod_eq_zero_of_dvd h4]
  simp [Nat.mod_eq_of_lt (show 1 < p by omega)]

-- The inverse computed by `ModInt::inv`
theorem inv_mul_eq_one (p x : Nat) (hp : IsPrime p) (h0 : 0 < x) (h1 : x < p) : (x * (x ^ (p - 2) % p)) % p = 1 := by
  have h := fermat p x hp h0 h1
  have e : x * x ^ (p - 2) = x ^ (p - 1) := by
    have : p - 1 = (p - 2) + 1 := by have := hp.1; omega
    rw [this, Nat.pow_succ, Nat.mul_comm]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, e]
  exact h

end Proofs.Fermat
