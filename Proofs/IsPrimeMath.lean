import Proofs.Fermat

/-! Pure Miller-Rabin facts for `is_prime` (library/number_theory/is_prime.hpp): the witness loop `wrun`/`mrwx`, and a prime
`n` has no witness (`mrwx_prime`: `mrwx n r (a ^ d % n) = false` for `1 ≤ a ≤ n - 1`, `n - 1 = d * 2 ^ r`). -/
namespace Proofs.IsPrimeMath
open Proofs.Fermat

/-- The squaring loop of `mr_witness` on the state `(x, cf, i)`, for at most `k` rounds. -/
def wrun (n r : Nat) : Nat → Nat × Bool × Nat → Nat × Bool × Nat
  | 0, s => s
  | k + 1, (x, cf, i) =>
    if i + 1 < r ∧ cf = true then wrun n r k ((x * x) % n, decide ((x * x) % n ≠ n - 1), i + 1) else (x, cf, i)

/-- `mr_witness n d r a` with `x = a ^ d mod n`: `true` when `a` proves `n` composite. -/
def mrwx (n r x : Nat) : Bool :=
  if x = 1 then false else if x = n - 1 then false else (wrun n r r (x, true, 0)).2.1

/-- The `i`-th base of `mr_base`. -/
def mrb (i : Nat) : Nat :=
  if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 5 else if i = 3 then 7 else if i = 4 then 11
  else if i = 5 then 13 else if i = 6 then 17 else if i = 7 then 19 else if i = 8 then 23 else if i = 9 then 29
  else if i = 10 then 31 else 37

theorem prime_dvd_mul (p u v : Nat) (hp : IsPrime p) (h : p ∣ u * v) : p ∣ u ∨ p ∣ v := by
  by_cases hu : p ∣ u
  · exact Or.inl hu
  · right
    have hg : Nat.gcd p u = 1 := by
      rcases hp.2 _ (Nat.gcd_dvd_left p u) with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ Nat.gcd_dvd_right p u) hu
    exact Nat.Coprime.dvd_of_dvd_mul_left hg h

theorem sqrt_one (p y : Nat) (hp : IsPrime p) (hy : y < p) (h : y * y % p = 1) : y = 1 ∨ y = p - 1 := by
  have hp2 := hp.1
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := by
    cases y with
    | zero => simp at h
    | succ z => exact ⟨z, rfl⟩
  have e : (z + 1) * (z + 1) = z * (z + 2) + 1 := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]; omega
  have hdiv := Nat.div_add_mod ((z + 1) * (z + 1)) p
  rw [h] at hdiv
  have hd : p ∣ z * (z + 2) := ⟨(z + 1) * (z + 1) / p, by omega⟩
  rcases prime_dvd_mul p z (z + 2) hp hd with h1 | h1
  · left
    obtain ⟨c, hc⟩ := h1
    have : c = 0 := by
      by_cases hc0 : c = 0
      · exact hc0
      · have : p * 1 ≤ p * c := Nat.mul_le_mul_left p (by omega)
        omega
    subst this; omega
  · right
    obtain ⟨c, hc⟩ := h1
    have : c = 1 := by
      by_cases hc0 : c = 0
      · subst hc0; omega
      · by_cases hc1 : c = 1
        · exact hc1
        · have : p * 2 ≤ p * c := Nat.mul_le_mul_left p (by omega)
          omega
    subst this; omega

def sq (n x0 : Nat) : Nat → Nat
  | 0 => x0
  | j + 1 => sq n x0 j * sq n x0 j % n

theorem sq_lt (n x0 : Nat) (hn : 0 < n) (h0 : x0 < n) : ∀ j, sq n x0 j < n
  | 0 => h0
  | j + 1 => by simp only [sq]; exact Nat.mod_lt _ hn

theorem sq_pow (n a d : Nat) : ∀ j, sq n (a ^ d % n) j = a ^ (d * 2 ^ j) % n
  | 0 => by simp [sq]
  | j + 1 => by
    simp only [sq]
    rw [sq_pow n a d j, ← Nat.mul_mod, ← Nat.pow_add]
    congr 2
    rw [Nat.pow_succ, Nat.mul_two, Nat.mul_add]

theorem find_neg (n x0 : Nat) (hp : IsPrime n) (h0 : x0 < n) (h1 : x0 ≠ 1) (h2 : x0 ≠ n - 1) :
    ∀ j, sq n x0 j = 1 → ∃ i, 1 ≤ i ∧ i < j ∧ sq n x0 i = n - 1
  | 0, h => by simp [sq] at h; exact absurd h h1
  | j + 1, h => by
    have hlt := sq_lt n x0 (by have := hp.1; omega) h0 j
    have hs : sq n x0 j * sq n x0 j % n = 1 := h
    rcases sqrt_one n _ hp hlt hs with e | e
    · obtain ⟨i, hi1, hi2, hi3⟩ := find_neg n x0 hp h0 h1 h2 j e
      exact ⟨i, hi1, by omega, hi3⟩
    · cases j with
      | zero => simp [sq] at e; exact absurd e h2
      | succ j' => exact ⟨j' + 1, by omega, by omega, e⟩

theorem wrun_false_state (n r : Nat) : ∀ (k x i : Nat), (wrun n r k (x, false, i)).2.1 = false
  | 0, x, i => by simp [wrun]
  | k + 1, x, i => by simp [wrun]

theorem wrun_find (n x0 r : Nat) : ∀ (k i : Nat), r ≤ i + k + 1 → ∀ j, 1 ≤ j → i + j < r → sq n x0 (i + j) = n - 1 →
    (wrun n r k (sq n x0 i, true, i)).2.1 = false
  | 0, i, hk, j, hj, hij, _ => by omega
  | k + 1, i, hk, j, hj, hij, hs => by
    have hc : i + 1 < r ∧ (true = true) := ⟨by omega, rfl⟩
    have e : wrun n r (k + 1) (sq n x0 i, true, i) = wrun n r k (sq n x0 (i + 1), decide (sq n x0 (i + 1) ≠ n - 1), i + 1) := by
      rw [wrun, if_pos ⟨hc.1, rfl⟩]
      rfl
    rw [e]
    by_cases hj1 : j = 1
    · subst hj1
      have : decide (sq n x0 (i + 1) ≠ n - 1) = false := by simp [hs]
      rw [this]; exact wrun_false_state n r k _ _
    · have hs' : sq n x0 (i + 1 + (j - 1)) = n - 1 := by
        have : i + 1 + (j - 1) = i + j := by omega
        rw [this]; exact hs
      have hd : decide (sq n x0 (i + 1) ≠ n - 1) = true ∨ decide (sq n x0 (i + 1) ≠ n - 1) = false := by
        cases decide (sq n x0 (i + 1) ≠ n - 1) <;> simp
      rcases hd with hd | hd
      · rw [hd]
        exact wrun_find n x0 r k (i + 1) (by omega) (j - 1) (by omega) (by omega) hs'
      · rw [hd]; exact wrun_false_state n r k _ _

theorem mrwx_prime (n d r a : Nat) (hp : IsPrime n) (ha0 : 0 < a) (ha1 : a < n) (hnd : n - 1 = d * 2 ^ r) :
    mrwx n r (a ^ d % n) = false := by
  have hn0 : 0 < n := by have := hp.1; omega
  have h0 : a ^ d % n < n := Nat.mod_lt _ hn0
  unfold mrwx
  by_cases h1 : a ^ d % n = 1
  · simp [h1]
  · by_cases h2 : a ^ d % n = n - 1
    · simp [h1, h2]
    · simp only [h1, h2, if_false]
      have hr : sq n (a ^ d % n) r = 1 := by
        rw [sq_pow, ← hnd]; exact fermat n a hp ha0 ha1
      obtain ⟨i, hi1, hi2, hi3⟩ := find_neg n _ hp h0 h1 h2 r hr
      have := wrun_find n (a ^ d % n) r r 0 (by omega) i hi1 (by omega) (by simpa using hi3)
      simpa [sq] using this

/-- Base `j` proves `n` composite (`n - 1 = d * 2 ^ r`, `d` odd). -/
def badBase (n d r j : Nat) : Prop := mrb j ≤ n - 2 ∧ mrwx n r (mrb j ^ d % n) = true

/-- The published witness-set computation (bases 2, 3, ..., 37 decide primality below `3.18e23`), restricted to the
inputs `is_prime` handles. It is NOT proved here; the theorems take it as an explicit hypothesis. -/
def MRWitnessSet : Prop := ∀ n : Nat, 3 ≤ n → n < 2 ^ 64 → n % 2 = 1 → ¬ IsPrime n →
  ∀ d r, n - 1 = d * 2 ^ r → d % 2 = 1 → ∃ j, j < 12 ∧ badBase n d r j

theorem mrb_le (j : Nat) : 2 ≤ mrb j ∧ mrb j ≤ 37 := by
  unfold mrb; repeat' (first | split | omega)

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have : d ≤ 2 := Nat.le_of_dvd (by decide) hd
  have : d ≠ 0 := by intro h; subst h; simp at hd
  omega

theorem odd_of_prime (n : Nat) (hp : IsPrime n) (h2 : n ≠ 2) : n % 2 = 1 := by
  by_cases h : n % 2 = 0
  · have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero h
    rcases hp.2 2 hd with h1 | h1 <;> omega
  · omega

/-- No base is bad for a prime. -/
theorem not_bad_of_prime (n d r j : Nat) (hp : IsPrime n) (hnd : n - 1 = d * 2 ^ r) : ¬ badBase n d r j := by
  intro ⟨h1, h2⟩
  have := mrb_le j
  rw [mrwx_prime n d r (mrb j) hp (by omega) (by omega) hnd] at h2
  exact Bool.false_ne_true h2

end Proofs.IsPrimeMath
