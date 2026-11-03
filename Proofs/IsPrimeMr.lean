import Proofs.IsPrimeExec
import Proofs.Fermat

/-! Miller-Rabin: a prime `n` has no witness (`mrwx n r (a ^ d % n) = false` for `1 ≤ a ≤ n - 1`, `n - 1 = d * 2 ^ r`). -/
namespace Proofs.IsPrimeMr
open Proofs.IsPrimeExec Proofs.Fermat

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

end Proofs.IsPrimeMr
