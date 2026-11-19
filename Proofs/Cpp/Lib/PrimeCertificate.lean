import Proofs.Cpp.Prelude
import Proofs.Math.Fermat

/-! Balanced trial-division certificates. Computation recurses on the tree
depth, rather than constructing a linear chain of divisor checks. -/
namespace Proofs.Cpp.PrimeCertificate

def oddChecks (n start : Nat) : Nat → Bool
  | 0 => decide (n % (2 * start + 3) ≠ 0)
  | depth + 1 => oddChecks n start depth && oddChecks n (start + 2 ^ depth) depth

theorem oddChecks_sound (n start depth : Nat) (h : oddChecks n start depth = true) :
    ∀ k, start ≤ k → k < start + 2 ^ depth → ¬(2 * k + 3) ∣ n := by
  induction depth generalizing start with
  | zero =>
    intro k hk hl
    have he : k = start := by simp only [Nat.pow_zero] at hl; omega
    subst k
    exact fun hd => (of_decide_eq_true h) (Nat.mod_eq_zero_of_dvd hd)
  | succ depth ih =>
    have hh := Bool.and_eq_true_iff.mp h
    intro k hk hl
    by_cases hm : k < start + 2 ^ depth
    · exact ih start hh.1 k hk hm
    · apply ih (start + 2 ^ depth) hh.2 k (by omega)
      rw [Nat.pow_succ] at hl
      omega

theorem prime_of_small_divisors (n bound : Nat) (hn : 2 ≤ n) (hb : n < bound * bound)
    (hcheck : ∀ d, 2 ≤ d → d < bound → ¬d ∣ n) : Proofs.Fermat.IsPrime n := by
  refine ⟨hn, ?_⟩
  intro d hd
  by_cases h1 : d = 1
  · exact Or.inl h1
  by_cases he : d = n
  · exact Or.inr he
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
  have hdn := Nat.le_of_dvd (by omega : 0 < n) hd
  have hprod : n / d * d = n := Nat.div_mul_cancel hd
  have hq0 : 0 < n / d := Nat.div_pos hdn hd0
  have hq2 : 2 ≤ n / d := by
    by_cases hq : 2 ≤ n / d
    · exact hq
    have hq1 : n / d = 1 := by omega
    rw [hq1, Nat.one_mul] at hprod
    exact False.elim (he hprod)
  by_cases hl : d < bound
  · exact False.elim (hcheck d (by omega) hl hd)
  · have hq : n / d < bound := by
      by_cases hq : n / d < bound
      · exact hq
      have hm := Nat.mul_le_mul (show bound ≤ n / d by omega) (show bound ≤ d by omega)
      rw [hprod] at hm
      omega
    exact False.elim (hcheck (n / d) hq2 hq ⟨d, hprod.symm⟩)

theorem prime_of_oddChecks (n depth : Nat) (hn : 2 ≤ n) (hodd : n % 2 ≠ 0)
    (hb : n < (2 * 2 ^ depth + 2) * (2 * 2 ^ depth + 2))
    (hcheck : oddChecks n 0 depth = true) : Proofs.Fermat.IsPrime n := by
  apply prime_of_small_divisors n (2 * 2 ^ depth + 2) hn hb
  intro d hd hl hdn
  rcases Nat.mod_two_eq_zero_or_one d with he | he
  · exact hodd (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero he) hdn))
  · let k := (d - 3) / 2
    have hk : k < 2 ^ depth := by dsimp [k]; omega
    have heq : 2 * k + 3 = d := by dsimp [k]; omega
    apply oddChecks_sound n 0 depth hcheck k (Nat.zero_le k) (by simpa using hk)
    rwa [heq]

theorem modint_prime : Proofs.Fermat.IsPrime 998244353 := by
  apply prime_of_oddChecks 998244353 14 (by decide) (by decide) (by decide)
  decide

end Proofs.Cpp.PrimeCertificate
