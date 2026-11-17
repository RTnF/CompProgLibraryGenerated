import Proofs.Cpp.Lib.ModIntMath
import Proofs.Cpp.Lib.PrimeCertificate
import Mathlib.Data.Nat.Choose.Basic

namespace Proofs.Cpp.ModIntFactorial

def factorialResidue (m n : Nat) : Nat := n.factorial % m

theorem factorial_step (m n : Nat) :
    (factorialResidue m n * (n + 1)) % m = factorialResidue m (n + 1) := by
  unfold factorialResidue
  rw [Nat.mod_mul_mod, Nat.factorial_succ, Nat.mul_comm]

theorem factorial_coprime (m n : Nat) (hp : Proofs.Fermat.IsPrime m) (hn : n < m) :
    Nat.Coprime n.factorial m := by
  revert hn
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Nat.factorial_succ]
    exact Nat.Coprime.mul_left (Proofs.Fermat.coprime_of_lt m (n + 1) hp (by omega) hn)
      (ih (by omega))

theorem factorial_nonzero (m n : Nat) (hp : Proofs.Fermat.IsPrime m) (hn : n < m) :
    factorialResidue m n ≠ 0 := by
  have hc := factorial_coprime m n hp hn
  intro hz
  have hg := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hz)
  change Nat.gcd n.factorial m = 1 at hc
  rw [hg] at hc
  have hm := hp.1
  omega

def denominator (m n k : Nat) : Nat := (k.factorial * (n - k).factorial) % m

theorem denominator_nonzero (m n k : Nat) (hp : Proofs.Fermat.IsPrime m)
    (hn : n < m) (hk : k ≤ n) : denominator m n k ≠ 0 := by
  have hc := Nat.Coprime.mul_left (factorial_coprime m k hp (by omega))
    (factorial_coprime m (n - k) hp (by omega))
  intro hz
  have hg := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hz)
  change Nat.gcd (k.factorial * (n - k).factorial) m = 1 at hc
  rw [hg] at hc
  have hm := hp.1
  omega

theorem quotient_of_product (m numerator divisor quotient inverse : Nat)
    (hnum : numerator = quotient * divisor) (hunit : divisor % m * inverse % m = 1) :
    numerator % m * inverse % m = quotient % m := by
  have hunit' : divisor * inverse % m = 1 := by rwa [← Nat.mod_mul_mod]
  rw [Nat.mod_mul_mod, hnum, Nat.mul_assoc, Nat.mul_mod, hunit']
  simp

def binomialResidue (m n k : Nat) : Nat :=
  factorialResidue m n * (denominator m n k ^ (m - 2) % m) % m

theorem binomial_correct (m n k : Nat) (hp : Proofs.Fermat.IsPrime m)
    (hn : n < m) (hk : k ≤ n) : binomialResidue m n k = n.choose k % m := by
  have hd0 := denominator_nonzero m n k hp hn hk
  have hdm : denominator m n k < m := Nat.mod_lt _ (by have := hp.1; omega)
  have hi := ModIntMath.inverse_residue_unit m (denominator m n k) hp (by omega) hdm
  have hnum : n.factorial = n.choose k * (k.factorial * (n - k).factorial) := by
    rw [← Nat.mul_assoc]
    exact (Nat.choose_mul_factorial_mul_factorial hk).symm
  exact quotient_of_product m _ _ _ _ hnum hi

theorem fixed_modulus_prime : Proofs.Fermat.IsPrime 998244353 := PrimeCertificate.modint_prime

end Proofs.Cpp.ModIntFactorial
