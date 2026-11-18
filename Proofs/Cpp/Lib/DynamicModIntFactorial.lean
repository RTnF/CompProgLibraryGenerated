import Proofs.Cpp.Lib.ModIntFactorial

namespace Proofs.Cpp.DynamicModIntFactorial

open Proofs.Cpp.ModIntFactorial

/-- The inverse cache reaches the requested entry without crossing the modulus. -/
theorem inverse_cache_bound (modulus requested : Nat) (h : requested < modulus) :
    requested < min (max 100000 (requested + 1)) modulus ∧
      min (max 100000 (requested + 1)) modulus ≤ modulus := by
  omega

/-- Appending the inverse of the next factor maintains the inverse-factorial
invariant used by the cache. -/
theorem inverse_factorial_step (m n previous : Nat) (hp : Proofs.Fermat.IsPrime m)
    (hn : n + 1 < m) (hprevious : factorialResidue m n * previous % m = 1) :
    factorialResidue m (n + 1) *
      (previous * ((n + 1) ^ (m - 2) % m) % m) % m = 1 := by
  let inverse := (n + 1) ^ (m - 2) % m
  have hunit : (n + 1) * inverse % m = 1 :=
    Proofs.Cpp.ModIntMath.inverse_residue_unit m (n + 1) hp (by omega) hn
  rw [← factorial_step]
  change (factorialResidue m n * (n + 1) % m) * (previous * inverse % m) % m = 1
  calc
    _ = (factorialResidue m n * (n + 1)) * (previous * inverse) % m :=
      (Nat.mul_mod _ _ _).symm
    _ = (factorialResidue m n * previous) * ((n + 1) * inverse) % m := by
      congr 1
      ac_rfl
    _ = 1 := by
      rw [Nat.mul_mod, hprevious, hunit, Nat.one_mul, Nat.mod_eq_of_lt (by have := hp.1; omega)]

/-- The query multiplies the numerator by the two cached inverses. Only the
cache invariants are needed, independently of cache capacity or history. -/
theorem choose_from_caches (m n k left right : Nat) (hk : k ≤ n)
    (hl : factorialResidue m k * left % m = 1)
    (hr : factorialResidue m (n - k) * right % m = 1) :
    (factorialResidue m n * left % m) * right % m = n.choose k % m := by
  have hl' : k.factorial * left % m = 1 := by
    simpa only [factorialResidue, Nat.mod_mul_mod] using hl
  have hr' : (n - k).factorial * right % m = 1 := by
    simpa only [factorialResidue, Nat.mod_mul_mod] using hr
  have hunit : ((k.factorial * (n - k).factorial) % m) * (left * right) % m = 1 := by
    rw [Nat.mod_mul_mod]
    have h :
        k.factorial * (n - k).factorial * (left * right) =
          (k.factorial * left) * ((n - k).factorial * right) := by ac_rfl
    rw [h, Nat.mul_mod, hl', hr', Nat.one_mul]
    exact (congrArg (· % m) hl').symm.trans ((Nat.mod_mod _ _).trans hl')
  rw [Nat.mod_mul_mod, Nat.mul_assoc]
  apply quotient_of_product m n.factorial (k.factorial * (n - k).factorial)
  · rw [← Nat.mul_assoc]
    exact (Nat.choose_mul_factorial_mul_factorial hk).symm
  · exact hunit

end Proofs.Cpp.DynamicModIntFactorial
