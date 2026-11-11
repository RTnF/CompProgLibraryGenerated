import Proofs.Cpp.Gen.SafeMod
import Proofs.Cpp.Lib.Basic

/-! # `safe_mod` (library/number_theory/safe_mod.hpp)

For `m > 0`, `safe_mod(x, m)` is the remainder of `x` in `[0, m)` (`Int.emod`), in one step. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.SafeMod

theorem safe_mod_spec (x m : Int) (hm : 0 < m) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.safe_mod x m ⦃⇓ r c => ⌜r = x % m ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.safe_mod]
  all_goals simp_all +zetaDelta [mod]
  all_goals
    have h1 := Int.emod_nonneg x (by omega : m ≠ 0)
    have h2 := Int.emod_lt_of_pos x hm
    have h3 : (m.natAbs : Int) = m := by omega
    rw [Int.tmod_eq_emod] at *
    by_cases hc : 0 ≤ x ∨ m ∣ x <;> simp only [hc, ite_true, ite_false] at * <;> omega

end Proofs.Cpp.SafeMod
