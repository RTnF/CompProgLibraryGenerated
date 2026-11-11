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

theorem safe_mod_value (x m : Int) (hm : 0 < m) :
    (if x.tmod m < 0 then x.tmod m + m else x.tmod m) = x % m := by
  have h1 := Int.emod_nonneg x (by omega : m ≠ 0)
  have h2 := Int.emod_lt_of_pos x hm
  have h3 : (m.natAbs : Int) = m := by omega
  rw [Int.tmod_eq_emod]
  by_cases hc : 0 ≤ x ∨ m ∣ x <;> simp only [hc, ite_true, ite_false] at * <;> split <;> omega

/-- The call as a step of a caller's proof (`mvcgen` uses it): the value `x % m` in one tick. -/
@[spec] theorem safe_mod_wp (x m : Int) (hm : 0 < m) {Q : PostCond Int PS} :
    ⦃fun c => Q.1 (x % m) (c + 1)⦄ cp.safe_mod x m ⦃Q⦄ := by
  mvcgen [cp.safe_mod]
  all_goals simp +zetaDelta [mod] at *
  · have e := safe_mod_value x m hm
    rw [if_pos ‹_›] at e
    rw [e]; assumption
  · have e := safe_mod_value x m hm
    rw [if_neg (by omega)] at e
    rw [e]; assumption

end Proofs.Cpp.SafeMod
