import Proofs.Cpp.Gen.Extrema
import Proofs.Cpp.Lib.Basic

/-! # `chmax`, `chmin` (library/number/extrema.hpp)

For any template parameters `S`, `T`: the comparison is the operator of the instance (`Cpp.HLt`), the assignment
its conversion (`Cpp.Conv`). For `S = T` with an order (the instance `long long`), the result is `max`/`min`. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.Extrema

theorem chmax_spec {S T : Type} [Conv T S] [HLt S T] (a : S) (b : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.chmax a b
    ⦃⇓ r c => ⌜r = (HLt.hlt a b, if HLt.hlt a b then (Conv.conv b : S) else a) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.chmax]
  all_goals simp_all +zetaDelta

theorem chmin_spec {S T : Type} [Conv T S] [HLt T S] (a : S) (b : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.chmin a b
    ⦃⇓ r c => ⌜r = (HLt.hlt b a, if HLt.hlt b a then (Conv.conv b : S) else a) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.chmin]
  all_goals simp_all +zetaDelta

/-- The instance `S = T = long long`: `chmax` stores `max a b` and reports `a < b`. -/
theorem chmax_int (a b : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.chmax a b ⦃⇓ r c => ⌜r = (decide (a < b), max a b) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.chmax]
  all_goals simp_all +zetaDelta [HLt.hlt, Conv.conv, max_def]
  all_goals try omega

/-- The instance `S = T = long long`: `chmin` stores `min a b` and reports `b < a`. -/
theorem chmin_int (a b : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.chmin a b ⦃⇓ r c => ⌜r = (decide (b < a), min a b) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.chmin]
  all_goals simp_all +zetaDelta [HLt.hlt, Conv.conv, min_def]
  all_goals try omega

end Proofs.Cpp.Extrema
