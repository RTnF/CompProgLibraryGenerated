import Proofs.IntegralExtrema
import Proofs.ExtremaInstances

namespace Proofs.IntegralExtremaShape
open Proofs.CppTemplate

-- Quantified over the supported builtin integral family, including mixed types.
-- These are specialization/shape facts, not whole-call correctness theorems.
theorem chmax_instantiates (left right : Integral) (policy : Bool) :
    (IntegralExtrema.chmax.instantiate [left,right] policy).isSome = true := by
  cases left <;> cases right <;> cases policy <;> decide

theorem chmin_instantiates (left right : Integral) (policy : Bool) :
    (IntegralExtrema.chmin.instantiate [left,right] policy).isSome = true := by
  cases left <;> cases right <;> cases policy <;> decide

theorem chmax_signed : IntegralExtrema.chmax.instantiate [.i32,.i32] =
    some ExtremaInstances.chmax__int__int := rfl

theorem chmin_signed : IntegralExtrema.chmin.instantiate [.i32,.i32] =
    some ExtremaInstances.chmin__int__int := rfl

theorem chmax_unsigned : IntegralExtrema.chmax.instantiate [.u32,.u32] =
    some ExtremaInstances.chmax__unsigned_int__unsigned_int := rfl

theorem chmin_unsigned : IntegralExtrema.chmin.instantiate [.u32,.u32] =
    some ExtremaInstances.chmin__unsigned_int__unsigned_int := rfl

end Proofs.IntegralExtremaShape
