import Proofs.Cpp.Gen.VectorSum
import Proofs.Cpp.Lib.Basic

/-! # `vector_sum` (library/array/vector_sum.hpp)

The sum of a vector over any additive monoid `T`, in `x.size + 1` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.VectorSum

theorem vector_sum_spec {T : Type} [AddMonoid T] [Inhabited T] (x : Array T) (t0 : Nat) :
    ⦃fun t => ⌜t = t0⌝⦄ cp.vector_sum x ⦃⇓ r t => ⌜r = x.toList.sum ∧ t = t0 + x.size + 1⌝⦄ := by
  mvcgen [cp.vector_sum]
  case inv1 => exact ⇓⟨xs, s⟩ t => ⌜s = (xs.prefix.map (Cpp.get x)).sum ∧ t = t0 + 1 + xs.prefix.length⌝
  all_goals simp_all +zetaDelta
  · omega
  · rw [Cpp.range_map_get x]; simp [Cpp.range_length, Cpp.size]; omega

end Proofs.Cpp.VectorSum
