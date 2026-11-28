import Proofs.Cpp.Gen.BitWidthU64
import Proofs.Cpp.Lib.Basic

/-! # `bit_width_u64` (library/number_theory/bit_width_u64.hpp)

The number of bits of `value` (`0` for `0`, otherwise `log2 value + 1`), in two steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.BitWidthU64

theorem bit_width_u64_spec (value : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.bit_width_u64 value
    ⦃⇓ r c => ⌜r = bitWidth value.toNat ∧ c = t0 + 2⌝⦄ := by
  mvcgen [cp.bit_width_u64]
  all_goals simp_all +zetaDelta

end Proofs.Cpp.BitWidthU64
