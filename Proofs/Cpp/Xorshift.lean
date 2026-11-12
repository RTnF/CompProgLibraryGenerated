import Proofs.Cpp.Gen.Xorshift
import Proofs.Cpp.Lib.Basic

/-! # `xorshift` (library/random/xorshift.hpp)

The 64 bit Xorshift step `x ^= x << 7; x ^= x >> 9` on `UInt64` (wrapping as in C++). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.Xorshift

/-- The state after one step. -/
def xnext (s : UInt64) : UInt64 :=
  let x := s ^^^ (s <<< 7)
  x ^^^ (x >>> 9)

/-- The state 0 is a fixed point (a full period needs a nonzero seed). -/
theorem xnext_zero : xnext 0 = 0 := by decide

/-- `Xor64(s)` holds the state `s`; one step. -/
theorem init_spec (s : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Xor64.init s ⦃⇓ r c => ⌜r.s = s ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Xor64.init]
  simp_all

/-- `get()` advances the state to `xnext s` and returns it; one step. -/
theorem get_spec (g : cp.Xor64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Xor64.get_ g ⦃⇓ r c => ⌜r.1 = xnext g.s ∧ r.2.s = xnext g.s ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Xor64.get_]
  simp_all +zetaDelta [xnext]

end Proofs.Cpp.Xorshift
