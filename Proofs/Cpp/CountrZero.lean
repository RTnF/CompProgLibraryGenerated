import Proofs.Cpp.Gen.CountrZero
import Proofs.Cpp.Lib.Basic

/-! # `countr_zero_u64` (library/number_theory/countr_zero.hpp)

The number of trailing zero bits of `n` (`64` for `0`): the result `r ≤ 64` has `2^r ∣ n` and, when
`r < 64`, not `2^(r+1) ∣ n`; two steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.CountrZero

theorem countr_zero_u64_spec (n : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.countr_zero_u64 n
    ⦃⇓ r c => ⌜0 ≤ r ∧ r ≤ 64 ∧ 2 ^ r.toNat ∣ n.toNat ∧ (r < 64 → ¬ 2 ^ (r.toNat + 1) ∣ n.toNat) ∧
               c = t0 + 2⌝⦄ := by
  mvcgen [cp.countr_zero_u64]
  all_goals simp +zetaDelta at *
  have h := countrZero_spec 64 n.toNat
  obtain ⟨hle, hd, hmax⟩ := h
  exact ⟨by omega, hd, by exact_mod_cast hmax, by assumption⟩

end Proofs.Cpp.CountrZero
