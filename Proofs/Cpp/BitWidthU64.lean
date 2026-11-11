import Proofs.Cpp.Gen.BitWidthU64
import Proofs.Cpp.Lib.Basic

/-! # `bit_width_u64` (library/number_theory/bit_width_u64.hpp)

The number of bits of `value` (`0` for `0`, otherwise `log2 value + 1`), in `bitWidth value + 2` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.BitWidthU64

/-- `std::bit_width`: `0` for `0`, otherwise `log2 n + 1`. -/
def bitWidth (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

@[simp] theorem bitWidth_zero : bitWidth 0 = 0 := rfl

theorem bitWidth_div_two (n : Nat) (h : 0 < n) : bitWidth (n / 2) + 1 = bitWidth n := by
  unfold bitWidth
  by_cases h1 : n = 1
  · subst h1; rfl
  · have h2 : 2 ≤ n := by omega
    rw [Nat.log2_def n]; simp only [h2, ite_true]
    simp [show n / 2 ≠ 0 by omega, show n ≠ 0 by omega]

theorem bit_width_u64_spec (value : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.bit_width_u64 value
    ⦃⇓ r c => ⌜r = bitWidth value.toNat ∧ c = t0 + 2 + bitWidth value.toNat⌝⦄ := by
  mvcgen [cp.bit_width_u64]
  case inv =>
    exact ⟨fun ⟨v, r⟩ c => ⌜0 ≤ r ∧ r.toNat + bitWidth v.toNat = bitWidth value.toNat ∧
                             c + bitWidth v.toNat = t0 + 1 + bitWidth value.toNat⌝,
           fun ⟨_, r⟩ c => ⌜r = bitWidth value.toNat ∧ c = t0 + 2 + bitWidth value.toNat⌝,
           fun ⟨v, _⟩ => v.toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  · obtain ⟨h0, hr, hc⟩ := ‹_ ∧ _ ∧ _›
    have hz : _ = (0 : UInt64) := ‹(_ : UInt64) = 0›
    simp [hz] at hr hc
    omega
  · obtain ⟨h0, hr, hc⟩ := ‹_ ∧ _ ∧ _›
    have hv : 0 < (‹UInt64 × Int›).1.toNat := by
      have hne : (‹UInt64 × Int›).1 ≠ 0 := ‹_›
      rcases Nat.eq_zero_or_pos (‹UInt64 × Int›).1.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hne
      · exact h
    have := bitWidth_div_two _ hv
    refine ⟨⟨by omega, by omega, by omega⟩, by omega⟩
  · exact ⟨‹_›, UInt64.toNat_lt _⟩
  · exact ‹_›

end Proofs.Cpp.BitWidthU64
