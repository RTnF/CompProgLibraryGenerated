import Proofs.Cpp.Gen.GcdU64
import Proofs.Cpp.Lib.Basic

/-! # `gcd_u64` (library/number_theory/gcd_u64.hpp)

Euclid's algorithm on 64 bit unsigned integers: the result is `Nat.gcd a b`, in at most
`log2 (a b) + 4` steps (`gcdCost`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.GcdU64

theorem gcd_u64_spec (a b : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.gcd_u64 a b
    ⦃⇓ r c => ⌜r.toNat = Nat.gcd a.toNat b.toNat ∧ c ≤ t0 + 2 + gcdCost a.toNat b.toNat⌝⦄ := by
  mvcgen [cp.gcd_u64]
  case inv =>
    exact ⟨fun ⟨x, y⟩ c => ⌜Nat.gcd x.toNat y.toNat = Nat.gcd a.toNat b.toNat ∧
                             c + gcdCost x.toNat y.toNat ≤ t0 + 1 + gcdCost a.toNat b.toNat⌝,
           fun ⟨x, _⟩ c => ⌜x.toNat = Nat.gcd a.toNat b.toNat ∧ c ≤ t0 + 2 + gcdCost a.toNat b.toNat⌝,
           fun ⟨_, y⟩ => y.toNat⟩
  all_goals simp_all +zetaDelta [fuel]
  · obtain ⟨hg, hc⟩ := ‹_ ∧ _›
    simp [gcdCost] at hc
    omega
  · obtain ⟨hg, hc⟩ := ‹_ ∧ _›
    have hy : (‹UInt64 × UInt64›).2 ≠ 0 := ‹_›
    have hy' : 0 < (‹UInt64 × UInt64›).2.toNat := by
      rcases Nat.eq_zero_or_pos (‹UInt64 × UInt64›).2.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hy
      · exact h
    have := gcdCost_step (‹UInt64 × UInt64›).1.toNat _ hy'
    refine ⟨⟨?_, ?_⟩, Nat.mod_lt _ hy'⟩
    · rw [← hg, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
    · omega
  · exact UInt64.toNat_lt _

end Proofs.Cpp.GcdU64
