import Proofs.Cpp.Prelude

namespace Proofs.Cpp

/-- The number of consecutive low zero bits in an unsigned word, bounded by its width. -/
def countrZero : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, n => if n % 2 = 0 then 1 + countrZero width (n / 2) else 0

theorem countrZero_spec (width n : Nat) :
    countrZero width n ≤ width ∧ 2 ^ countrZero width n ∣ n ∧
      (countrZero width n < width → ¬ 2 ^ (countrZero width n + 1) ∣ n) := by
  induction width generalizing n with
  | zero => simp [countrZero]
  | succ width ih =>
    by_cases he : n % 2 = 0
    · have hn : n = 2 * (n / 2) := by omega
      obtain ⟨hle, hd, hmax⟩ := ih (n / 2)
      simp only [countrZero, ite_eq_left he]
      refine ⟨by omega, ?_, fun hlt hd' => hmax (by omega) ?_⟩
      · rw [Nat.add_comm 1, Nat.pow_succ']
        have hd' := Nat.mul_dvd_mul_left 2 hd
        rwa [← hn] at hd'
      · rw [Nat.add_comm 1, Nat.pow_succ'] at hd'
        apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2)
        simpa only [← hn] using hd'
    · simp [countrZero, he, Nat.dvd_iff_mod_eq_zero, Nat.mod_one]

end Proofs.Cpp
