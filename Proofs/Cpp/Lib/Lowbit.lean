import Proofs.Cpp.Prelude
import Proofs.FenwickMath

/-! `i & -i` is the lowest set bit `lowb i` (Proofs.FenwickMath) for `i > 0`. -/

namespace Proofs.Cpp

open Proofs.FenwickMath

private theorem bitwise_self_ldiff : ∀ q : Nat, Nat.bitwise (fun x y => x && !y) q q = 0 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rw [Nat.bitwise]
    by_cases h : q = 0
    · simp [h]
    · simp only [h, ite_false]
      have := ih (q / 2) (by omega)
      simp [this]

theorem bitwise_ldiff_pred : ∀ k : Nat, 0 < k → Nat.bitwise (fun x y => x && !y) k (k - 1) = lowb k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [Nat.bitwise]
    by_cases h1 : k = 1
    · subst h1; simp [lowb]
    have hk1 : k - 1 ≠ 0 := by omega
    simp only [show k ≠ 0 by omega, hk1, ite_false]
    by_cases hodd : k % 2 = 1
    · have e : (k - 1) / 2 = k / 2 := by omega
      rw [e, bitwise_self_ldiff, lowb_odd k hodd]
      simp [hodd, show (k - 1) % 2 = 0 by omega]
    · have e : (k - 1) / 2 = k / 2 - 1 := by omega
      rw [e, ih (k / 2) (by omega) (by omega), lowb_even k hk (by omega)]
      simp [show k % 2 = 0 by omega, show (k - 1) % 2 = 1 by omega]
      omega

theorem land_neg_nat (k : Nat) (hk : 0 < k) : land (k : Int) (-(k : Int)) = (lowb k : Int) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have : -((m + 1 : Nat) : Int) = Int.negSucc m := by simp [Int.negSucc_eq]
  rw [this]
  simp only [land]
  have := bitwise_ldiff_pred (m + 1) hk
  simp at this
  simp [this]

/-- `i & -i` for a positive `int`. -/
theorem land_neg (i : Int) (hi : 0 < i) : land i (-i) = (lowb i.toNat : Int) := by
  have := land_neg_nat i.toNat (by omega)
  rwa [Int.toNat_of_nonneg (by omega)] at this

end Proofs.Cpp
