import Proofs.CppScalar
import Proofs.FloorSumSignedArithmetic

namespace Proofs.CppTargetCast
open Proofs.CppScalar

theorem decode_bounds (width : Nat) (x : Int) (positive : 0 < width) :
    -(2 ^ (width-1) : Int) ≤ signedDecode width x ∧
    signedDecode width x < 2 ^ (width-1) := by
  cases width with
  | zero => omega
  | succ k =>
    have half : 0 < (2 ^ k : Int) := Int.pow_pos (by decide)
    have full : 0 < (2 ^ (k+1) : Int) := Int.pow_pos (by decide)
    have low := Int.emod_nonneg x (by omega : (2 ^ (k+1) : Int) ≠ 0)
    have high := Int.emod_lt_of_pos x full
    unfold signedDecode
    simp only [Nat.succ_sub_one]
    by_cases h : x % (2 ^ (k+1)) < 2 ^ k
    · simp only [ite_eq_left h]
      omega
    · simp only [ite_eq_right h]
      rw [Int.pow_succ] at low high h ⊢
      omega

theorem decode_exact (width : Nat) (x : Int) (positive : 0 < width)
    (low : -(2 ^ (width-1) : Int) ≤ x) (high : x < 2 ^ (width-1)) :
    signedDecode width x = x := by
  cases width with
  | zero => omega
  | succ k =>
    simp only [Nat.succ_sub_one] at low high
    have half : 0 < (2 ^ k : Int) := Int.pow_pos (by decide)
    have full : (2 ^ (k+1) : Int) = 2 ^ k * 2 := by simpa using Int.pow_succ (2:Int) k
    by_cases nonnegative : 0 ≤ x
    · have remainder : x % (2 ^ (k+1)) = x := Int.emod_eq_of_lt nonnegative (by rw [full]; omega)
      simp [signedDecode,remainder,high]
    · have range : 0 ≤ x+2 ^ (k+1) ∧ x+2 ^ (k+1) < (2 ^ (k+1) : Int) := by rw [full]; omega
      have eqmod : (x+2 ^ (k+1)) % (2 ^ (k+1)) = x % (2 ^ (k+1)) := by simp
      have remainder := Int.emod_eq_of_lt range.1 range.2
      rw [eqmod] at remainder
      have branch : ¬ x+2 ^ (k+1) < (2 ^ k : Int) := by rw [full]; omega
      simp [signedDecode,remainder,branch]

theorem targetConvert_i32_valid (x : Int) :
    (⟨32,true,false⟩ : Ty).targetConvert x = some (signedDecode 32 x) ∧
    (⟨32,true,false⟩ : Ty).valid (signedDecode 32 x) = true := by
  have bounds := decode_bounds 32 x (by decide)
  simpa [Ty.targetConvert,Ty.valid] using bounds

theorem targetConvert_i64_valid (x : Int) :
    (⟨64,true,false⟩ : Ty).targetConvert x = some (signedDecode 64 x) ∧
    (⟨64,true,false⟩ : Ty).valid (signedDecode 64 x) = true := by
  have bounds := decode_bounds 64 x (by decide)
  simpa [Ty.targetConvert,Ty.valid] using bounds

theorem decode64_spec (x : Int) :
    signedDecode 64 x = Proofs.FloorSumSignedArithmetic.signedDecode64 x := by
  rfl

end Proofs.CppTargetCast
