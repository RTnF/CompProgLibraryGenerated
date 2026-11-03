import Proofs.FloorSumArithmetic

namespace Proofs.FloorSumSignedArithmetic
open Proofs.FloorSumArithmetic

def signedSum (m a b : Int) : Nat → Int
  | 0 => 0
  | n+1 => signedSum m a b n + (a*(n:Int)+b)/m

theorem term_normalization (i : Nat) (m a b : Int) (nonzero : m ≠ 0) :
    (a*(i:Int)+b)/m = (a%m*(i:Int)+b%m)/m + (a/m)*(i:Int)+b/m := by
  have num : a*(i:Int)+b = (a%m*(i:Int)+b%m)+((a/m)*(i:Int)+b/m)*m := by
    calc
      a*(i:Int)+b = (a%m+m*(a/m))*(i:Int)+(b%m+m*(b/m)) := by
        rw [Int.emod_add_mul_ediv,Int.emod_add_mul_ediv]
      _ = _ := by
        simp [Int.add_mul,Int.mul_add,Int.mul_assoc,Int.mul_comm,
          Int.add_assoc,Int.add_comm,Int.add_left_comm]
  rw [num,Int.add_mul_ediv_right _ _ nonzero]
  simp [Int.add_assoc]

theorem signedSum_normalization (n : Nat) (m a b : Int) (nonzero : m ≠ 0) :
    signedSum m a b n = (indexSum n:Int)*(a/m)+(n:Int)*(b/m)+signedSum m (a%m) (b%m) n := by
  induction n with
  | zero => simp [signedSum,indexSum]
  | succ n ih =>
    rw [signedSum,ih,term_normalization n m a b nonzero]
    simp [signedSum,indexSum,Int.mul_add,Int.mul_comm,Int.add_assoc,Int.add_comm,Int.add_left_comm]

theorem signedSum_of_nat (n m a b : Nat) :
    signedSum (m:Int) a b n = (directSum m a b n:Int) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [signedSum,directSum,ih]

theorem signedSum_normalization_natural (n m : Nat) (a b : Int) (positive : 0 < m) :
    signedSum (m:Int) a b n =
      (triangle n:Int)*(a/(m:Int))+(n:Int)*(b/(m:Int))+
      (directSum m (a%(m:Int)).toNat (b%(m:Int)).toNat n:Int) := by
  have nonzero : (m:Int) ≠ 0 := by omega
  have ar : 0 ≤ a%(m:Int) := Int.emod_nonneg _ nonzero
  have br : 0 ≤ b%(m:Int) := Int.emod_nonneg _ nonzero
  have lift := signedSum_of_nat n m (a%(m:Int)).toNat (b%(m:Int)).toNat
  simp only [Int.toNat_of_nonneg ar,Int.toNat_of_nonneg br] at lift
  rw [signedSum_normalization n m a b nonzero,indexSum_eq_triangle,lift]

theorem coefficient_correction (m a : Int) (nonzero : m ≠ 0) :
    (a%m-a)/m = -(a/m) := by
  have num : a%m-a = -(a/m)*m := by
    have decomposition := Int.emod_add_ediv_mul a m
    rw [Int.neg_mul]
    omega
  rw [num,Int.mul_ediv_cancel _ nonzero]

-- Signed decoding is a mathematical specification for the fixed compiler's conversion.
-- The default evaluator conversion remains checked; the optional targetCast
-- policy is related to this specification by CppTargetCast.decode64_spec.
def signedDecode64 (x : Int) : Int :=
  let r := x % (wordLimit:Int)
  if r < 9223372036854775808 then r else r-(wordLimit:Int)

theorem signedDecode64_bounds (x : Int) :
    -9223372036854775808 ≤ signedDecode64 x ∧ signedDecode64 x < 9223372036854775808 := by
  have low := Int.emod_nonneg x (by decide : (wordLimit:Int) ≠ 0)
  have high := Int.emod_lt_of_pos x (by decide : 0 < (wordLimit:Int))
  unfold signedDecode64
  by_cases half : x % (wordLimit:Int) < 9223372036854775808
  · simp only [ite_eq_left half]; omega
  · simp only [ite_eq_right half]
    simp only [wordLimit] at *
    omega

theorem signedDecode64_exact (x : Int)
    (low : -9223372036854775808 ≤ x) (high : x < 9223372036854775808) :
    signedDecode64 x = x := by
  by_cases nonnegative : 0 ≤ x
  · have remainder : x%(wordLimit:Int) = x := Int.emod_eq_of_lt nonnegative (by simp [wordLimit]; omega)
    simp [signedDecode64,remainder,high]
  · have range : 0 ≤ x+(wordLimit:Int) ∧ x+(wordLimit:Int) < (wordLimit:Int) := by
      simp [wordLimit]; omega
    have eqmod : (x+(wordLimit:Int))%(wordLimit:Int) = x%(wordLimit:Int) := by simp
    have remainder := Int.emod_eq_of_lt range.1 range.2
    rw [eqmod] at remainder
    simp only [signedDecode64,remainder]
    have negativeBranch : ¬ x+(wordLimit:Int) < 9223372036854775808 := by simp [wordLimit]; omega
    simp [negativeBranch]

theorem signed_result_outside_range :
    signedSum 1 0 9223372036854775807 2 = 18446744073709551614 ∧
    signedDecode64 (signedSum 1 0 9223372036854775807 2) = -2 := by decide

end Proofs.FloorSumSignedArithmetic
