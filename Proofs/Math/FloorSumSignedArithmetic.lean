import Proofs.Math.FloorSumArithmetic

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

end Proofs.FloorSumSignedArithmetic
