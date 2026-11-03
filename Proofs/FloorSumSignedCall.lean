import Proofs.Generated.FloorSumSigned
import Proofs.FloorSumSignedReturn

namespace Proofs.FloorSumSignedCall
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.SafeModProofs
open Proofs.FloorSumArithmetic Proofs.FloorSumState Proofs.FloorSumSignedState
open Proofs.FloorSumSignedCorrection Proofs.FloorSumSignedBranch Proofs.FloorSumSignedPrefix
open Proofs.FloorSumSignedReturn Proofs.FloorSumSignedArithmetic

def body : Stmt := FloorSumSignedInstance.floor_sum.body

theorem body_shape : body = .scope (.sequence (rangeAssertion 0 0)
    (.sequence (rangeAssertion 1 1) (.sequence (.sequence ansDeclaration .skip)
      (.sequence (normalizationBranch aCorrectionExpression 2)
        (.sequence (normalizationBranch bCorrectionExpression 3) (.sequence returnSuffix .skip)))))) := rfl

def normalizedAns (n m : Nat) (a b : Int) : Int :=
  correctedAns (correctedAns 0 (triangle n:Int) a m) (n:Int) b m

def normalizedTotal (n m : Nat) (a b : Int) : Int :=
  normalizedAns n m a b + (directSum m (normalizedCoefficient a m).toNat (normalizedCoefficient b m).toNat n:Int)

theorem restore_parameters (n m a b ans : Int) (caller : List Cell) (work base peak : Nat) :
    {mainState n m a b ans caller work base peak with
      memory := (mainState n m a b ans caller work base peak).memory.take (caller.length+4),
      bindings := (mainState n m a b ans caller work base peak).bindings.take 4} =
      Proofs.FloorSumSignedPrefix.parameterState n m a b caller work base peak := by
  have take : caller.take (caller.length+4) = caller := List.take_of_length_le (by omega)
  simp [mainState,Proofs.FloorSumSignedPrefix.parameterState,List.take_append,take]

-- Execute the actual generated body, rather than a replacement algorithm.
theorem body_runs (n m : Nat) (a b : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) :
    ∃ bodyWork finalPeak,
      runFuel 846 body (Proofs.FloorSumSignedPrefix.parameterState n m a b caller work base peak) =
      .finished ⟨Proofs.FloorSumSignedPrefix.parameterState n m (normalizedCoefficient a m) (normalizedCoefficient b m)
        caller (work+50+normalizationWork a m 34+normalizationWork b m 25+bodyWork) base finalPeak,
        some (signedDecode64 (normalizedTotal n m a b)),false⟩ ∧
      bodyWork ≤ 4229 ∧ finalPeak ≤ max peak (caller.length+35-base) ∧
      50+normalizationWork a m 34+normalizationWork b m 25+bodyWork ≤ 4378 ∧
      50+normalizationWork a m 34+normalizationWork b m 25+bodyWork ≤ 154+132*(m.log2+1) := by
  have validN := input_signed_valid n hn
  have validM := input_signed_valid m hm
  have first := assertion_runs n m a b n 0 caller work base peak 0 validN validM ha hb validN
    (by decide) (by decide) (by omega) (by exact_mod_cast hn) rfl
  let checkedPeak : Nat := max peak (caller.length+4-base+10)
  have second := assertion_runs n m a b m 1 caller (work+14) base checkedPeak 1 validN validM ha hb validM
    (by decide) (by decide) (by omega) (by exact_mod_cast hm) rfl
  simp [checkedPeak,Nat.add_assoc,Nat.max_assoc] at second
  have declared := declare_ans n m a b caller (work+28) base checkedPeak validN validM ha hb
  have declaredFuel := congrArg liftChecked declared
  change runFuel 3 ansDeclaration _ = .finished _ at declaredFuel
  have declaration := sequence_done 3 ansDeclaration .skip _ _ _ declaredFuel rfl
  have resource : max (caller.length+4-base+10) (caller.length+5-base+7) = caller.length+4-base+10 := by omega
  simp [checkedPeak,Nat.add_assoc,Nat.max_assoc,resource] at declaration
  obtain ⟨aPeak,firstBranch,aBound⟩ := a_normalization_branch n m a b 0 caller (work+31) base checkedPeak
    allocated hn hm positive ha hb (by decide)
  obtain ⟨bPeak,secondBranch,bBound⟩ := b_normalization_branch n m (normalizedCoefficient a m) b
    (correctedAns 0 (triangle n:Int) a m) caller (work+31+normalizationWork a m 34) base aPeak
    allocated hn hm positive (normalizedCoefficient_valid a m ha hm positive) hb
    (correctedAns_valid _ _ _ _ (by decide))
  have nonnegativeA := normalizedCoefficient_nonnegative a m positive
  have nonnegativeB := normalizedCoefficient_nonnegative b m positive
  have aNatural : ((normalizedCoefficient a m).toNat:Int) = normalizedCoefficient a m := Int.toNat_of_nonneg nonnegativeA
  have bNatural : ((normalizedCoefficient b m).toNat:Int) = normalizedCoefficient b m := Int.toNat_of_nonneg nonnegativeB
  obtain ⟨bodyWork,lastPeak,returned,workBound,lastBound,logBound⟩ := suffix_runs n m
    (normalizedCoefficient a m).toNat (normalizedCoefficient b m).toNat (normalizedAns n m a b) caller
    (work+31+normalizationWork a m 34+normalizationWork b m 25) base bPeak allocated hn hm positive
    (by rw [aNatural]; exact normalizedCoefficient_valid a m ha hm positive)
    (by rw [bNatural]; exact normalizedCoefficient_valid b m hb hm positive)
    (correctedAns_valid _ _ _ _ (correctedAns_valid _ _ _ _ (by decide)))
  rw [aNatural,bNatural] at returned
  have returnSequence := sequence_returns 839 returnSuffix .skip _ _ returned rfl
  have paddedB := runFuel_success_mono 15 825 _ _ _ secondBranch
  have branchB := sequence_done 840 _ _ _ _ _ paddedB returnSequence
  have paddedA := runFuel_success_mono 15 826 _ _ _ firstBranch
  have branchA := sequence_done 841 _ _ _ _ _ paddedA branchB
  have paddedDeclaration := runFuel_success_mono 4 838 _ _ _ declaration
  have afterM := sequence_done 842 _ _ _ _ _ paddedDeclaration branchA
  have paddedM := runFuel_success_mono 4 839 _ _ _ second
  have afterN := sequence_done 843 _ _ _ _ _ paddedM afterM
  have paddedN := runFuel_success_mono 4 840 _ _ _ first
  have assembled := sequence_done 844 _ _ _ _ _ paddedN afterN
  have restored := scope_done 845 _ _ _ assembled
  have memoryLength : (Proofs.FloorSumSignedPrefix.parameterState n m a b caller work base peak).memory.length = caller.length+4 := by
    simp [Proofs.FloorSumSignedPrefix.parameterState]
  have bindingLength : (Proofs.FloorSumSignedPrefix.parameterState n m a b caller work base peak).bindings.length = 4 := rfl
  have overheadBound := normalizationWork_bound a m 34
  have overheadBoundB := normalizationWork_bound b m 25
  refine ⟨bodyWork,lastPeak,?_,workBound,?_,by omega,by omega⟩
  · have total : work+31+normalizationWork a m 34+normalizationWork b m 25+bodyWork+19 =
        work+50+normalizationWork a m 34+normalizationWork b m 25+bodyWork := by omega
    simpa only [body_shape,memoryLength,bindingLength,restore_parameters,normalizedTotal,total] using restored
  · simp only [checkedPeak] at aBound
    omega

end Proofs.FloorSumSignedCall
