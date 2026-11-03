import Proofs.FloorSumSignedCall

namespace Proofs.FloorSumSignedSpecification
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.SafeModProofs
open Proofs.FloorSumArithmetic Proofs.FloorSumSignedArithmetic Proofs.FloorSumSignedBranch Proofs.FloorSumSignedCall

theorem remainder_quotient_zero (x m : Int) (positive : 0 < m) : (x%m)/m = 0 :=
  Int.ediv_eq_zero_of_lt (Int.emod_nonneg x (by omega)) (Int.emod_lt_of_pos x positive)

theorem sum_normalize_a (n : Nat) (m a b : Int) (positive : 0 < m) :
    signedSum m a b n = (triangle n:Int)*(a/m)+signedSum m (a%m) b n := by
  have original := signedSum_normalization n m a b (by omega)
  have normalized := signedSum_normalization n m (a%m) b (by omega)
  simp only [remainder_quotient_zero a m positive,Int.emod_emod,indexSum_eq_triangle,Int.mul_zero,Int.zero_add] at normalized
  rw [indexSum_eq_triangle] at original
  omega

theorem sum_normalize_b (n : Nat) (m a b : Int) (positive : 0 < m) :
    signedSum m a b n = (n:Int)*(b/m)+signedSum m a (b%m) n := by
  have original := signedSum_normalization n m a b (by omega)
  have normalized := signedSum_normalization n m a (b%m) (by omega)
  simp only [remainder_quotient_zero b m positive,Int.emod_emod,indexSum_eq_triangle,Int.mul_zero,Int.add_zero] at normalized
  rw [indexSum_eq_triangle] at original
  omega

def contribution (factor x : Int) (m : Nat) : Int := if x < 0 then factor*(x/(m:Int)) else 0

theorem correctedAns_mod (ans factor x : Int) (m : Nat) :
    (correctedAns ans factor x m)%(wordLimit:Int) = (ans+contribution factor x m)%(wordLimit:Int) := by
  by_cases negative : x < 0 <;>
    simp [correctedAns,contribution,negative,Int.mul_neg,Int.sub_neg]

theorem conditional_normalize_a (n m : Nat) (a b : Int) (positive : 0 < m) :
    signedSum (m:Int) a b n = contribution (triangle n:Int) a m+
      signedSum (m:Int) (normalizedCoefficient a m) b n := by
  by_cases negative : a < 0
  · simpa [contribution,normalizedCoefficient,negative] using sum_normalize_a n m a b (by omega)
  · simp [contribution,normalizedCoefficient,negative]

theorem conditional_normalize_b (n m : Nat) (a b : Int) (positive : 0 < m) :
    signedSum (m:Int) a b n = contribution (n:Int) b m+
      signedSum (m:Int) a (normalizedCoefficient b m) n := by
  by_cases negative : b < 0
  · simpa [contribution,normalizedCoefficient,negative] using sum_normalize_b n m a b (by omega)
  · simp [contribution,normalizedCoefficient,negative]

theorem conditional_sum (n m : Nat) (a b : Int) (positive : 0 < m) :
    signedSum (m:Int) a b n = contribution (triangle n:Int) a m+contribution (n:Int) b m+
      (directSum m (normalizedCoefficient a m).toNat (normalizedCoefficient b m).toNat n:Int) := by
  have natural := signedSum_of_nat n m (normalizedCoefficient a m).toNat (normalizedCoefficient b m).toNat
  rw [Int.toNat_of_nonneg (normalizedCoefficient_nonnegative a m positive),
      Int.toNat_of_nonneg (normalizedCoefficient_nonnegative b m positive)] at natural
  rw [conditional_normalize_a n m a b positive,
      conditional_normalize_b n m (normalizedCoefficient a m) b positive,natural]
  exact Int.add_assoc _ _ _ |>.symm

theorem normalizedTotal_mod (n m : Nat) (a b : Int) (positive : 0 < m) :
    normalizedTotal n m a b%(wordLimit:Int) = signedSum (m:Int) a b n%(wordLimit:Int) := by
  rw [conditional_sum n m a b positive]
  simp only [normalizedTotal,Proofs.FloorSumSignedCall.normalizedAns,Int.add_emod,correctedAns_mod,Int.emod_emod,Int.zero_add]

theorem normalizedTotal_decode (n m : Nat) (a b : Int) (positive : 0 < m) :
    signedDecode64 (normalizedTotal n m a b) = signedDecode64 (signedSum (m:Int) a b n) := by
  simp only [signedDecode64,normalizedTotal_mod n m a b positive]

-- The complete generated body's result is the stated signed mathematical sum,
-- decoded according to the explicitly selected compiler conversion contract.
theorem body_correct (n m : Nat) (a b : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) :
    ∃ bodyWork finalPeak,
      runFuel 846 body (Proofs.FloorSumSignedPrefix.parameterState n m a b caller work base peak) =
      .finished ⟨Proofs.FloorSumSignedPrefix.parameterState n m (normalizedCoefficient a m) (normalizedCoefficient b m)
        caller (work+50+normalizationWork a m 34+normalizationWork b m 25+bodyWork) base finalPeak,
        some (signedDecode64 (signedSum (m:Int) a b n)),false⟩ ∧
      bodyWork ≤ 4229 ∧ finalPeak ≤ max peak (caller.length+35-base) ∧
      50+normalizationWork a m 34+normalizationWork b m 25+bodyWork ≤ 4378 ∧
      50+normalizationWork a m 34+normalizationWork b m 25+bodyWork ≤ 154+132*(m.log2+1) := by
  simpa only [normalizedTotal_decode n m a b positive] using
    body_runs n m a b caller work base peak allocated hn hm positive ha hb


theorem parameters_shape : FloorSumSignedInstance.floor_sum.parameters =
    [⟨signed64,false,true⟩,⟨signed64,false,true⟩,⟨signed64,false,true⟩,⟨signed64,false,true⟩] := rfl

theorem resultType_shape : FloorSumSignedInstance.floor_sum.resultType = signed64 := rfl

theorem bind_parameters (n m a b : Int) (caller : List Cell)
    (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) :
    bindArguments {memory := caller,bindings := [],baseMemory := caller.length}
      FloorSumSignedInstance.floor_sum.parameters [.value n,.value m,.value a,.value b] =
      some (Proofs.FloorSumSignedPrefix.parameterState n m a b caller 0 caller.length 8) := by
  simp [parameters_shape,bindArguments,bindArgument,State.observe,hn,hm,ha,hb,
    Proofs.FloorSumSignedPrefix.parameterState,List.append_assoc,Nat.add_assoc]

theorem decoded_valid (value : Int) : signed64.valid (signedDecode64 value) = true := by
  have valid := (Proofs.CppTargetCast.targetConvert_i64_valid value).2
  simpa only [Proofs.CppTargetCast.decode64_spec,Proofs.SafeModProofs.signed64] using valid

theorem call_of_body (n m a b : Int) (caller : List Cell) (step : Step) (value : Int)
    (prepared : bindArguments {memory := caller,bindings := [],baseMemory := caller.length}
      FloorSumSignedInstance.floor_sum.parameters [.value n,.value m,.value a,.value b] =
      some (Proofs.FloorSumSignedPrefix.parameterState n m a b caller 0 caller.length 8))
    (completed : runFuel 846 FloorSumSignedInstance.floor_sum.body
      (Proofs.FloorSumSignedPrefix.parameterState n m a b caller 0 caller.length 8) = .finished step)
    (breaking : step.breaking = false) (returned : step.returned = some value)
    (valid : signed64.valid value = true) (memory : step.state.memory.take caller.length = caller) :
    FloorSumSignedInstance.floor_sum.callFuel 846 caller [.value n,.value m,.value a,.value b] =
      .finished ⟨value,caller,step.state.work,step.state.peak⟩ := by
  simp [LoopProgram.callFuel,prepared,liftChecked,bind,Outcome.bind,completed,breaking,returned,
    resultType_shape,valid,memory,pure]

theorem call_correct (n m : Nat) (a b : Int) (caller : List Cell)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) :
    ∃ work peak,
      FloorSumSignedInstance.floor_sum.callFuel 846 caller [.value n,.value m,.value a,.value b] =
        .finished ⟨signedDecode64 (signedSum (m:Int) a b n),caller,work,peak⟩ ∧
      work ≤ 4378 ∧ peak ≤ 35 ∧ work ≤ 154+132*(m.log2+1) := by
  have boundN := Proofs.FloorSumSignedCorrection.input_signed_valid n hn
  have boundM := Proofs.FloorSumSignedCorrection.input_signed_valid m hm
  have prepared := bind_parameters n m a b caller boundN boundM ha hb
  obtain ⟨bodyWork,finalPeak,completed,_,peakBound,workBound,logBound⟩ :=
    body_correct n m a b caller 0 caller.length 8 (Nat.le_refl _) hn hm positive ha hb
  change runFuel 846 FloorSumSignedInstance.floor_sum.body _ = _ at completed
  refine ⟨50+normalizationWork a m 34+normalizationWork b m 25+bodyWork,finalPeak,?_,by simpa using workBound,?_,by simpa using logBound⟩
  · have called := call_of_body n m a b caller _ _ prepared completed rfl rfl (decoded_valid _)
      (by simp [Proofs.FloorSumSignedPrefix.parameterState])
    simpa only [Proofs.FloorSumSignedPrefix.parameterState,Nat.zero_add] using called
  · simpa using peakBound

theorem call_exact_if_representable (n m : Nat) (a b : Int) (caller : List Cell)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true)
    (low : -9223372036854775808 ≤ signedSum (m:Int) a b n)
    (high : signedSum (m:Int) a b n < 9223372036854775808) :
    ∃ work peak,
      FloorSumSignedInstance.floor_sum.callFuel 846 caller [.value n,.value m,.value a,.value b] =
        .finished ⟨signedSum (m:Int) a b n,caller,work,peak⟩ ∧
      work ≤ 4378 ∧ peak ≤ 35 ∧ work ≤ 154+132*(m.log2+1) := by
  simpa only [signedDecode64_exact _ low high] using call_correct n m a b caller hn hm positive ha hb


theorem signedSum_modulus_one (n : Nat) (a b : Int) :
    signedSum 1 a b n = (triangle n:Int)*a+(n:Int)*b := by
  have normalized := signedSum_normalization_natural n 1 a b (by decide)
  have zero := Proofs.FloorSumArithmetic.directSum_stop n 1 0 0 (by simp)
  simpa [zero] using normalized

end Proofs.FloorSumSignedSpecification
