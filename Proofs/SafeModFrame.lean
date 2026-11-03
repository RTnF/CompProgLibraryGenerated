import Proofs.SafeModProofs
import Proofs.CppBaseFrame

namespace Proofs.SafeModFrame
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.CppStorageFrame
open Proofs.SafeModProofs

def parameterState (x m : Int) (caller : List Cell) (work peak : Nat) : State :=
  ⟨caller ++ [⟨signed64,x⟩,⟨signed64,m⟩],
    [⟨caller.length,true⟩,⟨caller.length+1,true⟩],work,caller.length,peak⟩

def bodyWork (x m : Int) : Nat := if x.tmod m < 0 then 15 else 11

theorem body_runs (x m : Int) (caller : List Cell) (work peak : Nat)
    (hx : signed64.valid x = true) (hm : signed64.valid m = true) (positive : 0 < m) :
    runFuel 9 SafeModInstance.safe_mod.body (parameterState x m caller work peak) =
      .finished ⟨parameterState (x%m) m caller (work+bodyWork x m) (max peak 8),some (x%m),false⟩ := by
  have htake : caller.take (caller.length+2) = caller := List.take_of_length_le (by omega)
  have hn : ¬ caller.length+1 < caller.length := by omega
  have hn2 : caller.length+1+1-caller.length = 2 := by omega
  have bx : -9223372036854775808 ≤ x ∧ x < 9223372036854775808 := of_decide_eq_true hx
  have bm : -9223372036854775808 ≤ m ∧ m < 9223372036854775808 := of_decide_eq_true hm
  have nonzero : m ≠ 0 := by omega
  have hq := quotient_valid x m hx hm positive
  have hr := remainder_valid x m hm positive
  have br : -9223372036854775808 ≤ x.tmod m ∧ x.tmod m < 9223372036854775808 := of_decide_eq_true hr
  have hchecked := checkedDivRem_remainder_exact signed64 x m nonzero hq hr
  simp only [signed64] at hchecked
  have norm := normalized_remainder x m positive
  by_cases negative : x.tmod m < 0
  · have rlow := Int.lt_tmod_of_pos x positive
    have badd : -9223372036854775808 ≤ x.tmod m+m ∧ x.tmod m+m < 9223372036854775808 := by omega
    have heq : x%m = x.tmod m+m := by simpa [negative] using norm.symm
    simp [SafeModInstance.safe_mod,signed64,parameterState,bodyWork,runFuel,liftChecked,bind,pure,Outcome.bind,
      Stmt.run,State.evaluate,State.environment,State.observe,Expr.eval,Expr.nodes,binaryValue,
      hchecked,Ty.convert,Ty.valid,List.getElem?_append,hn,hn2,List.take_append,htake,
      bx.1,bx.2,bm.1,bm.2,br.1,br.2,badd.1,badd.2,negative,heq,Nat.add_assoc]
  · have heq : x%m = x.tmod m := by simpa [negative] using norm.symm
    simp [SafeModInstance.safe_mod,signed64,parameterState,bodyWork,runFuel,liftChecked,bind,pure,Outcome.bind,
      Stmt.run,State.evaluate,State.environment,State.observe,Expr.eval,Expr.nodes,binaryValue,
      hchecked,Ty.convert,Ty.valid,List.getElem?_append,hn,hn2,List.take_append,htake,
      bx.1,bx.2,bm.1,bm.2,br.1,br.2,negative,heq,Nat.add_assoc]

theorem body_runs_withCallerBase (x m : Int) (caller : List Cell)
    (work initialPeak callerBase : Nat)
    (baseBound : callerBase ≤ caller.length)
    (peakBound : caller.length-callerBase ≤ initialPeak)
    (hx : signed64.valid x = true) (hm : signed64.valid m = true) (positive : 0 < m) :
    runFuel 9 SafeModInstance.safe_mod.body
      {parameterState x m caller work initialPeak with baseMemory := callerBase} =
      .finished ⟨{parameterState (x%m) m caller (work+bodyWork x m)
        (max initialPeak (8+caller.length-callerBase)) with baseMemory := callerBase},some (x%m),false⟩ := by
  let offset := caller.length-callerBase
  have within : offset ≤ caller.length := by simp [offset]
  have allocated : caller.length ≤ (parameterState x m caller work (initialPeak-offset)).memory.length := by
    simp [parameterState]
  have start : lowerBase (parameterState x m caller work (initialPeak-offset)) offset =
      {parameterState x m caller work initialPeak with baseMemory := callerBase} := by
    simp [lowerBase,parameterState,offset]
    constructor <;> omega
  have shifted := Proofs.CppBaseFrame.runFuel_lowerBase 9 SafeModInstance.safe_mod.body
    (parameterState x m caller work (initialPeak-offset)) offset within allocated
  rw [start,body_runs x m caller work (initialPeak-offset) hx hm positive] at shifted
  have final : lowerBase (parameterState (x%m) m caller (work+bodyWork x m)
      (max (initialPeak-offset) 8)) offset =
      {parameterState (x%m) m caller (work+bodyWork x m)
        (max initialPeak (8+caller.length-callerBase)) with baseMemory := callerBase} := by
    simp [lowerBase,parameterState,offset]
    constructor <;> omega
  simpa only [Proofs.CppBaseFrame.lowerOutcomeBase,Proofs.CppBaseFrame.lowerStepBase,final] using shifted

theorem bodyWork_bound (x m : Int) : bodyWork x m ≤ 15 := by
  simp only [bodyWork]
  split <;> decide

end Proofs.SafeModFrame
