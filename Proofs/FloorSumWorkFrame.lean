import Proofs.CppWorkFrame
import Proofs.FloorSumCall
import Proofs.CppBaseFrame

namespace Proofs.FloorSumWorkFrame
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.CppWorkFrame
open Proofs.FloorSumArithmetic Proofs.FloorSumCall
open Proofs.FloorSumState Proofs.FloorSumRound
open Proofs.CppStorageFrame

theorem initAns_runs_withPeak (fuel : Nat) (n m a b : Int) (caller : List Cell)
    (initialPeak : Nat)
    (hn : unsigned64.valid n = true) (hm : unsigned64.valid m = true)
    (ha : unsigned64.valid a = true) (hb : unsigned64.valid b = true) :
    runFuel (fuel+2) initAns {parameterState n m a b caller with peak := initialPeak} =
      .finished ⟨frameState n m a b 0 caller 3 (max initialPeak 12),none,false⟩ := by
  have env : ({parameterState n m a b caller with peak := initialPeak} : State).environment =
      some [n,m,a,b] := parameter_environment n m a b caller hn hm ha hb
  have he : ({parameterState n m a b caller with peak := initialPeak} : State).evaluate
      (.cast unsigned64 (.literal ⟨32,true,false⟩ 0)) = some ⟨0,2⟩ := by
    simp [State.evaluate,env,Expr.eval,Ty.convert,Ty.valid,unsigned64]
  simp only [initAns_shape,runFuel,Stmt.run,he]
  simp [Ty.convert,unsigned64,Expr.nodes,liftChecked,bind,Outcome.bind,
    parameterState,frameState,State.observe,List.append_assoc]

theorem body_runs_withPeak (n m a b : Nat) (caller : List Cell) (initialPeak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) :
    ∃ fn fm fa fb work peak : Nat,
      runFuel 836 FloorSumUnsignedInstance.floor_sum_unsigned.body
        {parameterState n m a b caller with peak := initialPeak} =
        .finished ⟨{parameterState fn fm fa fb caller with work := work,peak := peak},
          some ((directSum m a b n%wordLimit : Nat):Int),false⟩ ∧
      work ≤ 4229 ∧ peak ≤ max initialPeak 25 ∧ work ≤ 5+132*(m.log2+1) := by
  have nb : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mb : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have vn := unsigned64_valid n nb
  have vm := unsigned64_valid m mb
  have va := unsigned64_valid a ha
  have vb := unsigned64_valid b hb
  have zero : 0 < wordLimit := by decide
  obtain ⟨fn,fm,fa,fb,work,peak,hr,hfn,hpos,hfm,hfa,hfb,hw,hp,hlog⟩ :=
    loop_uniform_correct n m a b 0 caller 3 (max initialPeak 12) hn hm positive ha hb zero
  simp only [Nat.zero_add] at hr
  have fnb : fn < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have fmb : fm < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have resultBound := Nat.mod_lt (directSum m a b n) zero
  have ret := returnAns_runs 831 fn fm fa fb (directSum m a b n%wordLimit)
    caller work peak (unsigned64_valid fn fnb) (unsigned64_valid fm fmb)
    (unsigned64_valid fa hfa) (unsigned64_valid fb hfb) (unsigned64_valid _ resultBound)
  have padded := runFuel_success_mono 832 1 outerLoop _ _ hr
  have tail := sequence_finished 833 outerLoop returnAns _ _ _ padded ret
  have init := initAns_runs_withPeak 832 n m a b caller initialPeak vn vm va vb
  have core := sequence_finished 834 initAns (.sequence outerLoop returnAns) _ _ _ init tail
  refine ⟨fn,fm,fa,fb,work+2,max peak 11,?_,by omega,by omega,by omega⟩
  rw [body_shape]
  have scopeResult := scope_finished 835 _ _ _ core
  simpa [frameState,parameterState,List.take_append,List.take_of_length_le,Nat.add_assoc] using scopeResult

-- Reuse the whole generated C++ body proof with arbitrary accumulated caller work.
theorem body_runs_withWork (n m a b : Nat) (caller : List Cell) (extra : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) :
    ∃ fn fm fa fb work peak : Nat,
      runFuel 836 FloorSumUnsignedInstance.floor_sum_unsigned.body
        (addWork (parameterState n m a b caller) extra) =
        .finished ⟨{parameterState fn fm fa fb caller with work := work+extra,peak := peak},
          some ((directSum m a b n%wordLimit : Nat):Int),false⟩ ∧
      work ≤ 4229 ∧ peak ≤ 25 ∧ work ≤ 5+132*(m.log2+1) := by
  obtain ⟨fn,fm,fa,fb,work,peak,body,hw,hp,hlog⟩ :=
    body_runs n m a b caller hn hm positive ha hb
  refine ⟨fn,fm,fa,fb,work,peak,?_,hw,hp,hlog⟩
  rw [runFuel_addWork,body]
  rfl

theorem body_runs_withWorkAndPeak (n m a b : Nat) (caller : List Cell)
    (extra initialPeak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) :
    ∃ fn fm fa fb work peak : Nat,
      runFuel 836 FloorSumUnsignedInstance.floor_sum_unsigned.body
        {parameterState n m a b caller with work := extra,peak := initialPeak} =
        .finished ⟨{parameterState fn fm fa fb caller with work := work+extra,peak := peak},
          some ((directSum m a b n%wordLimit : Nat):Int),false⟩ ∧
      work ≤ 4229 ∧ peak ≤ max initialPeak 25 ∧ work ≤ 5+132*(m.log2+1) := by
  obtain ⟨fn,fm,fa,fb,work,peak,body,hw,hp,hlog⟩ :=
    body_runs_withPeak n m a b caller initialPeak hn hm positive ha hb
  refine ⟨fn,fm,fa,fb,work,peak,?_,hw,hp,hlog⟩
  have start : addWork {parameterState n m a b caller with peak := initialPeak} extra =
      {parameterState n m a b caller with work := extra,peak := initialPeak} := by
    simp [addWork,parameterState]
  rw [← start,runFuel_addWork,body]
  rfl

theorem body_runs_withCallerBase (n m a b : Nat) (caller : List Cell)
    (extra initialPeak callerBase : Nat)
    (baseBound : callerBase ≤ caller.length)
    (peakBound : caller.length-callerBase ≤ initialPeak)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) :
    ∃ fn fm fa fb work peak : Nat,
      runFuel 836 FloorSumUnsignedInstance.floor_sum_unsigned.body
        {parameterState n m a b caller with work := extra,baseMemory := callerBase,peak := initialPeak} =
        .finished ⟨{parameterState fn fm fa fb caller with
          work := work+extra,baseMemory := callerBase,peak := peak},
          some ((directSum m a b n%wordLimit : Nat):Int),false⟩ ∧
      work ≤ 4229 ∧ peak ≤ max initialPeak (25+caller.length-callerBase) ∧
      work ≤ 5+132*(m.log2+1) := by
  let offset := caller.length-callerBase
  obtain ⟨fn,fm,fa,fb,work,peak,body,hw,hp,hlog⟩ :=
    body_runs_withWorkAndPeak n m a b caller extra (initialPeak-offset) hn hm positive ha hb
  have within : offset ≤ caller.length := by simp [offset]
  have oldAllocated : caller.length ≤ (parameterState n m a b caller).memory.length := by
    simp [parameterState]
  have start : lowerBase
      {parameterState n m a b caller with work := extra,peak := initialPeak-offset} offset =
      {parameterState n m a b caller with work := extra,baseMemory := callerBase,peak := initialPeak} := by
    simp [lowerBase,parameterState,offset]
    constructor <;> omega
  have shifted := Proofs.CppBaseFrame.runFuel_lowerBase 836
    FloorSumUnsignedInstance.floor_sum_unsigned.body
    {parameterState n m a b caller with work := extra,peak := initialPeak-offset}
    offset within oldAllocated
  rw [body,start] at shifted
  refine ⟨fn,fm,fa,fb,work,peak+offset,?_,hw,?_,hlog⟩
  · simpa [Proofs.CppBaseFrame.lowerOutcomeBase,Proofs.CppBaseFrame.lowerStepBase,
      lowerBase,parameterState,offset,Nat.sub_sub_self baseBound] using shifted
  · simp [offset] at hp ⊢
    omega

end Proofs.FloorSumWorkFrame
