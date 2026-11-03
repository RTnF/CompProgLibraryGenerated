import Proofs.FloorSumRound

namespace Proofs.FloorSumCall
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop
open Proofs.FloorSumArithmetic Proofs.FloorSumState Proofs.FloorSumRound

def parameterState (n m a b : Int) (caller : List Cell) : State :=
  ⟨caller ++ [⟨unsigned64,n⟩,⟨unsigned64,m⟩,⟨unsigned64,a⟩,⟨unsigned64,b⟩],
    [⟨caller.length,true⟩,⟨caller.length+1,true⟩,⟨caller.length+2,true⟩,
      ⟨caller.length+3,true⟩],0,caller.length,8⟩

def initAns : Stmt := match FloorSumUnsignedInstance.floor_sum_unsigned.body with
  | .scope (.sequence first _) => first
  | _ => .skip

def returnAns : Stmt := match FloorSumUnsignedInstance.floor_sum_unsigned.body with
  | .scope (.sequence _ (.sequence _ last)) => last
  | _ => .skip

theorem initAns_shape : initAns =
    .sequence (.declare unsigned64 true (.cast unsigned64 (.literal ⟨32,true,false⟩ 0))) .skip := rfl

theorem returnAns_shape : returnAns = .sequence (.ret (.variable unsigned64 4)) .skip := rfl

theorem body_shape : FloorSumUnsignedInstance.floor_sum_unsigned.body =
    .scope (.sequence initAns (.sequence outerLoop returnAns)) := rfl

theorem parameters_bound (n m a b : Int) (caller : List Cell)
    (hn : unsigned64.valid n = true) (hm : unsigned64.valid m = true)
    (ha : unsigned64.valid a = true) (hb : unsigned64.valid b = true) :
    bindArguments {memory := caller,bindings := [],baseMemory := caller.length}
      FloorSumUnsignedInstance.floor_sum_unsigned.parameters [.value n,.value m,.value a,.value b] =
        some (parameterState n m a b caller) := by
  change bindArguments {memory := caller,bindings := [],baseMemory := caller.length}
    [⟨unsigned64,false,true⟩,⟨unsigned64,false,true⟩,⟨unsigned64,false,true⟩,⟨unsigned64,false,true⟩]
    [.value n,.value m,.value a,.value b] = _
  simp [bindArguments,bindArgument,parameterState,State.observe,hn,hm,ha,hb,
    Nat.add_assoc,List.append_assoc]

theorem parameter_environment (n m a b : Int) (caller : List Cell)
    (hn : unsigned64.valid n = true) (hm : unsigned64.valid m = true)
    (ha : unsigned64.valid a = true) (hb : unsigned64.valid b = true) :
    (parameterState n m a b caller).environment = some [n,m,a,b] := by
  have h0 : ¬ caller.length < caller.length := by omega
  have h1 : ¬ caller.length+1 < caller.length := by omega
  have h2 : ¬ caller.length+2 < caller.length := by omega
  have h3 : ¬ caller.length+3 < caller.length := by omega
  simp [parameterState,State.environment,List.getElem?_append,h0,h1,h2,h3,hn,hm,ha,hb]

theorem initAns_runs (fuel : Nat) (n m a b : Int) (caller : List Cell)
    (hn : unsigned64.valid n = true) (hm : unsigned64.valid m = true)
    (ha : unsigned64.valid a = true) (hb : unsigned64.valid b = true) :
    runFuel (fuel+2) initAns (parameterState n m a b caller) =
      .finished ⟨frameState n m a b 0 caller 3 12,none,false⟩ := by
  have env := parameter_environment n m a b caller hn hm ha hb
  have he : (parameterState n m a b caller).evaluate
      (.cast unsigned64 (.literal ⟨32,true,false⟩ 0)) = some ⟨0,2⟩ := by
    simp [State.evaluate,env,Expr.eval,Ty.convert,Ty.valid,unsigned64]
  simp only [initAns_shape,runFuel,Stmt.run,he]
  simp [Ty.convert,unsigned64,Expr.nodes,liftChecked,bind,Outcome.bind,
    parameterState,frameState,State.observe,List.append_assoc]

theorem returnAns_runs (fuel : Nat) (n m a b ans : Int) (caller : List Cell) (work peak : Nat)
    (hn : unsigned64.valid n = true) (hm : unsigned64.valid m = true)
    (ha : unsigned64.valid a = true) (hb : unsigned64.valid b = true)
    (hv : unsigned64.valid ans = true) :
    runFuel (fuel+2) returnAns (frameState n m a b ans caller work peak) =
      .finished ⟨frameState n m a b ans caller (work+2) (max peak 11),some ans,false⟩ := by
  have he : (frameState n m a b ans caller work peak).evaluate (.variable unsigned64 4) =
      some ⟨ans,1⟩ := by
    simp [State.evaluate,frame_environment n m a b ans caller work peak hn hm ha hb hv,
      Expr.eval,hv]
  simp only [returnAns_shape,runFuel,Stmt.run,he]
  simp [liftChecked,bind,Outcome.bind,pure,Expr.nodes,frameState,State.observe,Nat.add_assoc]

theorem body_runs (n m a b : Nat) (caller : List Cell)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) :
    ∃ fn fm fa fb work peak : Nat,
      runFuel 836 FloorSumUnsignedInstance.floor_sum_unsigned.body (parameterState n m a b caller) =
        .finished ⟨{parameterState fn fm fa fb caller with work := work,peak := peak},
          some ((directSum m a b n%wordLimit : Nat):Int),false⟩ ∧
      work ≤ 4229 ∧ peak ≤ 25 ∧ work ≤ 5+132*(m.log2+1) := by
  have nb : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mb : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have vn := unsigned64_valid n nb
  have vm := unsigned64_valid m mb
  have va := unsigned64_valid a ha
  have vb := unsigned64_valid b hb
  have zero : 0 < wordLimit := by decide
  obtain ⟨fn,fm,fa,fb,work,peak,hr,hfn,hpos,hfm,hfa,hfb,hw,hp,hlog⟩ :=
    loop_uniform_correct n m a b 0 caller 3 12 hn hm positive ha hb zero
  simp only [Nat.zero_add] at hr
  have fnb : fn < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have fmb : fm < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have resultBound := Nat.mod_lt (directSum m a b n) zero
  have ret := returnAns_runs 831 fn fm fa fb (directSum m a b n%wordLimit)
    caller work peak (unsigned64_valid fn fnb) (unsigned64_valid fm fmb)
    (unsigned64_valid fa hfa) (unsigned64_valid fb hfb) (unsigned64_valid _ resultBound)
  have padded := runFuel_success_mono 832 1 outerLoop _ _ hr
  have tail := sequence_finished 833 outerLoop returnAns _ _ _ padded ret
  have init := initAns_runs 832 n m a b caller vn vm va vb
  have core := sequence_finished 834 initAns (.sequence outerLoop returnAns) _ _ _ init tail
  refine ⟨fn,fm,fa,fb,work+2,max peak 11,?_,by omega,by omega,by omega⟩
  rw [body_shape]
  have scopeResult := scope_finished 835 _ _ _ core
  simpa [frameState,parameterState,List.take_append,List.take_of_length_le,Nat.add_assoc] using scopeResult

theorem resultType_shape : FloorSumUnsignedInstance.floor_sum_unsigned.resultType = unsigned64 := rfl

theorem callFuel_finished (p : LoopProgram) (fuel : Nat) (caller : List Cell)
    (args : List Argument) (state : State) (step : Step) (value : Int)
    (hargs : (args.all fun a => match a with
      | .value _ => true
      | .reference address => decide (address < caller.length)) = true)
    (hbind : bindArguments {memory := caller,bindings := [],baseMemory := caller.length}
      p.parameters args = some state)
    (hbody : runFuel fuel p.body state = .finished step)
    (hbreak : step.breaking = false) (hreturn : step.returned = some value)
    (hvalid : p.resultType.valid value = true) :
    p.callFuel fuel caller args =
      .finished ⟨value,step.state.memory.take caller.length,step.state.work,step.state.peak⟩ := by
  simp only [List.all_eq_true] at hargs
  simp [LoopProgram.callFuel,hbind,hbody,hbreak,hreturn,hvalid,liftChecked,bind,Outcome.bind,pure]
  intro arg member
  have accepted := hargs arg member
  cases arg with
  | value v => rfl
  | reference address => exact accepted

-- Successful completion proves termination and excludes both faults and fuel exhaustion.
-- The caller need not supply a valid cell environment: no caller-owned cell is read.
theorem floor_sum_unsigned_correct (n m a b : Nat) (caller : List Cell)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) :
    ∃ work peak : Nat,
      FloorSumUnsignedInstance.floor_sum_unsigned.callFuel 836 caller
        [.value n,.value m,.value a,.value b] =
          .finished ⟨(directSum m a b n%wordLimit : Nat),caller,work,peak⟩ ∧
      work ≤ 4229 ∧ peak ≤ 25 ∧ work ≤ 5+132*(m.log2+1) := by
  have nb : n < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have mb : m < wordLimit := by simp [inputLimit,wordLimit] at *; omega
  have binding := parameters_bound n m a b caller (unsigned64_valid n nb)
    (unsigned64_valid m mb) (unsigned64_valid a ha) (unsigned64_valid b hb)
  obtain ⟨fn,fm,fa,fb,work,peak,body,hw,hp,hlog⟩ := body_runs n m a b caller hn hm positive ha hb
  have validResult := unsigned64_valid (directSum m a b n%wordLimit)
    (Nat.mod_lt _ (by decide : 0 < wordLimit))
  refine ⟨work,peak,?_,hw,hp,hlog⟩
  have callResult := callFuel_finished FloorSumUnsignedInstance.floor_sum_unsigned 836 caller
    [.value n,.value m,.value a,.value b] _ _ _ (by rfl) binding body (by rfl) (by rfl)
    (by rw [resultType_shape]; exact validResult)
  have restore : ({parameterState fn fm fa fb caller with work := work,peak := peak}).memory.take
      caller.length = caller := by simp [parameterState]
  rw [restore] at callResult
  exact callResult

theorem floor_sum_unsigned_terminates (n m a b : Nat) (caller : List Cell)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : a < wordLimit) (hb : b < wordLimit) :
    FloorSumUnsignedInstance.floor_sum_unsigned.Terminates caller
      [.value n,.value m,.value a,.value b] := by
  obtain ⟨work,peak,success,_,_,_⟩ := floor_sum_unsigned_correct n m a b caller hn hm positive ha hb
  exact ⟨836,_,success⟩

end Proofs.FloorSumCall
