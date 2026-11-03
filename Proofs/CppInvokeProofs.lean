import Proofs.CppLoop

namespace Proofs.CppInvokeProofs
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop

theorem finish_result (caller : State) (ty : Ty) (callee : State) (value : Int)
    (valid : ty.valid value = true) :
    finishInvoke caller ty ⟨callee,some value,false⟩ = some
      ⟨({caller with memory := caller.memory ++ [⟨ty,value⟩], bindings := caller.bindings ++ [⟨caller.memory.length,false⟩], work := callee.work+1,peak := max caller.peak callee.peak} : State).observe 0,none,false⟩ := by
  simp [finishInvoke,valid]

theorem finish_missing_return (caller callee : State) (ty : Ty) :
    finishInvoke caller ty ⟨callee,none,false⟩ = none := by simp [finishInvoke]

theorem finish_break (caller callee : State) (ty : Ty) (value : Option Int) :
    finishInvoke caller ty ⟨callee,value,true⟩ = none := by simp [finishInvoke]

theorem finish_invalid (caller callee : State) (ty : Ty) (value : Int)
    (invalid : ty.valid value = false) :
    finishInvoke caller ty ⟨callee,some value,false⟩ = none := by simp [finishInvoke,invalid]

theorem result_caller_memory (caller : State) (ty : Ty) (step result : Step)
    (success : finishInvoke caller ty step = some result) :
    result.state.memory.take caller.memory.length = caller.memory ∧
    result.state.bindings.take caller.bindings.length = caller.bindings ∧
    result.returned = none ∧ result.breaking = false := by
  cases step with
  | mk callee value breaking =>
    cases breaking with
    | true => simp [finishInvoke] at success
    | false =>
      cases value with
      | none => simp [finishInvoke] at success
      | some value =>
        cases valid : ty.valid value with
        | false => simp [finishInvoke,valid] at success
        | true =>
          rw [finish_result caller ty callee value valid] at success
          cases success
          simp [State.observe]

theorem result_resources (caller : State) (ty : Ty) (step result : Step)
    (success : finishInvoke caller ty step = some result) :
    result.state.work = step.state.work+1 ∧
    result.state.peak = max (max caller.peak step.state.peak)
      (caller.memory.length+1-caller.baseMemory+caller.bindings.length+1) ∧
    result.state.baseMemory = caller.baseMemory := by
  cases step with
  | mk callee value breaking =>
    cases breaking with
    | true => simp [finishInvoke] at success
    | false =>
      cases value with
      | none => simp [finishInvoke] at success
      | some value =>
        cases valid : ty.valid value with
        | false => simp [finishInvoke,valid] at success
        | true =>
          rw [finish_result caller ty callee value valid] at success
          cases success
          simp [State.observe,Nat.add_assoc]

theorem invoke_run (caller callee : State) (parameters : List (Ty × Bool))
    (ty : Ty) (arguments : List Expr) (body : Stmt) (step : Step)
    (prepared : prepareInvoke caller parameters arguments = some callee)
    (completed : body.run callee = some step) :
    (Stmt.invoke parameters ty arguments body).run caller = finishInvoke caller ty step := by
  simp [Stmt.run,prepared,completed]

theorem invoke_fuel (fuel : Nat) (caller callee : State) (parameters : List (Ty × Bool))
    (ty : Ty) (arguments : List Expr) (body : Stmt) (step : Step)
    (prepared : prepareInvoke caller parameters arguments = some callee)
    (completed : runFuel fuel body callee = .finished step) :
    runFuel (fuel+1) (.invoke parameters ty arguments body) caller =
      liftChecked (finishInvoke caller ty step) := by
  simp [runFuel,prepared,completed,liftChecked,bind,Outcome.bind]

end Proofs.CppInvokeProofs
