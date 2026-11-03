import Proofs.CppMovePreparedCall
import Proofs.CppNestedEval

namespace Proofs.CppScalarReturnFrame
open Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.CppLoop Proofs.CppNestedCall
open Proofs.CppScalar Proofs.DynamicResultValid

theorem ret_core (fuel : Nat) (s : NState) (expression : NExpr) (step : NStep)
    (onlyScalar : expression.scalarOnly = true)
    (actual : Proofs.CppNestedProgram.runFuel fuel (.primitive (.ret expression)) s = .finished step) :
    Core s step.state ∧ step.returned.isSome = true ∧ step.breaking = false := by
  cases fuel with
  | zero => simp [Proofs.CppNestedProgram.runFuel] at actual
  | succ fuel =>
    cases evaluated : expression.eval s with
    | none => simp [Proofs.CppNestedProgram.runFuel,NStmt.run,evaluated,liftChecked] at actual
    | some pair =>
      rcases pair with ⟨after,value⟩
      have core := (eval_scalar expression s after value onlyScalar evaluated).1
      have same : (⟨(after.release s).charge 1 0,some (.scalar value),false⟩ : NStep) = step := by
        simpa only [Proofs.CppNestedProgram.runFuel,NStmt.run,evaluated,Bind.bind,Option.bind,liftChecked,Outcome.finished.injEq] using actual
      subst step
      obtain ⟨frame,slots,scope,memory,bindings,base⟩ := core
      refine ⟨⟨?_,slots,scope,memory,bindings,base⟩,rfl,rfl⟩
      change {after.frame with bindings := after.frame.bindings.take s.frame.bindings.length} = s.frame
      rw [frame]
      simp

theorem sequence_core (fuel : Nat) (s : NState) (expression : NExpr) (rest : Command) (step : NStep)
    (onlyScalar : expression.scalarOnly = true)
    (actual : Proofs.CppNestedProgram.runFuel fuel (.sequence (.primitive (.ret expression)) rest) s = .finished step) :
    Core s step.state ∧ step.returned.isSome = true ∧ step.breaking = false := by
  cases fuel with
  | zero => simp [Proofs.CppNestedProgram.runFuel] at actual
  | succ fuel =>
    cases firstRun : Proofs.CppNestedProgram.runFuel fuel (.primitive (.ret expression)) s with
    | fault => simp [Proofs.CppNestedProgram.runFuel,firstRun,bind,Outcome.bind] at actual
    | exhausted => simp [Proofs.CppNestedProgram.runFuel,firstRun,bind,Outcome.bind] at actual
    | finished first =>
      have core := ret_core fuel s expression first onlyScalar firstRun
      have same : first = step := by
        simpa only [Proofs.CppNestedProgram.runFuel,firstRun,bind,Outcome.bind,core.2.1,Bool.true_or,ite_true,pure,Outcome.finished.injEq] using actual
      subst step
      exact core

theorem retire_payload (before after : Proofs.CppNestedVectorBindings.Frame) (scope : Nat)
    (fresh : ∀ owner, before.state.forest.context owner ≠ some scope)
    (actual : before.retireScope scope = some after) :
    after.state.forest = before.state.forest ∧ after.state.storage.objects = before.state.storage.objects := by
  unfold Proofs.CppNestedVectorBindings.Frame.retireScope at actual
  obtain ⟨state,retired,done⟩ := bind_some _ _ _ actual
  unfold Proofs.CppNestedVectorStore.State.retireScope at retired
  split at retired
  · dsimp only at retired
    split at retired
    · have same := Option.some.inj retired
      subst state
      have same := Option.some.inj done
      subst after
      rw [Proofs.CppNestedScope.retired_fresh before.state scope fresh]
      exact ⟨rfl,rfl⟩
    · simp at retired
  · simp at retired

theorem finish_payload (caller callee out : NState) (ty : Ty) (returned : Option Ret) (result : Ret)
    (fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope)
    (actual : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,result)) :
    out.frame.state.forest = callee.frame.state.forest ∧ out.frame.state.storage.objects = callee.frame.state.storage.objects := by
  cases returned with
  | none => simp [Proofs.CppNestedCall.finish] at actual
  | some ret =>
    cases ret with
    | unit => simp [Proofs.CppNestedCall.finish] at actual
    | vector owner element => simp [Proofs.CppNestedCall.finish] at actual
    | scalar value =>
      unfold Proofs.CppNestedCall.finish at actual
      dsimp only at actual
      split at actual
      · split at actual
        · obtain ⟨⟨frame,r⟩,finished,rest⟩ := bind_some _ _ _ actual
          have same := congrArg Prod.fst (Option.some.inj finished)
          change callee.frame = frame at same
          subst frame
          obtain ⟨retired,retirement,done⟩ := bind_some _ _ _ rest
          have same := congrArg Prod.fst (Option.some.inj done)
          change _ = out at same
          subst out
          exact retire_payload callee.frame retired callee.scope fresh retirement
        · simp at actual
      · simp at actual

end Proofs.CppScalarReturnFrame
