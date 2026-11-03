import Proofs.CppMoveRestore
import Proofs.CppCallFrame

namespace Proofs.CppMoveCallRestore
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMoveContext
open Proofs.CppMoveHeaders Proofs.CppMoveRestore Proofs.CppLoop

theorem retire_valid (before after : Proofs.CppNestedVectorBindings.Frame) (scope : Nat)
    (actual : before.retireScope scope = some after) : after.state.wellFormed = true := by
  unfold Proofs.CppNestedVectorBindings.Frame.retireScope at actual
  obtain ⟨state,retired,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  have eq := Option.some.inj done
  subst after
  unfold Proofs.CppNestedVectorStore.State.retireScope at retired
  split at retired
  · dsimp only at retired
    split at retired
    · cases Option.some.inj retired
      assumption
    · simp at retired
  · simp at retired

theorem finish_valid (caller callee out : NState) (ty : Ty) (returned : Option Ret) (result : Ret)
    (actual : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,result)) :
    out.frame.state.wellFormed = true := by
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
        · obtain ⟨finished,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
          obtain ⟨retired,ran,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
          have eq := congrArg Prod.fst (Option.some.inj done)
          change _ = out at eq
          subst out
          exact retire_valid finished.1 retired callee.scope ran
        · simp at actual
      · simp at actual

theorem call_valid (program : NProgram) (fuel : Nat) (caller after : NState)
    (arguments : List NArgument) (result : Ret) (ty : Ty) (scalar : program.result = .scalar ty)
    (actual : program.callFuel fuel caller arguments = .finished (after,result)) :
    after.frame.state.wellFormed = true := by
  cases prep : prepare caller program.parameters arguments with
  | none => simp [NProgram.callFuel,prep,liftChecked,bind,Outcome.bind] at actual
  | some init =>
    cases ran : runFuel fuel program.body init with
    | fault => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | exhausted => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | finished step =>
      simp only [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
      split at actual
      · simp at actual
      · cases ended : Proofs.CppNestedCall.finish caller step.state program.result step.returned with
        | none => simp [ended] at actual
        | some pair =>
          simp only [ended] at actual
          have eq := Outcome.finished.inj actual
          subst pair
          rw [scalar] at ended
          exact finish_valid caller step.state after ty step.returned result ended

-- This theorem restores a completed existing call, including its scalar return.
-- It does not assert termination of an arbitrary body or a physical stack bound
-- for NestedCall.prepare, whose binding count includes projection metadata.
theorem call_restore_ready (program : NProgram) (fuel : Nat) (caller : Context)
    (ty retType : Ty) (arguments : List NArgument) (after : NState) (result : Ret)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, (project caller ty).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (actual : program.callFuel fuel (project caller ty) arguments = .finished (after,result)) :
    ∃ out, restoreContext caller ty after = some out ∧ project out ty = after := by
  have effects := Proofs.CppCallFrame.call_headers program fuel (project caller ty) after arguments result retType
    scalar allowed contexts actual
  obtain ⟨out,restored⟩ := restoreContext_ready caller ty after effects.slots effects.scopedState
    effects.vectorBindings effects.scalarBindings effects.memoryLength effects.base
    effects.headers effects.flags covered (call_valid program fuel (project caller ty) after arguments result retType scalar actual)
  exact ⟨out,restored,restoreContext_project caller out ty after restored covered⟩

theorem call_restore_terminates (program : NProgram) (caller : Context) (ty retType : Ty)
    (arguments : List NArgument) (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, (project caller ty).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (terminates : program.Terminates (project caller ty) arguments) :
    ∃ fuel out result, program.callFuel fuel (project caller ty) arguments = .finished (project out ty,result) ∧
      restoreContext caller ty (project out ty) = some out := by
  obtain ⟨fuel,⟨after,result⟩,actual⟩ := terminates
  obtain ⟨out,restored,equal⟩ := call_restore_ready program fuel caller ty retType arguments after result
    scalar allowed contexts covered actual
  exact ⟨fuel,out,result,by rw [equal]; exact actual,by rw [equal]; exact restored⟩

-- Preserve fault/exhausted outcomes and the actual return value. These counters
-- are those of the existing low-level interpreter, not a new physical bound.
def eligible (program : NProgram) : Bool := match program.result with
  | .scalar _ => Proofs.CppNoResizeScope.Allowed program.body
  | _ => false

def restoreCallFuel (program : NProgram) (fuel : Nat) (caller : Context) (ty : Ty)
    (arguments : List NArgument) : Outcome (Context × Ret) :=
  if eligible program then do
    let (after,result) ← program.callFuel fuel (project caller ty) arguments
    let out ← liftChecked (restoreContext caller ty after)
    pure (out,result)
  else .fault

theorem restoreCallFuel_ready (program : NProgram) (fuel : Nat) (caller : Context)
    (ty retType : Ty) (arguments : List NArgument) (after : NState) (result : Ret)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, (project caller ty).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (actual : program.callFuel fuel (project caller ty) arguments = .finished (after,result)) :
    ∃ out, restoreCallFuel program fuel caller ty arguments = .finished (out,result) ∧ project out ty = after := by
  obtain ⟨out,restored,equal⟩ := call_restore_ready program fuel caller ty retType arguments after result
    scalar allowed contexts covered actual
  refine ⟨out,?_,equal⟩
  simp [restoreCallFuel,eligible,scalar,allowed,actual,restored,bind,Outcome.bind,liftChecked,pure]

theorem restoreCallFuel_sound (program : NProgram) (fuel : Nat) (caller out : Context)
    (ty : Ty) (arguments : List NArgument) (result : Ret)
    (covered : OwnsAll caller.objects.heap)
    (actual : restoreCallFuel program fuel caller ty arguments = .finished (out,result)) :
    program.callFuel fuel (project caller ty) arguments = .finished (project out ty,result) := by
  by_cases accepted : eligible program = true
  ·
    cases low : program.callFuel fuel (project caller ty) arguments with
    | fault => simp [restoreCallFuel,accepted,low,bind,Outcome.bind] at actual
    | exhausted => simp [restoreCallFuel,accepted,low,bind,Outcome.bind] at actual
    | finished pair =>
      obtain ⟨after,ret⟩ := pair
      cases restored : restoreContext caller ty after with
      | none => simp [restoreCallFuel,accepted,low,restored,bind,Outcome.bind,liftChecked] at actual
      | some next =>
        have eq : (next,ret) = (out,result) := by
          simpa [restoreCallFuel,accepted,low,restored,bind,Outcome.bind,liftChecked,pure] using actual
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        rw [restoreContext_project caller next ty after restored covered]
  · simp [restoreCallFuel,accepted] at actual

-- The return value and complete low-level state are preserved together.
theorem call_restore_result (program : NProgram) (fuel : Nat) (caller out : Context)
    (ty : Ty) (arguments : List NArgument) (after : NState) (result : Ret)
    (actual : program.callFuel fuel (project caller ty) arguments = .finished (after,result))
    (restored : restoreContext caller ty after = some out) (covered : OwnsAll caller.objects.heap) :
    program.callFuel fuel (project caller ty) arguments = .finished (project out ty,result) := by
  rw [restoreContext_project caller out ty after restored covered]
  exact actual

end Proofs.CppMoveCallRestore
