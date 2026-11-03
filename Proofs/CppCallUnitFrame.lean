import Proofs.CppCallFrame

namespace Proofs.CppCallUnitFrame
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppCallFrame Proofs.CppBufferHeaders Proofs.CppNoResizeScope Proofs.DynamicResultValid
open Proofs.CppNestedEval Proofs.CppLoop

private theorem finish_none_frame (caller callee out : NState) (result : Ret)
    (headers : SameHeaders caller.frame.state callee.frame.state)
    (flags : callee.frame.rootWritable = caller.frame.rootWritable)
    (scopeEq : callee.scope = caller.scope+1)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : finish caller callee .unit none = some (out,result)) : CallEffects caller out := by
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner found
    rw [headers.forest] at found
    have bound := contexts owner callee.scope found
    rw [scopeEq] at bound
    omega
  unfold finish at actual
  dsimp only at actual
  split at actual
  · rename_i guarded
    obtain ⟨⟨frame,r⟩,finished,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj finished)
    change callee.frame = frame at eq
    subst frame
    obtain ⟨retired,ran,rest⟩ := bind_some _ _ _ rest
    obtain ⟨post,rw⟩ := retire_frame callee.frame retired callee.scope fresh ran
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = out at eq
    subst out
    refine ⟨headers.trans post,rw.trans flags,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
    · change (callee.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length
      simp [List.length_take,Nat.min_eq_left guarded.1]
    · change (callee.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
        caller.scalars.bindings.length = liveS caller
      simp [List.length_take,Nat.min_eq_left guarded.1,liveS]
  · simp at actual

theorem finish_unit_frame (caller callee out : NState) (returned : Option Ret) (result : Ret)
    (headers : SameHeaders caller.frame.state callee.frame.state)
    (flags : callee.frame.rootWritable = caller.frame.rootWritable)
    (scopeEq : callee.scope = caller.scope+1)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : finish caller callee .unit returned = some (out,result)) : CallEffects caller out := by
  cases returned with
  | none => exact finish_none_frame caller callee out result headers flags scopeEq contexts actual
  | some ret =>
    cases ret with
    | unit => exact finish_none_frame caller callee out result headers flags scopeEq contexts actual
    | scalar value => simp [finish] at actual
    | vector owner element => simp [finish] at actual

theorem call_headers (program : NProgram) (fuel : Nat) (caller out : NState) (args : List NArgument) (ret : Ret)
    (unit : program.result = .unit)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : program.callFuel fuel caller args = .finished (out,ret)) : CallEffects caller out := by
  cases prep : prepare caller program.parameters args with
  | none => simp [NProgram.callFuel,prep,liftChecked,bind,Outcome.bind] at actual
  | some init =>
    have initFrame := prepare_frame caller init program.parameters args prep
    have initScope := prepare_scope caller init program.parameters args prep
    have innerContexts : ∀ owner scope, init.frame.state.forest.context owner = some scope → scope ≤ init.scope := by
      intro owner scope found
      rw [initFrame.1] at found
      rw [initScope]
      exact Nat.le_trans (contexts owner scope found) (Nat.le_succ _)
    cases ran : runFuel fuel program.body init with
    | fault => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | exhausted => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | finished step =>
      have body := Proofs.CppNoResizeRun.run_headers fuel program.body init step allowed innerContexts ran
      have headers : SameHeaders caller.frame.state step.state.frame.state := by
        rw [← initFrame.1]
        exact body.headers
      simp only [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
      split at actual
      · simp at actual
      · cases ended : finish caller step.state program.result step.returned with
        | none => simp [ended] at actual
        | some pair =>
          simp only [ended] at actual
          have eq := Outcome.finished.inj actual
          subst pair
          rw [unit] at ended
          exact finish_unit_frame caller step.state out step.returned ret headers
            (body.flags.trans initFrame.2) (body.scopedState.trans initScope) contexts ended

end Proofs.CppCallUnitFrame
