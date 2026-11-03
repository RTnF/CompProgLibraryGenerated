import Proofs.CppPreparePeak
import Proofs.CppPeakRun
import Proofs.CppCallFrame

namespace Proofs.CppCallPeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppBufferHeaders Proofs.CppNoResizeStmt
open Proofs.DynamicResultValid Proofs.CppLoop Proofs.CppCallFrame Proofs.CppPeakComponents

theorem finish_peak (caller callee out : NState) (ty : Ty) (returned : Option Ret) (result : Ret)
    (headers : SameHeaders caller.frame.state callee.frame.state)
    (growth : Grows caller callee)
    (scopeEq : callee.scope = caller.scope+1)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,result)) : Grows caller out := by
  have fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope := by
    intro owner found
    rw [headers.forest] at found
    have bound := contexts owner callee.scope found
    rw [scopeEq] at bound
    omega
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
      · rename_i guarded
        try dsimp only at actual
        split at actual
        · obtain ⟨⟨frame,r⟩,finished,rest⟩ := bind_some _ _ _ actual
          have eq := congrArg Prod.fst (Option.some.inj finished)
          change callee.frame = frame at eq
          subst frame
          obtain ⟨retired,ran,rest⟩ := bind_some _ _ _ rest
          have retiredPeak := Proofs.CppWritePeak.retire_peak callee.frame retired callee.scope fresh ran
          have eq := congrArg Prod.fst (Option.some.inj rest)
          change _ = out at eq
          subst out
          apply Proofs.CppPeakScope.restore growth ?_ ?_ (Nat.le_refl _)
          · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
          · change callee.frame.state.storage.peak ≤ retired.state.storage.peak
            rw [retiredPeak]
            exact Nat.le_max_left _ _
        · simp at actual
      · simp at actual

theorem call_peak (program : NProgram) (fuel : Nat) (caller out : NState) (args : List NArgument) (ret : Ret) (retType : Ty)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : program.callFuel fuel caller args = .finished (out,ret)) : Grows caller out := by
  cases prep : prepare caller program.parameters args with
  | none => simp [NProgram.callFuel,prep,liftChecked,bind,Outcome.bind] at actual
  | some init =>
    have initFrame := prepare_frame caller init program.parameters args prep
    have initGrowth := Proofs.CppPreparePeak.prepare_peak caller init program.parameters args prep
    have initScope := prepare_scope caller init program.parameters args prep
    have innerContexts : ∀ owner scope, init.frame.state.forest.context owner = some scope → scope ≤ init.scope := by
      intro owner scope found
      rw [initFrame.1] at found
      rw [initScope]
      exact Nat.le_trans (contexts owner scope found) (Nat.le_succ _)
    cases ran : CppNestedProgram.runFuel fuel program.body init with
    | fault => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | exhausted => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | finished step =>
      have body := Proofs.CppPeakRun.run_grows fuel program.body init step allowed innerContexts ran
      have headers : SameHeaders caller.frame.state step.state.frame.state := by
        rw [← initFrame.1]
        exact body.base.headers
      simp only [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
      split at actual
      · simp at actual
      · cases ended : Proofs.CppNestedCall.finish caller step.state program.result step.returned with
        | none => simp [ended,liftChecked] at actual
        | some pair =>
          simp only [ended,liftChecked] at actual
          have eq := Outcome.finished.inj actual
          subst pair
          rw [scalar] at ended
          exact finish_peak caller step.state out _ step.returned ret headers (initGrowth.trans body.growth)
            (body.base.scopedState.trans initScope) contexts ended


end Proofs.CppCallPeak
