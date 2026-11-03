import Proofs.CppStoragePeak
import Proofs.CppCallFrame

namespace Proofs.CppCallStoragePeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppBufferHeaders Proofs.CppNoResizeStmt
open Proofs.DynamicResultValid Proofs.CppLoop Proofs.CppCallFrame

theorem finish_peak (caller callee out : NState) (ty : Ty) (returned : Option Ret) (result : Ret)
    (headers : SameHeaders caller.frame.state callee.frame.state)
    (peak : callee.frame.state.storage.peak ≤ Proofs.CppStoragePeak.bound caller)
    (scopeEq : callee.scope = caller.scope+1)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,result)) : out.frame.state.storage.peak ≤ Proofs.CppStoragePeak.bound caller := by
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
          change retired.state.storage.peak ≤ Proofs.CppStoragePeak.bound caller
          rw [retiredPeak,headers.live,headers.base]
          apply Nat.max_le.mpr
          refine ⟨peak,?_⟩
          exact Nat.le_trans (Nat.sub_le_sub_right (Nat.le_succ _) _) (Nat.le_max_right _ _)
        · simp at actual
      · simp at actual

theorem call_peak (program : NProgram) (fuel : Nat) (caller out : NState) (args : List NArgument) (ret : Ret) (retType : Ty)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : program.callFuel fuel caller args = .finished (out,ret)) : out.frame.state.storage.peak ≤ Proofs.CppStoragePeak.bound caller := by
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
    cases ran : CppNestedProgram.runFuel fuel program.body init with
    | fault => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | exhausted => simp [NProgram.callFuel,prep,ran,liftChecked,bind,Outcome.bind] at actual
    | finished step =>
      have body := Proofs.CppStoragePeak.run_peak fuel program.body init step allowed innerContexts ran
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
          have peak : step.state.frame.state.storage.peak ≤ Proofs.CppStoragePeak.bound caller := by
            have peak := body.peak
            simpa only [Proofs.CppStoragePeak.bound,initFrame.1] using peak
          exact finish_peak caller step.state out _ step.returned ret headers peak
            (body.base.scopedState.trans initScope) contexts ended


end Proofs.CppCallStoragePeak
