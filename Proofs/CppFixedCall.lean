import Proofs.CppFixedRun
import Proofs.CppCallFrame

namespace Proofs.CppFixedCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppBufferHeaders Proofs.CppNoResizeStmt
open Proofs.DynamicResultValid Proofs.CppLoop Proofs.CppCallFrame

theorem finish_values (caller callee out : NState) (ty : Ty) (returned : Option Ret) (result : Ret)
    (headers : SameHeaders caller.frame.state callee.frame.state)
    (scopeEq : callee.scope = caller.scope+1)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,result)) : ∀ owner, out.frame.state.storage.lookup owner = callee.frame.state.storage.lookup owner := by
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
          obtain ⟨_,lookups⟩ := Proofs.CppFixedScope.retire_values callee.frame retired callee.scope fresh ran
          have eq := congrArg Prod.fst (Option.some.inj rest)
          change _ = out at eq
          subst out
          exact lookups
        · simp at actual
      · simp at actual

theorem call_values (program : NProgram) (fuel : Nat) (caller out : NState) (args : List NArgument) (ret : Ret) (retType : Ty) (root : Nat)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppFixedRun.Allowed program.body = true)
    (target : ∀ init, prepare caller program.parameters args = some init → Proofs.CppFixedWrite.Target init root)
    (contexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (actual : program.callFuel fuel caller args = .finished (out,ret)) : ∀ owner, owner ≠ root → out.frame.state.storage.lookup owner = caller.frame.state.storage.lookup owner := by
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
      have body := Proofs.CppFixedRun.run_values fuel program.body init step root allowed (target init prep) innerContexts ran
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
          have preserved := finish_values caller step.state out _ step.returned ret headers
            (body.base.scopedState.trans initScope) contexts ended
          intro owner different
          exact (preserved owner).trans ((body.other owner different).trans (by rw [initFrame.1]))


theorem read_other (s t : NState) (root : Nat) (effects : CallEffects s t)
    (oldValid : s.frame.state.wellFormed = true) (newValid : t.frame.state.wellFormed = true)
    (lookups : ∀ owner, owner ≠ root → t.frame.state.storage.lookup owner = s.frame.state.storage.lookup owner)
    (reference : Reference) (different : reference.address.owner ≠ root) :
    t.frame.read reference = s.frame.read reference := by
  have objectEq : t.frame.object reference.address.owner (.integer reference.element) =
      s.frame.object reference.address.owner (.integer reference.element) := by
    simp only [Frame.object,oldValid,newValid,lookups _ different,effects.headers.forest]
  simp only [Frame.read,effects.grant reference,objectEq]

end Proofs.CppFixedCall
