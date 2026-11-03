import Proofs.CppPeakScope
import Proofs.CppNoResizeRun

namespace Proofs.CppPeakRun
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppLoop
open Proofs.CppNoResizeStmt Proofs.CppNoResizeScope Proofs.CppBufferHeaders Proofs.DynamicResultValid
open Proofs.CppPeakComponents

structure Effects (s : NState) (out : NStep) : Prop where
  base : Proofs.CppNoResizeStmt.Effects s out
  growth : Grows s out.state

theorem primitive (stmt : NStmt) (s : NState) (out : NStep)
    (allowed : Proofs.CppNoResizeStmt.Allowed stmt = true) (actual : stmt.run s = some out) : Effects s out :=
  ⟨Proofs.CppNoResizeStmt.primitive stmt s out allowed actual,Proofs.CppStmtPeak.primitive stmt s out allowed actual⟩

theorem compose (s : NState) (mid out : NStep) (a : Effects s mid) (b : Effects mid.state out) : Effects s out :=
  ⟨Proofs.CppNoResizeRun.compose s mid out a.base b.base,a.growth.trans b.growth⟩

theorem contexts_after {s : NState} {out : NStep} (effects : Effects s out)
    (before : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope) :
    ∀ owner scope, out.state.frame.state.forest.context owner = some scope → scope ≤ out.state.scope :=
  Proofs.CppNoResizeRun.contexts_after effects.base before

theorem condition (s t : NState) (e : NExpr) (v : Int) (actual : e.eval s = some (t,v)) :
    Effects s ⟨(t.release s).charge 1 0,none,false⟩ :=
  ⟨Proofs.CppNoResizeRun.condition s t e v actual,
    (Proofs.CppEvalPeak.expression_peak e s t v actual).trans ((release t s).trans (charge _ 1 0))⟩

theorem run_grows (fuel : Nat) (command : Command) (s : NState) (out : NStep)
    (allowed : Proofs.CppNoResizeScope.Allowed command = true)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : CppNestedProgram.runFuel fuel command s = .finished out) : Effects s out := by
  induction fuel generalizing command s out with
  | zero => simp [CppNestedProgram.runFuel] at actual
  | succ fuel ih =>
    cases command with
    | primitive stmt =>
      cases ran : stmt.run s with
      | none => simp [CppNestedProgram.runFuel,ran,liftChecked] at actual
      | some step =>
        simp only [CppNestedProgram.runFuel,ran,liftChecked] at actual
        have eq := Outcome.finished.inj actual
        subst out
        exact primitive stmt s step allowed ran
    | sequence first rest =>
      obtain ⟨firstAllowed,restAllowed⟩ := Bool.and_eq_true_iff.mp allowed
      cases head : CppNestedProgram.runFuel fuel first s with
      | fault => simp [CppNestedProgram.runFuel,head,bind,Outcome.bind] at actual
      | exhausted => simp [CppNestedProgram.runFuel,head,bind,Outcome.bind] at actual
      | finished step =>
        have firstEffects := ih first s step firstAllowed contexts head
        simp only [CppNestedProgram.runFuel,head,bind,Outcome.bind] at actual
        split at actual
        · have eq := Outcome.finished.inj actual
          subst out
          exact firstEffects
        · exact compose s step out firstEffects (ih rest step.state out restAllowed (contexts_after firstEffects contexts) actual)
    | scope body =>
      have innerContexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope+1 := by
        intro owner scope found
        exact Nat.le_trans (contexts owner scope found) (Nat.le_succ _)
      cases bodyRun : CppNestedProgram.runFuel fuel body {s with scope := s.scope+1} with
      | fault => simp [CppNestedProgram.runFuel,bodyRun,bind,Outcome.bind] at actual
      | exhausted => simp [CppNestedProgram.runFuel,bodyRun,bind,Outcome.bind] at actual
      | finished step =>
        have bodyEffects := ih body _ step allowed innerContexts bodyRun
        cases ended : s.leave step.state step.returned with
        | none => simp [CppNestedProgram.runFuel,bodyRun,ended,liftChecked,bind,Outcome.bind] at actual
        | some restored =>
          simp only [CppNestedProgram.runFuel,bodyRun,ended,liftChecked,bind,Outcome.bind] at actual
          have eq := Outcome.finished.inj actual
          subst out
          obtain ⟨headers,flags,scopeEq⟩ := leave_effect s step.state restored step.returned
            bodyEffects.base.headers bodyEffects.base.flags bodyEffects.base.returned contexts ended
          exact ⟨⟨headers,flags,scopeEq,bodyEffects.base.returned⟩,
            Proofs.CppPeakScope.leave_grows s step.state restored step.returned bodyEffects.base.headers ⟨bodyEffects.growth.scalar,bodyEffects.growth.storage,bodyEffects.growth.outer⟩ bodyEffects.base.returned contexts ended⟩
    | branch e yes no =>
      obtain ⟨yesAllowed,noAllowed⟩ := Bool.and_eq_true_iff.mp allowed
      cases ev : e.eval s with
      | none => simp [CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
      | some pair =>
        obtain ⟨t,v⟩ := pair
        have evaluated := condition s t e v ev
        simp only [CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
        split at actual
        · exact compose s _ out evaluated (ih no _ out noAllowed (contexts_after evaluated contexts) actual)
        · exact compose s _ out evaluated (ih yes _ out yesAllowed (contexts_after evaluated contexts) actual)
    | whileLoop e body =>
      cases ev : e.eval s with
      | none => simp [CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
      | some pair =>
        obtain ⟨t,v⟩ := pair
        have evaluated := condition s t e v ev
        simp only [CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
        split at actual
        · have eq := Outcome.finished.inj actual
          subst out
          exact evaluated
        · cases bodyRun : CppNestedProgram.runFuel fuel body ((t.release s).charge 1 0) with
          | fault => simp [bodyRun,bind,Outcome.bind] at actual
          | exhausted => simp [bodyRun,bind,Outcome.bind] at actual
          | finished step =>
            have bodyEffects := ih body _ step allowed (contexts_after evaluated contexts) bodyRun
            have combined := compose s _ step evaluated bodyEffects
            simp only [bodyRun,bind,Outcome.bind] at actual
            split at actual
            · have eq := Outcome.finished.inj actual
              subst out
              exact combined
            · split at actual
              · have eq := Outcome.finished.inj actual
                subst out
                exact ⟨⟨combined.base.headers,combined.base.flags,combined.base.scopedState,combined.base.returned⟩,combined.growth⟩
              · exact compose s step out combined
                  (ih (.whileLoop e body) step.state out allowed (contexts_after combined contexts) actual)
    | breakLoop =>
      simp only [CppNestedProgram.runFuel] at actual
      have eq := Outcome.finished.inj actual
      subst out
      exact ⟨⟨SameHeaders.refl _,rfl,rfl,trivial⟩,charge s 1 0⟩
    | invokeScalar program arguments => simp [Proofs.CppNoResizeScope.Allowed] at allowed

end Proofs.CppPeakRun
