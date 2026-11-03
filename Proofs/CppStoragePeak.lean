import Proofs.CppWritePeak
import Proofs.CppNoResizeRun

namespace Proofs.CppStoragePeak
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppLoop
open Proofs.CppNoResizeStmt Proofs.CppNoResizeScope Proofs.CppBufferHeaders Proofs.DynamicResultValid

def bound (s : NState) : Nat := max s.frame.state.storage.peak
  (s.frame.state.liveSpace+1-s.frame.state.storage.baseSpace)

structure Effects (s : NState) (out : NStep) : Prop where
  base : Proofs.CppNoResizeStmt.Effects s out
  peak : out.state.frame.state.storage.peak ≤ bound s

theorem primitive (stmt : NStmt) (s : NState) (out : NStep)
    (allowed : Proofs.CppNoResizeStmt.Allowed stmt = true) (actual : stmt.run s = some out) : Effects s out := by
  have base := Proofs.CppNoResizeStmt.primitive stmt s out allowed actual
  refine ⟨base,?_⟩
  cases stmt with
  | write container ty index expression =>
    exact Nat.le_of_eq (Proofs.CppWritePeak.stmt_write_peak s out container ty index expression actual)
  | _ =>
    have frame := Proofs.CppScalarFrame.scalar_frame _ s out (by exact allowed) actual
    unfold bound
    rw [frame.1]
    exact Nat.le_max_left _ _

theorem bound_after (s : NState) (out : NStep) (effects : Effects s out) : bound out.state ≤ bound s := by
  unfold bound
  rw [effects.base.headers.live,effects.base.headers.base]
  exact Nat.max_le.mpr ⟨effects.peak,Nat.le_max_right _ _⟩

theorem compose (s : NState) (mid out : NStep) (a : Effects s mid) (b : Effects mid.state out) : Effects s out :=
  ⟨Proofs.CppNoResizeRun.compose s mid out a.base b.base,Nat.le_trans b.peak (bound_after s mid a)⟩

theorem contexts_after {s : NState} {out : NStep} (effects : Effects s out)
    (before : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope) :
    ∀ owner scope, out.state.frame.state.forest.context owner = some scope → scope ≤ out.state.scope :=
  Proofs.CppNoResizeRun.contexts_after effects.base before

theorem condition (s t : NState) (e : NExpr) (v : Int) (actual : e.eval s = some (t,v)) :
    Effects s ⟨(t.release s).charge 1 0,none,false⟩ := by
  refine ⟨Proofs.CppNoResizeRun.condition s t e v actual,?_⟩
  have frame := Proofs.CppEvalFrame.expression_frame e s t v actual
  change t.frame.state.storage.peak ≤ bound s
  rw [frame.1]
  exact Nat.le_max_left _ _

theorem leave_peak (outer inner out : NState) (returned : Option Ret)
    (headers : SameHeaders outer.frame.state inner.frame.state)
    (peak : inner.frame.state.storage.peak ≤ bound outer)
    (value : ScalarResult returned)
    (contexts : ∀ owner scope, outer.frame.state.forest.context owner = some scope → scope ≤ outer.scope)
    (actual : outer.leave inner returned = some out) :
    out.frame.state.storage.peak ≤ bound outer := by
  have fresh : ∀ owner, inner.frame.state.forest.context owner ≠ some (outer.scope+1) := by
    intro owner found
    rw [headers.forest] at found
    have bound := contexts owner (outer.scope+1) found
    omega
  cases returned with
  | none =>
    unfold NState.leave at actual
    split at actual
    · dsimp only at actual
      obtain ⟨moved,movedEq,rest⟩ := bind_some _ _ _ actual
      have eq := Option.some.inj movedEq
      subst moved
      obtain ⟨retired,ran,rest⟩ := bind_some _ _ _ rest
      have retiredPeak := Proofs.CppWritePeak.retire_peak inner.frame retired (outer.scope+1) fresh ran
      have eq := Option.some.inj rest
      subst out
      change retired.state.storage.peak ≤ bound outer
      rw [retiredPeak,headers.live,headers.base]
      apply Nat.max_le.mpr
      refine ⟨peak,?_⟩
      exact Nat.le_trans (Nat.sub_le_sub_right (Nat.le_succ _) _) (Nat.le_max_right _ _)
    · simp at actual
  | some result =>
    cases result with
    | scalar v =>
      unfold NState.leave at actual
      split at actual
      · dsimp only at actual
        obtain ⟨moved,movedEq,rest⟩ := bind_some _ _ _ actual
        have eq := Option.some.inj movedEq
        subst moved
        obtain ⟨retired,ran,rest⟩ := bind_some _ _ _ rest
        have retiredPeak := Proofs.CppWritePeak.retire_peak inner.frame retired (outer.scope+1) fresh ran
        have eq := Option.some.inj rest
        subst out
        change retired.state.storage.peak ≤ bound outer
        rw [retiredPeak,headers.live,headers.base]
        apply Nat.max_le.mpr
        refine ⟨peak,?_⟩
        exact Nat.le_trans (Nat.sub_le_sub_right (Nat.le_succ _) _) (Nat.le_max_right _ _)
      · simp at actual
    | unit => simp [ScalarResult] at value
    | vector owner element => simp [ScalarResult] at value


theorem run_peak (fuel : Nat) (command : Command) (s : NState) (out : NStep)
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
            leave_peak s step.state restored step.returned bodyEffects.base.headers bodyEffects.peak bodyEffects.base.returned contexts ended⟩
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
                exact ⟨⟨combined.base.headers,combined.base.flags,combined.base.scopedState,combined.base.returned⟩,combined.peak⟩
              · exact compose s step out combined
                  (ih (.whileLoop e body) step.state out allowed (contexts_after combined contexts) actual)
    | breakLoop =>
      simp only [CppNestedProgram.runFuel] at actual
      have eq := Outcome.finished.inj actual
      subst out
      exact ⟨⟨SameHeaders.refl _,rfl,rfl,trivial⟩,Nat.le_max_left _ _⟩
    | invokeScalar program arguments => simp [Proofs.CppNoResizeScope.Allowed] at allowed

end Proofs.CppStoragePeak
