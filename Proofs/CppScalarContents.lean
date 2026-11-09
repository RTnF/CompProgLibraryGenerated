import Proofs.CppNoResizeRun

namespace Proofs.CppScalarContents
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppLoop Proofs.DynamicResultValid Proofs.CppEvalFrame Proofs.CppNoResizeStmt
open Proofs.CppNoResizeScope Proofs.CppBufferHeaders

-- Counter observations may change; owned buffers, forest and permissions do not.
structure Contents (before after : Frame) : Prop where
  forest : after.state.forest = before.state.forest
  objects : after.state.storage.objects = before.state.storage.objects
  base : after.state.storage.baseSpace = before.state.storage.baseSpace
  flags : after.rootWritable = before.rootWritable

theorem Contents.refl (f : Frame) : Contents f f := ⟨rfl,rfl,rfl,rfl⟩
theorem Contents.trans {a b c : Frame} (x : Contents a b) (y : Contents b c) : Contents a c :=
  ⟨y.forest.trans x.forest,y.objects.trans x.objects,y.base.trans x.base,y.flags.trans x.flags⟩
theorem Contents.of_frame_same {f g : Frame} (same : FrameSame f g) : Contents f g := by
  refine ⟨?_,?_,?_,same.2⟩ <;> rw [same.1]

def Allowed : Command → Bool
  | .primitive stmt => Proofs.CppScalarFrame.Scalar stmt
  | .sequence a b | .branch _ a b => Allowed a && Allowed b
  | .scope body | .whileLoop _ body => Allowed body
  | .breakLoop => true
  | _ => false

structure Stable (s : NState) (out : NStep) : Prop where
  effects : Proofs.CppNoResizeStmt.Effects s out
  contents : Contents s.frame out.state.frame

theorem compose (s : NState) (mid out : NStep) (a : Stable s mid) (b : Stable mid.state out) : Stable s out :=
  ⟨Proofs.CppNoResizeRun.compose s mid out a.effects b.effects,a.contents.trans b.contents⟩
theorem contexts_after {s : NState} {out : NStep} (stable : Stable s out)
    (before : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope) :
    ∀ owner scope, out.state.frame.state.forest.context owner = some scope → scope ≤ out.state.scope :=
  Proofs.CppNoResizeRun.contexts_after stable.effects before

theorem primitive (stmt : NStmt) (s : NState) (out : NStep)
    (form : Proofs.CppScalarFrame.Scalar stmt = true) (actual : stmt.run s = some out) : Stable s out := by
  have permitted : Proofs.CppNoResizeStmt.Allowed stmt = true := by
    cases stmt <;> simp_all [Proofs.CppNoResizeStmt.Allowed,Proofs.CppScalarFrame.Scalar]
  exact ⟨Proofs.CppNoResizeStmt.primitive stmt s out permitted actual,
    Contents.of_frame_same (Proofs.CppScalarFrame.scalar_frame stmt s out form actual)⟩

theorem condition (s t : NState) (e : NExpr) (v : Int) (actual : e.eval s = some (t,v)) :
    Stable s ⟨(t.release s).charge 1 0,none,false⟩ := by
  exact ⟨Proofs.CppNoResizeRun.condition s t e v actual,
    Contents.of_frame_same (expression_frame e s t v actual)⟩

theorem retire_contents (f g : Frame) (scope : Nat)
    (fresh : ∀ owner, f.state.forest.context owner ≠ some scope)
    (actual : f.retireScope scope = some g) : Contents f g := by
  unfold Frame.retireScope at actual
  obtain ⟨state,retired,rest⟩ := bind_some _ _ _ actual
  unfold State.retireScope at retired
  split at retired
  · dsimp only at retired
    split at retired
    · have eq := Option.some.inj retired
      subst state
      have eq := Option.some.inj rest
      subst g
      rw [Proofs.CppNestedScope.retired_fresh f.state scope fresh]
      exact ⟨rfl,rfl,rfl,rfl⟩
    · simp at retired
  · simp at retired

theorem leave_contents (outer inner out : NState) (returned : Option Ret)
    (contents : Contents outer.frame inner.frame) (value : ScalarResult returned)
    (contexts : ∀ owner scope, outer.frame.state.forest.context owner = some scope → scope ≤ outer.scope)
    (actual : outer.leave inner returned = some out) : Contents outer.frame out.frame := by
  have fresh : ∀ owner, inner.frame.state.forest.context owner ≠ some (outer.scope+1) := by
    intro owner found
    rw [contents.forest] at found
    have bound := contexts owner (outer.scope+1) found
    omega
  have scalar_leave (returned : Option Ret)
      (noVector : returned = none ∨ ∃ v, returned = some (.scalar v))
      (actual : outer.leave inner returned = some out) : Contents outer.frame out.frame := by
    rcases noVector with rfl | ⟨v,rfl⟩ <;>
      unfold NState.leave at actual <;> split at actual
    all_goals try {simp at actual}
    all_goals
      dsimp only at actual
      obtain ⟨moved,movedEq,rest⟩ := bind_some _ _ _ actual
      have eq := Option.some.inj movedEq
      subst moved
      obtain ⟨retired,ran,rest⟩ := bind_some _ _ _ rest
      have kept := retire_contents inner.frame retired (outer.scope+1) fresh ran
      have eq := Option.some.inj rest
      subst out
      have combined := contents.trans kept
      exact ⟨combined.forest,combined.objects,combined.base,combined.flags⟩
  cases returned with
  | none => exact scalar_leave none (Or.inl rfl) actual
  | some result =>
    cases result with
    | scalar v => exact scalar_leave _ (Or.inr ⟨v,rfl⟩) actual
    | unit => simp [ScalarResult] at value
    | vector owner element => simp [ScalarResult] at value

theorem run_stable (fuel : Nat) (command : Command) (s : NState) (out : NStep)
    (allowed : Allowed command = true)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : CppNestedProgram.runFuel fuel command s = .finished out) : Stable s out := by
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
            bodyEffects.effects.headers bodyEffects.effects.flags bodyEffects.effects.returned contexts ended
          exact ⟨⟨headers,flags,scopeEq,bodyEffects.effects.returned⟩,
            leave_contents s step.state restored step.returned bodyEffects.contents bodyEffects.effects.returned contexts ended⟩
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
          | fault => simp [bodyRun] at actual
          | exhausted => simp [bodyRun] at actual
          | finished step =>
            have bodyEffects := ih body _ step allowed (contexts_after evaluated contexts) bodyRun
            have combined := compose s _ step evaluated bodyEffects
            simp only [bodyRun] at actual
            split at actual
            · have eq := Outcome.finished.inj actual
              subst out
              exact combined
            · split at actual
              · have eq := Outcome.finished.inj actual
                subst out
                exact ⟨⟨combined.effects.headers,combined.effects.flags,combined.effects.scopedState,combined.effects.returned⟩,combined.contents⟩
              · exact compose s step out combined
                  (ih (.whileLoop e body) step.state out allowed (contexts_after combined contexts) actual)
    | breakLoop =>
      simp only [CppNestedProgram.runFuel] at actual
      have eq := Outcome.finished.inj actual
      subst out
      exact ⟨⟨SameHeaders.refl _,rfl,rfl,trivial⟩,Contents.refl _⟩
    | invokeScalar program arguments => simp [Allowed] at allowed


end Proofs.CppScalarContents
