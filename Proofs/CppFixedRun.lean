import Proofs.CppFixedScope

namespace Proofs.CppFixedRun
open Proofs.CppNestedProgram Proofs.CppLoop Proofs.CppFixedWrite
open Proofs.CppNoResizeStmt Proofs.CppBufferHeaders Proofs.CppExprPrefix

def AllowedStmt : NStmt → Bool
  | .write (.local 0) _ _ _ => true
  | stmt => Proofs.CppScalarFrame.Scalar stmt

def Allowed : Command → Bool
  | .primitive stmt => AllowedStmt stmt
  | .sequence a b | .branch _ a b => Allowed a && Allowed b
  | .scope body | .whileLoop _ body => Allowed body
  | .breakLoop => true
  | _ => false

theorem allowed_stmt (stmt : NStmt) (allowed : AllowedStmt stmt = true) :
    Proofs.CppNoResizeStmt.Allowed stmt = true := by
  cases stmt with
  | write container ty index expression => rfl
  | _ => exact allowed

theorem allowed_command (command : Command) (allowed : Allowed command = true) :
    Proofs.CppNoResizeScope.Allowed command = true := by
  induction command with
  | primitive stmt => exact allowed_stmt stmt allowed
  | sequence a b ha hb | branch e a b ha hb =>
    obtain ⟨aa,ab⟩ := Bool.and_eq_true_iff.mp allowed
    exact Bool.and_eq_true_iff.mpr ⟨ha aa,hb ab⟩
  | scope body ih | whileLoop e body ih => exact ih allowed
  | breakLoop => rfl
  | invokeScalar program args => exact allowed

structure Effects (s : NState) (out : NStep) (root : Nat) : Prop where
  base : Proofs.CppNoResizeStmt.Effects s out
  target : Target out.state root
  bindings : out.state.frame.bindings = s.frame.bindings
  slots : ∃ extra, out.state.slots = s.slots++extra
  other : ∀ owner, owner ≠ root → out.state.frame.state.storage.lookup owner = s.frame.state.storage.lookup owner

theorem scalar_primitive (stmt : NStmt) (s : NState) (out : NStep) (root : Nat)
    (form : Proofs.CppScalarFrame.Scalar stmt = true) (target : Target s root)
    (actual : stmt.run s = some out) : Effects s out root := by
  have base := Proofs.CppNoResizeStmt.scalar_effect stmt s out form actual
  have frame := scalar_full_frame stmt s out form actual
  obtain ⟨next,other⟩ := scalar_target stmt s out root form target actual
  exact ⟨base,next,congrArg Proofs.CppNestedVectorBindings.Frame.bindings frame.1,frame.2,fun owner _ => other owner⟩

theorem primitive (stmt : NStmt) (s : NState) (out : NStep) (root : Nat)
    (allowed : AllowedStmt stmt = true) (target : Target s root)
    (actual : stmt.run s = some out) : Effects s out root := by
  have base := Proofs.CppNoResizeStmt.primitive stmt s out (allowed_stmt stmt allowed) actual
  cases stmt with
  | write container ty index expression =>
    cases container with
    | «local» slot =>
      cases slot with
      | zero =>
        obtain ⟨next,bindings,slots,other⟩ := write_local s out root ty index expression target actual
        exact ⟨base,next,bindings,⟨[],by simpa using slots⟩,other⟩
      | succ slot => simp [AllowedStmt,Proofs.CppScalarFrame.Scalar] at allowed
    | row parent element index => simp [AllowedStmt,Proofs.CppScalarFrame.Scalar] at allowed
  | _ =>
    apply scalar_primitive _ s out root ?_ target actual
    exact allowed

theorem compose (s : NState) (mid out : NStep) (root : Nat)
    (a : Effects s mid root) (b : Effects mid.state out root) : Effects s out root := by
  obtain ⟨ea,sa⟩ := a.slots
  obtain ⟨eb,sb⟩ := b.slots
  refine ⟨Proofs.CppNoResizeRun.compose s mid out a.base b.base,b.target,b.bindings.trans a.bindings,?_,?_⟩
  · exact ⟨ea++eb,by rw [sb,sa,List.append_assoc]⟩
  · intro owner different
    exact (b.other owner different).trans (a.other owner different)

theorem contexts_after {s : NState} {out : NStep} {root : Nat} (effects : Effects s out root)
    (before : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope) :
    ∀ owner scope, out.state.frame.state.forest.context owner = some scope → scope ≤ out.state.scope :=
  Proofs.CppNoResizeRun.contexts_after effects.base before

theorem condition (s t : NState) (e : NExpr) (v : Int) (root : Nat) (target : Target s root)
    (actual : e.eval s = some (t,v)) : Effects s ⟨(t.release s).charge 1 0,none,false⟩ root := by
  have frame := release_frame e s t v actual
  have slots := (expression_prefix e s t v actual).1
  have bindings : ((t.release s).charge 1 0).frame.bindings = s.frame.bindings := congrArg Proofs.CppNestedVectorBindings.Frame.bindings frame
  have slotsEq : ((t.release s).charge 1 0).slots = s.slots := slots
  refine ⟨Proofs.CppNoResizeRun.condition s t e v actual,target_slots _ _ root target bindings ⟨[],by simpa using slotsEq⟩,bindings,⟨[],by simpa using slotsEq⟩,?_⟩
  intro owner different
  change (t.release s).frame.state.storage.lookup owner = s.frame.state.storage.lookup owner
  rw [frame]

theorem run_values (fuel : Nat) (command : Command) (s : NState) (out : NStep) (root : Nat)
    (allowed : Allowed command = true)
    (target : Target s root)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : CppNestedProgram.runFuel fuel command s = .finished out) : Effects s out root := by
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
        exact primitive stmt s step root allowed target ran
    | sequence first rest =>
      obtain ⟨firstAllowed,restAllowed⟩ := Bool.and_eq_true_iff.mp allowed
      cases head : CppNestedProgram.runFuel fuel first s with
      | fault => simp [CppNestedProgram.runFuel,head,bind,Outcome.bind] at actual
      | exhausted => simp [CppNestedProgram.runFuel,head,bind,Outcome.bind] at actual
      | finished step =>
        have firstEffects := ih first s step firstAllowed target contexts head
        simp only [CppNestedProgram.runFuel,head,bind,Outcome.bind] at actual
        split at actual
        · have eq := Outcome.finished.inj actual
          subst out
          exact firstEffects
        · exact compose s step out root firstEffects (ih rest step.state out restAllowed firstEffects.target (contexts_after firstEffects contexts) actual)
    | scope body =>
      have innerContexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope+1 := by
        intro owner scope found
        exact Nat.le_trans (contexts owner scope found) (Nat.le_succ _)
      cases bodyRun : CppNestedProgram.runFuel fuel body {s with scope := s.scope+1} with
      | fault => simp [CppNestedProgram.runFuel,bodyRun,bind,Outcome.bind] at actual
      | exhausted => simp [CppNestedProgram.runFuel,bodyRun,bind,Outcome.bind] at actual
      | finished step =>
        have bodyEffects := ih body {s with scope := s.scope+1} step allowed target innerContexts bodyRun
        cases ended : s.leave step.state step.returned with
        | none => simp [CppNestedProgram.runFuel,bodyRun,ended,liftChecked,bind,Outcome.bind] at actual
        | some restored =>
          simp only [CppNestedProgram.runFuel,bodyRun,ended,liftChecked,bind,Outcome.bind] at actual
          have eq := Outcome.finished.inj actual
          subst out
          obtain ⟨headers,flags,scopeEq⟩ := Proofs.CppNoResizeScope.leave_effect s step.state restored step.returned
            bodyEffects.base.headers bodyEffects.base.flags bodyEffects.base.returned contexts ended
          obtain ⟨bindings,slots,lookups⟩ := Proofs.CppFixedScope.leave_values s step.state restored step.returned
            bodyEffects.base.headers bodyEffects.bindings bodyEffects.base.returned contexts ended
          refine ⟨⟨headers,flags,scopeEq,bodyEffects.base.returned⟩,target_slots s restored root target bindings ⟨[],by simpa using slots⟩,bindings,⟨[],by simpa using slots⟩,?_⟩
          intro owner different
          exact (lookups owner).trans (bodyEffects.other owner different)
    | branch e yes no =>
      obtain ⟨yesAllowed,noAllowed⟩ := Bool.and_eq_true_iff.mp allowed
      cases ev : e.eval s with
      | none => simp [CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
      | some pair =>
        obtain ⟨t,v⟩ := pair
        have evaluated := condition s t e v root target ev
        simp only [CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
        split at actual
        · exact compose s _ out root evaluated (ih no _ out noAllowed evaluated.target (contexts_after evaluated contexts) actual)
        · exact compose s _ out root evaluated (ih yes _ out yesAllowed evaluated.target (contexts_after evaluated contexts) actual)
    | whileLoop e body =>
      cases ev : e.eval s with
      | none => simp [CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
      | some pair =>
        obtain ⟨t,v⟩ := pair
        have evaluated := condition s t e v root target ev
        simp only [CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
        split at actual
        · have eq := Outcome.finished.inj actual
          subst out
          exact evaluated
        · cases bodyRun : CppNestedProgram.runFuel fuel body ((t.release s).charge 1 0) with
          | fault => simp [bodyRun,bind,Outcome.bind] at actual
          | exhausted => simp [bodyRun,bind,Outcome.bind] at actual
          | finished step =>
            have bodyEffects := ih body _ step allowed evaluated.target (contexts_after evaluated contexts) bodyRun
            have combined := compose s _ step root evaluated bodyEffects
            simp only [bodyRun,bind,Outcome.bind] at actual
            split at actual
            · have eq := Outcome.finished.inj actual
              subst out
              exact combined
            · split at actual
              · have eq := Outcome.finished.inj actual
                subst out
                exact ⟨⟨combined.base.headers,combined.base.flags,combined.base.scopedState,combined.base.returned⟩,combined.target,combined.bindings,combined.slots,combined.other⟩
              · exact compose s step out root combined
                  (ih (.whileLoop e body) step.state out allowed combined.target (contexts_after combined contexts) actual)
    | breakLoop =>
      simp only [CppNestedProgram.runFuel] at actual
      have eq := Outcome.finished.inj actual
      subst out
      exact ⟨⟨SameHeaders.refl _,rfl,rfl,trivial⟩,target,rfl,⟨[],by simp⟩,fun _ _ => rfl⟩
    | invokeScalar program arguments => simp [Allowed] at allowed

end Proofs.CppFixedRun
