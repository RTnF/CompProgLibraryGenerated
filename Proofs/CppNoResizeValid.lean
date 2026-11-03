import Proofs.CppMoveCallRestore

namespace Proofs.CppNoResizeValid
open Proofs.CppNestedProgram Proofs.CppLoop Proofs.CppNestedVectorBindings
open Proofs.CppEvalFrame Proofs.CppNoResizeStmt Proofs.DynamicResultValid

theorem write_valid (f g : Frame) (reference : Reference) (value : Int)
    (actual : f.write reference value = some g) : g.state.wellFormed = true := by
  unfold Frame.write at actual
  obtain ⟨permission,_,rest⟩ := bind_some _ _ _ actual
  split at rest
  · obtain ⟨pair,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨result,_,committed⟩ := bind_some _ _ _ rest
    exact commit_success_valid f g reference.address.owner (.integer reference.element) result committed
  · simp at rest

theorem primitive_valid (stmt : NStmt) (s : NState) (out : NStep)
    (allowed : Proofs.CppNoResizeStmt.Allowed stmt = true) (valid : s.frame.state.wellFormed = true)
    (actual : stmt.run s = some out) : out.state.frame.state.wellFormed = true := by
  by_cases scalar : Proofs.CppScalarFrame.Scalar stmt = true
  · rw [(Proofs.CppScalarFrame.scalar_frame stmt s out scalar actual).1]
    exact valid
  · cases stmt <;> simp [Proofs.CppNoResizeStmt.Allowed,Proofs.CppScalarFrame.Scalar] at allowed scalar
    rename_i container ty index expression
    unfold NStmt.run at actual
    obtain ⟨⟨a,value⟩,_,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,owner⟩,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨⟨c,position⟩,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨frame,written,done⟩ := bind_some _ _ _ rest
    have eq := Option.some.inj done
    subst out
    exact write_valid c.frame frame reference value written

theorem leave_valid (outer inner out : NState) (returned : Option Ret)
    (scalar : ScalarResult returned) (actual : outer.leave inner returned = some out) :
    out.frame.state.wellFormed = true := by
  cases returned with
  | none =>
    unfold NState.leave at actual
    split at actual
    · dsimp only at actual
      obtain ⟨moved,movedEq,rest⟩ := bind_some _ _ _ actual
      have eq := Option.some.inj movedEq
      subst moved
      obtain ⟨retired,ran,done⟩ := bind_some _ _ _ rest
      have eq := Option.some.inj done
      subst out
      exact Proofs.CppMoveCallRestore.retire_valid inner.frame retired (outer.scope+1) ran
    · simp at actual
  | some ret =>
    cases ret with
    | scalar value =>
      unfold NState.leave at actual
      split at actual
      · dsimp only at actual
        obtain ⟨moved,movedEq,rest⟩ := bind_some _ _ _ actual
        have eq := Option.some.inj movedEq
        subst moved
        obtain ⟨retired,ran,done⟩ := bind_some _ _ _ rest
        have eq := Option.some.inj done
        subst out
        exact Proofs.CppMoveCallRestore.retire_valid inner.frame retired (outer.scope+1) ran
      · simp at actual
    | unit => contradiction
    | vector owner element => contradiction

open Proofs.CppNoResizeRun in
theorem condition_valid (s t : NState) (e : NExpr) (v : Int)
    (valid : s.frame.state.wellFormed = true) (actual : e.eval s = some (t,v)) :
    ((t.release s).charge 1 0).frame.state.wellFormed = true := by
  change t.frame.state.wellFormed = true
  rw [(expression_frame e s t v actual).1]
  exact valid

open Proofs.CppNoResizeRun in
theorem run_valid (fuel : Nat) (command : Command) (s : NState) (out : NStep)
    (allowed : Proofs.CppNoResizeScope.Allowed command = true)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (valid : s.frame.state.wellFormed = true)
    (actual : Proofs.CppNestedProgram.runFuel fuel command s = .finished out) : out.state.frame.state.wellFormed = true := by
  induction fuel generalizing command s out with
  | zero => simp [Proofs.CppNestedProgram.runFuel] at actual
  | succ fuel ih =>
    cases command with
    | primitive stmt =>
      cases ran : stmt.run s with
      | none => simp [Proofs.CppNestedProgram.runFuel,ran,liftChecked] at actual
      | some step =>
        simp only [Proofs.CppNestedProgram.runFuel,ran,liftChecked] at actual
        have eq := Outcome.finished.inj actual
        subst out
        exact primitive_valid stmt s step allowed valid ran
    | sequence first rest =>
      obtain ⟨firstAllowed,restAllowed⟩ := Bool.and_eq_true_iff.mp allowed
      cases head : Proofs.CppNestedProgram.runFuel fuel first s with
      | fault => simp [Proofs.CppNestedProgram.runFuel,head,bind,Outcome.bind] at actual
      | exhausted => simp [Proofs.CppNestedProgram.runFuel,head,bind,Outcome.bind] at actual
      | finished step =>
        have firstValid := ih first s step firstAllowed contexts valid head
        have firstEffects := run_headers fuel first s step firstAllowed contexts head
        simp only [Proofs.CppNestedProgram.runFuel,head,bind,Outcome.bind] at actual
        split at actual
        · have eq := Outcome.finished.inj actual
          subst out
          exact firstValid
        · exact ih rest step.state out restAllowed (contexts_after firstEffects contexts) firstValid actual
    | scope body =>
      have innerContexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope+1 := by
        intro owner scope found
        exact Nat.le_trans (contexts owner scope found) (Nat.le_succ _)
      cases bodyRun : Proofs.CppNestedProgram.runFuel fuel body {s with scope := s.scope+1} with
      | fault => simp [Proofs.CppNestedProgram.runFuel,bodyRun,bind,Outcome.bind] at actual
      | exhausted => simp [Proofs.CppNestedProgram.runFuel,bodyRun,bind,Outcome.bind] at actual
      | finished step =>
        have bodyEffects := run_headers fuel body _ step allowed innerContexts bodyRun
        cases ended : s.leave step.state step.returned with
        | none => simp [Proofs.CppNestedProgram.runFuel,bodyRun,ended,liftChecked,bind,Outcome.bind] at actual
        | some restored =>
          simp only [Proofs.CppNestedProgram.runFuel,bodyRun,ended,liftChecked,bind,Outcome.bind] at actual
          have eq := Outcome.finished.inj actual
          subst out
          exact leave_valid s step.state restored step.returned bodyEffects.returned ended
    | branch e yes no =>
      obtain ⟨yesAllowed,noAllowed⟩ := Bool.and_eq_true_iff.mp allowed
      cases ev : e.eval s with
      | none => simp [Proofs.CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
      | some pair =>
        obtain ⟨t,v⟩ := pair
        have evaluated := condition s t e v ev
        have evaluatedValid := condition_valid s t e v valid ev
        simp only [Proofs.CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
        split at actual
        · exact ih no _ out noAllowed (contexts_after evaluated contexts) evaluatedValid actual
        · exact ih yes _ out yesAllowed (contexts_after evaluated contexts) evaluatedValid actual
    | whileLoop e body =>
      cases ev : e.eval s with
      | none => simp [Proofs.CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
      | some pair =>
        obtain ⟨t,v⟩ := pair
        have evaluated := condition s t e v ev
        have evaluatedValid := condition_valid s t e v valid ev
        simp only [Proofs.CppNestedProgram.runFuel,ev,liftChecked,bind,Outcome.bind] at actual
        split at actual
        · have eq := Outcome.finished.inj actual
          subst out
          exact evaluatedValid
        · cases bodyRun : Proofs.CppNestedProgram.runFuel fuel body ((t.release s).charge 1 0) with
          | fault => simp [bodyRun] at actual
          | exhausted => simp [bodyRun] at actual
          | finished step =>
            have bodyValid := ih body _ step allowed (contexts_after evaluated contexts) evaluatedValid bodyRun
            have bodyEffects := run_headers fuel body _ step allowed (contexts_after evaluated contexts) bodyRun
            have combined := compose s _ step evaluated bodyEffects
            simp only [bodyRun] at actual
            split at actual
            · have eq := Outcome.finished.inj actual
              subst out
              exact bodyValid
            · split at actual
              · have eq := Outcome.finished.inj actual
                subst out
                exact bodyValid
              · exact ih (.whileLoop e body) step.state out allowed (contexts_after combined contexts) bodyValid actual
    | breakLoop =>
      simp only [Proofs.CppNestedProgram.runFuel] at actual
      have eq := Outcome.finished.inj actual
      subst out
      exact valid
    | invokeScalar program arguments => simp [Proofs.CppNoResizeScope.Allowed] at allowed

end Proofs.CppNoResizeValid
