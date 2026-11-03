import Proofs.BeatsBindingStmt
import Proofs.BeatsSlotRun

namespace Proofs.BeatsBindingCycle
open Proofs.CppNestedProgram Proofs.CppScalar
open Proofs.CppLoop (Outcome liftChecked)
open Proofs.BeatsSlotCycle (CoreStmt CoreCommand)

theorem release_long (after before : NState) (long : 16 ≤ after.frame.bindings.length)
    (base : 16 ≤ before.frame.bindings.length) : 16 ≤ (after.release before).frame.bindings.length := by
  change 16 ≤ (after.frame.bindings.take before.frame.bindings.length).length
  simp only [List.length_take]
  omega

theorem leave_long (outer inner : NState) (returned : Option Ret) (out : NState)
    (base : 16 ≤ outer.frame.bindings.length) (long : 16 ≤ inner.frame.bindings.length)
    (ran : outer.leave inner returned = some out) : 16 ≤ out.frame.bindings.length := by
  rw [leave_normal] at ran
  split at ran
  · cases found : exitFrame inner.frame outer.scope returned with
    | none => simp only [found,Option.map_none] at ran; contradiction
    | some frame =>
      simp only [found,Option.map_some] at ran
      cases ran
      change 16 ≤ (frame.bindings.take outer.frame.bindings.length).length
      rw [exitFrame_bindings _ _ _ _ found]
      simp only [List.length_take]
      omega
  · contradiction

theorem stmt_long (st : NStmt) (s : NState) (long : 16 ≤ s.frame.bindings.length)
    (core : CoreStmt st = true) (r : NStep) (ran : st.run s = some r) :
    16 ≤ r.state.frame.bindings.length := by
  cases st <;> simp only [CoreStmt,Bool.false_eq_true] at core
  case skip => cases ran; exact long
  case retUnit => cases ran; exact long
  case declare ty w e =>
    simp only [NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨⟨t,v⟩,he,v',_,out⟩
    cases out
    exact release_long t s (Nat.le_trans long (expr_binding_growth s t e v he)) long
  case assign i ty e =>
    simp only [NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨⟨t,v⟩,he,⟨binding,cell⟩,_,out⟩
    cases writable : binding.writable <;> cases converted : ty.convert v <;>
      simp [writable,converted] at out
    cases out
    exact release_long t s (Nat.le_trans long (expr_binding_growth s t e v he)) long
  case write c ty i v =>
    simp only [NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨⟨t,value⟩,he,⟨u,owner⟩,hc,⟨z,position⟩,hi,ref,_,frame,written,out⟩
    cases out
    change 16 ≤ (frame.bindings.take s.frame.bindings.length).length
    rw [write_bindings _ _ _ _ written]
    have first := (expr_related v).growth _ t value he
    have second := (container_related c).growth t u owner hc
    have third := (expr_related i).growth u z position hi
    change s.frame.bindings.length ≤ t.frame.bindings.length at first
    simp only [List.length_take]
    omega
  case ret e =>
    simp only [NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨⟨t,v⟩,he,out⟩
    cases out
    exact release_long t s (Nat.le_trans long (expr_binding_growth s t e v he)) long
  case retVector i =>
    simp only [NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨index,_,binding,_,out⟩
    cases out
    exact long
  case check e =>
    simp only [NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨⟨t,v⟩,he,out⟩
    split at out
    · simp at out
    · cases out
      exact release_long t s (Nat.le_trans long (expr_binding_growth s t e v he)) long

theorem stmt_commute (st : NStmt) (s : NState) (long : 16 ≤ s.frame.bindings.length)
    (core : CoreStmt st = true) : (st.run s).map viewStep = st.run (view s) := by
  cases st <;> simp only [CoreStmt,Bool.false_eq_true] at core
  case skip => rfl
  case retUnit => rfl
  case declare ty w e => exact declare_run_view s long ty w e
  case assign i ty e => exact assign_run_view s long i ty e
  case write c ty i v => exact write_run_view s long c ty i v
  case retVector i =>
    simp only [NStmt.run,vectorSlot,Bind.bind,Option.map_bind,Function.comp_def]
    cases found : s.vectorSlot i with
    | none => rfl
    | some index =>
      simp only [Option.map_some,Option.bind_some]
      rw [show (view s).frame = rebind s.frame from rfl,lookup s.frame long]
      cases s.frame.bindings[index]? <;> rfl
  case ret e =>
    have equal := expr_eval_view s long e
    cases ran : e.eval s with
    | none => simp only [ran,Option.map_none] at equal; simp [NStmt.run,ran,← equal]
    | some pair =>
      obtain ⟨t,v⟩ := pair
      have wide := Nat.le_trans long (expr_binding_growth s t e v ran)
      simp only [ran,Option.map_some] at equal
      simp only [NStmt.run,ran,← equal,Bind.bind,Option.bind_some]
      rw [← release_view t s wide long]
      rfl
  case check e =>
    have equal := expr_eval_view s long e
    cases ran : e.eval s with
    | none => simp only [ran,Option.map_none] at equal; simp [NStmt.run,ran,← equal]
    | some pair =>
      obtain ⟨t,v⟩ := pair
      have wide := Nat.le_trans long (expr_binding_growth s t e v ran)
      simp only [ran,Option.map_some] at equal
      simp only [NStmt.run,ran,← equal,Bind.bind,Option.bind_some]
      rw [← release_view t s wide long]
      by_cases zero : v = 0 <;> simp [zero,viewStep,view] <;> rfl

theorem scope_view (s : NState) : (view s).scope = s.scope := rfl

theorem run_long : ∀ fuel c s r, CoreCommand c = true → 16 ≤ s.frame.bindings.length →
    runFuel fuel c s = .finished r → 16 ≤ r.state.frame.bindings.length := by
  intro fuel
  induction fuel with
  | zero => intro c s r core long ran; cases ran
  | succ fuel ih =>
    intro c s r core long ran
    cases c with
    | primitive st =>
      simp only [runFuel] at ran
      cases step : st.run s with
      | none => simp [liftChecked,step] at ran
      | some next =>
        simp [liftChecked,step] at ran
        cases ran
        exact stmt_long st s long core _ step
    | sequence a b =>
      have parts : CoreCommand a = true ∧ CoreCommand b = true := by simpa [CoreCommand] using core
      simp only [runFuel,Bind.bind] at ran
      cases first : runFuel fuel a s with
      | exhausted => simp [first,Outcome.bind] at ran
      | fault => simp [first,Outcome.bind] at ran
      | finished step =>
        simp only [first,Outcome.bind] at ran
        have nextLong := ih a s step parts.1 long first
        split at ran
        · cases ran; exact nextLong
        · exact ih b step.state r parts.2 nextLong ran
    | scope b =>
      simp only [runFuel,Bind.bind] at ran
      cases body : runFuel fuel b {s with scope := s.scope+1} with
      | exhausted => simp [body,Outcome.bind] at ran
      | fault => simp [body,Outcome.bind] at ran
      | finished step =>
        simp only [body,Outcome.bind] at ran
        cases restored : s.leave step.state step.returned with
        | none => simp [restored,liftChecked] at ran
        | some t =>
          simp [restored,liftChecked] at ran
          cases ran
          exact leave_long s step.state step.returned t long
            (ih b {s with scope := s.scope+1} step core long body) restored
    | branch e y n =>
      have parts : CoreCommand y = true ∧ CoreCommand n = true := by simpa [CoreCommand] using core
      simp only [runFuel,Bind.bind] at ran
      cases eval : e.eval s with
      | none => simp [eval,liftChecked,Outcome.bind] at ran
      | some pair =>
        obtain ⟨t,v⟩ := pair
        simp only [eval,liftChecked,Outcome.bind] at ran
        have nextLong : 16 ≤ ((t.release s).charge 1 0).frame.bindings.length :=
          release_long t s (Nat.le_trans long (expr_binding_growth s t e v eval)) long
        split at ran
        · exact ih n _ r parts.2 nextLong ran
        · exact ih y _ r parts.1 nextLong ran
    | whileLoop e b =>
      have bodyCore : CoreCommand b = true := core
      simp only [runFuel,Bind.bind] at ran
      cases eval : e.eval s with
      | none => simp [eval,liftChecked,Outcome.bind] at ran
      | some pair =>
        obtain ⟨t,v⟩ := pair
        simp only [eval,liftChecked,Outcome.bind] at ran
        have nextLong : 16 ≤ ((t.release s).charge 1 0).frame.bindings.length :=
          release_long t s (Nat.le_trans long (expr_binding_growth s t e v eval)) long
        split at ran
        · cases ran; exact nextLong
        · cases body : runFuel fuel b ((t.release s).charge 1 0) with
          | exhausted => simp [body] at ran
          | fault => simp [body] at ran
          | finished step =>
            simp only [body] at ran
            have bodyLong := ih b _ step bodyCore nextLong body
            split at ran
            · cases ran; exact bodyLong
            · split at ran
              · cases ran; exact bodyLong
              · exact ih (.whileLoop e b) step.state r core bodyLong ran
    | breakLoop => cases ran; exact long
    | invokeScalar _ _ => simp [CoreCommand] at core

def outcomeView : Outcome NStep → Outcome NStep
  | .finished step => .finished (viewStep step)
  | .fault => .fault
  | .exhausted => .exhausted

theorem view_lift (q : Option NStep) : outcomeView (liftChecked q) = liftChecked (q.map viewStep) := by
  cases q <;> rfl

theorem run_view : ∀ fuel c s, CoreCommand c = true → 16 ≤ s.frame.bindings.length →
    outcomeView (runFuel fuel c s) = runFuel fuel c (view s) := by
  intro fuel
  induction fuel with
  | zero => intro c s core long; rfl
  | succ fuel ih =>
    intro c s core long
    cases c with
    | primitive st =>
      rw [runFuel,runFuel,view_lift,stmt_commute st s long core]
    | sequence a b =>
      have parts : CoreCommand a = true ∧ CoreCommand b = true := by simpa [CoreCommand] using core
      have equal := ih a s parts.1 long
      simp only [runFuel,Bind.bind]
      cases first : runFuel fuel a s with
      | exhausted => simp only [first,outcomeView] at equal; simp [← equal,Outcome.bind,outcomeView]
      | fault => simp only [first,outcomeView] at equal; simp [← equal,Outcome.bind,outcomeView]
      | finished step =>
        simp only [first,outcomeView] at equal
        simp only [← equal,Outcome.bind,viewStep]
        have nextLong := run_long fuel a s step parts.1 long first
        cases stop : (step.returned.isSome || step.breaking)
        · exact ih b step.state parts.2 nextLong
        · rfl
    | scope b =>
      have equal := ih b {s with scope := s.scope+1} core long
      rw [enter_view] at equal
      simp only [runFuel,Bind.bind,scope_view]
      cases body : runFuel fuel b {s with scope := s.scope+1} with
      | exhausted => simp only [body,outcomeView] at equal; simp [← equal,Outcome.bind,outcomeView]
      | fault => simp only [body,outcomeView] at equal; simp [← equal,Outcome.bind,outcomeView]
      | finished step =>
        simp only [body,outcomeView] at equal
        simp only [← equal,Outcome.bind,viewStep]
        have leave := leave_view s step.state step.returned long (run_long fuel b {s with scope := s.scope+1} step core long body)
        cases restored : s.leave step.state step.returned with
        | none => simp only [restored,Option.map_none] at leave; simp [← leave,liftChecked,outcomeView]
        | some t =>
          simp only [restored,Option.map_some] at leave
          simp [← leave,liftChecked,outcomeView,viewStep] <;> rfl
    | branch e y n =>
      have parts : CoreCommand y = true ∧ CoreCommand n = true := by simpa [CoreCommand] using core
      have equal := expr_eval_view s long e
      simp only [runFuel,Bind.bind]
      cases evaluated : e.eval s with
      | none => simp only [evaluated,Option.map_none] at equal; simp [← equal,liftChecked,Outcome.bind,outcomeView]
      | some pair =>
        obtain ⟨t,v⟩ := pair
        simp only [evaluated,Option.map_some] at equal
        simp only [← equal,liftChecked,Outcome.bind]
        have wide := Nat.le_trans long (expr_binding_growth s t e v evaluated)
        rw [← release_view t s wide long,← charge]
        have nextLong : 16 ≤ ((t.release s).charge 1 0).frame.bindings.length := release_long t s wide long
        by_cases zero : v = 0 <;> simp only [beq_iff_eq,zero,ite_true,ite_false]
        · exact ih n _ parts.2 nextLong
        · exact ih y _ parts.1 nextLong
    | whileLoop e b =>
      have equal := expr_eval_view s long e
      simp only [runFuel,Bind.bind]
      cases evaluated : e.eval s with
      | none => simp only [evaluated,Option.map_none] at equal; simp [← equal,liftChecked,Outcome.bind,outcomeView]
      | some pair =>
        obtain ⟨t,v⟩ := pair
        simp only [evaluated,Option.map_some] at equal
        simp only [← equal,liftChecked,Outcome.bind]
        have wide := Nat.le_trans long (expr_binding_growth s t e v evaluated)
        rw [← release_view t s wide long,← charge]
        have nextLong : 16 ≤ ((t.release s).charge 1 0).frame.bindings.length := release_long t s wide long
        by_cases zero : v = 0 <;> simp only [beq_iff_eq,zero,ite_true,ite_false]
        · rfl
        · have bodyEq := ih b ((t.release s).charge 1 0) core nextLong
          cases body : runFuel fuel b ((t.release s).charge 1 0) with
          | exhausted => simp only [body,outcomeView] at bodyEq; simp [← bodyEq,outcomeView]
          | fault => simp only [body,outcomeView] at bodyEq; simp [← bodyEq,outcomeView]
          | finished step =>
            simp only [body,outcomeView] at bodyEq
            simp only [← bodyEq,viewStep]
            have bodyLong := run_long fuel b _ step core nextLong body
            cases returned : step.returned.isSome
            · cases breaking : step.breaking
              · exact ih (.whileLoop e b) step.state core bodyLong
              · rfl
            · rfl
    | breakLoop => rfl
    | invokeScalar _ _ => simp [CoreCommand] at core

end Proofs.BeatsBindingCycle
