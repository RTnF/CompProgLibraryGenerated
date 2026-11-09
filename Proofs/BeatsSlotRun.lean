import Proofs.BeatsSlotStmt

namespace Proofs.CppSlotRename
open Proofs.CppNestedProgram

def stmt (f : Nat → Nat) : NStmt → NStmt
  | .skip => .skip
  | .declare ty w e => .declare ty w (expr f e)
  | .constructRows ty w e => .constructRows ty w (expr f e)
  | .declareVector ty w => .declareVector ty w
  | .fillVector ty w n v => .fillVector ty w (expr f n) (expr f v)
  | .assign i ty e => .assign (f i) ty (expr f e)
  | .write c ty i v => .write (container f c) ty (expr f i) (expr f v)
  | .reserve c ty e => .reserve (container f c) ty (expr f e)
  | .append c ty e => .append (container f c) ty (expr f e)
  | .assignRange c i j ty a b => .assignRange (container f c) (f i) (f j) ty a b
  | .ret e => .ret (expr f e)
  | .retVector i => .retVector (f i)
  | .check e => .check (expr f e)
  | .sortVec c ty => .sortVec (container f c) ty
  | .sortPairs a b ty => .sortPairs (container f a) (container f b) ty
  | .dedupVec c ty => .dedupVec (container f c) ty
  | .appendRow c ty => .appendRow (container f c) ty
  | .copyVector c ty w => .copyVector (container f c) ty w
  | .retUnit => .retUnit

def command (f : Nat → Nat) : Command → Command
  | .primitive s => .primitive (stmt f s)
  | .sequence a b => .sequence (command f a) (command f b)
  | .scope b => .scope (command f b)
  | .branch c y n => .branch (expr f c) (command f y) (command f n)
  | .whileLoop c b => .whileLoop (expr f c) (command f b)
  | .breakLoop => .breakLoop
  -- These expressions address scalar bindings, whose order is unchanged.
  | .invokeScalar p args => .invokeScalar p args

end Proofs.CppSlotRename

namespace Proofs.BeatsSlotCycle
open Proofs.CppNestedProgram Proofs.CppMixedInvoke Proofs.CppScalar
open Proofs.CppSlotRename
open Proofs.CppLoop (Outcome liftChecked)

-- The primitives used by the lowered Beats bodies, plus returns and checks.
-- Other vector operations are renamed syntactically but not accepted here.
def CoreStmt : NStmt → Bool
  | .skip | .declare _ _ _ | .assign _ _ _ | .write _ _ _ _
    | .ret _ | .retVector _ | .retUnit | .check _ => true
  | _ => false

def CoreCommand : Command → Bool
  | .primitive s => CoreStmt s
  | .sequence a b => CoreCommand a && CoreCommand b
  | .scope b => CoreCommand b
  | .branch _ y n => CoreCommand y && CoreCommand n
  | .whileLoop _ b => CoreCommand b
  | .breakLoop => true
  | .invokeScalar _ _ => false

theorem stmt_long (st : NStmt) (s : NState) (long : 16 ≤ s.slots.length)
    (core : CoreStmt st = true) (r : NStep) (ran : (stmt cycle st).run s = some r) :
    16 ≤ r.state.slots.length := by
  cases st <;> simp only [CoreStmt,Bool.false_eq_true] at core
  case skip => cases ran; exact long
  case retUnit => cases ran; exact long
  case declare ty w e =>
    simp only [stmt,NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨⟨t,v⟩,he,v',hv,out⟩
    cases out
    change 16 ≤ (t.slots++[_]).length
    have same := (expr_related e).slots s t v he
    simp only [List.length_append,List.length_singleton,same]
    omega
  case assign i ty e =>
    simp only [stmt,NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨⟨t,v⟩,he,⟨binding,cell⟩,_,out⟩
    cases writable : binding.writable <;> cases converted : ty.convert v <;>
      simp [writable,converted] at out
    cases out
    change 16 ≤ t.slots.length
    rw [(expr_related e).slots s t v he]
    exact long
  case write c ty i v =>
    simp only [stmt,NStmt.run,Bind.bind,Option.bind_eq_some_iff,expr_nodes,container_nodes] at ran
    rcases ran with ⟨⟨t,value⟩,he,⟨u,owner⟩,hc,⟨z,position⟩,hi,ref,_,frame,_,out⟩
    cases out
    change 16 ≤ z.slots.length
    rw [(expr_related i).slots u z position hi,(container_related c).slots t u owner hc,
      (expr_related v).slots _ t value he]
    exact long
  case ret e =>
    simp only [stmt,NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨⟨t,v⟩,he,out⟩
    cases out
    change 16 ≤ t.slots.length
    rw [(expr_related e).slots s t v he]
    exact long
  case retVector i =>
    simp only [stmt,NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨index,_,binding,_,out⟩
    cases out
    exact long
  case check e =>
    simp only [stmt,NStmt.run,Bind.bind,Option.bind_eq_some_iff] at ran
    rcases ran with ⟨⟨t,v⟩,he,out⟩
    split at out
    · simp at out
    · cases out
      change 16 ≤ t.slots.length
      rw [(expr_related e).slots s t v he]
      exact long

theorem stmt_commute (st : NStmt) (s : NState) (long : 16 ≤ s.slots.length)
    (core : CoreStmt st = true) :
    ((stmt cycle st).run s).map permuteStep = st.run (permute s) := by
  cases st <;> simp only [CoreStmt,Bool.false_eq_true] at core
  case skip => rfl
  case retUnit => rfl
  case declare ty w e => exact declare_run_permute s long ty w e
  case assign i ty e => exact assign_run_permute s long i ty e
  case write c ty i v => exact write_run_permute s long c ty i v
  case retVector i =>
    simp only [stmt,NStmt.run,vectorSlot_permute s long,frame_permute]
    cases found : s.vectorSlot (cycle i) with
    | none => simp []
    | some owner =>
      cases binding : s.frame.bindings[owner]? <;> simp [binding,permuteStep,permute] <;> rfl
  case ret e =>
    have equal := expr_eval_permute s long e
    cases ran : (expr cycle e).eval s with
    | none => simp only [ran,Option.map_none] at equal; simp [stmt,NStmt.run,ran,← equal]
    | some pair =>
      obtain ⟨t,v⟩ := pair
      simp only [ran,Option.map_some] at equal
      simp only [stmt,NStmt.run,ran,← equal,Bind.bind,Option.bind_some]
      simp [permuteStep,permute,NState.release] <;> rfl
  case check e =>
    have equal := expr_eval_permute s long e
    cases ran : (expr cycle e).eval s with
    | none => simp only [ran,Option.map_none] at equal; simp [stmt,NStmt.run,ran,← equal]
    | some pair =>
      obtain ⟨t,v⟩ := pair
      simp only [ran,Option.map_some] at equal
      simp only [stmt,NStmt.run,ran,← equal,Bind.bind,Option.bind_some]
      by_cases zero : v = 0 <;> simp [zero,permuteStep,permute,NState.release] <;> rfl

theorem leave_slots (outer inner : NState) (ret : Option Ret) (t : NState)
    (ran : outer.leave inner ret = some t) : t.slots = outer.slots := by
  simp only [NState.leave] at ran
  split at ran
  · cases ret with
    | none =>
      simp only [Bind.bind,Option.bind_some,Option.bind_eq_some_iff] at ran
      rcases ran with ⟨frame,_,out⟩
      cases out
      rfl
    | some returned =>
      cases returned <;> simp only [Bind.bind,Option.bind_some,Option.bind_eq_some_iff] at ran
      all_goals first
        | (rcases ran with ⟨moved,_,retired,_,out⟩; cases out; rfl)
        | (rcases ran with ⟨retired,_,out⟩; cases out; rfl)
  · simp at ran

theorem run_long : ∀ fuel c s r, CoreCommand c = true → 16 ≤ s.slots.length →
    runFuel fuel (command cycle c) s = .finished r → 16 ≤ r.state.slots.length := by
  intro fuel
  induction fuel with
  | zero => intro c s r core long ran; cases ran
  | succ fuel ih =>
    intro c s r core long ran
    cases c with
    | primitive st =>
      simp only [command,runFuel] at ran
      cases step : (stmt cycle st).run s with
      | none => simp [liftChecked,step] at ran
      | some next =>
        simp [liftChecked,step] at ran
        cases ran
        exact stmt_long st s long core _ step
    | sequence a b =>
      have parts : CoreCommand a = true ∧ CoreCommand b = true := by simpa [CoreCommand] using core
      simp only [command,runFuel,Bind.bind] at ran
      cases first : runFuel fuel (command cycle a) s with
      | exhausted => simp [first,Outcome.bind] at ran
      | fault => simp [first,Outcome.bind] at ran
      | finished step =>
        simp only [first,Outcome.bind] at ran
        have nextLong := ih a s step parts.1 long first
        split at ran
        · cases ran; exact nextLong
        · exact ih b step.state r parts.2 nextLong ran
    | scope b =>
      simp only [command,runFuel,Bind.bind] at ran
      cases body : runFuel fuel (command cycle b) {s with scope := s.scope+1} with
      | exhausted => simp [body,Outcome.bind] at ran
      | fault => simp [body,Outcome.bind] at ran
      | finished step =>
        simp only [body,Outcome.bind] at ran
        cases restored : s.leave step.state step.returned with
        | none => simp [restored,liftChecked] at ran
        | some t =>
          simp [restored,liftChecked] at ran
          cases ran
          rw [leave_slots s step.state step.returned t restored]
          exact long
    | branch e y n =>
      have parts : CoreCommand y = true ∧ CoreCommand n = true := by simpa [CoreCommand] using core
      simp only [command,runFuel,Bind.bind] at ran
      cases eval : (expr cycle e).eval s with
      | none => simp [eval,liftChecked,Outcome.bind] at ran
      | some pair =>
        obtain ⟨t,v⟩ := pair
        simp only [eval,liftChecked,Outcome.bind] at ran
        have nextLong : 16 ≤ ((t.release s).charge 1 0).slots.length := by
          change 16 ≤ t.slots.length
          rw [(expr_related e).slots s t v eval]
          exact long
        split at ran
        · exact ih n _ r parts.2 nextLong ran
        · exact ih y _ r parts.1 nextLong ran
    | whileLoop e b =>
      have bodyCore : CoreCommand b = true := core
      simp only [command,runFuel,Bind.bind] at ran
      cases eval : (expr cycle e).eval s with
      | none => simp [eval,liftChecked,Outcome.bind] at ran
      | some pair =>
        obtain ⟨t,v⟩ := pair
        simp only [eval,liftChecked,Outcome.bind] at ran
        have nextLong : 16 ≤ ((t.release s).charge 1 0).slots.length := by
          change 16 ≤ t.slots.length
          rw [(expr_related e).slots s t v eval]
          exact long
        split at ran
        · cases ran; exact nextLong
        · cases body : runFuel fuel (command cycle b) ((t.release s).charge 1 0) with
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
  | .finished step => .finished (permuteStep step)
  | .fault => .fault
  | .exhausted => .exhausted

theorem view_lift (q : Option NStep) : outcomeView (liftChecked q) = liftChecked (q.map permuteStep) := by
  cases q <;> rfl

theorem run_permute : ∀ fuel c s, CoreCommand c = true → 16 ≤ s.slots.length →
    outcomeView (runFuel fuel (command cycle c) s) = runFuel fuel c (permute s) := by
  intro fuel
  induction fuel with
  | zero => intro c s core long; rfl
  | succ fuel ih =>
    intro c s core long
    cases c with
    | primitive st =>
      rw [command,runFuel,runFuel,view_lift,stmt_commute st s long core]
    | sequence a b =>
      have parts : CoreCommand a = true ∧ CoreCommand b = true := by simpa [CoreCommand] using core
      have equal := ih a s parts.1 long
      simp only [command,runFuel,Bind.bind]
      cases first : runFuel fuel (command cycle a) s with
      | exhausted => simp only [first,outcomeView] at equal; simp [← equal,Outcome.bind,outcomeView]
      | fault => simp only [first,outcomeView] at equal; simp [← equal,Outcome.bind,outcomeView]
      | finished step =>
        simp only [first,outcomeView] at equal
        simp only [← equal,Outcome.bind,permuteStep]
        have nextLong := run_long fuel a s step parts.1 long first
        cases stop : (step.returned.isSome || step.breaking)
        · exact ih b step.state parts.2 nextLong
        · rfl
    | scope b =>
      have equal := ih b {s with scope := s.scope+1} core long
      rw [enter_permute] at equal
      simp only [command,runFuel,Bind.bind,scope_permute]
      cases body : runFuel fuel (command cycle b) {s with scope := s.scope+1} with
      | exhausted => simp only [body,outcomeView] at equal; simp [← equal,Outcome.bind,outcomeView]
      | fault => simp only [body,outcomeView] at equal; simp [← equal,Outcome.bind,outcomeView]
      | finished step =>
        simp only [body,outcomeView] at equal
        simp only [← equal,Outcome.bind,permuteStep]
        have leave := leave_permute s step.state step.returned
        cases restored : s.leave step.state step.returned with
        | none => simp only [restored,Option.map_none] at leave; simp [← leave,liftChecked,outcomeView]
        | some t =>
          simp only [restored,Option.map_some] at leave
          simp [← leave,liftChecked,outcomeView,permuteStep] <;> rfl
    | branch e y n =>
      have parts : CoreCommand y = true ∧ CoreCommand n = true := by simpa [CoreCommand] using core
      have equal := expr_eval_permute s long e
      simp only [command,runFuel,Bind.bind]
      cases evaluated : (expr cycle e).eval s with
      | none => simp only [evaluated,Option.map_none] at equal; simp [← equal,liftChecked,Outcome.bind,outcomeView]
      | some pair =>
        obtain ⟨t,v⟩ := pair
        simp only [evaluated,Option.map_some] at equal
        simp only [← equal,liftChecked,Outcome.bind]
        rw [← release_permute,← charge_permute]
        have nextLong : 16 ≤ ((t.release s).charge 1 0).slots.length := by
          change 16 ≤ t.slots.length
          rw [(expr_related e).slots s t v evaluated]
          exact long
        by_cases zero : v = 0 <;> simp only [beq_iff_eq,zero,ite_true,ite_false]
        · exact ih n _ parts.2 nextLong
        · exact ih y _ parts.1 nextLong
    | whileLoop e b =>
      have equal := expr_eval_permute s long e
      simp only [command,runFuel,Bind.bind]
      cases evaluated : (expr cycle e).eval s with
      | none => simp only [evaluated,Option.map_none] at equal; simp [← equal,liftChecked,Outcome.bind,outcomeView]
      | some pair =>
        obtain ⟨t,v⟩ := pair
        simp only [evaluated,Option.map_some] at equal
        simp only [← equal,liftChecked,Outcome.bind]
        rw [← release_permute,← charge_permute]
        have nextLong : 16 ≤ ((t.release s).charge 1 0).slots.length := by
          change 16 ≤ t.slots.length
          rw [(expr_related e).slots s t v evaluated]
          exact long
        by_cases zero : v = 0 <;> simp only [beq_iff_eq,zero,ite_true,ite_false]
        · rfl
        · have bodyEq := ih b ((t.release s).charge 1 0) core nextLong
          cases body : runFuel fuel (command cycle b) ((t.release s).charge 1 0) with
          | exhausted => simp only [body,outcomeView] at bodyEq; simp [← bodyEq,outcomeView]
          | fault => simp only [body,outcomeView] at bodyEq; simp [← bodyEq,outcomeView]
          | finished step =>
            simp only [body,outcomeView] at bodyEq
            simp only [← bodyEq,permuteStep]
            have bodyLong := run_long fuel b _ step core nextLong body
            cases returned : step.returned.isSome
            · cases breaking : step.breaking
              · exact ih (.whileLoop e b) step.state core bodyLong
              · rfl
            · rfl
    | breakLoop => rfl
    | invokeScalar _ _ => simp [CoreCommand] at core

end Proofs.BeatsSlotCycle
