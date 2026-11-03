import Proofs.DynamicOwnedRuns
import Proofs.DynamicResultScope

namespace Proofs.DynamicResultRuns
open Proofs.CppNestedProgram Proofs.DynamicOwnedState Proofs.DynamicExpr
open Proofs.CppLoop (Outcome liftChecked)

structure Step where
  state : State
  returned : Option Ret := none
  breaking : Bool := false

structure Matches (p : Step) (a : NStep) : Prop where
  state : Realizes p.state a.state
  returned : a.returned = p.returned
  breaking : a.breaking = p.breaking

def ofOwned (p : DynamicOwnedControl.Step) : Step := ⟨p.state,p.returned.map Ret.scalar,p.breaking⟩

-- This is a coupled Hoare execution certificate, not an unchecked extension
-- of the pure interpreter: each reached append must supply its actual room.
def Runs (command : Command) (st : State) (s : NState) (Q : Step → NStep → Prop) : Prop :=
  Realizes st s ∧ Proofs.CppNestedHoare.RunsTo command s (fun a => ∃ p, Matches p a ∧ Q p a)

theorem Runs.mono {command : Command} {st : State} {s : NState} {P Q : Step → NStep → Prop}
    (run : Runs command st s P) (weaker : ∀ p a, P p a → Q p a) : Runs command st s Q := by
  refine ⟨run.1,run.2.mono ?_⟩
  rintro a ⟨p,matched,post⟩
  exact ⟨p,matched,weaker p a post⟩

theorem Runs.inspect {command : Command} {st : State} {s : NState} {Q : Step → NStep → Prop}
    (run : Runs command st s Q) : Runs command st s (fun p a => Matches p a ∧ Q p a) :=
  ⟨run.1,run.2.mono (fun a ⟨p,matched,post⟩ => ⟨p,matched,matched,post⟩)⟩

theorem Runs.identify {command : Command} {st : State} {s : NState} {Q : Step → NStep → Prop}
    (run : Runs command st s Q) (fuel : Nat) (actual : NStep)
    (ran : CppNestedProgram.runFuel fuel command s = .finished actual) :
    Runs command st s (fun p a => a = actual ∧ Q p a) := by
  obtain ⟨real,otherFuel,a,executed,p,matched,post⟩ := run
  have same := Proofs.CppNestedHoare.runFuel_success_unique otherFuel fuel command s a actual executed ran
  exact ⟨real,otherFuel,a,executed,p,matched,same,post⟩

-- Reuse the existing scalar/constructor certificates without weakening their
-- strong state relation or dropping any resource postconditions.
theorem Runs.lift {command : Command} {st : State} {s : NState}
    {P : DynamicOwnedControl.Step → NStep → Prop} {Q : Step → NStep → Prop}
    (run : DynamicOwnedRuns.Runs command st s P) (post : ∀ p a, P p a → Q (ofOwned p) a) :
    Runs command st s Q := by
  refine ⟨run.1,run.2.mono ?_⟩
  rintro a ⟨p,matched,good⟩
  exact ⟨ofOwned p,⟨matched.state,matched.returned,matched.breaking⟩,post p a good⟩

theorem Runs.control (st : State) (s : NState) (real : Realizes st s) (command : Command)
    (fuel : Nat) (p : DynamicOwnedControl.Step) (pureRun : DynamicOwnedControl.runFuel fuel command st = .finished p) :
    Runs command st s (fun q _ => q = ofOwned p) :=
  Runs.lift (DynamicOwnedRuns.Runs.control st s real command fuel p pureRun) (fun _ _ same => congrArg ofOwned same)

theorem Runs.primitive (st : State) (s : NState) (real : Realizes st s) (stmt : NStmt) (p : DynamicOwnedControl.Step)
    (pureRun : DynamicOwnedControl.primitive stmt st = some p) :
    Runs (.primitive stmt) st s (fun q _ => q = ofOwned p) :=
  Runs.lift (DynamicOwnedRuns.Runs.primitive st s real stmt p pureRun) (fun _ _ same => congrArg ofOwned same)

theorem Runs.retVector (st : State) (s : NState) (real : Realizes st s) (slot : Nat) (value : Ret)
    (pureRun : DynamicVectorReturn.run st slot = some value) :
    Runs (.primitive (.retVector slot)) st s (fun p a => p = ⟨st,some value,false⟩ ∧ a.state.work = s.work+1) := by
  obtain ⟨ran,after,work⟩ := DynamicVectorReturn.sound st s real slot value pureRun
  exact ⟨real,Proofs.CppNestedHoare.RunsTo.primitive ran ⟨⟨st,some value,false⟩,⟨after,rfl,rfl⟩,rfl,work⟩⟩

theorem Runs.append (st : State) (s : NState) (real : Realizes st s) (stmt : NStmt) (final : State)
    (pureRun : DynamicOwnedAppend.run stmt st = some final)
    (room : DynamicOwnedAppend.Available st s stmt) :
    Runs (.primitive stmt) st s (fun p _ => p = ⟨final,none,false⟩) := by
  obtain ⟨out,ran,after⟩ := DynamicOwnedAppend.sound st s real stmt final pureRun room
  exact ⟨real,Proofs.CppNestedHoare.RunsTo.primitive ran ⟨⟨final,none,false⟩,⟨after,rfl,rfl⟩,rfl⟩⟩

theorem Runs.breakLoop (st : State) (s : NState) (real : Realizes st s) :
    Runs .breakLoop st s (fun p _ => p = ⟨st,none,true⟩) :=
  Runs.control st s real .breakLoop 1 ⟨st,none,true⟩ rfl

theorem Runs.sequence {first rest : Command} {st : State} {s : NState} {Q : Step → NStep → Prop}
    (run : Runs first st s fun p a =>
      ((p.returned.isSome = true ∨ p.breaking = true) ∧ Q p a) ∨
      (p.returned = none ∧ p.breaking = false ∧ Runs rest p.state a.state Q)) :
    Runs (.sequence first rest) st s Q := by
  refine ⟨run.1,Proofs.CppNestedHoare.RunsTo.sequence (run.2.mono ?_)⟩
  rintro a ⟨p,matched,paths⟩
  rcases paths with ⟨stop,post⟩ | ⟨ret,br,tail⟩
  · have halted : a.returned.isSome = true ∨ a.breaking = true ∧ True := by
      rcases stop with r | b
      · exact Or.inl (by simpa [matched.returned] using r)
      · exact Or.inr ⟨matched.breaking.trans b,True.intro⟩
    exact Or.inl ⟨halted,p,matched,post⟩
  · exact Or.inr ⟨by simp [matched.returned,ret],matched.breaking.trans br,tail.2⟩

theorem Runs.seq {first rest : Command} {st : State} {s : NState} {Q : Step → NStep → Prop}
    (run : Runs first st s fun p a => p.returned = none ∧ p.breaking = false ∧ Runs rest p.state a.state Q) :
    Runs (.sequence first rest) st s Q := Runs.sequence (run.mono fun _ _ post => Or.inr post)

theorem Runs.scope {body : Command} {st : State} {s : NState} {Q : Step → NStep → Prop}
    (real : Realizes st s)
    (run : Runs body (DynamicOwnedCleanup.enter st) {s with scope := s.scope+1} fun p a =>
      ∃ final, DynamicResultScope.leave st p.state p.returned = some final ∧
        ∀ out, s.leave a.state a.returned = some out → Q {p with state := final} {a with state := out}) :
    Runs (.scope body) st s Q := by
  refine ⟨real,Proofs.CppNestedHoare.RunsTo.scope (run.2.mono ?_)⟩
  rintro a ⟨p,matched,final,left,post⟩
  obtain ⟨out,done,after⟩ := DynamicResultScope.sound st p.state final s a.state real matched.state p.returned left
  have actual : s.leave a.state a.returned = some out := by rw [matched.returned]; exact done
  exact ⟨out,actual,{p with state := final},⟨after,matched.returned,matched.breaking⟩,post out actual⟩

theorem Runs.branch {condition : NExpr} {yes no : Command} {st : State} {s : NState}
    {v : Int} {Q : Step → NStep → Prop} (real : Realizes st s)
    (value : denote st.params st.core.locals st.core.contents condition = some v)
    (branches : ∀ next, condition.eval s = some (next,v) → Realizes st ((next.release s).charge 1 0) →
      Runs (if v = 0 then no else yes) st ((next.release s).charge 1 0) Q) :
    Runs (.branch condition yes no) st s Q := by
  obtain ⟨next,eval,after⟩ := DynamicOwnedControl.guard st s real condition v value
  exact ⟨real,Proofs.CppNestedHoare.RunsTo.branch eval (branches next eval after).2⟩

-- Room and resource witnesses may be part of I. Only continuing iterations
-- must decrease the ghost counter; a return or break can occur at zero.
theorem Runs.whileGhostStop {condition : NExpr} {body : Command}
    (I : Nat → State → NState → Prop) (Q : Step → NStep → Prop)
    (step : ∀ g st s, Realizes st s → I g st s →
      ∃ v, denote st.params st.core.locals st.core.contents condition = some v ∧
      ∀ next, condition.eval s = some (next,v) → Realizes st ((next.release s).charge 1 0) →
        (v = 0 → Q ⟨st,none,false⟩ ⟨(next.release s).charge 1 0,none,false⟩) ∧
        (v ≠ 0 → Runs body st ((next.release s).charge 1 0) fun p a =>
          (p.returned.isSome = true ∧ Q p a) ∨
          (p.returned = none ∧ ((p.breaking = true ∧ Q {p with breaking := false} {a with breaking := false}) ∨
            (p.breaking = false ∧ ∃ g', g' < g ∧ I g' p.state a.state))))) :
    ∀ g st s, Realizes st s → I g st s → Runs (.whileLoop condition body) st s Q := by
  intro g
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro st s real initial
    obtain ⟨v,value,paths⟩ := step g st s real initial
    obtain ⟨next,evaluated,after⟩ := DynamicOwnedControl.guard st s real condition v value
    obtain ⟨exit,continues⟩ := paths next evaluated after
    refine ⟨real,?_⟩
    by_cases zero : v = 0
    · exact ⟨1,⟨(next.release s).charge 1 0,none,false⟩,by simp [CppNestedProgram.runFuel,evaluated,zero,liftChecked,bind,pure,Outcome.bind],⟨st,none,false⟩,⟨after,rfl,rfl⟩,exit zero⟩
    · obtain ⟨_,fuel,a,ran,p,matched,post⟩ := continues zero
      rcases post with ⟨ret,good⟩ | ⟨ret,⟨br,good⟩ | ⟨br,g',less,inv⟩⟩
      · have actualRet : a.returned.isSome = true := by simpa [matched.returned] using ret
        exact ⟨fuel+1,a,by simp [CppNestedProgram.runFuel,evaluated,zero,ran,actualRet,liftChecked,bind,pure,Outcome.bind],p,matched,good⟩
      · have actualRet : a.returned = none := by simp [matched.returned,ret]
        have actualBr : a.breaking = true := matched.breaking.trans br
        exact ⟨fuel+1,{a with breaking := false},by simp [CppNestedProgram.runFuel,evaluated,zero,ran,actualRet,actualBr,liftChecked,bind,pure,Outcome.bind],{p with breaking := false},⟨matched.state,matched.returned,rfl⟩,good⟩
      · obtain ⟨_,tailFuel,last,tailRun,q,lastMatch,good⟩ := ih g' less p.state a.state matched.state inv
        have first := Proofs.CppNestedHoare.runFuel_success_mono fuel tailFuel body ((next.release s).charge 1 0) a ran
        have rest := Proofs.CppNestedHoare.runFuel_success_mono tailFuel fuel (.whileLoop condition body) a.state last tailRun
        rw [Nat.add_comm tailFuel fuel] at rest
        have actualRet : a.returned = none := by simp [matched.returned,ret]
        have actualBr : a.breaking = false := matched.breaking.trans br
        exact ⟨fuel+tailFuel+1,last,by simp [CppNestedProgram.runFuel,evaluated,zero,first,actualRet,actualBr,rest,liftChecked,bind,pure,Outcome.bind],q,lastMatch,good⟩

end Proofs.DynamicResultRuns
