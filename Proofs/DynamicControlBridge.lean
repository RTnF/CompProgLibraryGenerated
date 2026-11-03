import Proofs.DynamicControlHoare
import Proofs.DynamicAppendValue
import Proofs.CppNestedHoare

namespace Proofs.DynamicControlBridge
open Proofs.CppNestedProgram Proofs.DynamicControl Proofs.MultiVecDynamic
open Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicExprDerive Proofs.DynamicExprCertified
open Proofs.CppLoop (Outcome liftChecked)

structure Matches (params : List Parameter) (pure : Step) (actual : NStep) : Prop where
  state : Realizes params pure.state.locals pure.state.contents actual.state
  returned : actual.returned = pure.returned.map Ret.scalar
  breaking : actual.breaking = pure.breaking

-- Coupled postconditions can retain allocation witnesses and amortised
-- potentials instead of quantifying them away between successive operations.
def Runs (params : List Parameter) (command : Command) (st : DynamicStmt.State) (s : NState)
    (Q : Step → NStep → Prop) : Prop :=
  ∃ pure actual, DynamicControlHoare.Runs params command st (· = pure) ∧
    CppNestedHoare.RunsTo command s (· = actual) ∧ Matches params pure actual ∧ Q pure actual

theorem Runs.mono {params : List Parameter} {command : Command} {st : DynamicStmt.State} {s : NState}
    {P Q : Step → NStep → Prop} (run : Runs params command st s P)
    (weaker : ∀ pure actual, P pure actual → Q pure actual) : Runs params command st s Q := by
  obtain ⟨pure,actual,p,a,m,post⟩ := run
  exact ⟨pure,actual,p,a,m,weaker pure actual post⟩

theorem Runs.inspect {params : List Parameter} {command : Command} {st : DynamicStmt.State} {s : NState}
    {Q : Step → NStep → Prop} (run : Runs params command st s Q) :
    Runs params command st s (fun pure actual => Matches params pure actual ∧ Q pure actual) := by
  obtain ⟨pure,actual,p,a,matched,post⟩ := run
  exact ⟨pure,actual,p,a,matched,matched,post⟩

theorem Runs.primitive {params : List Parameter} {stmt : NStmt} {st : DynamicStmt.State} {s : NState}
    {pure : DynamicStmt.Step} {actual : NStep} {Q : Step → NStep → Prop}
    (p : DynamicStmt.run params stmt st = some pure) (a : stmt.run s = some actual)
    (matched : DynamicScalarSound.Matches params pure actual) (post : Q (ofStmt pure) actual) :
    Runs params (.primitive stmt) st s Q :=
  ⟨ofStmt pure,actual,DynamicControlHoare.Runs.primitive p rfl,CppNestedHoare.RunsTo.primitive a rfl,
    ⟨matched.state,matched.returned,matched.breaking⟩,post⟩

theorem Runs.scalar {params : List Parameter} {stmt : NStmt} {st : DynamicStmt.State} {s : NState}
    (realizes : Realizes params st.locals st.contents s)
    (ready : DynamicScalarSound.ScalarReady params st stmt) (pure : DynamicStmt.Step)
    (run : DynamicStmt.run params stmt st = some pure) :
    Runs params (.primitive stmt) st s (fun final actual =>
      final = ofStmt pure ∧ actual.state.work ≤ s.work+DynamicScalarSound.workBound stmt ∧
      actual.state.peak ≤ max s.peak (max s.scalars.peak
        (Proofs.CppNestedEval.liveS s+DynamicScalarSound.tempBound stmt)+s.frame.state.storage.peak)) := by
  obtain ⟨actual,ran,matched,work,peak⟩ := DynamicScalarSound.sound params st s realizes stmt ready pure run
  exact Runs.primitive run ran matched ⟨rfl,work,peak⟩

theorem Runs.sequence {params : List Parameter} {first rest : Command} {st : DynamicStmt.State} {s : NState}
    {Q : Step → NStep → Prop}
    (run : Runs params first st s fun pure actual =>
      ((pure.returned.isSome = true ∨ pure.breaking = true) ∧ Q pure actual) ∨
      (pure.returned = none ∧ pure.breaking = false ∧ Runs params rest pure.state actual.state Q)) :
    Runs params (.sequence first rest) st s Q := by
  obtain ⟨pure,actual,p,a,matched,post⟩ := run
  rcases post with ⟨stop,good⟩ | ⟨ret,br,tail⟩
  · have stopActual : actual.returned.isSome = true ∨ actual.breaking = true ∧ True := by
      rcases stop with r | b
      · exact Or.inl (by simpa [matched.returned] using r)
      · exact Or.inr ⟨matched.breaking.trans b,True.intro⟩
    exact ⟨pure,actual,DynamicControlHoare.Runs.sequence (p.mono fun _ same => by subst_vars; exact Or.inl ⟨stop,rfl⟩),
      CppNestedHoare.RunsTo.sequence (a.mono fun _ same => by subst_vars; exact Or.inl ⟨stopActual,rfl⟩),matched,good⟩
  · obtain ⟨final,finalActual,p',a',matched',good⟩ := tail
    have actualRet : actual.returned = none := by simp [matched.returned,ret]
    have actualBr : actual.breaking = false := matched.breaking.trans br
    exact ⟨final,finalActual,DynamicControlHoare.Runs.seq (p.mono fun _ same => by subst_vars; exact ⟨ret,br,p'⟩),
      CppNestedHoare.RunsTo.seq (a.mono fun _ same => by subst_vars; exact ⟨actualRet,actualBr,a'⟩),matched',good⟩

theorem Runs.seq {params : List Parameter} {first rest : Command} {st : DynamicStmt.State} {s : NState}
    {Q : Step → NStep → Prop}
    (run : Runs params first st s fun pure actual => pure.returned = none ∧ pure.breaking = false ∧
      Runs params rest pure.state actual.state Q) : Runs params (.sequence first rest) st s Q :=
  Runs.sequence (run.mono fun _ _ post => Or.inr post)

-- The same pure guard value selects both branches. Its vector reads may use
-- temporary references; Ready supplies their lifetime and resource proofs.
theorem Runs.branch {params : List Parameter} {condition : NExpr} {yes no : Command}
    {st : DynamicStmt.State} {s : NState} {v : Int} {Q : Step → NStep → Prop}
    (realizes : Realizes params st.locals st.contents s) (ready : Ready params st.locals st.contents condition)
    (value : denote params st.locals st.contents condition = some v)
    (branches : ∀ next, condition.eval s = some (next,v) →
      Realizes params st.locals st.contents ((next.release s).charge 1 0) →
      Runs params (if v = 0 then no else yes) st ((next.release s).charge 1 0) Q) :
    Runs params (.branch condition yes no) st s Q := by
  obtain ⟨_,next,extra,ev⟩ := DynamicExprCertified.sound (derive ready v value) s realizes
  have preserved := (ev_preserves params st.locals st.contents s next realizes condition v extra _ _ ev).1
  obtain ⟨pure,actual,p,a,matched,good⟩ := branches next ev.1 preserved
  exact ⟨pure,actual,DynamicControlHoare.Runs.branch value p,CppNestedHoare.RunsTo.branch ev.1 a,matched,good⟩

-- Independent successful fuels can always be increased to one common fuel.
theorem Runs.aligned {params : List Parameter} {command : Command} {st : DynamicStmt.State} {s : NState}
    {Q : Step → NStep → Prop} (run : Runs params command st s Q) :
    ∃ fuel pure actual, DynamicControl.runFuel params fuel command st = .finished pure ∧
      CppNestedProgram.runFuel fuel command s = .finished actual ∧ Matches params pure actual ∧ Q pure actual := by
  obtain ⟨pure,actual,⟨pFuel,pStep,pRun,pEq⟩,⟨aFuel,aStep,aRun,aEq⟩,matched,post⟩ := run
  subst pStep
  subst aStep
  refine ⟨pFuel+aFuel,pure,actual,success_mono params pFuel aFuel command st pure pRun,?_,matched,post⟩
  rw [Nat.add_comm]
  exact CppNestedHoare.runFuel_success_mono aFuel pFuel command s actual aRun

theorem Runs.of_run {params : List Parameter} {command : Command} {st : DynamicStmt.State} {s : NState}
    {fuel : Nat} {pure : Step} {actual : NStep} {Q : Step → NStep → Prop}
    (p : DynamicControl.runFuel params fuel command st = .finished pure)
    (a : CppNestedProgram.runFuel fuel command s = .finished actual)
    (matched : Matches params pure actual) (post : Q pure actual) : Runs params command st s Q :=
  ⟨pure,actual,⟨fuel,pure,p,rfl⟩,⟨fuel,actual,a,rfl⟩,matched,post⟩

theorem Runs.scope {params : List Parameter} {body : Command} {st : DynamicStmt.State} {s : NState}
    {Q : Step → NStep → Prop}
    (run : Runs params body st {s with scope := s.scope+1} fun pure actual =>
      ∃ p a, leave st pure.state = some p ∧ s.leave actual.state actual.returned = some a ∧
        Matches params {pure with state := p} {actual with state := a} ∧
        Q {pure with state := p} {actual with state := a}) : Runs params (.scope body) st s Q := by
  obtain ⟨pure,actual,pRun,aRun,_,p,a,pLeft,aLeft,matched,post⟩ := run
  exact ⟨{pure with state := p},{actual with state := a},
    DynamicControlHoare.Runs.scope (pRun.mono fun _ same => by subst_vars; exact ⟨p,pLeft,rfl⟩),
    CppNestedHoare.RunsTo.scope (aRun.mono fun _ same => by subst_vars; exact ⟨a,aLeft,rfl⟩),matched,post⟩

-- Coupled loop invariants may retain concrete allocation witnesses and costs.
-- Only continuing iterations must decrease the ghost counter.
theorem Runs.whileGhostStop {params : List Parameter} {condition : NExpr} {body : Command}
    (I : Nat → DynamicStmt.State → NState → Prop) (Q : Step → NStep → Prop)
    (step : ∀ g st s, Realizes params st.locals st.contents s → I g st s →
      ∃ v, denote params st.locals st.contents condition = some v ∧ Ready params st.locals st.contents condition ∧
      ∀ next, condition.eval s = some (next,v) →
        Realizes params st.locals st.contents ((next.release s).charge 1 0) →
        (v = 0 → Q ⟨st,none,false⟩ ⟨(next.release s).charge 1 0,none,false⟩) ∧
        (v ≠ 0 → Runs params body st ((next.release s).charge 1 0) fun pure actual =>
          (pure.returned.isSome = true ∧ Q pure actual) ∨
          (pure.returned = none ∧ ((pure.breaking = true ∧ Q {pure with breaking := false} {actual with breaking := false}) ∨
            (pure.breaking = false ∧ ∃ g', g' < g ∧ I g' pure.state actual.state))))) :
    ∀ g st s, Realizes params st.locals st.contents s → I g st s →
      Runs params (.whileLoop condition body) st s Q := by
  intro g
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro st s realizes initial
    obtain ⟨v,value,ready,paths⟩ := step g st s realizes initial
    obtain ⟨_,next,extra,ev⟩ := DynamicExprCertified.sound (derive ready v value) s realizes
    have preserved := (ev_preserves params st.locals st.contents s next realizes condition v extra _ _ ev).1
    obtain ⟨exit,continues⟩ := paths next ev.1 preserved
    by_cases zero : v = 0
    · apply Runs.of_run (fuel := 1) (pure := ⟨st,none,false⟩) (actual := ⟨(next.release s).charge 1 0,none,false⟩)
      · simp [DynamicControl.runFuel,value,zero,liftChecked,bind,pure,Outcome.bind]
      · simp [CppNestedProgram.runFuel,ev.1,zero,liftChecked,bind,pure,Outcome.bind]
      · exact ⟨preserved,rfl,rfl⟩
      · exact exit zero
    · obtain ⟨fuel,p,a,pRun,aRun,matched,post⟩ := (continues zero).aligned
      rcases post with ⟨ret,good⟩ | ⟨ret,⟨br,good⟩ | ⟨br,g',less,inv⟩⟩
      · have aRet : a.returned.isSome = true := by simpa [matched.returned] using ret
        apply Runs.of_run (fuel := fuel+1) (pure := p) (actual := a)
        · simpa [DynamicControl.runFuel,value,zero,pRun,ret,liftChecked,bind,pure,Outcome.bind]
        · simpa [CppNestedProgram.runFuel,ev.1,zero,aRun,aRet,liftChecked,bind,pure,Outcome.bind]
        · exact matched
        · exact good
      · have aRet : a.returned = none := by simp [matched.returned,ret]
        have aBr : a.breaking = true := matched.breaking.trans br
        apply Runs.of_run (fuel := fuel+1) (pure := {p with breaking := false}) (actual := {a with breaking := false})
        · simpa [DynamicControl.runFuel,value,zero,pRun,ret,br,liftChecked,bind,pure,Outcome.bind]
        · simpa [CppNestedProgram.runFuel,ev.1,zero,aRun,aRet,aBr,liftChecked,bind,pure,Outcome.bind]
        · exact ⟨matched.state,matched.returned,rfl⟩
        · exact good
      · obtain ⟨tailFuel,final,actualFinal,tailP,tailA,matched',post⟩ := (ih g' less p.state a.state matched.state inv).aligned
        have pFirst := success_mono params fuel tailFuel body st p pRun
        have aFirst := CppNestedHoare.runFuel_success_mono fuel tailFuel body ((next.release s).charge 1 0) a aRun
        have pRest := success_mono params tailFuel fuel (.whileLoop condition body) p.state final tailP
        have aRest := CppNestedHoare.runFuel_success_mono tailFuel fuel (.whileLoop condition body) a.state actualFinal tailA
        rw [Nat.add_comm tailFuel fuel] at pRest aRest
        have aRet : a.returned = none := by simp [matched.returned,ret]
        have aBr : a.breaking = false := matched.breaking.trans br
        apply Runs.of_run (fuel := fuel+tailFuel+1) (pure := final) (actual := actualFinal)
        · simp [DynamicControl.runFuel,value,zero,pFirst,ret,br,pRest,liftChecked,bind,pure,Outcome.bind]
        · simp [CppNestedProgram.runFuel,ev.1,zero,aFirst,aRet,aBr,aRest,liftChecked,bind,pure,Outcome.bind]
        · exact matched'
        · exact post

end Proofs.DynamicControlBridge
