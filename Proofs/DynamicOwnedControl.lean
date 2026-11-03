import Proofs.DynamicOwnedCleanup
import Proofs.DynamicOwnedScalar

namespace Proofs.DynamicOwnedControl
open Proofs.CppNestedProgram Proofs.DynamicExpr Proofs.DynamicOwnedState
open Proofs.CppLoop (Outcome liftChecked)

structure Step where
  state : State
  returned : Option Int := none
  breaking : Bool := false

structure Matches (p : Step) (a : NStep) : Prop where
  state : Realizes p.state a.state
  returned : a.returned = p.returned.map Ret.scalar
  breaking : a.breaking = p.breaking

def primitive (stmt : NStmt) (st : State) : Option Step := match stmt with
  | .skip | .declare _ _ _ | .assign _ _ _ | .ret _ | .check _ => do
      let final ← DynamicStmt.run st.params stmt st.core
      some ⟨{st with core := final.state},final.returned,false⟩
  | other => do
      let final ← runConstruct other st
      some ⟨final,none,false⟩

def runFuel : Nat → Command → State → Outcome Step
  | 0,_,_ => .exhausted
  | fuel+1,command,st => match command with
    | .primitive stmt => liftChecked (primitive stmt st)
    | .sequence first rest => do
        let p ← runFuel fuel first st
        if p.returned.isSome || p.breaking then pure p else runFuel fuel rest p.state
    | .scope body => do
        let p ← runFuel fuel body (DynamicOwnedCleanup.enter st)
        let final ← liftChecked (DynamicOwnedCleanup.leave st p.state)
        pure {p with state := final}
    | .branch condition yes no => do
        let v ← liftChecked (denote st.params st.core.locals st.core.contents condition)
        if v = 0 then runFuel fuel no st else runFuel fuel yes st
    | .whileLoop condition body => do
        let v ← liftChecked (denote st.params st.core.locals st.core.contents condition)
        if v = 0 then pure ⟨st,none,false⟩ else do
          let p ← runFuel fuel body st
          if p.returned.isSome then pure p
          else if p.breaking then pure {p with breaking := false}
          else runFuel fuel (.whileLoop condition body) p.state
    | .breakLoop => pure ⟨st,none,true⟩
    | .invokeScalar _ _ => .fault

theorem primitive_sound (st : State) (s : NState) (real : Realizes st s) (stmt : NStmt) (p : Step)
    (pure : primitive stmt st = some p) : ∃ a, stmt.run s = some a ∧ Matches p a := by
  cases stmt with
  | skip | declare _ _ _ | assign _ _ _ | ret _ | check _ =>
    simp only [primitive] at pure
    obtain ⟨final,scalar,same⟩ := DynamicResultValid.bind_some _ _ _ pure
    have equal := Option.some.inj same
    subst p
    obtain ⟨out,ran,after,returned,breaking,_⟩ := DynamicOwnedScalar.sound st s real _ (by trivial) final scalar
    exact ⟨out,ran,⟨after,returned,breaking⟩⟩
  | _ =>
    simp only [primitive] at pure
    obtain ⟨final,constructed,same⟩ := DynamicResultValid.bind_some _ _ _ pure
    have equal := Option.some.inj same
    subst p
    obtain ⟨out,ran,after⟩ := DynamicOwnedConstruct.sound st s real _ final constructed
    exact ⟨⟨out,none,false⟩,ran,⟨after,rfl,rfl⟩⟩

theorem guard (st : State) (s : NState) (real : Realizes st s) (condition : NExpr) (v : Int)
    (pure : denote st.params st.core.locals st.core.contents condition = some v) :
    ∃ next, condition.eval s = some (next,v) ∧ Realizes st ((next.release s).charge 1 0) := by
  obtain ⟨_,next,extra,ev⟩ := DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) v pure) s real.data
  have data := (Proofs.DynamicRealizes.ev_preserves st.params st.core.locals st.core.contents s next real.data condition v extra _ _ ev).1
  refine ⟨next,ev.1,⟨data,?_,?_,?_⟩⟩
  · change next.frame.state.storage.objects.length = st.nextOwner
    rw [ev.2.1.1,real.owner]
  · change (next.release s).frame.bindings.length = st.nextBinding
    rw [DynamicConstructCore.release_bindings s next extra ev.2.2,real.binding]
  · change next.scope = st.scope
    exact ev.2.1.2.2.2.1.trans real.scopedState

theorem sound (fuel : Nat) (command : Command) (st : State) (s : NState) (real : Realizes st s) (p : Step)
    (pureRun : runFuel fuel command st = .finished p) :
    ∃ a, CppNestedProgram.runFuel fuel command s = .finished a ∧ Matches p a := by
  induction fuel generalizing command st s p with
  | zero => simp [runFuel] at pureRun
  | succ fuel ih =>
    cases command with
    | primitive stmt =>
      cases ran : primitive stmt st with
      | none => simp [runFuel,ran,liftChecked] at pureRun
      | some q =>
        have same : q = p := by simpa [runFuel,ran,liftChecked] using pureRun
        subst q
        obtain ⟨a,actual,matched⟩ := primitive_sound st s real stmt p ran
        exact ⟨a,by simp [CppNestedProgram.runFuel,actual,liftChecked],matched⟩
    | breakLoop =>
      have same : (⟨st,none,true⟩ : Step) = p := by simpa [runFuel,pure] using pureRun
      subst p
      exact ⟨⟨s.charge 1 0,none,true⟩,rfl,⟨⟨⟨real.data.locals,real.data.heap⟩,real.owner,real.binding,real.scopedState⟩,rfl,rfl⟩⟩
    | invokeScalar _ _ => simp [runFuel] at pureRun
    | sequence first rest =>
      cases firstRun : runFuel fuel first st with
      | fault => simp [runFuel,firstRun,bind,Outcome.bind] at pureRun
      | exhausted => simp [runFuel,firstRun,bind,Outcome.bind] at pureRun
      | finished q =>
        obtain ⟨a,actual,matched⟩ := ih first st s real q firstRun
        by_cases stop : (q.returned.isSome || q.breaking) = true
        · have same : q = p := by simpa [runFuel,firstRun,stop,bind,pure,Outcome.bind] using pureRun
          subst p
          have stopped : (a.returned.isSome || a.breaking) = true := by simpa [matched.returned,matched.breaking] using stop
          exact ⟨a,by simp [CppNestedProgram.runFuel,actual,stopped,bind,pure,Outcome.bind],matched⟩
        · have tail : runFuel fuel rest q.state = .finished p := by simpa [runFuel,firstRun,stop,bind,Outcome.bind] using pureRun
          obtain ⟨last,tailRun,lastMatch⟩ := ih rest q.state a.state matched.state p tail
          have continues : (a.returned.isSome || a.breaking) ≠ true := by simpa [matched.returned,matched.breaking] using stop
          exact ⟨last,by simp [CppNestedProgram.runFuel,actual,continues,tailRun,bind,Outcome.bind],lastMatch⟩
    | scope body =>
      cases bodyRun : runFuel fuel body (DynamicOwnedCleanup.enter st) with
      | fault => simp [runFuel,bodyRun,bind,Outcome.bind] at pureRun
      | exhausted => simp [runFuel,bodyRun,bind,Outcome.bind] at pureRun
      | finished q =>
        cases left : DynamicOwnedCleanup.leave st q.state with
        | none => simp [runFuel,bodyRun,left,liftChecked,bind,Outcome.bind] at pureRun
        | some final =>
          have same : {q with state := final} = p := by simpa [runFuel,bodyRun,left,liftChecked,bind,pure,Outcome.bind] using pureRun
          subst p
          obtain ⟨a,actual,matched⟩ := ih body (DynamicOwnedCleanup.enter st) {s with scope := s.scope+1} (DynamicOwnedCleanup.enter_real st s real) q bodyRun
          obtain ⟨done,restored,_⟩ := DynamicOwnedCleanup.sound st q.state final s a.state real matched.state q.returned left
          have actualLeft : s.leave a.state a.returned = some (DynamicOwnedScope.left s a.state) := by rw [matched.returned]; exact done
          exact ⟨{a with state := DynamicOwnedScope.left s a.state},by simp [CppNestedProgram.runFuel,actual,actualLeft,liftChecked,bind,pure,Outcome.bind],⟨restored,matched.returned,matched.breaking⟩⟩
    | branch condition yes no =>
      cases value : denote st.params st.core.locals st.core.contents condition with
      | none => simp [runFuel,value,liftChecked,bind,Outcome.bind] at pureRun
      | some v =>
        obtain ⟨next,evaluated,after⟩ := guard st s real condition v value
        by_cases zero : v = 0
        · have tail : runFuel fuel no st = .finished p := by simpa [runFuel,value,zero,liftChecked,bind,Outcome.bind] using pureRun
          obtain ⟨a,actual,matched⟩ := ih no st ((next.release s).charge 1 0) after p tail
          exact ⟨a,by simp [CppNestedProgram.runFuel,evaluated,zero,actual,liftChecked,bind,Outcome.bind],matched⟩
        · have tail : runFuel fuel yes st = .finished p := by simpa [runFuel,value,zero,liftChecked,bind,Outcome.bind] using pureRun
          obtain ⟨a,actual,matched⟩ := ih yes st ((next.release s).charge 1 0) after p tail
          exact ⟨a,by simp [CppNestedProgram.runFuel,evaluated,zero,actual,liftChecked,bind,Outcome.bind],matched⟩
    | whileLoop condition body =>
      cases value : denote st.params st.core.locals st.core.contents condition with
      | none => simp [runFuel,value,liftChecked,bind,Outcome.bind] at pureRun
      | some v =>
        obtain ⟨next,evaluated,after⟩ := guard st s real condition v value
        by_cases zero : v = 0
        · have same : (⟨st,none,false⟩ : Step) = p := by simpa [runFuel,value,zero,liftChecked,bind,pure,Outcome.bind] using pureRun
          subst p
          exact ⟨⟨(next.release s).charge 1 0,none,false⟩,by simp [CppNestedProgram.runFuel,evaluated,zero,liftChecked,bind,pure,Outcome.bind],⟨after,rfl,rfl⟩⟩
        · cases bodyRun : runFuel fuel body st with
          | fault => simp [runFuel,value,zero,bodyRun,liftChecked,bind,Outcome.bind] at pureRun
          | exhausted => simp [runFuel,value,zero,bodyRun,liftChecked,bind,Outcome.bind] at pureRun
          | finished q =>
            obtain ⟨a,actual,matched⟩ := ih body st ((next.release s).charge 1 0) after q bodyRun
            by_cases ret : q.returned.isSome = true
            · have same : q = p := by simpa [runFuel,value,zero,bodyRun,ret,liftChecked,bind,pure,Outcome.bind] using pureRun
              subst p
              have actualRet : a.returned.isSome = true := by simpa [matched.returned] using ret
              exact ⟨a,by simp [CppNestedProgram.runFuel,evaluated,zero,actual,actualRet,liftChecked,bind,pure,Outcome.bind],matched⟩
            · by_cases br : q.breaking = true
              · have same : {q with breaking := false} = p := by simpa [runFuel,value,zero,bodyRun,ret,br,liftChecked,bind,pure,Outcome.bind] using pureRun
                subst p
                have actualRet : a.returned.isSome = false := by cases returned : q.returned <;> simp_all [matched.returned]
                have actualBr : a.breaking = true := matched.breaking.trans br
                exact ⟨{a with breaking := false},by simp [CppNestedProgram.runFuel,evaluated,zero,actual,actualRet,actualBr,liftChecked,bind,pure,Outcome.bind],⟨matched.state,matched.returned,rfl⟩⟩
              · have tail : runFuel fuel (.whileLoop condition body) q.state = .finished p := by simpa [runFuel,value,zero,bodyRun,ret,br,liftChecked,bind,Outcome.bind] using pureRun
                obtain ⟨last,tailRun,lastMatch⟩ := ih (.whileLoop condition body) q.state a.state matched.state p tail
                have actualRet : a.returned.isSome = false := by cases returned : q.returned <;> simp_all [matched.returned]
                have actualBr : a.breaking = false := by simpa [matched.breaking] using br
                exact ⟨last,by simp [CppNestedProgram.runFuel,evaluated,zero,actual,actualRet,actualBr,tailRun,liftChecked,bind,Outcome.bind],lastMatch⟩

end Proofs.DynamicOwnedControl
