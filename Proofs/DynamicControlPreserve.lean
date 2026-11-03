import Proofs.DynamicPreserve

namespace Proofs.DynamicControlPreserve
open Proofs.CppNestedProgram Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicPreserve
open Proofs.DynamicControl Proofs.CppLoop

theorem run (params : List Parameter) (fuel : Nat) (command : Command) (st : DynamicStmt.State) (out : Step)
    (success : DynamicControl.runFuel params fuel command st = .finished out) : Preserved st out.state := by
  induction fuel generalizing command st out with
  | zero => simp [DynamicControl.runFuel] at success
  | succ fuel ih =>
    cases command with
    | primitive stmt =>
      cases ran : DynamicStmt.run params stmt st with
      | none => simp [DynamicControl.runFuel,ran,liftChecked,bind,Outcome.bind] at success
      | some result =>
        have same : ofStmt result = out := by simpa [DynamicControl.runFuel,ran,liftChecked,bind,pure,Outcome.bind] using success
        subst out
        exact primitive params st stmt result ran
    | breakLoop =>
      have same : (⟨st,none,true⟩ : Step) = out := by simpa [DynamicControl.runFuel,pure] using success
      subst out; exact Preserved.refl st
    | invokeScalar _ _ => simp [DynamicControl.runFuel] at success
    | sequence first rest =>
      cases ran : DynamicControl.runFuel params fuel first st with
      | fault => simp [DynamicControl.runFuel,ran,bind,Outcome.bind] at success
      | exhausted => simp [DynamicControl.runFuel,ran,bind,Outcome.bind] at success
      | finished middle =>
        have firstPres := ih first st middle ran
        by_cases stop : (middle.returned.isSome || middle.breaking) = true
        · have same : middle = out := by simpa [DynamicControl.runFuel,ran,stop,bind,pure,Outcome.bind] using success
          subst out; exact firstPres
        · have tail : DynamicControl.runFuel params fuel rest middle.state = .finished out := by
            simpa [DynamicControl.runFuel,ran,stop,bind,Outcome.bind] using success
          exact firstPres.trans (ih rest middle.state out tail)
    | scope body =>
      cases ran : DynamicControl.runFuel params fuel body st with
      | fault => simp [DynamicControl.runFuel,ran,bind,Outcome.bind] at success
      | exhausted => simp [DynamicControl.runFuel,ran,bind,Outcome.bind] at success
      | finished middle =>
        cases left : DynamicControl.leave st middle.state with
        | none => simp [DynamicControl.runFuel,ran,left,liftChecked,bind,Outcome.bind] at success
        | some final =>
          have same : {middle with state := final} = out := by simpa [DynamicControl.runFuel,ran,left,liftChecked,bind,pure,Outcome.bind] using success
          subst out
          exact DynamicPreserve.leave st middle.state final (ih body st middle ran).1 left
    | branch condition yes no =>
      cases value : denote params st.locals st.contents condition with
      | none => simp [DynamicControl.runFuel,value,liftChecked,bind,Outcome.bind] at success
      | some v =>
        by_cases zero : v = 0
        · have ran : DynamicControl.runFuel params fuel no st = .finished out := by
            simpa [DynamicControl.runFuel,value,zero,liftChecked,bind,Outcome.bind] using success
          exact ih no st out ran
        · have ran : DynamicControl.runFuel params fuel yes st = .finished out := by
            simpa [DynamicControl.runFuel,value,zero,liftChecked,bind,Outcome.bind] using success
          exact ih yes st out ran
    | whileLoop condition body =>
      cases value : denote params st.locals st.contents condition with
      | none => simp [DynamicControl.runFuel,value,liftChecked,bind,Outcome.bind] at success
      | some v =>
        by_cases zero : v = 0
        · have same : (⟨st,none,false⟩ : Step) = out := by simpa [DynamicControl.runFuel,value,zero,liftChecked,bind,pure,Outcome.bind] using success
          subst out; exact Preserved.refl st
        · cases ran : DynamicControl.runFuel params fuel body st with
          | fault => simp [DynamicControl.runFuel,value,zero,ran,liftChecked,bind,Outcome.bind] at success
          | exhausted => simp [DynamicControl.runFuel,value,zero,ran,liftChecked,bind,Outcome.bind] at success
          | finished middle =>
            have bodyPres := ih body st middle ran
            by_cases ret : middle.returned.isSome = true
            · have same : middle = out := by simpa [DynamicControl.runFuel,value,zero,ran,ret,liftChecked,bind,pure,Outcome.bind] using success
              subst out; exact bodyPres
            · by_cases br : middle.breaking = true
              · have same : {middle with breaking := false} = out := by simpa [DynamicControl.runFuel,value,zero,ran,ret,br,liftChecked,bind,pure,Outcome.bind] using success
                subst out; exact bodyPres
              · have tail : DynamicControl.runFuel params fuel (.whileLoop condition body) middle.state = .finished out := by
                  simpa [DynamicControl.runFuel,value,zero,ran,ret,br,liftChecked,bind,Outcome.bind] using success
                exact bodyPres.trans (ih (.whileLoop condition body) middle.state out tail)

-- This applies to a certified body without inspecting the successful fuel.
theorem coupled {params : List Parameter} {command : Command} {st : DynamicStmt.State} {s : NState}
    {Q : Step → NStep → Prop} (body : DynamicControlBridge.Runs params command st s Q) :
    DynamicControlBridge.Runs params command st s (fun p a => Preserved st p.state ∧ Q p a) := by
  obtain ⟨p,a,⟨fuel,result,ran,same⟩,actual,matched,post⟩ := body
  subst result
  exact ⟨p,a,⟨fuel,p,ran,rfl⟩,actual,matched,run params fuel command st p ran,post⟩

end Proofs.DynamicControlPreserve
