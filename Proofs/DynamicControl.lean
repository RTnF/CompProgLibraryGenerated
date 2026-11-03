import Proofs.DynamicStmt

namespace Proofs.DynamicControl
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.DynamicExpr
open Proofs.CppLoop (Outcome liftChecked)

structure Step where
  state : DynamicStmt.State
  returned : Option Int := none
  breaking : Bool := false

def ofStmt (step : DynamicStmt.Step) : Step := ⟨step.state,step.returned,false⟩

-- Only scalar locals are created by the supported pure primitives. Scope
-- cleanup preserves updates to outer cells and drops newly declared locals.
def leave (outer inner : DynamicStmt.State) : Option DynamicStmt.State :=
  if outer.locals.memory.length ≤ inner.locals.memory.length ∧
      (inner.locals.memory.take outer.locals.memory.length).map Proofs.CppState.Cell.type =
        outer.locals.memory.map Proofs.CppState.Cell.type then
    some ⟨⟨inner.locals.memory.take outer.locals.memory.length,outer.locals.bindings,outer.locals.slots⟩,inner.contents⟩
  else none

def runFuel (params : List Proofs.MultiVecDynamic.Parameter) : Nat → Command → DynamicStmt.State → Outcome Step
  | 0,_,_ => .exhausted
  | fuel+1,command,s => match command with
    | .primitive statement => do
        let step ← liftChecked (DynamicStmt.run params statement s)
        pure (ofStmt step)
    | .sequence first rest => do
        let step ← runFuel params fuel first s
        if step.returned.isSome || step.breaking then pure step else runFuel params fuel rest step.state
    | .scope body => do
        let step ← runFuel params fuel body s
        let restored ← liftChecked (leave s step.state)
        pure {step with state := restored}
    | .branch condition yes no => do
        let value ← liftChecked (denote params s.locals s.contents condition)
        if value == 0 then runFuel params fuel no s else runFuel params fuel yes s
    | .whileLoop condition body => do
        let value ← liftChecked (denote params s.locals s.contents condition)
        if value == 0 then pure ⟨s,none,false⟩ else do
          let step ← runFuel params fuel body s
          if step.returned.isSome then pure step
          else if step.breaking then pure {step with breaking := false}
          else runFuel params fuel (.whileLoop condition body) step.state
    | .breakLoop => pure ⟨s,none,true⟩
    | .invokeScalar _ _ => .fault

-- Unsupported calls are not classified as C++ failures by this interpreter.
theorem success_mono (params : List Proofs.MultiVecDynamic.Parameter) (fuel extra : Nat)
    (command : Command) (s : DynamicStmt.State) (step : Step)
    (success : runFuel params fuel command s = .finished step) :
    runFuel params (fuel+extra) command s = .finished step := by
  induction fuel generalizing command s step with
  | zero => simp [runFuel] at success
  | succ fuel ih =>
    have added : fuel+1+extra = (fuel+extra)+1 := by omega
    rw [added]
    cases command with
    | primitive statement => simpa [runFuel] using success
    | breakLoop => simpa [runFuel] using success
    | invokeScalar _ _ => simp [runFuel] at success
    | scope body =>
      cases ran : runFuel params fuel body s with
      | fault => simp [runFuel,ran,bind,Outcome.bind] at success
      | exhausted => simp [runFuel,ran,bind,Outcome.bind] at success
      | finished middle =>
        have more := ih body s middle ran
        simpa [runFuel,ran,more,bind,Outcome.bind] using success
    | sequence first rest =>
      cases ran : runFuel params fuel first s with
      | fault => simp [runFuel,ran,bind,Outcome.bind] at success
      | exhausted => simp [runFuel,ran,bind,Outcome.bind] at success
      | finished middle =>
        have more := ih first s middle ran
        by_cases stop : (middle.returned.isSome || middle.breaking) = true
        · simpa [runFuel,ran,more,bind,pure,Outcome.bind,stop] using success
        · have tail : runFuel params fuel rest middle.state = .finished step := by
            simpa [runFuel,ran,bind,Outcome.bind,stop] using success
          have moreTail := ih rest middle.state step tail
          simp [runFuel,more,moreTail,bind,Outcome.bind,stop]
    | branch condition yes no =>
      cases value : denote params s.locals s.contents condition with
      | none => simp [runFuel,value,liftChecked,bind,Outcome.bind] at success
      | some v =>
        by_cases zero : v = 0
        · have ran : runFuel params fuel no s = .finished step := by
            simpa [runFuel,value,liftChecked,bind,Outcome.bind,zero] using success
          simpa [runFuel,value,liftChecked,bind,Outcome.bind,zero] using ih no s step ran
        · have ran : runFuel params fuel yes s = .finished step := by
            simpa [runFuel,value,liftChecked,bind,Outcome.bind,zero] using success
          simpa [runFuel,value,liftChecked,bind,Outcome.bind,zero] using ih yes s step ran
    | whileLoop condition body =>
      cases value : denote params s.locals s.contents condition with
      | none => simp [runFuel,value,liftChecked,bind,Outcome.bind] at success
      | some v =>
        by_cases zero : v = 0
        · simpa [runFuel,value,liftChecked,bind,pure,Outcome.bind,zero] using success
        · cases ran : runFuel params fuel body s with
          | fault => simp [runFuel,value,ran,liftChecked,bind,Outcome.bind,zero] at success
          | exhausted => simp [runFuel,value,ran,liftChecked,bind,Outcome.bind,zero] at success
          | finished middle =>
            have more := ih body s middle ran
            by_cases returned : middle.returned.isSome = true
            · simpa [runFuel,value,ran,more,liftChecked,bind,pure,Outcome.bind,zero,returned] using success
            · by_cases breaking : middle.breaking = true
              · simpa [runFuel,value,ran,more,liftChecked,bind,pure,Outcome.bind,zero,returned,breaking] using success
              · have tail : runFuel params fuel (.whileLoop condition body) middle.state = .finished step := by
                  simpa [runFuel,value,ran,liftChecked,bind,Outcome.bind,zero,returned,breaking] using success
                have moreTail := ih (.whileLoop condition body) middle.state step tail
                simp [runFuel,value,more,moreTail,liftChecked,bind,Outcome.bind,zero,returned,breaking]

theorem success_unique (params : List Proofs.MultiVecDynamic.Parameter) (first second : Nat)
    (command : Command) (s : DynamicStmt.State) (a b : Step)
    (one : runFuel params first command s = .finished a)
    (two : runFuel params second command s = .finished b) : a = b := by
  have x := success_mono params first second command s a one
  have y := success_mono params second first command s b two
  rw [Nat.add_comm second first,x] at y
  exact Outcome.finished.inj y

end Proofs.DynamicControl
