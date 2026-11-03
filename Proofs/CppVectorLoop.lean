import Proofs.CppVectorProgram

namespace Proofs.CppVectorLoop
open Proofs.CppMixedInvoke Proofs.CppVectorProgram Proofs.CppLoop

inductive Command where
  | primitive (statement : Stmt)
  | sequence (first rest : Command)
  | scope (body : Command)
  | branch (condition : Expr) (yes no : Command)
  | whileLoop (condition : Expr) (body : Command)
  | breakLoop
deriving DecidableEq, Repr

structure Step where
  state : State
  returned : Option Int := none
  breaking : Bool := false
deriving DecidableEq, Repr

def runFuel : Nat → Command → State → Outcome Step
  | 0,_,_ => .exhausted
  | fuel+1,command,s => match command with
    | .primitive statement => do
        let step ← liftChecked (statement.run s)
        pure ⟨step.state,step.returned,false⟩
    | .sequence first rest => do
        let step ← runFuel fuel first s
        if step.returned.isSome || step.breaking then pure step else runFuel fuel rest step.state
    | .scope body => do
        let step ← runFuel fuel body s
        let restored ← liftChecked (leaveScope s step.state)
        pure {step with state := restored}
    | .branch condition yes no => do
        let (next,value) ← liftChecked (condition.eval s)
        if value == 0 then runFuel fuel no (next.charge 1 0)
        else runFuel fuel yes (next.charge 1 0)
    | .whileLoop condition body => do
        let (next,value) ← liftChecked (condition.eval s)
        if value == 0 then pure ⟨next.charge 1 0,none,false⟩ else do
          let step ← runFuel fuel body (next.charge 1 0)
          if step.returned.isSome then pure step
          else if step.breaking then pure {step with breaking := false}
          else runFuel fuel (.whileLoop condition body) step.state
    | .breakLoop => pure ⟨s.charge 1 0,none,true⟩

structure LoopProgram where
  parameters : List CppVectorBindings.Parameter
  resultType : CppScalar.Ty
  body : Command
deriving DecidableEq, Repr

def LoopProgram.callFuel (program : LoopProgram) (fuel : Nat) (caller : State)
    (arguments : List Argument) : Outcome State := do
  let initial ← liftChecked (prepare caller program.parameters arguments)
  let step ← runFuel fuel program.body initial
  if step.breaking then .fault else do
    let value ← liftChecked step.returned
    liftChecked (finishScalar caller step.state program.resultType value)

def LoopProgram.Terminates (program : LoopProgram) (caller : State) (arguments : List Argument) : Prop :=
  ∃ fuel result, program.callFuel fuel caller arguments = .finished result

theorem runFuel_zero (command : Command) (s : State) : runFuel 0 command s = .exhausted := rfl

theorem break_runs (fuel : Nat) (s : State) :
    runFuel (fuel+1) .breakLoop s = .finished ⟨s.charge 1 0,none,true⟩ := rfl

theorem runFuel_success_mono (fuel extra : Nat) (command : Command) (s : State) (step : Step)
    (success : runFuel fuel command s = .finished step) :
    runFuel (fuel+extra) command s = .finished step := by
  induction fuel generalizing command s step with
  | zero => simp [runFuel] at success
  | succ fuel ih =>
      have added : fuel+1+extra = (fuel+extra)+1 := by omega
      rw [added]
      cases command with
      | primitive statement => simpa [runFuel] using success
      | breakLoop => simpa [runFuel] using success
      | scope body =>
          cases ran : runFuel fuel body s with
          | fault => simp [runFuel,ran,bind,Outcome.bind] at success
          | exhausted => simp [runFuel,ran,bind,Outcome.bind] at success
          | finished middle =>
              have more := ih body s middle ran
              simpa [runFuel,ran,more,bind,Outcome.bind] using success
      | sequence first rest =>
          cases ran : runFuel fuel first s with
          | fault => simp [runFuel,ran,bind,Outcome.bind] at success
          | exhausted => simp [runFuel,ran,bind,Outcome.bind] at success
          | finished middle =>
              have more := ih first s middle ran
              by_cases stop : (middle.returned.isSome || middle.breaking) = true
              · simpa [runFuel,ran,more,bind,pure,Outcome.bind,stop] using success
              · have tail : runFuel fuel rest middle.state = .finished step := by
                  simpa [runFuel,ran,bind,Outcome.bind,stop] using success
                have moreTail := ih rest middle.state step tail
                simp [runFuel,more,moreTail,bind,Outcome.bind,stop]
      | branch condition yes no =>
          cases evaluated : condition.eval s with
          | none => simp [runFuel,evaluated,liftChecked,bind,Outcome.bind] at success
          | some pair =>
              rcases pair with ⟨next,value⟩
              by_cases zero : value = 0
              · have ran : runFuel fuel no (next.charge 1 0) = .finished step := by
                  simpa [runFuel,evaluated,liftChecked,bind,Outcome.bind,zero] using success
                have more := ih no (next.charge 1 0) step ran
                simpa [runFuel,evaluated,liftChecked,bind,Outcome.bind,zero] using more
              · have ran : runFuel fuel yes (next.charge 1 0) = .finished step := by
                  simpa [runFuel,evaluated,liftChecked,bind,Outcome.bind,zero] using success
                have more := ih yes (next.charge 1 0) step ran
                simpa [runFuel,evaluated,liftChecked,bind,Outcome.bind,zero] using more
      | whileLoop condition body =>
          cases evaluated : condition.eval s with
          | none => simp [runFuel,evaluated,liftChecked,bind,Outcome.bind] at success
          | some pair =>
              rcases pair with ⟨next,value⟩
              by_cases zero : value = 0
              · simpa [runFuel,evaluated,liftChecked,bind,pure,Outcome.bind,zero] using success
              · cases ran : runFuel fuel body (next.charge 1 0) with
                | fault => simp [runFuel,evaluated,ran,liftChecked,bind,Outcome.bind,zero] at success
                | exhausted => simp [runFuel,evaluated,ran,liftChecked,bind,Outcome.bind,zero] at success
                | finished middle =>
                    have more := ih body (next.charge 1 0) middle ran
                    by_cases returned : middle.returned.isSome = true
                    · simpa [runFuel,evaluated,ran,more,liftChecked,bind,pure,Outcome.bind,zero,returned] using success
                    · by_cases breaking : middle.breaking = true
                      · simpa [runFuel,evaluated,ran,more,liftChecked,bind,pure,Outcome.bind,zero,returned,breaking] using success
                      · have tail : runFuel fuel (.whileLoop condition body) middle.state = .finished step := by
                          simpa [runFuel,evaluated,ran,liftChecked,bind,Outcome.bind,zero,returned,breaking] using success
                        have moreTail := ih (.whileLoop condition body) middle.state step tail
                        simp [runFuel,evaluated,more,moreTail,liftChecked,bind,Outcome.bind,zero,returned,breaking]

theorem runFuel_success_unique (first second : Nat) (command : Command) (s : State)
    (a b : Step) (one : runFuel first command s = .finished a)
    (two : runFuel second command s = .finished b) : a = b := by
  have oneMore := runFuel_success_mono first second command s a one
  have twoMore := runFuel_success_mono second first command s b two
  rw [Nat.add_comm second first,oneMore] at twoMore
  exact Outcome.finished.inj twoMore

theorem LoopProgram.callFuel_success_mono (program : LoopProgram) (fuel extra : Nat)
    (caller : State) (arguments : List Argument) (result : State)
    (success : program.callFuel fuel caller arguments = .finished result) :
    program.callFuel (fuel+extra) caller arguments = .finished result := by
  cases prepared : prepare caller program.parameters arguments with
  | none => simp [callFuel,prepared,liftChecked,bind,Outcome.bind] at success
  | some initial =>
      cases ran : runFuel fuel program.body initial with
      | fault => simp [callFuel,prepared,ran,liftChecked,bind,Outcome.bind] at success
      | exhausted => simp [callFuel,prepared,ran,liftChecked,bind,Outcome.bind] at success
      | finished step =>
          have more := runFuel_success_mono fuel extra program.body initial step ran
          simpa [callFuel,prepared,ran,more,liftChecked,bind,Outcome.bind] using success

theorem LoopProgram.callFuel_success_unique (program : LoopProgram) (first second : Nat)
    (caller : State) (arguments : List Argument) (a b : State)
    (one : program.callFuel first caller arguments = .finished a)
    (two : program.callFuel second caller arguments = .finished b) : a = b := by
  have oneMore := program.callFuel_success_mono first second caller arguments a one
  have twoMore := program.callFuel_success_mono second first caller arguments b two
  rw [Nat.add_comm second first,oneMore] at twoMore
  exact Outcome.finished.inj twoMore

theorem while_return_exits (fuel : Nat) (s next : State) (condition : Expr) (value : Int)
    (body : Command) (step : Step) (evaluated : condition.eval s = some (next,value))
    (nonzero : value ≠ 0) (ran : runFuel fuel body (next.charge 1 0) = .finished step)
    (returned : step.returned.isSome = true) :
    runFuel (fuel+1) (.whileLoop condition body) s = .finished step := by
  simp [runFuel,evaluated,nonzero,ran,returned,liftChecked,bind,pure,Outcome.bind]

theorem while_break_exits (fuel : Nat) (s next : State) (condition : Expr) (value : Int)
    (evaluated : condition.eval s = some (next,value)) (nonzero : value ≠ 0) :
    runFuel (fuel+2) (.whileLoop condition .breakLoop) s =
      .finished ⟨(next.charge 1 0).charge 1 0,none,false⟩ := by
  simp [runFuel,evaluated,nonzero,liftChecked,bind,pure,Outcome.bind]

end Proofs.CppVectorLoop
