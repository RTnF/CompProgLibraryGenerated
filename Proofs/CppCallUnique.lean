import Proofs.CppNestedCall
import Proofs.CppNestedHoare

namespace Proofs.CppCallUnique
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop

theorem call_unique (program : NProgram) (first second : Nat) (caller : NState) (args : List NArgument)
    (a b : NState × Ret) (one : program.callFuel first caller args = .finished a)
    (two : program.callFuel second caller args = .finished b) : a = b := by
  cases prep : prepare caller program.parameters args with
  | none => simp [NProgram.callFuel,prep,liftChecked,bind,Outcome.bind] at one
  | some init =>
    cases firstRun : CppNestedProgram.runFuel first program.body init with
    | fault => simp [NProgram.callFuel,prep,firstRun,liftChecked,bind,Outcome.bind] at one
    | exhausted => simp [NProgram.callFuel,prep,firstRun,liftChecked,bind,Outcome.bind] at one
    | finished firstStep =>
      cases secondRun : CppNestedProgram.runFuel second program.body init with
      | fault => simp [NProgram.callFuel,prep,secondRun,liftChecked,bind,Outcome.bind] at two
      | exhausted => simp [NProgram.callFuel,prep,secondRun,liftChecked,bind,Outcome.bind] at two
      | finished secondStep =>
        have same := Proofs.CppNestedHoare.runFuel_success_unique first second program.body init firstStep secondStep firstRun secondRun
        subst secondStep
        simp only [NProgram.callFuel,prep,firstRun,liftChecked,bind,Outcome.bind] at one
        simp only [NProgram.callFuel,prep,secondRun,liftChecked,bind,Outcome.bind] at two
        exact Outcome.finished.inj (one.symm.trans two)

end Proofs.CppCallUnique
