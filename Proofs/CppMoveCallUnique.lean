import Proofs.CppMoveCallLayout
import Proofs.CppNestedHoare

namespace Proofs.CppMoveCallUnique
open Proofs.CppMoveContext Proofs.CppNestedCall Proofs.CppNestedProgram Proofs.CppLoop

theorem call_success_mono (program : NProgram) (fuel extra : Nat) (caller : Context)
    (ty : Proofs.CppScalar.Ty) (args : List NArgument) (result : Context × Ret)
    (actual : Proofs.CppMoveCallBindings.callFuel program fuel caller ty args = .finished result) :
    Proofs.CppMoveCallBindings.callFuel program (fuel+extra) caller ty args = .finished result := by
  by_cases allowed : Proofs.CppMoveCallRestore.eligible program
  · cases prep : prepareArguments caller ty program.parameters args with
    | none => simp [Proofs.CppMoveCallBindings.callFuel,allowed,prep,liftChecked,bind,Outcome.bind] at actual
    | some prepared =>
      cases compacted : Proofs.CppMoveCallBindings.compact (project prepared ty) with
      | none => simp [Proofs.CppMoveCallBindings.callFuel,allowed,prep,compacted,liftChecked,bind,Outcome.bind] at actual
      | some initial =>
        cases body : Proofs.CppNestedProgram.runFuel fuel program.body initial with
        | fault => simp [Proofs.CppMoveCallBindings.callFuel,allowed,prep,compacted,body,liftChecked,bind,Outcome.bind] at actual
        | exhausted => simp [Proofs.CppMoveCallBindings.callFuel,allowed,prep,compacted,body,liftChecked,bind,Outcome.bind] at actual
        | finished step =>
          have more := Proofs.CppNestedHoare.runFuel_success_mono fuel extra program.body initial step body
          simp only [Proofs.CppMoveCallBindings.callFuel,ite_eq_left allowed,prep,compacted,
            body,liftChecked,bind,Outcome.bind] at actual
          simpa only [Proofs.CppMoveCallBindings.callFuel,ite_eq_left allowed,prep,compacted,
            more,liftChecked,bind,Outcome.bind] using actual
  · simp [Proofs.CppMoveCallBindings.callFuel,allowed] at actual

theorem call_unique (program : NProgram) (first second : Nat) (caller : Context)
    (ty : Proofs.CppScalar.Ty) (args : List NArgument) (a b : Context × Ret)
    (one : Proofs.CppMoveCallBindings.callFuel program first caller ty args = .finished a)
    (two : Proofs.CppMoveCallBindings.callFuel program second caller ty args = .finished b) : a = b := by
  have firstMore := call_success_mono program first second caller ty args a one
  have secondMore := call_success_mono program second first caller ty args b two
  rw [Nat.add_comm second first] at secondMore
  exact Outcome.finished.inj (firstMore.symm.trans secondMore)

end Proofs.CppMoveCallUnique
