import Proofs.CppConstructorView
import Proofs.CppConstructorFinish

namespace Proofs.CppUnitReturn
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop

theorem ret_run (s : NState) :
    NStmt.retUnit.run s = some ⟨s.charge 1 0,some .unit,false⟩ := rfl

theorem ret_work (s : NState) : (s.charge 1 0).work = s.work+1 := by
  simp [NState.work,NState.charge,NState.observe,Proofs.CppState.State.observe,Nat.add_assoc,Nat.add_comm]

theorem ret_data (s : NState) :
    (s.charge 1 0).scalars.memory = s.scalars.memory ∧
    (s.charge 1 0).scalars.bindings = s.scalars.bindings ∧
    (s.charge 1 0).frame = s.frame ∧ (s.charge 1 0).slots = s.slots ∧
    (s.charge 1 0).scope = s.scope := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem finish_unit (caller callee : NState) :
    finish caller callee .unit (some .unit) = finish caller callee .unit none := rfl

theorem sequence_stops (fuel : Nat) (rest : Command) (s : NState) :
    Proofs.CppNestedProgram.runFuel (fuel+2) (.sequence (.primitive .retUnit) rest) s =
      .finished ⟨s.charge 1 0,some .unit,false⟩ := by
  simp [Proofs.CppNestedProgram.runFuel,NStmt.run,Bind.bind,Outcome.bind,liftChecked,Pure.pure]

theorem construct_old_of_steps (program : NProgram) (fuel : Nat) (caller initial callee out : NState)
    (arguments : List NArgument) (vectorSlot : Nat) (element : Proofs.CppVectorOwnership.Element)
    (fields : List Proofs.CppConstructorFinish.ScalarField) (obj : Proofs.CppConstructorFinish.ObjectRef)
    (unit : program.result = .unit)
    (prepared : prepare caller program.parameters arguments = some initial)
    (executed : Proofs.CppNestedProgram.runFuel fuel program.body initial = .finished ⟨callee,some .unit,false⟩)
    (finished : Proofs.CppConstructorFinish.finish caller callee vectorSlot element fields = some (out,obj)) :
    program.constructFuel fuel caller arguments vectorSlot element fields = .finished (out,obj) := by
  simp [NProgram.constructFuel,unit,prepared,executed,finished,liftChecked,Bind.bind,Outcome.bind]

theorem construct_view_of_steps (program : NProgram) (fuel : Nat) (caller initial callee out : NState)
    (arguments : List NArgument) (vectorSlot : Nat) (fields : List Proofs.CppConstructorFinish.ScalarField)
    (profile : Proofs.CppClassCopy.Profile) (obj : Proofs.CppConstructorFinish.ObjectRef)
    (prepared : prepare caller program.parameters arguments = some initial)
    (executed : Proofs.CppNestedProgram.runFuel fuel program.body initial = .finished ⟨callee,some .unit,false⟩)
    (finished : Proofs.CppConstructorView.finishProfile caller callee vectorSlot fields profile = some (out,obj)) :
    Proofs.CppConstructorView.constructProfileFuel program fuel caller arguments vectorSlot fields profile =
      .finished (out,obj) := by
  simp [Proofs.CppConstructorView.constructProfileFuel,prepared,executed,finished,liftChecked,Bind.bind,Outcome.bind]

end Proofs.CppUnitReturn
