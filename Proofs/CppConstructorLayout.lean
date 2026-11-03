import Proofs.CppConstructorPeak

namespace Proofs.CppConstructorLayout
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish
open Proofs.CppLoop Proofs.CppNestedVectorStore Proofs.DynamicResultValid

-- The copied scalar values are captured from the actual callee. Their prefix
-- may contain caller writes; it is not replaced by an old memory snapshot.
def Layout (caller out : NState) (object : ObjectRef) : Prop :=
  ∃ (oldCells : List Proofs.CppState.Cell) (values : List ScalarValue),
    oldCells.length = caller.scalars.memory.length ∧ oldCells.map Proofs.CppState.Cell.type = caller.scalars.memory.map Proofs.CppState.Cell.type ∧
    out.scalars.memory = oldCells++values.map Prod.fst ∧
    out.scalars.bindings = caller.scalars.bindings++scalarBindings caller.scalars.memory.length values ∧
    out.slots = caller.slots++[.vector caller.frame.bindings.length]++scalarLocations caller.scalars.bindings.length values.length ∧
    out.scope = caller.scope ∧ out.scalars.baseMemory = caller.scalars.baseMemory ∧ object = reference caller values.length

theorem finish_layout (caller callee out : NState) (vslot : Nat) (element : Proofs.CppVectorOwnership.Element)
    (fields : List ScalarField) (object : ObjectRef)
    (actual : Proofs.CppConstructorFinish.finish caller callee vslot element fields = some (out,object)) : Layout caller out object := by
  unfold Proofs.CppConstructorFinish.finish at actual
  split at actual
  · rename_i ready
    obtain ⟨index,_,rest⟩ := bind_some _ _ _ actual
    obtain ⟨binding,_,rest⟩ := bind_some _ _ _ rest
    split at rest
    · obtain ⟨values,_,rest⟩ := bind_some _ _ _ rest
      obtain ⟨moved,_,rest⟩ := bind_some _ _ _ rest
      obtain ⟨retired,_,same⟩ := bind_some _ _ _ rest
      have equal := Prod.mk.inj (Option.some.inj same)
      rw [← equal.1,← equal.2]
      refine ⟨callee.scalars.memory.take caller.scalars.memory.length,values,?_,ready.2.2,rfl,rfl,rfl,rfl,rfl,rfl⟩
      exact List.length_take_of_le ready.2.1
    · simp at rest
  · simp at actual

theorem construct_layout (program : NProgram) (fuel : Nat) (caller out : NState)
    (arguments : List NArgument) (vslot : Nat) (element : Proofs.CppVectorOwnership.Element) (fields : List ScalarField) (object : ObjectRef)
    (unit : program.result = .unit)
    (actual : program.constructFuel fuel caller arguments vslot element fields = .finished (out,object)) :
    Layout caller out object := by
  simp only [NProgram.constructFuel,unit,ite_true] at actual
  cases prep : prepare caller program.parameters arguments with
  | none => simp [prep,liftChecked,bind,Outcome.bind] at actual
  | some initial =>
    simp only [prep,liftChecked,bind,Outcome.bind] at actual
    cases ran : runFuel fuel program.body initial with
    | fault => simp [ran] at actual
    | exhausted => simp [ran] at actual
    | finished step =>
      simp only [ran] at actual
      split at actual
      · contradiction
      · cases exported : Proofs.CppConstructorFinish.finish caller step.state vslot element fields with
        | none => simp [exported] at actual
        | some pair =>
          simp only [exported,Outcome.finished.injEq] at actual
          subst pair
          exact finish_layout caller step.state out vslot element fields object exported

end Proofs.CppConstructorLayout
