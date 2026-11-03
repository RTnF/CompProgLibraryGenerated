import Proofs.CppClassCopy
import Proofs.CppConstructorPeak

namespace Proofs.CppConstructorView
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppConstructorFinish Proofs.CppNestedVectorBindings Proofs.CppLoop

-- Qualifying an exported field changes its view, never the value or address.
-- A requested writable view must already be permitted by construction.
def restrictValues : List ScalarValue → List (Ty × Bool) → Option (List ScalarValue)
  | [],[] => some []
  | value::values,field::fields => do
      if value.1.type = field.1 ∧ (field.2 = true → value.2 = true) then
        let tail ← restrictValues values fields
        some ((value.1,field.2)::tail)
      else none
  | _,_ => none

theorem restrict_identity (values : List ScalarValue) :
    restrictValues values (values.map fun v => (v.1.type,v.2)) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [restrictValues,ih]

theorem restrict_cells (values : List ScalarValue) (fields : List (Ty × Bool))
    (viewed : List ScalarValue) (actual : restrictValues values fields = some viewed) :
    viewed.map Prod.fst = values.map Prod.fst := by
  induction values generalizing fields viewed with
  | nil => cases fields <;> simp [restrictValues] at actual; subst viewed; rfl
  | cons value values ih =>
    cases fields with
    | nil => simp [restrictValues] at actual
    | cons field fields =>
      unfold restrictValues at actual
      split at actual
      · cases ran : restrictValues values fields with
        | none => simp [ran] at actual
        | some tail =>
          simp only [ran,Bind.bind,Option.bind,Option.some.injEq] at actual
          subst viewed
          simp only [List.map_cons,ih fields tail ran]
      · simp at actual

theorem restrict_length (values : List ScalarValue) (fields : List (Ty × Bool))
    (viewed : List ScalarValue) (actual : restrictValues values fields = some viewed) :
    viewed.length = values.length := by
  simpa only [List.length_map] using congrArg List.length (restrict_cells values fields viewed actual)

-- Flags are the only changed parts of a successful scalar export view.
def Views : List ScalarValue → List (Ty × Bool) → List ScalarValue → Prop
  | [],[],[] => True
  | source::sources,field::fields,target::targets =>
      target.1 = source.1 ∧ target.2 = field.2 ∧ source.1.type = field.1 ∧
        (field.2 = true → source.2 = true) ∧ Views sources fields targets
  | _,_,_ => False

theorem restrict_complete (values : List ScalarValue) (fields : List (Ty × Bool))
    (viewed : List ScalarValue) (allowed : Views values fields viewed) :
    restrictValues values fields = some viewed := by
  induction values generalizing fields viewed with
  | nil => cases fields <;> cases viewed <;> simp_all [Views,restrictValues]
  | cons source sources ih =>
    cases fields with
    | nil => simp [Views] at allowed
    | cons field fields =>
      cases viewed with
      | nil => simp [Views] at allowed
      | cons target targets =>
        obtain ⟨cells,flags,typed,permission,tail⟩ := allowed
        have equal : target = (source.1,field.2) := Prod.ext cells flags
        have guarded : source.1.type = field.1 ∧ (field.2 = true → source.2 = true) := ⟨typed,permission⟩
        simp only [restrictValues,ite_eq_left guarded,ih fields targets tail,
          Bind.bind,Option.bind,equal]

theorem restrict_sound (values : List ScalarValue) (fields : List (Ty × Bool))
    (viewed : List ScalarValue) (actual : restrictValues values fields = some viewed) :
    Views values fields viewed := by
  induction values generalizing fields viewed with
  | nil => cases fields <;> simp [restrictValues] at actual; subst viewed; trivial
  | cons source sources ih =>
    cases fields with
    | nil => simp [restrictValues] at actual
    | cons field fields =>
      unfold restrictValues at actual
      split at actual
      · rename_i permitted
        cases ran : restrictValues sources fields with
        | none => simp [ran] at actual
        | some targets =>
          simp only [ran,Bind.bind,Option.bind,Option.some.injEq] at actual
          subst viewed
          exact ⟨rfl,rfl,permitted.1,permitted.2,ih fields targets ran⟩
      · simp at actual

def finishProfile (caller callee : NState) (vectorSlot : Nat) (fields : List ScalarField)
    (profile : Proofs.CppClassCopy.Profile) : Option (NState × ObjectRef) := do
  if callee.scope = caller.scope+1 ∧ caller.scalars.memory.length ≤ callee.scalars.memory.length ∧
      (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
        caller.scalars.memory.map Proofs.CppState.Cell.type then
    let index ← callee.vectorSlot vectorSlot
    let binding ← callee.frame.bindings[index]?
    if binding.element = .integer profile.element ∧ binding.header = .root callee.scope ∧
        (profile.vectorWritable = true → binding.writable = true) then
      let values ← Proofs.CppConstructorFinish.captureAll callee fields
      let viewed ← restrictValues values profile.scalarFields
      let moved ← callee.frame.transferRoot binding.owner (.integer profile.element) callee.scope caller.scope
      let retired ← moved.retireScope callee.scope
      some (restored caller callee retired {binding with writable := profile.vectorWritable} viewed,
        reference caller viewed.length)
    else none
  else none

def constructProfileFuel (program : NProgram) (fuel : Nat) (caller : NState)
    (arguments : List NArgument) (vectorSlot : Nat) (fields : List ScalarField)
    (profile : Proofs.CppClassCopy.Profile) : Outcome (NState × ObjectRef) := do
  let initial ← liftChecked (prepare caller program.parameters arguments)
  let step ← Proofs.CppNestedProgram.runFuel fuel program.body initial
  if (step.returned.isSome && step.returned != some Ret.unit) || step.breaking then .fault else
    liftChecked (finishProfile caller step.state vectorSlot fields profile)

theorem finish_of_parts (caller callee : NState) (vectorSlot index : Nat)
    (fields : List ScalarField) (profile : Proofs.CppClassCopy.Profile)
    (binding : Proofs.CppNestedVectorBindings.Binding) (values viewed : List ScalarValue)
    (moved retired : Frame)
    (scope : callee.scope = caller.scope+1)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type)
    (slot : callee.vectorSlot vectorSlot = some index)
    (found : callee.frame.bindings[index]? = some binding)
    (typed : binding.element = .integer profile.element)
    (header : binding.header = .root callee.scope)
    (permission : profile.vectorWritable = true → binding.writable = true)
    (captured : Proofs.CppConstructorFinish.captureAll callee fields = some values)
    (restricted : restrictValues values profile.scalarFields = some viewed)
    (transferred : callee.frame.transferRoot binding.owner (.integer profile.element) callee.scope caller.scope = some moved)
    (retirement : moved.retireScope callee.scope = some retired) :
    finishProfile caller callee vectorSlot fields profile =
      some (restored caller callee retired {binding with writable := profile.vectorWritable} viewed,
        reference caller viewed.length) := by
  have outer : callee.scope = caller.scope+1 ∧ caller.scalars.memory.length ≤ callee.scalars.memory.length ∧
      (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
        caller.scalars.memory.map Proofs.CppState.Cell.type := ⟨scope,fits,types⟩
  have inner : binding.element = .integer profile.element ∧ binding.header = .root callee.scope ∧
      (profile.vectorWritable = true → binding.writable = true) := ⟨typed,header,permission⟩
  simp only [finishProfile,ite_eq_left outer,slot,found,Bind.bind,Option.bind,ite_eq_left inner,captured,
    restricted,transferred,retirement]

theorem construct_of_steps (program : NProgram) (fuel : Nat) (caller initial callee out : NState)
    (arguments : List NArgument) (vectorSlot : Nat) (fields : List ScalarField)
    (profile : Proofs.CppClassCopy.Profile) (obj : ObjectRef)
    (prepared : prepare caller program.parameters arguments = some initial)
    (executed : Proofs.CppNestedProgram.runFuel fuel program.body initial = .finished ⟨callee,none,false⟩)
    (finished : finishProfile caller callee vectorSlot fields profile = some (out,obj)) :
    constructProfileFuel program fuel caller arguments vectorSlot fields profile = .finished (out,obj) := by
  simp [constructProfileFuel,prepared,executed,finished,liftChecked,Bind.bind,Outcome.bind]

theorem restored_view_facts (caller callee : NState) (frame : Frame)
    (binding : Proofs.CppNestedVectorBindings.Binding) (values viewed : List ScalarValue)
    (writable : Bool) (cells : viewed.map Prod.fst = values.map Prod.fst) :
    let original := restored caller callee frame binding values
    let qualified := restored caller callee frame {binding with writable := writable} viewed
    qualified.scalars.memory = original.scalars.memory ∧ qualified.slots = original.slots ∧
      qualified.scope = original.scope ∧ qualified.frame.state = original.frame.state ∧
      qualified.frame.rootWritable = original.frame.rootWritable ∧ qualified.work = original.work ∧
      qualified.scalars.peak = original.scalars.peak ∧
      qualified.frame.state.storage.peak = original.frame.state.storage.peak ∧
      qualified.peak = original.peak := by
  have length : viewed.length = values.length := by
    simpa only [List.length_map] using congrArg List.length cells
  simp [restored,NState.observe,NState.work,Proofs.CppState.State.observe,
    Proofs.CppConstructorPeak.scalarBindings_length,cells,length]

theorem restored_old_grant (caller callee : NState) (frame : Frame)
    (binding : Proofs.CppNestedVectorBindings.Binding) (values viewed : List ScalarValue)
    (writable : Bool) (reference : Proofs.CppNestedVectorBindings.Reference)
    (bound : reference.slot < caller.frame.bindings.length) :
    (restored caller callee frame {binding with writable := writable} viewed).frame.grant reference =
      (restored caller callee frame binding values).frame.grant reference := by
  simp only [restored,NState.observe,Frame.grant,Frame.maximum,List.getElem?_append_left bound]
  rfl

theorem restored_old_read (caller callee : NState) (frame : Frame)
    (binding : Proofs.CppNestedVectorBindings.Binding) (values viewed : List ScalarValue)
    (writable : Bool) (reference : Proofs.CppNestedVectorBindings.Reference)
    (bound : reference.slot < caller.frame.bindings.length) :
    (restored caller callee frame {binding with writable := writable} viewed).frame.read reference =
      (restored caller callee frame binding values).frame.read reference := by
  simp only [restored,NState.observe,Frame.read,Frame.grant,Frame.maximum,Frame.object,List.getElem?_append_left bound]
  rfl

theorem restored_old_scalar (caller callee : NState) (frame : Frame)
    (binding : Proofs.CppNestedVectorBindings.Binding) (values viewed : List ScalarValue)
    (writable : Bool) (slot index : Nat) (ty : Ty)
    (originalSlot : caller.scalarSlot slot = some index)
    (bound : index < caller.scalars.bindings.length)
    (cells : viewed.map Prod.fst = values.map Prod.fst) :
    (restored caller callee frame {binding with writable := writable} viewed).scalarCell slot ty =
      (restored caller callee frame binding values).scalarCell slot ty := by
  have inside : slot < caller.slots.length := by
    by_cases inside : slot < caller.slots.length
    · exact inside
    · have missing := List.getElem?_eq_none_iff.mpr (show caller.slots.length ≤ slot by omega)
      simp [NState.scalarSlot,missing] at originalSlot
  have before : (restored caller callee frame binding values).scalarSlot slot = some index := by
    simpa only [restored,NState.observe,NState.scalarSlot,List.append_assoc,
      List.getElem?_append_left inside] using originalSlot
  have after : (restored caller callee frame {binding with writable := writable} viewed).scalarSlot slot = some index := by
    simpa only [restored,NState.observe,NState.scalarSlot,List.append_assoc,
      List.getElem?_append_left inside] using originalSlot
  simp only [NState.scalarCell,before,after,Bind.bind,Option.bind]
  simp only [restored,NState.observe,Proofs.CppState.State.observe,List.getElem?_append_left bound,cells]

end Proofs.CppConstructorView
