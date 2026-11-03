import Proofs.DynamicTransfer
import Proofs.DynamicRetire
import Proofs.CppNestedCall

namespace Proofs.CppConstructorFinish
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedVectorBindings Proofs.CppRootModel Proofs.CppVectorOwnership
open Proofs.DynamicTransfer Proofs.DynamicRetire
open Proofs.CppState (Cell)

structure ScalarField where
  slot : Nat
  type : Ty
  deriving DecidableEq, Repr

structure ObjectRef where
  vectorSlot : Nat
  scalarSlots : List Nat
  deriving DecidableEq, Repr

abbrev ScalarValue := Cell × Bool

def capture (s : NState) (field : ScalarField) : Option ScalarValue := do
  let (binding,cell) ← s.scalarCell field.slot field.type
  some (cell,binding.writable)

def captureAll (s : NState) (fields : List ScalarField) : Option (List ScalarValue) :=
  fields.mapM (capture s)

def scalarBindings (start : Nat) : List ScalarValue → List Proofs.CppState.Binding
  | [] => []
  | value::values => ⟨start,value.2⟩::scalarBindings (start+1) values

def scalarLocations (start count : Nat) : List Proofs.CppMixedInvoke.Location :=
  (List.range count).map fun i => .scalar (start+i)

-- The selected owned root survives; other callee roots and all unselected
-- scalar temporaries are retired. Values are copied into new caller cells.
def restored (caller callee : NState) (frame : Frame) (binding : Binding)
    (values : List ScalarValue) : NState :=
  let scalars : Proofs.CppState.State := {caller.scalars with
    memory := callee.scalars.memory.take caller.scalars.memory.length ++ values.map Prod.fst,
    bindings := caller.scalars.bindings ++ scalarBindings caller.scalars.memory.length values,
    work := callee.scalars.work+values.length+1,
    peak := max caller.scalars.peak callee.scalars.peak}
  let rebound : Frame := {frame with bindings := caller.frame.bindings ++
    [⟨binding.owner,binding.element,binding.writable,.root caller.scope⟩]}
  (⟨scalars.observe 0,rebound,caller.slots ++ [.vector caller.frame.bindings.length] ++
    scalarLocations caller.scalars.bindings.length values.length,
    caller.scope,max caller.peak callee.peak⟩ : NState).observe

def reference (caller : NState) (count : Nat) : ObjectRef :=
  ⟨caller.slots.length,(List.range count).map fun i => caller.slots.length+1+i⟩

def finish (caller callee : NState) (vectorSlot : Nat) (element : Element)
    (fields : List ScalarField) : Option (NState × ObjectRef) := do
  if callee.scope = caller.scope+1 ∧ caller.scalars.memory.length ≤ callee.scalars.memory.length ∧
      (callee.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type then
    let index ← callee.vectorSlot vectorSlot
    let binding ← callee.frame.bindings[index]?
    if binding.element = element ∧ binding.header = .root callee.scope then
      let values ← captureAll callee fields
      let moved ← callee.frame.transferRoot binding.owner element callee.scope caller.scope
      let retired ← moved.retireScope callee.scope
      some (restored caller callee retired binding values,reference caller values.length)
    else none
  else none

def FieldsMatch (s : NState) : List ScalarField → List ScalarValue → Prop
  | [],[] => True
  | field::fields,value::values => (∃ binding,
      s.scalarCell field.slot field.type = some (binding,value.1) ∧ binding.writable = value.2) ∧
      FieldsMatch s fields values
  | _,_ => False

theorem captureAll_ok (s : NState) (fields : List ScalarField) (values : List ScalarValue)
    (matched : FieldsMatch s fields values) : captureAll s fields = some values := by
  induction fields generalizing values with
  | nil =>
    cases values with
    | nil => rfl
    | cons value values => simp [FieldsMatch] at matched
  | cons field fields ih =>
    cases values with
    | nil => simp [FieldsMatch] at matched
    | cons value values =>
      obtain ⟨⟨binding,found,flag⟩,tail⟩ := matched
      have rest := ih values tail
      simp only [captureAll] at rest ⊢
      simp [List.mapM_cons,capture,found,flag,rest]

theorem finish_ok (caller callee : NState) (vectorSlot index : Nat) (element : Element)
    (fields : List ScalarField) (values : List ScalarValue) (binding : Binding) (view : View)
    (scope : callee.scope = caller.scope+1)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (slot : callee.vectorSlot vectorSlot = some index) (found : callee.frame.bindings[index]? = some binding)
    (typed : binding.element = element) (header : binding.header = .root callee.scope)
    (matched : FieldsMatch callee fields values)
    (model : Models callee.frame.state binding.owner view)
    (viewElement : view.element = element) (viewScope : view.scope = callee.scope) :
    ∃ out, finish caller callee vectorSlot element fields = some (out,reference caller values.length) ∧
      out = restored caller callee (retiredFrame (movedFrame callee.frame binding.owner caller.scope view) callee.scope) binding values ∧
      Models out.frame.state binding.owner (inScope view caller.scope) ∧
      out.scalars.memory = callee.scalars.memory.take caller.scalars.memory.length ++ values.map Prod.fst ∧
      out.scalars.bindings = caller.scalars.bindings ++ scalarBindings caller.scalars.memory.length values ∧
      out.slots = caller.slots ++ [.vector caller.frame.bindings.length] ++
        scalarLocations caller.scalars.bindings.length values.length ∧ out.scope = caller.scope := by
  have moved := Proofs.DynamicTransfer.frame_runs callee.frame binding.owner caller.scope view model
  rw [viewElement,viewScope] at moved
  have movedModel := Proofs.DynamicTransfer.Models.moved model caller.scope
  have retired := Proofs.DynamicRetire.frame_runs (movedFrame callee.frame binding.owner caller.scope view)
    callee.scope movedModel.valid
  have kept := Proofs.DynamicRetire.Models.retired movedModel callee.scope
    (by cases view <;> simp [inScope,View.scope,scope])
  let out := restored caller callee
    (retiredFrame (movedFrame callee.frame binding.owner caller.scope view) callee.scope) binding values
  refine ⟨out,?_,rfl,kept,rfl,rfl,rfl,rfl⟩
  simp only [scope] at moved retired
  simp [finish,scope,fits,types,slot,found,typed,header,captureAll_ok callee fields values matched,
    moved,retired,out]


-- An existing root view is unchanged whenever it belongs to another scope.
theorem old_view_kept (caller callee : NState) (binding : Binding) (view oldView : View)
    (oldRoot : Nat) (values : List ScalarValue)
    (model : Models callee.frame.state binding.owner view)
    (old : Models callee.frame.state oldRoot oldView)
    (different : oldRoot ≠ binding.owner) (oldScope : oldView.scope ≠ callee.scope) :
    Models (restored caller callee
      (retiredFrame (movedFrame callee.frame binding.owner caller.scope view) callee.scope) binding values).frame.state
      oldRoot oldView := by
  exact Proofs.DynamicRetire.Models.retired (Proofs.DynamicTransfer.Models.other model old different caller.scope)
    callee.scope oldScope

theorem restored_vector (caller callee : NState) (frame : Frame) (binding : Binding)
    (values : List ScalarValue) :
    (restored caller callee frame binding values).vectorSlot (caller.slots.length) =
      some caller.frame.bindings.length ∧
    (restored caller callee frame binding values).frame.bindings[caller.frame.bindings.length]? =
      some ⟨binding.owner,binding.element,binding.writable,.root caller.scope⟩ := by
  simp [restored,NState.observe,NState.vectorSlot,List.append_assoc,List.getElem?_append_right]

theorem scalarBindings_get (values : List ScalarValue) (start j : Nat) (cell : Cell) (wr : Bool)
    (found : values[j]? = some (cell,wr)) :
    (scalarBindings start values)[j]? = some ⟨start+j,wr⟩ := by
  induction values generalizing start j with
  | nil => simp at found
  | cons value values ih =>
    cases j with
    | zero =>
      have same : value = (cell,wr) := Option.some.inj found
      subst value
      rfl
    | succ j =>
      have tail : values[j]? = some (cell,wr) := found
      simpa [scalarBindings,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (start+1) j tail

theorem restored_scalar (caller callee : NState) (frame : Frame) (binding : Binding)
    (values : List ScalarValue) (j : Nat) (cell : Cell) (wr : Bool)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (found : values[j]? = some (cell,wr)) (valid : cell.type.valid cell.value = true) :
    (restored caller callee frame binding values).scalarCell (caller.slots.length+1+j) cell.type =
      some (⟨caller.scalars.memory.length+j,wr⟩,cell) := by
  let out := restored caller callee frame binding values
  have inside : j < values.length := (List.getElem?_eq_some_iff.mp found).1
  have loc : out.slots[caller.slots.length+1+j]? = some (.scalar (caller.scalars.bindings.length+j)) := by
    change (caller.slots ++ [.vector caller.frame.bindings.length] ++
      scalarLocations caller.scalars.bindings.length values.length)[caller.slots.length+1+j]? = _
    rw [List.append_assoc,List.getElem?_append_right (by omega)]
    have diff : caller.slots.length+1+j-caller.slots.length = j+1 := by omega
    rw [diff]
    change (scalarLocations caller.scalars.bindings.length values.length)[j]? = _
    simp [scalarLocations,List.getElem?_map,List.getElem?_range inside]
  have b : out.scalars.bindings[caller.scalars.bindings.length+j]? =
      some ⟨caller.scalars.memory.length+j,wr⟩ := by
    change (caller.scalars.bindings ++ scalarBindings caller.scalars.memory.length values)[caller.scalars.bindings.length+j]? = _
    rw [List.getElem?_append_right (by omega)]
    simpa using scalarBindings_get values caller.scalars.memory.length j cell wr found
  have c : out.scalars.memory[caller.scalars.memory.length+j]? = some cell := by
    have length : (callee.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
      simp [List.length_take,Nat.min_eq_left fits]
    change ((callee.scalars.memory.take caller.scalars.memory.length) ++ values.map Prod.fst)[caller.scalars.memory.length+j]? = _
    rw [List.getElem?_append_right (by omega),length]
    simp [List.getElem?_map,found]
  change out.scalarCell _ _ = _
  simp [NState.scalarCell,NState.scalarSlot,loc,b,c,valid]

-- This entry point retains an object rather than using unit finish, which
-- would retire the constructor's fields. Layouts are supplied by the source bridge.
def _root_.Proofs.CppNestedCall.NProgram.constructFuel (program : NProgram) (fuel : Nat) (caller : NState) (args : List NArgument)
    (vectorSlot : Nat) (element : Element) (fields : List ScalarField) :
    Proofs.CppLoop.Outcome (NState × ObjectRef) := do
  if program.result = .unit then
    let init ← Proofs.CppLoop.liftChecked (prepare caller program.parameters args)
    let step ← runFuel fuel program.body init
    if step.breaking || (step.returned.isSome && step.returned != some Ret.unit) then .fault else
      Proofs.CppLoop.liftChecked (finish caller step.state vectorSlot element fields)
  else .fault


theorem construct_of_steps (program : NProgram) (fuel : Nat) (caller init callee out : NState)
    (args : List NArgument) (vectorSlot : Nat) (element : Element) (fields : List ScalarField) (object : ObjectRef)
    (unit : program.result = .unit) (prepared : prepare caller program.parameters args = some init)
    (ran : runFuel fuel program.body init = .finished ⟨callee,none,false⟩)
    (exported : finish caller callee vectorSlot element fields = some (out,object)) :
    program.constructFuel fuel caller args vectorSlot element fields = .finished (out,object) := by
  simp [NProgram.constructFuel,unit,prepared,ran,exported,Proofs.CppLoop.liftChecked,bind,Proofs.CppLoop.Outcome.bind]

end Proofs.CppConstructorFinish
