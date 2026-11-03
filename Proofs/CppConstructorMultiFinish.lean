import Proofs.CppConstructorFinish
import Proofs.CppConstructorRoots

namespace Proofs.CppConstructorMultiFinish
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
open Proofs.CppRootModel Proofs.CppVector Proofs.CppConstructorRoots
open Proofs.CppConstructorFinish (ScalarField ScalarValue FieldsMatch captureAll scalarBindings scalarLocations)
open Proofs.CppState (Cell)

structure VectorField where
  slot : Nat
  element : Element
  deriving DecidableEq, Repr

structure ObjectRef where
  vectorSlots : List Nat
  scalarSlots : List Nat
  deriving DecidableEq, Repr

-- Resolve permissions and the actual header while all callee roots still live.
def captureVector (s : NState) (field : VectorField) : Option Binding := do
  let index ← s.vectorSlot field.slot
  let (binding,_) ← s.frame.resolve index field.element
  if binding.element = field.element ∧ binding.header = .root s.scope then some binding else none

def captureVectors (s : NState) (fields : List VectorField) : Option (List Binding) :=
  fields.mapM (captureVector s)

def descriptors (bindings : List Binding) : List RootSpec :=
  bindings.map fun binding => (binding.owner,binding.element)

def rebound (scope : Nat) (bindings : List Binding) : List Binding :=
  bindings.map fun binding => {binding with header := .root scope}

def vectorLocations (start count : Nat) : List Proofs.CppMixedInvoke.Location :=
  (List.range count).map fun i => .vector (start+i)

def restored (caller callee : NState) (frame : Frame) (bindings : List Binding)
    (values : List ScalarValue) : NState :=
  let scalars : Proofs.CppState.State := {caller.scalars with
    memory := callee.scalars.memory.take caller.scalars.memory.length ++ values.map Prod.fst,
    bindings := caller.scalars.bindings ++ scalarBindings caller.scalars.memory.length values,
    work := callee.scalars.work+bindings.length+values.length+1,
    peak := max caller.scalars.peak callee.scalars.peak}
  let finalFrame := {frame with bindings := caller.frame.bindings ++ rebound caller.scope bindings}
  (⟨scalars.observe 0,finalFrame,
    caller.slots ++ vectorLocations caller.frame.bindings.length bindings.length ++
      scalarLocations caller.scalars.bindings.length values.length,
    caller.scope,max caller.peak callee.peak⟩ : NState).observe

def reference (caller : NState) (vectors scalars : Nat) : ObjectRef :=
  ⟨(List.range vectors).map (fun i => caller.slots.length+i),
    (List.range scalars).map (fun i => caller.slots.length+vectors+i)⟩

def finish (caller callee : NState) (vectors : List VectorField) (scalars : List ScalarField) :
    Option (NState × ObjectRef) := do
  if callee.scope = caller.scope+1 ∧ caller.scalars.memory.length ≤ callee.scalars.memory.length ∧
      (callee.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type then
    let bindings ← captureVectors callee vectors
    let values ← captureAll callee scalars
    let frame ← finishRoots callee.frame (descriptors bindings) callee.scope caller.scope
    some (restored caller callee frame bindings values,reference caller bindings.length values.length)
  else none

def VectorFieldsMatch (s : NState) : List VectorField → List Binding → Prop
  | [],[] => True
  | field::fields,binding::bindings => (∃ index buffer,
      s.vectorSlot field.slot = some index ∧ s.frame.resolve index field.element = some (binding,buffer) ∧
      binding.element = field.element ∧ binding.header = .root s.scope) ∧
      VectorFieldsMatch s fields bindings
  | _,_ => False

theorem captureVectors_ok (s : NState) (fields : List VectorField) (bindings : List Binding)
    (matched : VectorFieldsMatch s fields bindings) : captureVectors s fields = some bindings := by
  induction fields generalizing bindings with
  | nil => cases bindings with
    | nil => rfl
    | cons b bs => simp [VectorFieldsMatch] at matched
  | cons field fields ih =>
    cases bindings with
    | nil => simp [VectorFieldsMatch] at matched
    | cons binding bindings =>
      obtain ⟨⟨index,buffer,slot,resolved,typed,header⟩,tail⟩ := matched
      have rest := ih bindings tail
      simp only [captureVectors] at rest ⊢
      simp [List.mapM_cons,captureVector,slot,resolved,typed,header,rest]

theorem finish_ok (caller callee : NState) (vectors : List VectorField) (scalars : List ScalarField)
    (bindings : List Binding) (values : List ScalarValue) (roots : List Root)
    (scope : callee.scope = caller.scope+1)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (vectorMatch : VectorFieldsMatch callee vectors bindings) (scalarMatch : FieldsMatch callee scalars values)
    (selected : descriptors bindings = specs roots) (distinct : (roots.map Prod.fst).Nodup)
    (valid : callee.frame.state.wellFormed = true) (models : HaveModels callee.frame roots callee.scope) :
    ∃ out, finish caller callee vectors scalars = some (out,reference caller bindings.length values.length) ∧
      out = restored caller callee (Proofs.DynamicRetire.retiredFrame
        (movedAll callee.frame roots caller.scope) callee.scope) bindings values ∧
      (∀ root ∈ roots, Models out.frame.state root.1 (Proofs.DynamicTransfer.inScope root.2 caller.scope)) ∧
      (∀ owner view, Models callee.frame.state owner view → owner ∉ roots.map Prod.fst →
        view.scope ≠ callee.scope → Models out.frame.state owner view) ∧
      out.scalars.memory = callee.scalars.memory.take caller.scalars.memory.length ++ values.map Prod.fst ∧
      out.scalars.bindings = caller.scalars.bindings ++ scalarBindings caller.scalars.memory.length values ∧
      out.frame.bindings = caller.frame.bindings ++ rebound caller.scope bindings ∧
      out.slots = caller.slots ++ vectorLocations caller.frame.bindings.length bindings.length ++
        scalarLocations caller.scalars.bindings.length values.length ∧ out.scope = caller.scope := by
  obtain ⟨ran,exported,kept⟩ := finishRoots_ok callee.frame roots callee.scope caller.scope valid
    (by omega) distinct models
  rw [← selected] at ran
  let out := restored caller callee (Proofs.DynamicRetire.retiredFrame
    (movedAll callee.frame roots caller.scope) callee.scope) bindings values
  refine ⟨out,?_,rfl,exported,kept,rfl,rfl,rfl,rfl,rfl⟩
  unfold finish
  split
  · simp only [captureVectors_ok callee vectors bindings vectorMatch,
      Proofs.CppConstructorFinish.captureAll_ok callee scalars values scalarMatch,
      Bind.bind,Option.bind,ran]
    rfl
  · rename_i failed
    exact (failed ⟨scope,fits,types⟩).elim

-- Slot lookup sees newly bound caller headers, preserving owner, element and
-- per-binding writable flags. The root permission table comes from the frame.
theorem restored_vector (caller callee : NState) (frame : Frame) (bindings : List Binding)
    (values : List ScalarValue) (j : Nat) (binding : Binding) (found : bindings[j]? = some binding) :
    (restored caller callee frame bindings values).vectorSlot (caller.slots.length+j) =
      some (caller.frame.bindings.length+j) ∧
    (restored caller callee frame bindings values).frame.bindings[caller.frame.bindings.length+j]? =
      some {binding with header := .root caller.scope} := by
  have inside : j < bindings.length := (List.getElem?_eq_some_iff.mp found).1
  constructor
  · change (do
      let loc ← (caller.slots ++ vectorLocations caller.frame.bindings.length bindings.length ++
        scalarLocations caller.scalars.bindings.length values.length)[caller.slots.length+j]?
      match loc with | .vector index => some index | _ => none) = _
    rw [List.append_assoc,List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (show j < (vectorLocations caller.frame.bindings.length bindings.length).length by
      simpa [vectorLocations] using inside)]
    simp [vectorLocations,List.getElem?_map,List.getElem?_range inside]
  · change (caller.frame.bindings ++ rebound caller.scope bindings)[caller.frame.bindings.length+j]? = _
    rw [List.getElem?_append_right (by omega)]
    simp [rebound,List.getElem?_map,found]


theorem restored_scalar (caller callee : NState) (frame : Frame) (bindings : List Binding)
    (values : List ScalarValue) (j : Nat) (cell : Cell) (wr : Bool)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (found : values[j]? = some (cell,wr)) (valid : cell.type.valid cell.value = true) :
    (restored caller callee frame bindings values).scalarCell
      (caller.slots.length+bindings.length+j) cell.type =
      some (⟨caller.scalars.memory.length+j,wr⟩,cell) := by
  let out := restored caller callee frame bindings values
  have inside : j < values.length := (List.getElem?_eq_some_iff.mp found).1
  have loc : out.slots[caller.slots.length+bindings.length+j]? =
      some (.scalar (caller.scalars.bindings.length+j)) := by
    change (caller.slots ++ vectorLocations caller.frame.bindings.length bindings.length ++
      scalarLocations caller.scalars.bindings.length values.length)[caller.slots.length+bindings.length+j]? = _
    rw [List.getElem?_append_right (by simp [vectorLocations])]
    have diff : caller.slots.length+bindings.length+j-
        (caller.slots ++ vectorLocations caller.frame.bindings.length bindings.length).length = j := by
      simp only [List.length_append,vectorLocations,List.length_map,List.length_range]
      omega
    rw [diff]
    simp [scalarLocations,List.getElem?_map,List.getElem?_range inside]
  have b : out.scalars.bindings[caller.scalars.bindings.length+j]? =
      some ⟨caller.scalars.memory.length+j,wr⟩ := by
    change (caller.scalars.bindings ++ scalarBindings caller.scalars.memory.length values)[caller.scalars.bindings.length+j]? = _
    rw [List.getElem?_append_right (by omega)]
    simpa using Proofs.CppConstructorFinish.scalarBindings_get values caller.scalars.memory.length j cell wr found
  have c : out.scalars.memory[caller.scalars.memory.length+j]? = some cell := by
    have length : (callee.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
      simp [List.length_take,Nat.min_eq_left fits]
    change ((callee.scalars.memory.take caller.scalars.memory.length) ++ values.map Prod.fst)[caller.scalars.memory.length+j]? = _
    rw [List.getElem?_append_right (by omega),length]
    simp [List.getElem?_map,found]
  change out.scalarCell _ _ = _
  simp [NState.scalarCell,NState.scalarSlot,loc,b,c,valid]

-- The source bridge supplies field descriptors, preserving its declaration map.
-- This entry point also supports scalar-only and vector-only classes.
def _root_.Proofs.CppNestedCall.NProgram.constructMembersFuel (program : NProgram) (fuel : Nat)
    (caller : NState) (args : List NArgument) (vectors : List VectorField) (scalars : List ScalarField) :
    Proofs.CppLoop.Outcome (NState × ObjectRef) := do
  if program.result = .unit then
    let init ← Proofs.CppLoop.liftChecked (prepare caller program.parameters args)
    let step ← runFuel fuel program.body init
    if step.breaking || (step.returned.isSome && step.returned != some Ret.unit) then .fault else
      Proofs.CppLoop.liftChecked (finish caller step.state vectors scalars)
  else .fault

theorem construct_of_steps (program : NProgram) (fuel : Nat) (caller init callee out : NState)
    (args : List NArgument) (vectors : List VectorField) (scalars : List ScalarField) (object : ObjectRef)
    (unit : program.result = .unit) (prepared : prepare caller program.parameters args = some init)
    (ran : runFuel fuel program.body init = .finished ⟨callee,none,false⟩)
    (exported : finish caller callee vectors scalars = some (out,object)) :
    program.constructMembersFuel fuel caller args vectors scalars = .finished (out,object) := by
  simp [NProgram.constructMembersFuel,unit,prepared,ran,exported,
    Proofs.CppLoop.liftChecked,bind,Proofs.CppLoop.Outcome.bind]

end Proofs.CppConstructorMultiFinish
