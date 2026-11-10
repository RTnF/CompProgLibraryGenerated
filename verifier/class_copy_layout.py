"""Connect copy FieldDecls to constructor export slots in one audited TU.

This establishes translation layouts, copy permission profiles, multi-member
constructor views and member-copy commands. Arbitrary class call sites,
assignment/move and whole-class proofs remain separate obligations.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

from ast_stream import class_construction_stages, class_factory_stages, class_method_functions
from inline_ast import inline_functions
from class_copy import audit_copy_record, spelling
from nested_ir import NestedBody, parse_element, emit_lean
from scalar_ir import apply_conversion_policy, lean_type, TYPES
from state_ir import ValueCalls
from vector_bindings import bindings_from_audit, verify_type_probes
from vector_stl import translation_unit, audit_vector_nodes


MEMBER_FACTORY_SUPPORT = r'''
namespace MemberFactory
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish

def referenceFields (caller : NState) : List (Ty × Bool) → List Nat → Option (List NArgument)
  | [],[] => some []
  | (ty,writable)::fields,slot::slots => do
      let (binding,_) ← caller.scalarCell slot ty
      if writable && !binding.writable then none else do
        let rest ← referenceFields caller fields slots
        some (.scalarReference slot::rest)
  | _,_ => none

def referenceArguments (caller : NState) : List (List (Ty × Bool)) → List ObjectRef → Option (List NArgument)
  | [],[] => some []
  | fields::profiles,object::objects => do
      if !object.vectorSlots.isEmpty then none else do
        let args ← referenceFields caller fields object.scalarSlots
        let rest ← referenceArguments caller profiles objects
        some (args++rest)
  | _,_ => none
def valueFields (caller : NState) : List (Ty × Bool) → List Nat → Option (List NArgument)
  | [],[] => some []
  | (ty,_)::fields,slot::slots => do
      let (_,cell) ← caller.scalarCell slot ty
      let rest ← valueFields caller fields slots
      some (.value (.literal ty cell.value)::rest)
  | _,_ => none

def objectArguments (caller : NState) : List (Bool × List (Ty × Bool)) → List ObjectRef → Option (List NArgument)
  | [],[] => some []
  | (byValue,fields)::profiles,object::objects => do
      if !object.vectorSlots.isEmpty then none else do
        let args ← if byValue then valueFields caller fields object.scalarSlots
                   else referenceFields caller fields object.scalarSlots
        let rest ← objectArguments caller profiles objects
        some (args++rest)
  | _,_ => none
end MemberFactory
'''


MEMBER_VIEW_SUPPORT = r'''
namespace MemberView
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.CppNestedVectorBindings Proofs.CppConstructorMultiFinish Proofs.CppConstructorRoots

def restrictVectors : List Binding → List Bool → Option (List Binding)
  | [],[] => some []
  | binding::bindings,permission::permissions => do
      if permission = true → binding.writable = true then
        let tail ← restrictVectors bindings permissions
        some ({binding with writable := permission}::tail)
      else none
  | _,_ => none

theorem restrict_identity (bindings : List Binding) :
    restrictVectors bindings (bindings.map Binding.writable) = some bindings := by
  induction bindings with
  | nil => rfl
  | cons binding bindings ih => simp [restrictVectors,ih]

def VectorView : List Binding → List Binding → Prop
  | [],[] => True
  | source::sources,target::targets =>
      target.owner = source.owner ∧ target.element = source.element ∧
      target.header = source.header ∧ (target.writable = true → source.writable = true) ∧
      VectorView sources targets
  | _,_ => False

theorem restrict_properties (bindings : List Binding) (permissions : List Bool)
    (viewed : List Binding) (actual : restrictVectors bindings permissions = some viewed) :
    descriptors viewed = descriptors bindings ∧
      viewed.map Binding.writable = permissions ∧ viewed.length = bindings.length ∧
      VectorView bindings viewed := by
  induction bindings generalizing permissions viewed with
  | nil =>
    cases permissions <;> simp [restrictVectors] at actual
    subst viewed
    exact ⟨rfl,rfl,rfl,True.intro⟩
  | cons binding bindings ih =>
    cases permissions with
    | nil => simp [restrictVectors] at actual
    | cons permission permissions =>
      unfold restrictVectors at actual
      split at actual
      · rename_i permitted
        cases ran : restrictVectors bindings permissions with
        | none => simp [ran] at actual
        | some tail =>
          simp only [ran,Bind.bind,Option.bind,Option.some.injEq] at actual
          subst viewed
          obtain ⟨owners,flags,length,view⟩ := ih permissions tail ran
          refine ⟨?_,?_,?_,?_⟩
          · change (binding.owner,binding.element)::descriptors tail =
              (binding.owner,binding.element)::descriptors bindings
            exact congrArg (List.cons (binding.owner,binding.element)) owners
          · exact congrArg (List.cons permission) flags
          · exact congrArg Nat.succ length
          · exact ⟨rfl,rfl,rfl,permitted,view⟩
      · simp at actual

def finishView (caller callee : NState) (vectors : List VectorField)
    (scalars : List Proofs.CppConstructorFinish.ScalarField) (vectorPermissions : List Bool)
    (scalarPermissions : List (Ty × Bool)) : Option (NState × ObjectRef) := do
  if callee.scope = caller.scope+1 ∧ caller.scalars.memory.length ≤ callee.scalars.memory.length ∧
      (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
        caller.scalars.memory.map Proofs.CppState.Cell.type then
    let bindings ← captureVectors callee vectors
    let values ← Proofs.CppConstructorFinish.captureAll callee scalars
    let viewedBindings ← restrictVectors bindings vectorPermissions
    let viewedValues ← Proofs.CppConstructorView.restrictValues values scalarPermissions
    let frame ← finishRoots callee.frame (descriptors viewedBindings) callee.scope caller.scope
    some (restored caller callee frame viewedBindings viewedValues,
      reference caller viewedBindings.length viewedValues.length)
  else none

def constructViewFuel (program : NProgram) (fuel : Nat) (caller : NState)
    (arguments : List NArgument) (vectors : List VectorField)
    (scalars : List Proofs.CppConstructorFinish.ScalarField) (vectorPermissions : List Bool)
    (scalarPermissions : List (Ty × Bool)) : Outcome (NState × ObjectRef) := do
  let initial ← liftChecked (prepare caller program.parameters arguments)
  let step ← runFuel fuel program.body initial
  if (step.returned.isSome && step.returned != some Ret.unit) || step.breaking then .fault else
    liftChecked (finishView caller step.state vectors scalars vectorPermissions scalarPermissions)

theorem constructView_of_steps (program : NProgram) (fuel : Nat) (caller initial callee out : NState)
    (arguments : List NArgument) (vectors : List VectorField)
    (scalars : List Proofs.CppConstructorFinish.ScalarField) (vectorPermissions : List Bool)
    (scalarPermissions : List (Ty × Bool)) (object : ObjectRef) (returned : Option Ret)
    (prepared : prepare caller program.parameters arguments = some initial)
    (executed : runFuel fuel program.body initial = .finished ⟨callee,returned,false⟩)
    (completed : returned = none ∨ returned = some Ret.unit)
    (exported : finishView caller callee vectors scalars vectorPermissions scalarPermissions = some (out,object)) :
    constructViewFuel program fuel caller arguments vectors scalars vectorPermissions scalarPermissions =
      .finished (out,object) := by
  rcases completed with rfl | rfl <;>
    simp [constructViewFuel,prepared,executed,exported,liftChecked,Bind.bind,Outcome.bind]

theorem finishView_ok (caller callee : NState) (vectors : List VectorField)
    (scalars : List Proofs.CppConstructorFinish.ScalarField) (vectorPermissions : List Bool)
    (scalarPermissions : List (Ty × Bool)) (bindings viewedBindings : List Binding)
    (values viewedValues : List Proofs.CppConstructorFinish.ScalarValue) (roots : List Root)
    (scope : callee.scope = caller.scope+1)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type)
    (vectorMatch : VectorFieldsMatch callee vectors bindings)
    (scalarMatch : Proofs.CppConstructorFinish.FieldsMatch callee scalars values)
    (vectorView : restrictVectors bindings vectorPermissions = some viewedBindings)
    (scalarView : Proofs.CppConstructorView.restrictValues values scalarPermissions = some viewedValues)
    (selected : descriptors bindings = specs roots) (distinct : (roots.map Prod.fst).Nodup)
    (valid : callee.frame.state.wellFormed = true) (models : HaveModels callee.frame roots callee.scope) :
    ∃ out, finishView caller callee vectors scalars vectorPermissions scalarPermissions =
        some (out,reference caller viewedBindings.length viewedValues.length) ∧
      (∀ root ∈ roots, Proofs.CppRootModel.Models out.frame.state root.1
        (Proofs.DynamicTransfer.inScope root.2 caller.scope)) ∧
      (∀ owner view, Proofs.CppRootModel.Models callee.frame.state owner view →
        owner ∉ roots.map Prod.fst → view.scope ≠ callee.scope →
        Proofs.CppRootModel.Models out.frame.state owner view) ∧
      out.scalars.memory = callee.scalars.memory.take caller.scalars.memory.length ++ values.map Prod.fst ∧
      out.frame.bindings = caller.frame.bindings ++ rebound caller.scope viewedBindings ∧
      out.scalars.bindings = caller.scalars.bindings ++
        Proofs.CppConstructorFinish.scalarBindings caller.scalars.memory.length viewedValues ∧
      out.scope = caller.scope := by
  have same := (restrict_properties bindings vectorPermissions viewedBindings vectorView).1
  have selectedView : descriptors viewedBindings = specs roots := same.trans selected
  obtain ⟨ran,exported,kept⟩ := finishRoots_ok callee.frame roots callee.scope caller.scope valid
    (by omega) distinct models
  rw [← selectedView] at ran
  let frame := Proofs.DynamicRetire.retiredFrame (movedAll callee.frame roots caller.scope) callee.scope
  let out := restored caller callee frame viewedBindings viewedValues
  refine ⟨out,?_,exported,kept,?_,rfl,rfl,rfl⟩
  · unfold finishView
    rw [ite_eq_left ⟨scope,fits,types⟩]
    simp only [captureVectors_ok callee vectors bindings vectorMatch,
      Proofs.CppConstructorFinish.captureAll_ok callee scalars values scalarMatch,
      vectorView,scalarView,Bind.bind,Option.bind,ran]
    rfl
  · change callee.scalars.memory.take caller.scalars.memory.length ++ viewedValues.map Prod.fst = _
    rw [Proofs.CppConstructorView.restrict_cells values scalarPermissions viewedValues scalarView]

end MemberView
'''

MEMBER_COPY_SUPPORT = r'''
namespace MemberCopy
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop

inductive Field where
  | vector (slot : Nat) (type : Ty) (writable : Bool)
  | scalar (slot : Nat) (type : Ty) (writable : Bool)
  deriving DecidableEq, Repr

def statement : Field → NStmt
  | .vector slot ty writable => .copyVector (.local slot) ty writable
  | .scalar slot ty writable => .declare ty writable (.variable ty slot)

def validate (s : NState) : List Field → Option Unit
  | [] => some ()
  | field::fields => do
      match field with
      | .vector slot ty _ =>
        let index ← s.vectorSlot slot
        let _ ← s.frame.resolve index (.integer ty)
        pure ()
      | .scalar slot ty _ =>
        let _ ← s.scalarCell slot ty
        pure ()
      validate s fields

def command : List Field → Command
  | [] => .primitive .skip
  | field::fields => .sequence (.primitive (statement field)) (command fields)

def reference (s : NState) (fields : List Field) : Proofs.CppConstructorMultiFinish.ObjectRef :=
  ⟨fields.zipIdx.filterMap (fun (field,index) => match field with
      | .vector .. => some (s.slots.length+index) | _ => none),
   fields.zipIdx.filterMap (fun (field,index) => match field with
      | .scalar .. => some (s.slots.length+index) | _ => none)⟩

def runCopyFuel (fuel : Nat) (s : NState) (fields : List Field) : Outcome NStep := do
  let _ ← liftChecked (validate s fields)
  runFuel fuel (command fields) s

-- Each member uses the already verified ordinary scalar/vector statement.
-- This relation composes their actual states in source declaration order.
inductive Steps : List Field → NState → NState → Prop
  | nil (s) : Steps [] s s
  | cons (field fields before middle after)
      (head : (statement field).run before = some ⟨middle,none,false⟩)
      (tail : Steps fields middle after) : Steps (field::fields) before after

theorem command_complete (fields : List Field) (before after : NState)
    (steps : Steps fields before after) :
    runFuel (fields.length+1) (command fields) before = .finished ⟨after,none,false⟩ := by
  induction steps with
  | nil => rfl
  | cons field fields before middle after head tail ih =>
    exact Proofs.CppClassCopyCommands.sequence_run (fields.length+1) _ _ before middle after
      (Proofs.CppClassCopyCommands.primitive_run fields.length _ before middle head) ih

theorem copy_complete (fields : List Field) (before after : NState)
    (ready : validate before fields = some ()) (steps : Steps fields before after) :
    runCopyFuel (fields.length+1) before fields = .finished ⟨after,none,false⟩ := by
  simp only [runCopyFuel,ready,liftChecked,Bind.bind,Outcome.bind,command_complete fields before after steps]

-- Readiness uses source cells/buffers and frame metadata, rather than assuming
-- that the member-copy statements have already succeeded.
inductive Ready : List Field → NState → NState → Prop
  | nil (s) : Ready [] s s
  | scalar (slot ty writable fields before after)
      (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
      (found : before.scalarCell slot ty = some (binding,cell))
      (tail : Ready fields (Proofs.CppClassCopyCommands.scalarStep before ty writable cell.value) after) :
      Ready (.scalar slot ty writable::fields) before after
  | vector (slot ty writable fields before after index)
      (binding : Proofs.CppNestedVectorBindings.Binding)
      (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
      (found : before.vectorSlot slot = some index)
      (resolved : before.frame.resolve index (.integer ty) = some (binding,buffer))
      (lengths : before.frame.rootWritable.length = before.frame.state.forest.objects.length)
      (supported : Proofs.CppVectorBindings.supported ty)
      (tail : Ready fields (Proofs.CppCopyStatementFacts.result before (before.charge 1 1)
        buffer ty writable) after) : Ready (.vector slot ty writable::fields) before after

theorem ready_steps (fields : List Field) (before after : NState)
    (ready : Ready fields before after) : Steps fields before after := by
  induction ready with
  | nil s => exact .nil s
  | scalar slot ty writable fields before after binding cell found tail ih =>
    refine Steps.cons (.scalar slot ty writable) fields before _ after ?_ ih
    exact Proofs.CppClassCopyCommands.scalar_run before slot ty writable binding cell found
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    have evaluated : (Container.local slot).eval before = some (before.charge 1 1,index) := by
      simp [Container.eval,found]
    have copied := (Proofs.CppCopyStatementFacts.completes before (before.charge 1 1)
      (.local slot) index binding buffer ty writable evaluated resolved lengths supported).1
    refine Steps.cons (.vector slot ty writable) fields before _ after ?_ ih
    simpa only [statement,Proofs.CppCopyStatement.statement_run] using copied

theorem copy_ready_complete (fields : List Field) (before after : NState)
    (initial : validate before fields = some ()) (ready : Ready fields before after) :
    runCopyFuel (fields.length+1) before fields = .finished ⟨after,none,false⟩ :=
  copy_complete fields before after initial (ready_steps fields before after ready)

theorem resolve_root_kept (f g : Proofs.CppNestedVectorBindings.Frame)
    (extension : Proofs.CppFrameExtension.Extends f g) (index : Nat) (ty : Ty)
    (binding : Proofs.CppNestedVectorBindings.Binding)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (scope : Nat)
    (root : binding.header = .root scope)
    (actual : f.resolve index (.integer ty) = some (binding,buffer)) :
    g.resolve index (.integer ty) = some (binding,buffer) := by
  have parsed := actual
  unfold Proofs.CppNestedVectorBindings.Frame.resolve at parsed
  obtain ⟨b,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ parsed
  obtain ⟨owner,header,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨⟨buf,tag⟩,object,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨maximum,maximumFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  split at rest
  · rename_i good
    obtain ⟨sameBinding,sameBuffer⟩ := Prod.mk.inj (Option.some.inj rest)
    subst b
    subst buf
    have ownerEq : binding.owner = owner := good.1
    subst owner
    have parts := Proofs.CppFrameCopy.object_parts f binding.owner ty buffer tag object
    have inside := Proofs.CppVectorStore.lookup_bound f.state.storage binding.owner buffer parts.2.1
    have nextFound := (extension.bindings index (List.getElem?_eq_some_iff.mp found).1).trans found
    have headerEq : g.headerOwner binding = f.headerOwner binding := by
      simp only [Proofs.CppNestedVectorBindings.Frame.headerOwner,root]
      rw [Proofs.CppFrameExtension.object_eq f g extension binding.owner binding.element inside]
    have objectEq := Proofs.CppFrameExtension.object_eq f g extension binding.owner (.integer ty) inside
    have maximumEq := Proofs.CppFrameExtension.maximum_eq f g extension binding.owner
      (by have := (Proofs.CppNestedVectorStore.wellFormed_parts f.state extension.oldValid).1; omega)
    simp only [Proofs.CppNestedVectorBindings.Frame.resolve,nextFound,Bind.bind,Option.bind,
      headerEq,header,objectEq,object,maximumEq,maximumFound]
    exact ite_eq_left ⟨True.intro,good.2.1,good.2.2⟩
  · simp at rest

theorem vector_slot_prefix (before after : NState) (extra : List Proofs.CppMixedInvoke.Location)
    (slots : after.slots = before.slots++extra) (slot index : Nat)
    (found : before.vectorSlot slot = some index) : after.vectorSlot slot = some index := by
  have parsed := found
  unfold NState.vectorSlot at parsed
  obtain ⟨location,lookup,_⟩ := Proofs.DynamicResultValid.bind_some _ _ _ parsed
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  simpa only [NState.vectorSlot,slots,List.getElem?_append_left inside] using found

def Keeps (before after : NState) : Prop :=
  (∀ slot ty binding cell, before.scalarCell slot ty = some (binding,cell) →
    after.scalarCell slot ty = some (binding,cell)) ∧
  (∀ slot ty index binding buffer scope, before.vectorSlot slot = some index →
    before.frame.resolve index (.integer ty) = some (binding,buffer) → binding.header = .root scope →
    after.vectorSlot slot = some index ∧ after.frame.resolve index (.integer ty) = some (binding,buffer))

theorem Keeps.refl (s : NState) : Keeps s s := ⟨by intros; assumption,by intros; exact ⟨by assumption,by assumption⟩⟩

theorem Keeps.trans {a b c : NState} (first : Keeps a b) (second : Keeps b c) : Keeps a c := by
  constructor
  · intro slot ty binding cell found
    exact second.1 _ _ _ _ (first.1 _ _ _ _ found)
  · intro slot ty index binding buffer scope slotFound resolved root
    obtain ⟨slotNext,resolveNext⟩ := first.2 _ _ _ _ _ _ slotFound resolved root
    exact second.2 _ _ _ _ _ _ slotNext resolveNext root

def Good (s : NState) : Prop := s.frame.state.wellFormed = true ∧
  s.frame.rootWritable.length = s.frame.state.forest.objects.length

def Source (s : NState) : Field → Prop
  | .scalar slot ty _ => ∃ binding cell, s.scalarCell slot ty = some (binding,cell)
  | .vector slot ty _ => ∃ index binding buffer scope, s.vectorSlot slot = some index ∧
      s.frame.resolve index (.integer ty) = some (binding,buffer) ∧ binding.header = .root scope ∧
      Proofs.CppVectorBindings.supported ty

def Sources (s : NState) (fields : List Field) : Prop := ∀ field ∈ fields, Source s field

theorem sources_kept {before after : NState} (kept : Keeps before after) (fields : List Field)
    (sources : Sources before fields) : Sources after fields := by
  intro field member
  cases field with
  | scalar slot ty writable =>
    obtain ⟨binding,cell,found⟩ := sources _ member
    exact ⟨binding,cell,kept.1 _ _ _ _ found⟩
  | vector slot ty writable =>
    obtain ⟨index,binding,buffer,scope,found,resolved,root,supported⟩ := sources _ member
    obtain ⟨slotNext,resolveNext⟩ := kept.2 _ _ _ _ _ _ found resolved root
    exact ⟨index,binding,buffer,scope,slotNext,resolveNext,root,supported⟩

theorem sources_validated (s : NState) (fields : List Field) (sources : Sources s fields) :
    validate s fields = some () := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    have tail := ih (fun f member => sources f (List.mem_cons_of_mem _ member))
    have head := sources field (by simp)
    cases field with
    | scalar slot ty writable =>
      obtain ⟨binding,cell,found⟩ := head
      simp [validate,found,tail]
    | vector slot ty writable =>
      obtain ⟨index,binding,buffer,scope,found,resolved,_,_⟩ := head
      simp [validate,found,resolved,tail]

theorem scalar_keeps (s : NState) (ty : Ty) (writable : Bool) (value : Int) :
    Keeps s (Proofs.CppClassCopyCommands.scalarStep s ty writable value) := by
  constructor
  · exact Proofs.CppClassCopyCommands.scalar_step_keeps s ty writable value
  · intro slot sourceTy index binding buffer scope found resolved root
    refine ⟨vector_slot_prefix s _ [.scalar s.scalars.bindings.length] rfl slot index found,?_⟩
    exact resolved

theorem scalar_destination (s : NState) (ty : Ty) (writable : Bool) (value : Int)
    (valid : ty.valid value = true) :
    (Proofs.CppClassCopyCommands.scalarStep s ty writable value).scalarCell s.slots.length ty =
      some (⟨s.scalars.memory.length,writable⟩,⟨ty,value⟩) := by
  simp [Proofs.CppClassCopyCommands.scalarStep,NState.scalarCell,NState.scalarSlot,
    NState.declared,NState.charge,NState.observe,Proofs.CppState.State.observe,valid]

theorem resolved_payload (f : Proofs.CppNestedVectorBindings.Frame) (index : Nat) (ty : Ty)
    (binding : Proofs.CppNestedVectorBindings.Binding) (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (resolved : f.resolve index (.integer ty) = some (binding,buffer)) :
    buffer.Valid (Proofs.CppNestedVectorStore.accepts (.integer ty)) := by
  obtain ⟨tag,object⟩ := Proofs.CppFrameCopy.resolve_object f index ty binding buffer resolved
  obtain ⟨valid,storage,forest,typed⟩ := Proofs.CppFrameCopy.object_parts f binding.owner ty buffer tag object
  obtain ⟨actual,found,_,payload⟩ :=
    Proofs.CppNestedVectorStore.wellFormed_buffer f.state binding.owner buffer valid storage
  have same : actual = tag := Option.some.inj (found.symm.trans forest)
  subst actual
  simpa only [typed] using payload.1

def vectorResult (s : NState) (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (ty : Ty) (writable : Bool) : NState :=
  Proofs.CppCopyStatementFacts.result s (s.charge 1 1) buffer ty writable

theorem vector_destination (s : NState) (index : Nat) (ty : Ty) (writable : Bool)
    (binding : Proofs.CppNestedVectorBindings.Binding) (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (resolved : s.frame.resolve index (.integer ty) = some (binding,buffer))
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (supported : Proofs.CppVectorBindings.supported ty) :
    (vectorResult s buffer ty writable).vectorSlot s.slots.length = some s.frame.bindings.length ∧
    (vectorResult s buffer ty writable).frame.resolve s.frame.bindings.length (.integer ty) =
      some (Proofs.CppFrameCopy.copyBinding s.frame ty s.scope writable,
        Proofs.CppVectorCopy.copied buffer s.frame.state.storage.objects.length) := by
  obtain ⟨tag,object⟩ := Proofs.CppFrameCopy.resolve_object s.frame index ty binding buffer resolved
  have valid := (Proofs.CppFrameCopy.object_parts s.frame binding.owner ty buffer tag object).1
  constructor
  · simp [vectorResult,Proofs.CppCopyStatementFacts.result,NState.release,NState.charge,
      NState.observe,NState.vectorSlot]
  · have copied := Proofs.CppFrameCopy.copied_resolve s.frame buffer ty s.scope writable
      valid lengths supported (resolved_payload s.frame index ty binding buffer resolved)
    simpa only [vectorResult,Proofs.CppCopyStatementFacts.result,NState.release,NState.charge,
      NState.observe,List.take_length] using copied

theorem vector_extension (s : NState) (slot index : Nat) (ty : Ty) (writable : Bool)
    (binding : Proofs.CppNestedVectorBindings.Binding)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (found : s.vectorSlot slot = some index)
    (resolved : s.frame.resolve index (.integer ty) = some (binding,buffer))
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (supported : Proofs.CppVectorBindings.supported ty) :
    Proofs.CppFrameExtension.Extends s.frame (vectorResult s buffer ty writable).frame := by
  have evaluated : (Container.local slot).eval s = some (s.charge 1 1,index) := by
    simp [Container.eval,found]
  have extension := (Proofs.CppCopyStatementFacts.completes s (s.charge 1 1) (.local slot)
    index binding buffer ty writable evaluated resolved lengths supported).2
  simpa only [vectorResult,NState.release,NState.charge,NState.observe,List.take_length] using extension

theorem vector_keeps (s : NState) (slot index : Nat) (ty : Ty) (writable : Bool)
    (binding : Proofs.CppNestedVectorBindings.Binding)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (found : s.vectorSlot slot = some index)
    (resolved : s.frame.resolve index (.integer ty) = some (binding,buffer))
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (supported : Proofs.CppVectorBindings.supported ty) : Keeps s (vectorResult s buffer ty writable) := by
  have extension := vector_extension s slot index ty writable binding buffer found resolved lengths supported
  constructor
  · exact Proofs.CppCopyStatementFacts.keeps_scalar s (s.charge 1 1) buffer ty writable
  · intro oldSlot oldTy oldIndex oldBinding oldBuffer oldScope oldFound oldResolved root
    have slots : (vectorResult s buffer ty writable).slots =
        s.slots++[.vector s.frame.bindings.length] := by
      simp [vectorResult,Proofs.CppCopyStatementFacts.result,NState.release,NState.charge,NState.observe]
    exact ⟨vector_slot_prefix s _ _ slots oldSlot oldIndex oldFound,
      resolve_root_kept _ _ extension oldIndex oldTy oldBinding oldBuffer oldScope root oldResolved⟩

theorem sources_ready (s : NState) (fields : List Field) (good : Good s) (sources : Sources s fields) :
    ∃ after, Ready fields s after ∧ Good after ∧ Keeps s after := by
  induction fields generalizing s with
  | nil => exact ⟨s,.nil s,good,Keeps.refl s⟩
  | cons field fields ih =>
    have head := sources field (by simp)
    have tail : Sources s fields := fun f member => sources f (List.mem_cons_of_mem _ member)
    cases field with
    | scalar slot ty writable =>
      obtain ⟨binding,cell,found⟩ := head
      let next := Proofs.CppClassCopyCommands.scalarStep s ty writable cell.value
      have kept := scalar_keeps s ty writable cell.value
      have goodNext : Good next := good
      obtain ⟨after,ready,goodAfter,keptAfter⟩ := ih next goodNext (sources_kept kept fields tail)
      exact ⟨after,.scalar slot ty writable fields s after binding cell found ready,
        goodAfter,kept.trans keptAfter⟩
    | vector slot ty writable =>
      obtain ⟨index,binding,buffer,scope,found,resolved,root,supported⟩ := head
      let next := vectorResult s buffer ty writable
      have extension := vector_extension s slot index ty writable binding buffer found resolved good.2 supported
      have kept := vector_keeps s slot index ty writable binding buffer found resolved good.2 supported
      have goodNext : Good next := ⟨extension.newValid,extension.newLengths⟩
      obtain ⟨after,ready,goodAfter,keptAfter⟩ := ih next goodNext (sources_kept kept fields tail)
      exact ⟨after,.vector slot ty writable fields s after index binding buffer
        found resolved good.2 supported ready,goodAfter,kept.trans keptAfter⟩

theorem source_copy_complete (s : NState) (fields : List Field) (good : Good s)
    (sources : Sources s fields) :
    ∃ after, runCopyFuel (fields.length+1) s fields = .finished ⟨after,none,false⟩ ∧
      Good after ∧ Keeps s after := by
  obtain ⟨after,ready,goodAfter,kept⟩ := sources_ready s fields good sources
  exact ⟨after,copy_ready_complete fields s after (sources_validated s fields sources) ready,goodAfter,kept⟩

theorem ready_shape (fields : List Field) (before after : NState)
    (ready : Ready fields before after) :
    after.slots.length = before.slots.length + fields.length ∧ after.scope = before.scope := by
  induction ready with
  | nil s => exact ⟨by simp,rfl⟩
  | scalar slot ty writable fields before after binding cell found tail ih =>
    refine ⟨?_,ih.2⟩
    simpa [Proofs.CppClassCopyCommands.scalarStep,NState.declared,NState.charge,NState.observe,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih.1
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    refine ⟨?_,ih.2⟩
    simpa [Proofs.CppCopyStatementFacts.result,NState.release,NState.charge,NState.observe,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih.1

theorem source_copy_layout (s : NState) (fields : List Field)
    (good : Good s) (sources : Sources s fields) :
    ∃ after, runCopyFuel (fields.length+1) s fields = .finished ⟨after,none,false⟩ ∧
      Good after ∧ Keeps s after ∧
      after.slots.length = s.slots.length + fields.length ∧ after.scope = s.scope := by
  obtain ⟨after,ready,goodAfter,kept⟩ := sources_ready s fields good sources
  have shape := ready_shape fields s after ready
  exact ⟨after,copy_ready_complete fields s after (sources_validated s fields sources)
    ready,goodAfter,kept,shape.1,shape.2⟩

def Copied (before after : NState) : Field → Nat → Prop
  | .scalar slot ty writable, target =>
      ∀ binding cell, before.scalarCell slot ty = some (binding,cell) →
        ∃ targetBinding targetCell, after.scalarCell target ty = some (targetBinding,targetCell) ∧
          targetCell.value = cell.value ∧ targetBinding.writable = writable
  | .vector slot ty writable, target =>
      ∀ index binding buffer scope, before.vectorSlot slot = some index →
        before.frame.resolve index (.integer ty) = some (binding,buffer) → binding.header = .root scope →
        ∃ targetIndex targetBinding targetBuffer,
          after.vectorSlot target = some targetIndex ∧
          after.frame.resolve targetIndex (.integer ty) = some (targetBinding,targetBuffer) ∧
          targetBinding.header = .root before.scope ∧ targetBuffer.items = buffer.items ∧
          targetBinding.writable = writable ∧ targetBuffer.capacity = buffer.items.length ∧
          targetBuffer.limit = buffer.limit ∧ targetBuffer.epoch = 0 ∧ targetBuffer.owner = targetBinding.owner

theorem copied_source_kept {a b c : NState} (kept : Keeps a b) (scope : b.scope = a.scope)
    (field : Field) (target : Nat) (copied : Copied b c field target) : Copied a c field target := by
  cases field with
  | scalar slot ty writable =>
    intro binding cell found
    exact copied binding cell (kept.1 _ _ _ _ found)
  | vector slot ty writable =>
    intro index binding buffer root found resolved header
    obtain ⟨nextFound,nextResolved⟩ := kept.2 _ _ _ _ _ _ found resolved header
    obtain ⟨i,bf,buf,slotFound,actual,rooted,items,permission,capacity,limit,epoch,owner⟩ :=
      copied index binding buffer root nextFound nextResolved header
    exact ⟨i,bf,buf,slotFound,actual,scope ▸ rooted,items,permission,capacity,limit,epoch,owner⟩

theorem copied_target_kept {a b c : NState} (kept : Keeps b c)
    (field : Field) (target : Nat) (copied : Copied a b field target) : Copied a c field target := by
  cases field with
  | scalar slot ty writable =>
    intro binding cell found
    obtain ⟨bf,cl,actual,value,permission⟩ := copied binding cell found
    exact ⟨bf,cl,kept.1 _ _ _ _ actual,value,permission⟩
  | vector slot ty writable =>
    intro index binding buffer root found resolved header
    obtain ⟨i,bf,buf,slotFound,actual,rooted,items,permission,capacity,limit,epoch,owner⟩ := copied index binding buffer root found resolved header
    obtain ⟨nextFound,nextResolved⟩ := kept.2 _ _ _ _ _ _ slotFound actual rooted
    exact ⟨i,bf,buf,nextFound,nextResolved,rooted,items,permission,capacity,limit,epoch,owner⟩

theorem scalar_copied (s : NState) (slot : Nat) (ty : Ty) (writable : Bool)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (found : s.scalarCell slot ty = some (binding,cell)) :
    Copied s (Proofs.CppClassCopyCommands.scalarStep s ty writable cell.value)
      (.scalar slot ty writable) s.slots.length := by
  intro b c actual
  have same := Prod.mk.inj (Option.some.inj (actual.symm.trans found))
  obtain ⟨sameBinding,sameCell⟩ := same
  subst b
  subst c
  exact ⟨_,_,scalar_destination s ty writable cell.value
    (Proofs.CppClassCopyCommands.scalar_cell_facts s slot ty binding cell found).2,rfl,rfl⟩

theorem vector_copied (s : NState) (slot index : Nat) (ty : Ty) (writable : Bool)
    (binding : Proofs.CppNestedVectorBindings.Binding)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (found : s.vectorSlot slot = some index)
    (resolved : s.frame.resolve index (.integer ty) = some (binding,buffer))
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (supported : Proofs.CppVectorBindings.supported ty) :
    Copied s (vectorResult s buffer ty writable) (.vector slot ty writable) s.slots.length := by
  intro i b buf root actual actualResolve _
  have equalIndex := Option.some.inj (actual.symm.trans found)
  subst i
  have same := Prod.mk.inj (Option.some.inj (actualResolve.symm.trans resolved))
  obtain ⟨sameBinding,sameBuffer⟩ := same
  subst b
  subst buf
  obtain ⟨newSlot,newResolve⟩ := vector_destination s index ty writable binding buffer resolved lengths supported
  exact ⟨_,_,_,newSlot,newResolve,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def Targets (before after : NState) : Nat → List Field → Prop
  | _, [] => True
  | base, field::fields => Copied before after field base ∧ Targets before after (base+1) fields

theorem targets_source_kept {a b c : NState} (kept : Keeps a b) (scope : b.scope = a.scope)
    (fields : List Field) (base : Nat) (targets : Targets b c base fields) : Targets a c base fields := by
  induction fields generalizing base with
  | nil => trivial
  | cons field fields ih =>
    exact ⟨copied_source_kept kept scope field base targets.1,ih (base+1) targets.2⟩

theorem ready_keeps (fields : List Field) (before after : NState)
    (ready : Ready fields before after) : Keeps before after := by
  induction ready with
  | nil s => exact Keeps.refl s
  | scalar slot ty writable fields before after binding cell found tail ih =>
    exact (scalar_keeps before ty writable cell.value).trans ih
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    exact (vector_keeps before slot index ty writable binding buffer found resolved lengths supported).trans ih

theorem ready_targets (fields : List Field) (before after : NState)
    (ready : Ready fields before after) : Targets before after before.slots.length fields := by
  induction ready with
  | nil s => trivial
  | scalar slot ty writable fields before after binding cell found tail ih =>
    refine ⟨copied_target_kept (ready_keeps _ _ _ tail) _ _
      (scalar_copied before slot ty writable binding cell found),?_⟩
    have result := targets_source_kept (scalar_keeps before ty writable cell.value) rfl _ _ ih
    simpa [Proofs.CppClassCopyCommands.scalarStep,NState.declared,NState.charge,NState.observe] using result
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    have kept := vector_keeps before slot index ty writable binding buffer found resolved lengths supported
    refine ⟨copied_target_kept (ready_keeps _ _ _ tail) _ _
      (vector_copied before slot index ty writable binding buffer found resolved lengths supported),?_⟩
    have result := targets_source_kept kept rfl _ _ ih
    simpa [vectorResult,Proofs.CppCopyStatementFacts.result,NState.release,NState.charge,NState.observe] using result

theorem targets_at (before after : NState) (fields : List Field) (base i : Nat) (field : Field)
    (targets : Targets before after base fields) (found : fields[i]? = some field) :
    Copied before after field (base+i) := by
  induction fields generalizing base i with
  | nil => simp at found
  | cons head fields ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst head
      simpa using targets.1
    | succ i =>
      have result := ih (base+1) i targets.2 found
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

def vectorField : Field → Bool | .vector .. => true | .scalar .. => false
def scalarField : Field → Bool | .vector .. => false | .scalar .. => true

inductive FieldsCopied (before after : NState) : List Field → List Nat → Prop
  | nil : FieldsCopied before after [] []
  | cons {field slot fields slots} (head : Copied before after field slot)
      (tail : FieldsCopied before after fields slots) :
      FieldsCopied before after (field::fields) (slot::slots)

def ObjectCopies (before after : NState) (fields : List Field)
    (object : Proofs.CppConstructorMultiFinish.ObjectRef) : Prop :=
  FieldsCopied before after
    (fields.filter vectorField) object.vectorSlots ∧
  FieldsCopied before after
    (fields.filter scalarField) object.scalarSlots

theorem selected_targets (before after : NState) (base : Nat) (choose : Field → Bool)
    (entries : List (Field × Nat))
    (targets : ∀ entry ∈ entries, Copied before after entry.1 (base+entry.2)) :
    FieldsCopied before after
      ((entries.map Prod.fst).filter choose)
      (entries.filterMap (fun entry => if choose entry.1 then some (base+entry.2) else none)) := by
  induction entries with
  | nil => exact .nil
  | cons entry entries ih =>
    have tail := ih (fun e member => targets e (List.mem_cons_of_mem _ member))
    by_cases selected : choose entry.1 = true
    · simpa [selected] using FieldsCopied.cons (targets entry (by simp)) tail
    · simpa [selected] using tail

theorem targets_object (before after : NState) (fields : List Field)
    (targets : Targets before after before.slots.length fields) :
    ObjectCopies before after fields (reference before fields) := by
  have all (entry : Field × Nat) (member : entry ∈ fields.zipIdx) :
      Copied before after entry.1 (before.slots.length+entry.2) :=
    targets_at before after fields before.slots.length entry.2 entry.1 targets
      (List.mem_zipIdx_iff_getElem?.mp member)
  constructor
  · have selected := selected_targets before after before.slots.length vectorField fields.zipIdx all
    have same : (fun entry : Field × Nat => if vectorField entry.1 then some (before.slots.length+entry.2) else none) =
        (fun entry => match entry.1 with | .vector .. => some (before.slots.length+entry.2) | _ => none) := by
      funext entry
      cases entry.1 <;> rfl
    simpa only [List.zipIdx_map_fst,same,reference] using selected
  · have selected := selected_targets before after before.slots.length scalarField fields.zipIdx all
    have same : (fun entry : Field × Nat => if scalarField entry.1 then some (before.slots.length+entry.2) else none) =
        (fun entry => match entry.1 with | .scalar .. => some (before.slots.length+entry.2) | _ => none) := by
      funext entry
      cases entry.1 <;> rfl
    simpa only [List.zipIdx_map_fst,same,reference] using selected

theorem source_copy_values (s : NState) (fields : List Field) (good : Good s) (sources : Sources s fields) :
    ∃ after, runCopyFuel (fields.length+1) s fields = .finished ⟨after,none,false⟩ ∧
      Good after ∧ Keeps s after ∧ after.slots.length = s.slots.length+fields.length ∧
      after.scope = s.scope ∧ ObjectCopies s after fields (reference s fields) := by
  obtain ⟨after,ready,goodAfter,kept⟩ := sources_ready s fields good sources
  have shape := ready_shape fields s after ready
  exact ⟨after,copy_ready_complete fields s after (sources_validated s fields sources) ready,
    goodAfter,kept,shape.1,shape.2,targets_object s after fields (ready_targets fields s after ready)⟩

def Position (after : NState) (scope : Nat) : Field → Nat → Nat → Nat → Prop
  | .scalar _ ty _, slot, _, address =>
      ∃ binding cell, after.scalarCell slot ty = some (binding,cell) ∧ binding.address = address
  | .vector _ ty _, slot, owner, _ =>
      ∃ index binding buffer, after.vectorSlot slot = some index ∧
        after.frame.resolve index (.integer ty) = some (binding,buffer) ∧
        binding.header = .root scope ∧ binding.owner = owner ∧ buffer.owner = owner

def Placements (after : NState) (scope : Nat) : Nat → Nat → Nat → List Field → Prop
  | _,_,_,[] => True
  | slot,owner,address,(field@(.scalar ..))::fields =>
      Position after scope field slot owner address ∧ Placements after scope (slot+1) owner (address+1) fields
  | slot,owner,address,(field@(.vector ..))::fields =>
      Position after scope field slot owner address ∧ Placements after scope (slot+1) (owner+1) address fields

theorem position_kept {before after : NState} (kept : Keeps before after)
    (scope : Nat) (field : Field) (slot owner address : Nat)
    (position : Position before scope field slot owner address) :
    Position after scope field slot owner address := by
  cases field with
  | scalar source ty writable =>
    obtain ⟨binding,cell,found,located⟩ := position
    exact ⟨binding,cell,kept.1 _ _ _ _ found,located⟩
  | vector source ty writable =>
    obtain ⟨index,binding,buffer,found,resolved,root,located,owner⟩ := position
    obtain ⟨nextFound,nextResolve⟩ := kept.2 _ _ _ _ _ _ found resolved root
    exact ⟨index,binding,buffer,nextFound,nextResolve,root,located,owner⟩

theorem ready_placements (fields : List Field) (before after : NState)
    (ready : Ready fields before after) :
    Placements after before.scope before.slots.length before.frame.state.storage.objects.length
      before.scalars.memory.length fields := by
  induction ready with
  | nil s => trivial
  | scalar slot ty writable fields before after binding cell found tail ih =>
    have head : Position (Proofs.CppClassCopyCommands.scalarStep before ty writable cell.value)
        before.scope (.scalar slot ty writable) before.slots.length
        before.frame.state.storage.objects.length before.scalars.memory.length := by
      exact ⟨_,_,scalar_destination before ty writable cell.value
        (Proofs.CppClassCopyCommands.scalar_cell_facts before slot ty binding cell found).2,rfl⟩
    refine ⟨position_kept (ready_keeps _ _ _ tail) _ _ _ _ _ head,?_⟩
    simpa [Proofs.CppClassCopyCommands.scalarStep,NState.declared,NState.charge,NState.observe,
      Proofs.CppState.State.observe] using ih
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    obtain ⟨newSlot,newResolve⟩ := vector_destination before index ty writable binding buffer resolved lengths supported
    have head : Position (vectorResult before buffer ty writable) before.scope
        (.vector slot ty writable) before.slots.length before.frame.state.storage.objects.length
        before.scalars.memory.length := ⟨_,_,_,newSlot,newResolve,rfl,rfl,rfl⟩
    refine ⟨position_kept (ready_keeps _ _ _ tail) _ _ _ _ _ head,?_⟩
    simpa [vectorResult,Proofs.CppCopyStatementFacts.result,NState.release,NState.charge,NState.observe,
      Proofs.CppState.State.observe,Proofs.CppFrameCopy.copiedFrame,Proofs.CppNestedCopy.cloned] using ih

theorem ready_counts (fields : List Field) (before after : NState)
    (ready : Ready fields before after) :
    after.frame.state.storage.objects.length = before.frame.state.storage.objects.length +
        (fields.filter vectorField).length ∧
    after.scalars.memory.length = before.scalars.memory.length + (fields.filter scalarField).length := by
  induction ready with
  | nil s => exact ⟨by simp,by simp⟩
  | scalar slot ty writable fields before after binding cell found tail ih =>
    simpa [List.filter_cons,vectorField,scalarField,Proofs.CppClassCopyCommands.scalarStep,NState.declared,NState.charge,
      NState.observe,Proofs.CppState.State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    simpa [List.filter_cons,vectorField,scalarField,Proofs.CppCopyStatementFacts.result,NState.release,NState.charge,NState.observe,
      Proofs.CppState.State.observe,Proofs.CppFrameCopy.copiedFrame,Proofs.CppNestedCopy.cloned,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih

theorem placements_at (after : NState) (scope : Nat) (fields : List Field)
    (base owner address i : Nat) (field : Field)
    (placed : Placements after scope base owner address fields) (found : fields[i]? = some field) :
    Position after scope field (base+i) (owner+((fields.take i).filter vectorField).length)
      (address+((fields.take i).filter scalarField).length) := by
  induction fields generalizing base owner address i with
  | nil => simp at found
  | cons head fields ih =>
    cases head <;> cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst field
      simpa using placed.1
    | succ i =>
      have result := ih _ _ _ i placed.2 found
      simpa [List.take_succ_cons,List.filter_cons,vectorField,scalarField,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

theorem source_copy_positions (s : NState) (fields : List Field) (good : Good s) (sources : Sources s fields) :
    ∃ after, runCopyFuel (fields.length+1) s fields = .finished ⟨after,none,false⟩ ∧
      Good after ∧ Keeps s after ∧ after.slots.length = s.slots.length+fields.length ∧
      after.scope = s.scope ∧ ObjectCopies s after fields (reference s fields) ∧
      Placements after s.scope s.slots.length s.frame.state.storage.objects.length s.scalars.memory.length fields ∧
      after.frame.state.storage.objects.length = s.frame.state.storage.objects.length + (fields.filter vectorField).length ∧
      after.scalars.memory.length = s.scalars.memory.length + (fields.filter scalarField).length := by
  obtain ⟨after,ready,goodAfter,kept⟩ := sources_ready s fields good sources
  have shape := ready_shape fields s after ready
  have counts := ready_counts fields s after ready
  exact ⟨after,copy_ready_complete fields s after (sources_validated s fields sources) ready,
    goodAfter,kept,shape.1,shape.2,targets_object s after fields (ready_targets fields s after ready),
    ready_placements fields s after ready,counts.1,counts.2⟩

def vectorOwner (s : NState) (slot : Nat) (ty : Ty) : Option Nat := do
  let index ← s.vectorSlot slot
  let (binding,_) ← s.frame.resolve index (.integer ty)
  pure binding.owner

def scalarAddress (s : NState) (slot : Nat) (ty : Ty) : Option Nat := do
  let (binding,_) ← s.scalarCell slot ty
  pure binding.address

theorem placed_vector_owner (after : NState) (scope base owner address : Nat) (fields : List Field)
    (placed : Placements after scope base owner address fields)
    (i source : Nat) (ty : Ty) (writable : Bool) (found : fields[i]? = some (.vector source ty writable)) :
    vectorOwner after (base+i) ty = some (owner+((fields.take i).filter vectorField).length) := by
  obtain ⟨index,binding,buffer,slot,resolved,_,located,_⟩ :=
    placements_at after scope fields base owner address i (.vector source ty writable) placed found
  simp [vectorOwner,slot,resolved,located]

theorem placed_scalar_address (after : NState) (scope base owner address : Nat) (fields : List Field)
    (placed : Placements after scope base owner address fields)
    (i source : Nat) (ty : Ty) (writable : Bool) (found : fields[i]? = some (.scalar source ty writable)) :
    scalarAddress after (base+i) ty = some (address+((fields.take i).filter scalarField).length) := by
  obtain ⟨binding,cell,actual,located⟩ :=
    placements_at after scope fields base owner address i (.scalar source ty writable) placed found
  simp [scalarAddress,actual,located]

theorem selected_prefix_strict (choose : Field → Bool) (fields : List Field) (i j : Nat) (field : Field)
    (found : fields[i]? = some field) (selected : choose field = true) (earlier : i < j) :
    ((fields.take i).filter choose).length < ((fields.take j).filter choose).length := by
  induction fields generalizing i j with
  | nil => simp at found
  | cons head fields ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst head
      cases j with
      | zero => omega
      | succ j => simp [List.take_succ_cons,selected]
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have result := ih i j found (by omega)
        by_cases headSelected : choose head = true
        · simpa [List.take_succ_cons,headSelected] using result
        · simpa [List.take_succ_cons,headSelected] using result

theorem vector_owners_distinct (after : NState) (scope base owner address : Nat) (fields : List Field)
    (placed : Placements after scope base owner address fields) (i j sourceA sourceB : Nat)
    (tyA tyB : Ty) (writableA writableB : Bool)
    (first : fields[i]? = some (.vector sourceA tyA writableA))
    (second : fields[j]? = some (.vector sourceB tyB writableB)) (earlier : i < j) :
    vectorOwner after (base+i) tyA ≠ vectorOwner after (base+j) tyB := by
  rw [placed_vector_owner after scope base owner address fields placed i sourceA tyA writableA first,
    placed_vector_owner after scope base owner address fields placed j sourceB tyB writableB second]
  intro equal
  have strict := selected_prefix_strict vectorField fields i j (.vector sourceA tyA writableA) first rfl earlier
  exact (Nat.ne_of_lt (Nat.add_lt_add_left strict owner)) (Option.some.inj equal)

theorem scalar_addresses_distinct (after : NState) (scope base owner address : Nat) (fields : List Field)
    (placed : Placements after scope base owner address fields) (i j sourceA sourceB : Nat)
    (tyA tyB : Ty) (writableA writableB : Bool)
    (first : fields[i]? = some (.scalar sourceA tyA writableA))
    (second : fields[j]? = some (.scalar sourceB tyB writableB)) (earlier : i < j) :
    scalarAddress after (base+i) tyA ≠ scalarAddress after (base+j) tyB := by
  rw [placed_scalar_address after scope base owner address fields placed i sourceA tyA writableA first,
    placed_scalar_address after scope base owner address fields placed j sourceB tyB writableB second]
  intro equal
  have strict := selected_prefix_strict scalarField fields i j (.scalar sourceA tyA writableA) first rfl earlier
  exact (Nat.ne_of_lt (Nat.add_lt_add_left strict address)) (Option.some.inj equal)

theorem vector_old_separated (after : NState) (scope base owner address : Nat) (fields : List Field)
    (placed : Placements after scope base owner address fields)
    (i source oldOwner : Nat) (ty : Ty) (writable : Bool)
    (found : fields[i]? = some (.vector source ty writable)) (old : oldOwner < owner) :
    vectorOwner after (base+i) ty ≠ some oldOwner := by
  rw [placed_vector_owner after scope base owner address fields placed i source ty writable found]
  intro equal
  have strict := Nat.lt_of_lt_of_le old (Nat.le_add_right owner ((fields.take i).filter vectorField).length)
  exact (Nat.ne_of_gt strict) (Option.some.inj equal)

theorem scalar_old_separated (after : NState) (scope base owner address : Nat) (fields : List Field)
    (placed : Placements after scope base owner address fields)
    (i source oldAddress : Nat) (ty : Ty) (writable : Bool)
    (found : fields[i]? = some (.scalar source ty writable)) (old : oldAddress < address) :
    scalarAddress after (base+i) ty ≠ some oldAddress := by
  rw [placed_scalar_address after scope base owner address fields placed i source ty writable found]
  intro equal
  have strict := Nat.lt_of_lt_of_le old (Nat.le_add_right address ((fields.take i).filter scalarField).length)
  exact (Nat.ne_of_gt strict) (Option.some.inj equal)

def fieldWork (s : NState) : Field → Nat
  | .scalar .. => 2
  | .vector slot ty _ => ((s.vectorSlot slot >>= fun index =>
      s.frame.resolve index (.integer ty)).map (fun pair => pair.2.items.length+3)).getD 0

def copyWork (s : NState) (fields : List Field) : Nat := (fields.map (fieldWork s)).sum

theorem field_work_kept {before after : NState} (kept : Keeps before after)
    (field : Field) (source : Source before field) : fieldWork after field = fieldWork before field := by
  cases field with
  | scalar slot ty writable => rfl
  | vector slot ty writable =>
    obtain ⟨index,binding,buffer,scope,found,resolved,root,_⟩ := source
    obtain ⟨nextFound,nextResolved⟩ := kept.2 _ _ _ _ _ _ found resolved root
    simp [fieldWork,found,resolved,nextFound,nextResolved]

theorem copy_work_kept {before after : NState} (kept : Keeps before after)
    (fields : List Field) (sources : Sources before fields) : copyWork after fields = copyWork before fields := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    have head := field_work_kept kept field (sources field (by simp))
    have tail := ih (fun f member => sources f (List.mem_cons_of_mem _ member))
    change fieldWork after field + copyWork after fields = fieldWork before field + copyWork before fields
    rw [head,tail]

theorem ready_work (fields : List Field) (before after : NState)
    (ready : Ready fields before after) (sources : Sources before fields) :
    after.work = before.work + copyWork before fields := by
  induction ready with
  | nil s => simp [copyWork]
  | scalar slot ty writable fields before after binding cell found tail ih =>
    have kept := scalar_keeps before ty writable cell.value
    have tailSources : Sources before fields := fun f member => sources f (List.mem_cons_of_mem _ member)
    have result := ih (sources_kept kept fields tailSources)
    have cost := Proofs.CppClassCopyCommands.scalar_step_work before ty writable cell.value
    rw [copy_work_kept kept fields tailSources,cost] at result
    simpa [copyWork,fieldWork,Nat.add_assoc] using result
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    have kept := vector_keeps before slot index ty writable binding buffer found resolved lengths supported
    have tailSources : Sources before fields := fun f member => sources f (List.mem_cons_of_mem _ member)
    have result := ih (sources_kept kept fields tailSources)
    obtain ⟨tag,object⟩ := Proofs.CppFrameCopy.resolve_object before.frame index ty binding buffer resolved
    have valid := (Proofs.CppFrameCopy.object_parts before.frame binding.owner ty buffer tag object).1
    have cost : (vectorResult before buffer ty writable).work = before.work+buffer.items.length+3 :=
      Proofs.CppClassCopyCommands.vector_result_work before buffer ⟨ty,writable,[]⟩ valid
    change after.work = (vectorResult before buffer ty writable).work + copyWork (vectorResult before buffer ty writable) fields at result
    rw [copy_work_kept kept fields tailSources,cost] at result
    simpa [copyWork,fieldWork,found,resolved,Nat.add_assoc] using result

theorem source_copy_work (s : NState) (fields : List Field) (good : Good s) (sources : Sources s fields) :
    ∃ after, runCopyFuel (fields.length+1) s fields = .finished ⟨after,none,false⟩ ∧
      Good after ∧ Keeps s after ∧ after.slots.length = s.slots.length+fields.length ∧
      after.scope = s.scope ∧ ObjectCopies s after fields (reference s fields) ∧
      Placements after s.scope s.slots.length s.frame.state.storage.objects.length s.scalars.memory.length fields ∧
      after.frame.state.storage.objects.length = s.frame.state.storage.objects.length + (fields.filter vectorField).length ∧
      after.scalars.memory.length = s.scalars.memory.length + (fields.filter scalarField).length ∧
      after.work = s.work + copyWork s fields := by
  obtain ⟨after,ready,goodAfter,kept⟩ := sources_ready s fields good sources
  have shape := ready_shape fields s after ready
  have counts := ready_counts fields s after ready
  exact ⟨after,copy_ready_complete fields s after (sources_validated s fields sources) ready,
    goodAfter,kept,shape.1,shape.2,targets_object s after fields (ready_targets fields s after ready),
    ready_placements fields s after ready,counts.1,counts.2,ready_work fields s after ready sources⟩

open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.CppLoop

def scalarPeakBound (s : NState) (budget : Nat) : Nat := max s.scalars.peak (liveS s+budget)
def storagePeakBound (s : NState) (budget : Nat) : Nat := max s.frame.state.storage.peak
  (s.frame.state.liveSpace+budget-s.frame.state.storage.baseSpace)
def peakBound (s : NState) (budget : Nat) : Nat :=
  max s.peak (scalarPeakBound s budget+storagePeakBound s budget)

structure SpaceBounds (before after : NState) (budget : Nat) : Prop where
  storageBase : after.frame.state.storage.baseSpace = before.frame.state.storage.baseSpace
  scalarLive : liveS after ≤ liveS before+budget
  storageLive : after.frame.state.liveSpace ≤ before.frame.state.liveSpace+budget
  scalarPeak : after.scalars.peak ≤ scalarPeakBound before budget
  storagePeak : after.frame.state.storage.peak ≤ storagePeakBound before budget
  peak : after.peak ≤ peakBound before budget

theorem SpaceBounds.refl (s : NState) : SpaceBounds s s 0 := by
  refine ⟨rfl,by simp,by simp,?_,?_,?_⟩
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_left _ _

theorem scalar_bound_mono (s : NState) (p q : Nat) (small : p ≤ q) :
    scalarPeakBound s p ≤ scalarPeakBound s q := by
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.add_le_add_left small (liveS s)) (Nat.le_max_right _ _)⟩

theorem storage_bound_mono (s : NState) (p q : Nat) (small : p ≤ q) :
    storagePeakBound s p ≤ storagePeakBound s q := by
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.sub_le_sub_right (Nat.add_le_add_left small s.frame.state.liveSpace) _) (Nat.le_max_right _ _)⟩

theorem peak_bound_mono (s : NState) (p q : Nat) (small : p ≤ q) : peakBound s p ≤ peakBound s q := by
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.add_le_add (scalar_bound_mono s p q small) (storage_bound_mono s p q small)) (Nat.le_max_right _ _)⟩

theorem SpaceBounds.trans {a b c : NState} {first rest : Nat}
    (head : SpaceBounds a b first) (tail : SpaceBounds b c rest) : SpaceBounds a c (first+rest) := by
  have smaller : first ≤ first+rest := Nat.le_add_right _ _
  have scalarNext : scalarPeakBound b rest ≤ scalarPeakBound a (first+rest) := by
    refine Nat.max_le.mpr ⟨Nat.le_trans head.scalarPeak (scalar_bound_mono a first _ smaller),?_⟩
    have live : liveS b+rest ≤ liveS a+(first+rest) := by
      simpa only [Nat.add_assoc] using Nat.add_le_add_right head.scalarLive rest
    exact Nat.le_trans live (Nat.le_max_right _ _)
  have storageNext : storagePeakBound b rest ≤ storagePeakBound a (first+rest) := by
    refine Nat.max_le.mpr ⟨Nat.le_trans head.storagePeak (storage_bound_mono a first _ smaller),?_⟩
    have live : b.frame.state.liveSpace+rest ≤ a.frame.state.liveSpace+(first+rest) := by
      simpa only [Nat.add_assoc] using Nat.add_le_add_right head.storageLive rest
    rw [head.storageBase]
    exact Nat.le_trans (Nat.sub_le_sub_right live _) (Nat.le_max_right _ _)
  have outerNext : peakBound b rest ≤ peakBound a (first+rest) := by
    exact Nat.max_le.mpr ⟨Nat.le_trans head.peak (peak_bound_mono a first _ smaller),
      Nat.le_trans (Nat.add_le_add scalarNext storageNext) (Nat.le_max_right _ _)⟩
  refine ⟨tail.storageBase.trans head.storageBase,?_,?_,
    Nat.le_trans tail.scalarPeak scalarNext,Nat.le_trans tail.storagePeak storageNext,Nat.le_trans tail.peak outerNext⟩
  · simpa only [Nat.add_assoc] using Nat.le_trans tail.scalarLive (Nat.add_le_add_right head.scalarLive rest)
  · simpa only [Nat.add_assoc] using Nat.le_trans tail.storageLive (Nat.add_le_add_right head.storageLive rest)

theorem scalar_space (s : NState) (ty : Ty) (writable : Bool) (value : Int) :
    SpaceBounds s (Proofs.CppClassCopyCommands.scalarStep s ty writable value) 2 := by
  obtain ⟨live,scalar,peak⟩ := Proofs.CppClassCopyCommands.scalar_step_bounds s ty writable value
  have storage : (Proofs.CppClassCopyCommands.scalarStep s ty writable value).frame = s.frame := rfl
  refine ⟨rfl,live,?_,scalar,?_,?_⟩
  · rw [storage]
    omega
  · change s.frame.state.storage.peak ≤ max _ _
    exact Nat.le_max_left _ _
  · simp only [peakBound,scalarPeakBound,storagePeakBound]
    omega

theorem vector_space (s : NState) (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (ty : Ty) (writable : Bool) (valid : s.frame.state.wellFormed = true) :
    SpaceBounds s (vectorResult s buffer ty writable) (buffer.items.length+3) := by
  obtain ⟨scalar,storage,peak,live⟩ :=
    Proofs.CppClassCopyCommands.vector_result_peaks s buffer ⟨ty,writable,[]⟩ valid
  have resident := (Proofs.CppCopyStatementFacts.result_cost s (s.charge 1 1) buffer ty writable valid).2.1
  change (vectorResult s buffer ty writable).frame.state.liveSpace = s.frame.state.liveSpace+buffer.items.length+1 at resident
  change (vectorResult s buffer ty writable).scalars.peak = _ at scalar
  change (vectorResult s buffer ty writable).frame.state.storage.peak = _ at storage
  change (vectorResult s buffer ty writable).peak = _ at peak
  change liveS (vectorResult s buffer ty writable) = liveS s at live
  simp only [Proofs.CppClassCopyCommands.copiedStoragePeak] at storage peak
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · rw [live]
    omega
  · rw [resident]
    omega
  · simp only [scalarPeakBound]
    omega
  · simp only [storagePeakBound]
    omega
  · simp only [peakBound,scalarPeakBound,storagePeakBound]
    omega

theorem ready_space (fields : List Field) (before after : NState)
    (ready : Ready fields before after) (sources : Sources before fields) :
    SpaceBounds before after (copyWork before fields) := by
  induction ready with
  | nil s => exact SpaceBounds.refl s
  | scalar slot ty writable fields before after binding cell found tail ih =>
    have kept := scalar_keeps before ty writable cell.value
    have tailSources : Sources before fields := fun f member => sources f (List.mem_cons_of_mem _ member)
    have later := ih (sources_kept kept fields tailSources)
    have combined := (scalar_space before ty writable cell.value).trans later
    rw [copy_work_kept kept fields tailSources] at combined
    simpa only [copyWork,List.map_cons,List.sum_cons,fieldWork] using combined
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    have kept := vector_keeps before slot index ty writable binding buffer found resolved lengths supported
    have tailSources : Sources before fields := fun f member => sources f (List.mem_cons_of_mem _ member)
    have later := ih (sources_kept kept fields tailSources)
    obtain ⟨tag,object⟩ := Proofs.CppFrameCopy.resolve_object before.frame index ty binding buffer resolved
    have valid := (Proofs.CppFrameCopy.object_parts before.frame binding.owner ty buffer tag object).1
    have combined := (vector_space before buffer ty writable valid).trans later
    change SpaceBounds before after (buffer.items.length+3 + copyWork (vectorResult before buffer ty writable) fields) at combined
    rw [copy_work_kept kept fields tailSources] at combined
    simpa [copyWork,fieldWork,found,resolved] using combined

theorem source_copy_space (s : NState) (fields : List Field) (good : Good s) (sources : Sources s fields) :
    ∃ after, runCopyFuel (fields.length+1) s fields = .finished ⟨after,none,false⟩ ∧
      Good after ∧ Keeps s after ∧ after.slots.length = s.slots.length+fields.length ∧
      after.scope = s.scope ∧ ObjectCopies s after fields (reference s fields) ∧
      Placements after s.scope s.slots.length s.frame.state.storage.objects.length s.scalars.memory.length fields ∧
      after.frame.state.storage.objects.length = s.frame.state.storage.objects.length + (fields.filter vectorField).length ∧
      after.scalars.memory.length = s.scalars.memory.length + (fields.filter scalarField).length ∧
      after.work = s.work+copyWork s fields ∧ SpaceBounds s after (copyWork s fields) := by
  obtain ⟨after,ready,goodAfter,kept⟩ := sources_ready s fields good sources
  have shape := ready_shape fields s after ready
  have counts := ready_counts fields s after ready
  exact ⟨after,copy_ready_complete fields s after (sources_validated s fields sources) ready,
    goodAfter,kept,shape.1,shape.2,targets_object s after fields (ready_targets fields s after ready),
    ready_placements fields s after ready,counts.1,counts.2,ready_work fields s after ready sources,
    ready_space fields s after ready sources⟩

theorem invalid_source (fuel : Nat) (s : NState) (fields : List Field)
    (invalid : validate s fields = none) : runCopyFuel fuel s fields = .fault := by
  simp [runCopyFuel,invalid,liftChecked,Bind.bind,Outcome.bind]

end MemberCopy

namespace MemberCopy
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore

def PreservesContainers (before after : NState) : Prop :=
  ∀ slot index expected binding buffer,
    before.vectorSlot slot = some index →
    before.frame.resolve index expected = some (binding,buffer) →
    after.vectorSlot slot = some index ∧
      after.frame.resolve index expected = some (binding,buffer)

theorem ready_preserves_containers (fields : List Field) (before after : NState)
    (ready : Ready fields before after) : PreservesContainers before after := by
  induction ready with
  | nil s => intro slot index expected binding buffer found resolved; exact ⟨found,resolved⟩
  | scalar slot ty writable fields before after binding cell found tail ih =>
    intro oldSlot oldIndex expected oldBinding oldBuffer oldFound oldResolved
    have nextSlot := vector_slot_prefix before (Proofs.CppClassCopyCommands.scalarStep before ty writable cell.value) [.scalar before.scalars.bindings.length]
      rfl oldSlot oldIndex oldFound
    exact ih oldSlot oldIndex expected oldBinding oldBuffer nextSlot oldResolved
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    intro oldSlot oldIndex expected oldBinding oldBuffer oldFound oldResolved
    have extension := vector_extension before slot index ty writable binding buffer found resolved lengths supported
    have slots : (vectorResult before buffer ty writable).slots =
        before.slots++[.vector before.frame.bindings.length] := by
      simp [vectorResult,Proofs.CppCopyStatementFacts.result,NState.release,NState.charge,NState.observe]
    have nextSlot := vector_slot_prefix before _ _ slots oldSlot oldIndex oldFound
    have nextResolve := Proofs.CppFrameResolveExtension.resolve_kept _ _ extension oldIndex expected
      oldBinding oldBuffer oldResolved
    exact ih oldSlot oldIndex expected oldBinding oldBuffer nextSlot nextResolve

theorem source_copy_preserves_containers (s : NState) (fields : List Field)
    (good : Good s) (sources : Sources s fields) :
    ∃ after, runCopyFuel (fields.length+1) s fields = .finished ⟨after,none,false⟩ ∧
      Good after ∧ Keeps s after ∧ PreservesContainers s after := by
  obtain ⟨after,ready,goodAfter,kept⟩ := sources_ready s fields good sources
  exact ⟨after,copy_ready_complete fields s after (sources_validated s fields sources) ready,
    goodAfter,kept,ready_preserves_containers fields s after ready⟩
end MemberCopy

namespace MemberCopy
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings

def PreservesReferences (before after : NState) : Prop :=
  ∀ reference value, before.frame.read reference = some value → after.frame.read reference = some value

theorem ready_preserves_references (fields : List Field) (before after : NState)
    (ready : Ready fields before after) : PreservesReferences before after := by
  induction ready with
  | nil s => intro reference value actual; exact actual
  | scalar slot ty writable fields before after binding cell found tail ih =>
    intro reference value actual
    exact ih reference value actual
  | vector slot ty writable fields before after index binding buffer found resolved lengths supported tail ih =>
    intro reference value actual
    have extension := vector_extension before slot index ty writable binding buffer found resolved lengths supported
    exact ih reference value (Proofs.CppFrameExtension.read_kept _ _ extension reference value actual)

theorem source_copy_preserves_observers (s : NState) (fields : List Field)
    (good : Good s) (sources : Sources s fields) :
    ∃ after, runCopyFuel (fields.length+1) s fields = .finished ⟨after,none,false⟩ ∧
      Good after ∧ Keeps s after ∧ PreservesContainers s after ∧ PreservesReferences s after := by
  obtain ⟨after,ready,goodAfter,kept⟩ := sources_ready s fields good sources
  exact ⟨after,copy_ready_complete fields s after (sources_validated s fields sources) ready,
    goodAfter,kept,ready_preserves_containers fields s after ready,
    ready_preserves_references fields s after ready⟩
end MemberCopy

'''


def _field_layout(record, plan, stage, body):
    original = [n for n in record['inner'] if n.get('kind') == 'FieldDecl']
    layout = stage['_construction_fields']
    if len(layout) != len(original) or len(original) != len(plan['fields']):
        raise ValueError('constructor and copy field counts differ')
    result = []
    for ordinal, (field, copy_field, local) in enumerate(zip(original, plan['fields'], layout, strict=True)):
        if (field['id'] != copy_field['field_id'] or local.get('field_id') != field['id'] or
                local.get('declared_type') != spelling(field) or
                local.get('mutable') != bool(field.get('mutable')) or local['name'] != field['name']):
            raise ValueError('constructor and copy fields must share declaration identity and order')
        slot = body.slots[local['id']]
        binding = body.bindings[slot]
        vector = copy_field['kind'] in ('vector_copy','vector_assign')
        if vector:
            element = parse_element(copy_field['element'])
        else:
            # The vector parser excludes vector<bool>; ordinary scalar bool
            # members remain supported and must keep their boolean type.
            width, signed, boolean = TYPES[copy_field['type']]
            element = dict(width=width, signed=signed, boolean=boolean)
        if (binding['kind'] != ('vector' if vector else 'scalar') or binding['element'] != element or
                binding['writable'] != copy_field['writable']):
            raise ValueError('field slot type or declared permission differs from the audited copy')
        result.append(dict(name=field['name'], ordinal=ordinal, slot=slot,
                           kind='vector' if vector else 'scalar', element=element,
                           declared_writable=copy_field['writable'], mutable=bool(field.get('mutable'))))
    return result


def _verify_member_signature(source,result,owner,method,include_dirs):
    """Check declaration types in C++, including injected nested record names."""
    from clang_ast import clang_command
    from class_lowering import selected_type_pattern,scalar_record_type
    from ast_stream import _display_name
    target=result['_copy_qualified'];receiver=owner['_copy_qualified']
    pattern=selected_type_pattern(result,_display_name(result))
    if pattern is None:
        pattern=re.compile(r'(?:::)?(?:'+re.escape(target)+'|'+re.escape(_display_name(result))+')')
    arguments=[]
    for p in method.get('inner',[]):
        if p.get('kind')!='ParmVarDecl' or p.get('id') in method['_factory_receiver_fields']:continue
        ty=spelling(p)
        if scalar_record_type(p.get('type',{}),pattern):
            suffix=' &&' if ty.endswith('&&') else ' &' if ty.endswith('&') else ''
            bare=ty.removesuffix('&&').removesuffix('&').strip()
            ty=('const ' if bare.startswith('const ') or bare.endswith(' const') else '')+'::'+target+suffix
        arguments.append(ty)
    original=method['_factory_receiver']['method_type']
    suffix=original[original.rfind(')')+1:]
    returned=('const ' if original.split('(',1)[0].strip().startswith('const ') else '')+'::'+target
    prototype=returned+' (::'+receiver+'::*)('+','.join(arguments)+')'+suffix
    name=method['_factory_source_name']
    instance=method['_factory_receiver'].get('template_instance')
    if instance:
        name+='<' + ','.join(a if a in TYPES else '::'+a for a in instance['type_arguments']) + '>'
    identifiers=set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',prototype+' '+receiver+' '+name))
    identifiers.update(('__is_same','decltype','static_assert'))
    guard=' || '.join('defined('+n+')' for n in sorted(identifiers))
    probe=('#if '+guard+'\n#error record member signature keywords must not be macros\n#endif\n'
        'static_assert(__is_same(decltype(&::'+receiver+'::'+name+'),'+prototype+'),'
        '"selected receiver/member/result signature mismatch");\n')
    command=clang_command()
    for directory in include_dirs:command+=['-I',str(Path(directory).resolve(strict=True))]
    checked=subprocess.run([*command,'-include',str(source),'-'],input=probe,text=True,capture_output=True)
    if checked.returncode:
        raise ValueError('record member signature identity probe failed: '+checked.stderr)


def lower_class_layout(source, qualified, include_dirs=(), signed_conversion='checked', *, multiple_vectors=False,
                       template_instance=None, factory_exports=False, friend_exports=False, companion_instances=(), receiver_methods=()):
    from class_templates import RecordArgument,instantiate_members
    if not isinstance(receiver_methods,tuple) or any(not isinstance(r,tuple) or len(r) not in (2,3) or
            type(r[0]) is not int or r[0]<0 or not isinstance(r[1],str) or
            not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',r[1]) or
            (len(r)==3 and (not isinstance(r[2],tuple) or not r[2] or
                any(not isinstance(a,RecordArgument) and (not isinstance(a,str) or a not in TYPES) for a in r[2])))
            for r in receiver_methods):
        raise ValueError('receiver methods require structured record indices, names and optional type arguments')
    requests=[(r[0],r[1],r[2] if len(r)==3 else None) for r in receiver_methods]
    if not isinstance(companion_instances,tuple):
        raise ValueError('companion instances require a tuple of structured selections')
    if len(receiver_methods)!=len(set(receiver_methods)):
        raise ValueError('duplicate record-returning member request')
    if any(i>len(companion_instances) or any(isinstance(a,RecordArgument) and a.index>len(companion_instances)
            for a in (args or ())) for i,_,args in requests):
        raise ValueError('receiver record index is outside selected records')
    if receiver_methods and not factory_exports:
        raise ValueError('record-returning members require factory exports')
    if friend_exports and not factory_exports:
        raise ValueError('friend exports require factory exports')
    if factory_exports and not multiple_vectors:
        raise ValueError('factory exports require member exports')
    source = Path(source).resolve(strict=True)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    selected = qualified
    witness_digest = None
    if template_instance is not None:
        from class_templates import TemplateInstance
        if not isinstance(template_instance, TemplateInstance):
            raise ValueError('a structured template instance is required for class layout')
        selected = template_instance.target(qualified)
        witness_digest = hashlib.sha256(template_instance.witness.read_bytes()).hexdigest()
    records, callees = [], []
    _, roots = translation_unit(source, include_dirs, callees=callees,
                                copy_class=qualified, copy_records=records, template_instance=template_instance,
                                companion_instances=companion_instances)
    if len(records) != 1+len(companion_instances):
        raise ValueError('one original class and the requested companions are required')
    record = records[0]
    record['_copy_qualified'] = selected
    plan = audit_copy_record(source, selected, record, roots, include_dirs,
                             vector_anywhere=multiple_vectors, multiple_vectors=multiple_vectors)
    stages = class_construction_stages(record, source, standard_roots=roots, include_dirs=include_dirs)
    if not stages:
        raise ValueError('implicit default construction requires a separate stage model')
    if factory_exports:
        from ast_stream import member_factory_method
        from class_copy import audit_class_fields
        member_methods=[];selected_owners={}
        for index,name,args in requests:
            if index not in selected_owners:
                owner=records[index]
                owner['_copy_qualified']=selected if index==0 else companion_instances[index-1][1].target(companion_instances[index-1][0])
                audit_class_fields(source,owner['_copy_qualified'],owner,roots)
                instances={}
                for i,n,arguments in requests:
                    if i==index and arguments is not None:instances.setdefault(n,[]).append(arguments)
                if instances:owner,_=instantiate_members(owner,instances,record_arguments=records)
                selected_owners[index]=owner
            owner=selected_owners[index];model_name=name
            if args is not None:
                types=[records[a.index]['_template_witness_origin']['requested'] if isinstance(a,RecordArgument) else a for a in args]
                matches=[m for m in owner['inner'] if m.get('_member_template_instance',{}).get('source_name')==name and
                         m['_member_template_instance']['type_arguments']==types]
                if len(matches)!=1:raise ValueError('one selected member template instance required')
                model_name=matches[0]['name']
            member=member_factory_method(owner,model_name,index,source)
            _verify_member_signature(source,record,owner,member,include_dirs)
            member_methods.append(member)
        stages += class_factory_stages(record, source, include_friends=friend_exports,member_methods=member_methods,
                                       standard_roots=roots, include_dirs=include_dirs)
    if multiple_vectors:
        helpers = []
        for function in class_method_functions(record, source, include_constructors=False):
            if '_all_fields' not in function:
                function['_construction_helper'] = True
                helpers.append(function)
        stages = inline_functions(stages, [*helpers, *callees])
    audited = audit_vector_nodes(source, stages, roots, include_dirs)
    schemas = bindings_from_audit(source, audited, include_dirs)['functions']
    apply_conversion_policy([*audited['functions'], *callees], signed_conversion)
    calls = ValueCalls(callees)
    functions, probes, used_callees = [], [], {}
    for stage, schema in zip(audited['functions'], schemas, strict=True):
        body = NestedBody(stage, schema, calls, source)
        function = body.lower()
        function['parameters'] = schema['parameters']
        function['class_fields'] = _field_layout(record, plan, stage, body)
        if '_factory_stage' in stage:
            function['class_factory'] = stage['_factory_stage']
        if not multiple_vectors:
            vector, *scalars = function['class_fields']
            function['class_export'] = dict(vector_slot=vector['slot'], element=vector['element'],
                                           scalar_fields=[dict(slot=f['slot'], type=f['element']) for f in scalars])
        functions.append(function)
        probes.extend(body.probes)
        used_callees.update(body.callees)
    verify_type_probes(source, probes, include_dirs)
    if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
        raise ValueError('class source changed during layout generation')
    if template_instance is not None and hashlib.sha256(template_instance.witness.read_bytes()).hexdigest() != witness_digest:
        raise ValueError('template witness changed during layout generation')
    coverage = 'audited_constructor_and_factory_field_layout' if factory_exports else 'audited_constructor_field_layout'
    if friend_exports:
        coverage = 'audited_constructor_factory_and_friend_field_layout'
    if receiver_methods:
        coverage = 'audited_constructor_factory_and_record_member_field_layout'
    result = dict(coverage=coverage, qualified_class=selected, source_sha256=digest,
                  fields=[dict(name=f['name'], kind=f['kind'], writable=f['writable'],
                               mutable=bool(original.get('mutable')),
                               type=f.get('element', f.get('type')))
                          for original,f in zip([n for n in record['inner'] if n.get('kind')=='FieldDecl'],
                                                plan['fields'],strict=True)],
                  functions=functions, callees=[used_callees[name] for name in sorted(used_callees)])
    if template_instance is not None:
        result['template_instance'] = dict(arguments=list(template_instance.arguments),
            nested_members=list(template_instance.nested_members), witness_sha256=witness_digest,
            generic_types_verified=False, full_cpp_object_lifetime_verified=False)
    if companion_instances:
        result['companions']=[dict(qualified_class=q,arguments=list(i.arguments),nested_members=list(i.nested_members),
            selected_type=i.target(q)) for q,i in companion_instances]
    if receiver_methods:
        result['receiver_methods']=[dict(record_index=i,method=n,**(
            {'type_arguments':m['_factory_receiver']['template_instance']['type_arguments']} if args is not None else {}))
            for (i,n,args),m in zip(requests,member_methods,strict=True)]
    if signed_conversion != 'checked':
        result['signed_conversion'] = signed_conversion
    return result


SHARED_SUPPORT_IMPORTS = ['import Proofs.CppClassCopyCommands', 'import Proofs.CppConstructorMultiFinish', 'import Proofs.CppConstructorView', 'import Proofs.CppFrameResolveExtension', 'import Proofs.CppNestedCall']


def member_support_module():
    """The instance-independent support code shared by every member-export model (`Proofs/MemberSupport.lean`)."""
    return '\n'.join([*SHARED_SUPPORT_IMPORTS, MEMBER_VIEW_SUPPORT, MEMBER_COPY_SUPPORT,
                      MEMBER_FACTORY_SUPPORT, ''])


def emit_class_layout(source, qualified, namespace='Proofs.Generated.ClassLayout', include_dirs=(),
                      signed_conversion='checked', *, member_exports=False, template_instance=None,
                      factory_exports=False, friend_exports=False, companion_instances=(), receiver_methods=(), shared_support=False):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', namespace):
        raise ValueError('invalid Lean namespace')
    ir = lower_class_layout(source, qualified, include_dirs, signed_conversion, multiple_vectors=member_exports,
                            template_instance=template_instance, factory_exports=factory_exports,
                            friend_exports=friend_exports,companion_instances=companion_instances,receiver_methods=receiver_methods)
    # emit_lean validates the namespace and every emitted function identifier.
    program = emit_lean(ir, namespace+'.Stages', constructor_exports=member_exports,
                        share_commands=member_exports)
    if member_exports:
        coverage = 'constructor_and_factory_member_exports' if factory_exports else 'constructor_member_exports'
        if friend_exports:
            coverage = 'constructor_factory_and_friend_member_exports'
        if receiver_methods:
            coverage = 'constructor_factory_and_record_returning_member_exports'
        imports = (['import Proofs.MemberSupport'] if shared_support else
                   ['import Proofs.CppConstructorView', 'import Proofs.CppClassCopyCommands',
                    'import Proofs.CppFrameResolveExtension'])
        lines = [*imports, program, f'namespace {namespace}',
                 'open Proofs.CppNestedProgram Proofs.CppNestedCall',
                 f'def qualifiedClass : String := {json.dumps(ir["qualified_class"])}',
                 f'def sourceSHA256 : String := {json.dumps(ir["source_sha256"])}',
                 f'def coverage : String := {json.dumps(coverage)}']
        if not shared_support:
            lines += [MEMBER_VIEW_SUPPORT, MEMBER_COPY_SUPPORT]
            if factory_exports:
                lines.append(MEMBER_FACTORY_SUPPORT)
        if template_instance is not None:
            lines += [f'def templateWitnessSHA256 : String := {json.dumps(ir["template_instance"]["witness_sha256"])}',
                      'def genericTypesVerified : Bool := false',
                      'def fullObjectLifetimeVerified : Bool := false']
        def permission(field):
            return f"({str(field['writable']).lower()} && (!targetConst || {str(field['mutable']).lower()}))"
        def member_type(field):
            width, signed, boolean = TYPES[field['type']]
            return lean_type(dict(width=width,signed=signed,boolean=boolean))
        vector_flags = ','.join(permission(f) for f in ir['fields'] if f['kind']=='vector_copy')
        scalar_flags = ','.join(f'({member_type(f)},{permission(f)})'
                                for f in ir['fields'] if f['kind']=='scalar_copy')
        vector_binder = 'targetConst' if vector_flags else '_targetConst'
        lines += [f'def vectorPermissions ({vector_binder} : Bool) : List Bool := [{vector_flags}]',
                  f'def scalarPermissions (targetConst : Bool) : List (Proofs.CppScalar.Ty × Bool) := [{scalar_flags}]']
        fields = ir['fields']
        vectors = sum(f['kind']=='vector_copy' for f in fields)
        lines += ['def copyFields (source : Proofs.CppConstructorMultiFinish.ObjectRef) (targetConst : Bool) :',
                  '    Option (List MemberCopy.Field) := do',
                  f'  if source.vectorSlots.length != {vectors} || source.scalarSlots.length != {len(fields)-vectors}',
                  '      then none else pure ()']
        positions = {'vector_copy':0,'scalar_copy':0}
        descriptors = []
        for ordinal,field in enumerate(fields):
            vector = field['kind']=='vector_copy'
            kind = 'vector' if vector else 'scalar'
            slots = 'vectorSlots' if vector else 'scalarSlots'
            index = positions[field['kind']]
            positions[field['kind']] += 1
            lines.append(f'  let slot{ordinal} ← source.{slots}[{index}]?')
            descriptors.append(f'.{kind} slot{ordinal} {member_type(field)} {permission(field)}')
        lines += ['  pure ['+','.join(descriptors)+']',
                  'def copyFuel (fuel : Nat) (state : NState) (source : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (targetConst : Bool) : Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) := do',
                  '  let fields ← Proofs.CppLoop.liftChecked (copyFields source targetConst)',
                  '  let step ← MemberCopy.runCopyFuel fuel state fields',
                  '  if step.returned.isSome || step.breaking then .fault else',
                  '    pure (step.state,MemberCopy.reference state fields)',
                  'theorem copy_of_fields (state : NState) (source : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (targetConst : Bool) (fields : List MemberCopy.Field)',
                  '    (assembled : copyFields source targetConst = some fields)',
                  '    (good : MemberCopy.Good state) (sources : MemberCopy.Sources state fields) :',
                  '    ∃ after, copyFuel (fields.length+1) state source targetConst =',
                  '        .finished (after,MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Good after ∧ MemberCopy.Keeps state after := by',
                  '  obtain ⟨after,ran,goodAfter,kept⟩ := MemberCopy.source_copy_complete state fields good sources',
                  '  refine ⟨after,?_,goodAfter,kept⟩',
                  '  simp [copyFuel,assembled,ran,Proofs.CppLoop.liftChecked,Bind.bind,Proofs.CppLoop.Outcome.bind]; rfl',
                  'theorem copy_containers_of_fields (state : NState) (source : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (targetConst : Bool) (fields : List MemberCopy.Field)',
                  '    (assembled : copyFields source targetConst = some fields)',
                  '    (good : MemberCopy.Good state) (sources : MemberCopy.Sources state fields) :',
                  '    ∃ after, copyFuel (fields.length+1) state source targetConst =',
                  '        .finished (after,MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Good after ∧ MemberCopy.Keeps state after ∧',
                  '      MemberCopy.PreservesContainers state after := by',
                  '  obtain ⟨after,ran,goodAfter,kept,containers⟩ :=',
                  '    MemberCopy.source_copy_preserves_containers state fields good sources',
                  '  refine ⟨after,?_,goodAfter,kept,containers⟩',
                  '  simp [copyFuel,assembled,ran,Proofs.CppLoop.liftChecked,Bind.bind,Proofs.CppLoop.Outcome.bind]; rfl',
                  'theorem copy_observers_of_fields (state : NState) (source : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (targetConst : Bool) (fields : List MemberCopy.Field)',
                  '    (assembled : copyFields source targetConst = some fields)',
                  '    (good : MemberCopy.Good state) (sources : MemberCopy.Sources state fields) :',
                  '    ∃ after, copyFuel (fields.length+1) state source targetConst =',
                  '        .finished (after,MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Good after ∧ MemberCopy.Keeps state after ∧',
                  '      MemberCopy.PreservesContainers state after ∧ MemberCopy.PreservesReferences state after := by',
                  '  obtain ⟨after,ran,goodAfter,kept,containers,references⟩ :=',
                  '    MemberCopy.source_copy_preserves_observers state fields good sources',
                  '  refine ⟨after,?_,goodAfter,kept,containers,references⟩',
                  '  simp [copyFuel,assembled,ran,Proofs.CppLoop.liftChecked,Bind.bind,Proofs.CppLoop.Outcome.bind]; rfl',
                  'theorem copy_layout_of_fields (state : NState) (source : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (targetConst : Bool) (fields : List MemberCopy.Field)',
                  '    (assembled : copyFields source targetConst = some fields)',
                  '    (good : MemberCopy.Good state) (sources : MemberCopy.Sources state fields) :',
                  '    ∃ after, copyFuel (fields.length+1) state source targetConst =',
                  '        .finished (after,MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Good after ∧ MemberCopy.Keeps state after ∧',
                  '      after.slots.length = state.slots.length + fields.length ∧ after.scope = state.scope := by',
                  '  obtain ⟨after,ran,goodAfter,kept,slots,scope⟩ := MemberCopy.source_copy_layout state fields good sources',
                  '  refine ⟨after,?_,goodAfter,kept,slots,scope⟩',
                  '  simp [copyFuel,assembled,ran,Proofs.CppLoop.liftChecked,Bind.bind,Proofs.CppLoop.Outcome.bind]; rfl',
                  'theorem copy_values_of_fields (state : NState) (source : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (targetConst : Bool) (fields : List MemberCopy.Field)',
                  '    (assembled : copyFields source targetConst = some fields)',
                  '    (good : MemberCopy.Good state) (sources : MemberCopy.Sources state fields) :',
                  '    ∃ after, copyFuel (fields.length+1) state source targetConst =',
                  '        .finished (after,MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Good after ∧ MemberCopy.Keeps state after ∧',
                  '      after.slots.length = state.slots.length + fields.length ∧ after.scope = state.scope ∧',
                  '      MemberCopy.ObjectCopies state after fields (MemberCopy.reference state fields) := by',
                  '  obtain ⟨after,ran,goodAfter,kept,slots,scope,values⟩ := MemberCopy.source_copy_values state fields good sources',
                  '  refine ⟨after,?_,goodAfter,kept,slots,scope,values⟩',
                  '  simp [copyFuel,assembled,ran,Proofs.CppLoop.liftChecked,Bind.bind,Proofs.CppLoop.Outcome.bind]; rfl',
                  'theorem copy_positions_of_fields (state : NState) (source : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (targetConst : Bool) (fields : List MemberCopy.Field)',
                  '    (assembled : copyFields source targetConst = some fields)',
                  '    (good : MemberCopy.Good state) (sources : MemberCopy.Sources state fields) :',
                  '    ∃ after, copyFuel (fields.length+1) state source targetConst =',
                  '        .finished (after,MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Good after ∧ MemberCopy.Keeps state after ∧',
                  '      after.slots.length = state.slots.length + fields.length ∧ after.scope = state.scope ∧',
                  '      MemberCopy.ObjectCopies state after fields (MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Placements after state.scope state.slots.length state.frame.state.storage.objects.length',
                  '        state.scalars.memory.length fields ∧',
                  '      after.frame.state.storage.objects.length = state.frame.state.storage.objects.length +',
                  '        (fields.filter MemberCopy.vectorField).length ∧',
                  '      after.scalars.memory.length = state.scalars.memory.length + (fields.filter MemberCopy.scalarField).length := by',
                  '  obtain ⟨after,ran,goodAfter,kept,slots,scope,values,placed,vectors,scalars⟩ :=',
                  '    MemberCopy.source_copy_positions state fields good sources',
                  '  refine ⟨after,?_,goodAfter,kept,slots,scope,values,placed,vectors,scalars⟩',
                  '  simp [copyFuel,assembled,ran,Proofs.CppLoop.liftChecked,Bind.bind,Proofs.CppLoop.Outcome.bind]; rfl',
                  'theorem copy_work_of_fields (state : NState) (source : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (targetConst : Bool) (fields : List MemberCopy.Field)',
                  '    (assembled : copyFields source targetConst = some fields)',
                  '    (good : MemberCopy.Good state) (sources : MemberCopy.Sources state fields) :',
                  '    ∃ after, copyFuel (fields.length+1) state source targetConst =',
                  '        .finished (after,MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Good after ∧ MemberCopy.Keeps state after ∧',
                  '      after.slots.length = state.slots.length + fields.length ∧ after.scope = state.scope ∧',
                  '      MemberCopy.ObjectCopies state after fields (MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Placements after state.scope state.slots.length state.frame.state.storage.objects.length',
                  '        state.scalars.memory.length fields ∧',
                  '      after.frame.state.storage.objects.length = state.frame.state.storage.objects.length +',
                  '        (fields.filter MemberCopy.vectorField).length ∧',
                  '      after.scalars.memory.length = state.scalars.memory.length + (fields.filter MemberCopy.scalarField).length ∧',
                  '      after.work = state.work + MemberCopy.copyWork state fields := by',
                  '  obtain ⟨after,ran,goodAfter,kept,slots,scope,values,placed,vectors,scalars,work⟩ :=',
                  '    MemberCopy.source_copy_work state fields good sources',
                  '  refine ⟨after,?_,goodAfter,kept,slots,scope,values,placed,vectors,scalars,work⟩',
                  '  simp [copyFuel,assembled,ran,Proofs.CppLoop.liftChecked,Bind.bind,Proofs.CppLoop.Outcome.bind]; rfl',
                  'theorem copy_space_of_fields (state : NState) (source : Proofs.CppConstructorMultiFinish.ObjectRef)',
                  '    (targetConst : Bool) (fields : List MemberCopy.Field)',
                  '    (assembled : copyFields source targetConst = some fields)',
                  '    (good : MemberCopy.Good state) (sources : MemberCopy.Sources state fields) :',
                  '    ∃ after, copyFuel (fields.length+1) state source targetConst =',
                  '        .finished (after,MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Good after ∧ MemberCopy.Keeps state after ∧',
                  '      after.slots.length = state.slots.length + fields.length ∧ after.scope = state.scope ∧',
                  '      MemberCopy.ObjectCopies state after fields (MemberCopy.reference state fields) ∧',
                  '      MemberCopy.Placements after state.scope state.slots.length state.frame.state.storage.objects.length',
                  '        state.scalars.memory.length fields ∧',
                  '      after.frame.state.storage.objects.length = state.frame.state.storage.objects.length +',
                  '        (fields.filter MemberCopy.vectorField).length ∧',
                  '      after.scalars.memory.length = state.scalars.memory.length + (fields.filter MemberCopy.scalarField).length ∧',
                  '      after.work = state.work + MemberCopy.copyWork state fields ∧',
                  '      MemberCopy.SpaceBounds state after (MemberCopy.copyWork state fields) := by',
                  '  obtain ⟨after,ran,goodAfter,kept,slots,scope,values,placed,vectors,scalars,work,space⟩ :=',
                  '    MemberCopy.source_copy_space state fields good sources',
                  '  refine ⟨after,?_,goodAfter,kept,slots,scope,values,placed,vectors,scalars,work,space⟩',
                  '  simp [copyFuel,assembled,ran,Proofs.CppLoop.liftChecked,Bind.bind,Proofs.CppLoop.Outcome.bind]; rfl']
        for function in ir['functions']:
            name = function['name']
            lines += [f'def «{name}» : NProgram := Stages.«{name}»',
                      f'def «{name}_exportFuel» := Stages.«{name}».exportMembersFuel',
                      f'def «{name}_exportViewFuel» (fuel : Nat) (caller : NState)',
                      '    (arguments : List NArgument) (targetConst : Bool) :',
                      '    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=',
                      f'  MemberView.constructViewFuel Stages.«{name}» fuel caller arguments',
                      f'    Stages.«{name}».vectorFields Stages.«{name}».scalarFields',
                      '    (vectorPermissions targetConst) (scalarPermissions targetConst)']
            groups=function.get('class_factory',{}).get('arguments',[])
            if groups and all(g['kind'] in ('record_reference','record_value') for g in groups):
                by_value=any(g['kind']=='record_value' for g in groups)
                profiles=[];start=0
                for group in groups:
                    fields=[]
                    for parameter in function['parameters'][start:start+group['count']]:
                        fields.append('('+lean_type(parameter['element'])+','+str(parameter['writable']).lower()+')')
                    profile='['+', '.join(fields)+']'
                    profiles.append('('+str(group['kind']=='record_value').lower()+','+profile+')' if by_value else profile)
                    start+=group['count']
                argument_helper='objectArguments' if by_value else 'referenceArguments'
                lines += [f'def «{name}_exportObjectsFuel» (fuel : Nat) (caller : NState)',
                          '    (objects : List Proofs.CppConstructorMultiFinish.ObjectRef) (targetConst : Bool) :',
                          '    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=',
                          f'  match MemberFactory.{argument_helper} caller [{", ".join(profiles)}] objects with',
                          '  | none => .fault',
                          f'  | some args => «{name}_exportViewFuel» fuel caller args targetConst']
        return '\n'.join([*lines, f'end {namespace}', ''])
    lines = ['import Proofs.CppClassCopyCommands', 'import Proofs.CppConstructorView', program, f'namespace {namespace}',
             'open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish',
             f'def qualifiedClass : String := {json.dumps(ir["qualified_class"])}',
             f'def sourceSHA256 : String := {json.dumps(ir["source_sha256"])}']
    def field_type(field):
        width, signed, boolean = TYPES[field['type']]
        return lean_type(dict(width=width, signed=signed, boolean=boolean))
    vector, *scalars = ir['fields']
    def permission(field):
        return f"({str(field['writable']).lower()} && (!targetConst || {str(field['mutable']).lower()}))"
    profiles = ', '.join(f"({field_type(f)},{permission(f)})" for f in scalars)
    lines += [f"def profileFor (targetConst : Bool) : Proofs.CppClassCopy.Profile := ⟨{field_type(vector)},"
              f"{permission(vector)},[{profiles}]⟩",
              'def profile : Proofs.CppClassCopy.Profile := profileFor false',
              'def constProfile : Proofs.CppClassCopy.Profile := profileFor true',
              'def copy (state : NState) (source : ObjectRef) : Option (NState × ObjectRef) :=',
              '  Proofs.CppClassCopy.copyClass state source profile',
              'def copyConst (state : NState) (source : ObjectRef) : Option (NState × ObjectRef) :=',
              '  Proofs.CppClassCopy.copyClass state source constProfile',
              'def copyCommand (source : ObjectRef) (targetConst : Bool) : Option Command :=',
              '  Proofs.CppClassCopyCommands.copyCommand source (profileFor targetConst)',
              'def runCopyFuel (fuel : Nat) (state : NState) (source : ObjectRef) (targetConst : Bool) :',
              '    Proofs.CppLoop.Outcome NStep :=',
              '  Proofs.CppClassCopyCommands.runCopyFuel fuel state source (profileFor targetConst)']
    for function in ir['functions']:
        name = function['name']
        export = function['class_export']
        scalar_fields = ', '.join(f"⟨{f['slot']},{lean_type(f['type'])}⟩" for f in export['scalar_fields'])
        lines += [f'def «{name}» : NProgram := Stages.«{name}»',
                  f"def «{name}_vectorSlot» : Nat := {export['vector_slot']}",
                  f"def «{name}_scalarFields» : List ScalarField := [{scalar_fields}]",
                  f'def «{name}_exportFuel» (fuel : Nat) (caller : NState) (args : List NArgument) :',
                  '    Proofs.CppLoop.Outcome (NState × ObjectRef) :=',
                  f'  «{name}».constructFuel fuel caller args «{name}_vectorSlot»',
                  f"    (.integer {lean_type(export['element'])}) «{name}_scalarFields»",
                  f'def «{name}_exportViewFuel» (fuel : Nat) (caller : NState) (args : List NArgument)',
                  '    (targetConst : Bool) : Proofs.CppLoop.Outcome (NState × ObjectRef) :=',
                  f'  Proofs.CppConstructorView.constructProfileFuel «{name}» fuel caller args',
                  f'    «{name}_vectorSlot» «{name}_scalarFields» (profileFor targetConst)']
    return '\n'.join([*lines, f'end {namespace}', ''])
