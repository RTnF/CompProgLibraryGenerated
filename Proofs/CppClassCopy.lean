import Proofs.CppFrameCopy
import Proofs.CppConstructorFinish

namespace Proofs.CppClassCopy
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppConstructorFinish Proofs.CppFrameCopy

-- A profile describes a vector followed by scalar fields in declaration order.
-- Source constness does not decide the permissions of the copied members.
structure Profile where
  element : Ty
  vectorWritable : Bool
  scalarFields : List (Ty × Bool)
deriving DecidableEq, Repr

def capture (s : NState) (slot : Nat) (field : Ty × Bool) : Option ScalarValue := do
  let (_,cell) ← s.scalarCell slot field.1
  some (cell,field.2)

def captureAll (s : NState) (slots : List Nat) (fields : List (Ty × Bool)) : Option (List ScalarValue) :=
  if slots.length = fields.length then
    (slots.zip fields).mapM fun pair => capture s pair.1 pair.2
  else none

def finish (s : NState) (frame : Frame) (vectorBinding : Nat) (values : List ScalarValue) : NState :=
  let scalars : Proofs.CppState.State := {s.scalars with
    memory := s.scalars.memory++values.map Prod.fst
    bindings := s.scalars.bindings++scalarBindings s.scalars.memory.length values
    work := s.scalars.work+(values.length+1)}
  ({s with
    scalars := scalars.observe 0
    frame := frame
    slots := s.slots++(.vector vectorBinding :: scalarLocations s.scalars.bindings.length values.length)} : NState).observe

def copyClass (s : NState) (source : ObjectRef) (profile : Profile) : Option (NState × ObjectRef) := do
  let index ← s.vectorSlot source.vectorSlot
  let (frame,binding) ← copyVector s.frame index profile.element s.scope profile.vectorWritable
  let values ← captureAll s source.scalarSlots profile.scalarFields
  some (finish s frame binding values,reference s values.length)

theorem capture_two (s : NState) (first second : Nat) (a b : Ty × Bool)
    (ba bb : Proofs.CppState.Binding) (ca cb : Proofs.CppState.Cell)
    (one : s.scalarCell first a.1 = some (ba,ca)) (two : s.scalarCell second b.1 = some (bb,cb)) :
    captureAll s [first,second] [a,b] = some [(ca,a.2),(cb,b.2)] := by
  simp [captureAll,capture,one,two]

theorem copy_runs (s : NState) (source : ObjectRef) (profile : Profile)
    (index binding : Nat) (frame : Frame) (values : List ScalarValue)
    (slot : s.vectorSlot source.vectorSlot = some index)
    (copied : copyVector s.frame index profile.element s.scope profile.vectorWritable = some (frame,binding))
    (captured : captureAll s source.scalarSlots profile.scalarFields = some values) :
    copyClass s source profile = some (finish s frame binding values,reference s values.length) := by
  simp [copyClass,slot,copied,captured]

end Proofs.CppClassCopy

