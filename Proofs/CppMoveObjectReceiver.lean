import Proofs.CppMoveReceiverResolve

namespace Proofs.CppMoveObjectReceiver
open Proofs.CppScalar Proofs.CppMoveContext Proofs.CppMoveReceiverResolve
open Proofs.CppConstructorFinish Proofs.CppNestedProgram

-- Primitive caller layout facts; a completed scalarCell run is not a field.
structure Field (s : Context) (ty : Ty) where
  slot : Nat
  index : Nat
  address : Nat
  writable : Bool
  value : Int
  located : scalarSlot s slot = some index
  bound : s.scalars.bindings[index]? = some ⟨address,writable⟩
  found : s.scalars.memory[address]? = some ⟨ty,value⟩
  valid : ty.valid value = true

theorem Field.cell (s : Context) (ty : Ty) (field : Field s ty) :
    (project s ty).scalarCell field.slot ty = some (⟨field.address,field.writable⟩,⟨ty,field.value⟩) := by
  rw [project_scalarCell]
  simp [field.located,field.bound,field.found,field.valid]

structure Receiver (s : Context) (object : ObjectRef) (ty : Ty) where
  counter : Field s ty
  size : Field s ty
  fields : object.scalarSlots = [counter.slot,size.slot]
  counterWritable : counter.writable = true
  viewSlot : Nat
  view : Proofs.CppMoveViews.View
  header : Proofs.CppMoveHeaders.Header
  located : vectorView s object.vectorSlot = some viewSlot
  resolved : Proofs.CppMoveViews.resolve s.objects viewSlot = some (view,header)
  writable : view.writable = true

theorem Receiver.capture (s : Context) (object : ObjectRef) (ty : Ty) (receiver : Receiver s object ty) :
    captureBorrow s object.vectorSlot true = some ⟨receiver.view.header,true⟩ := by
  apply captureBorrow_runs s object.vectorSlot receiver.viewSlot true receiver.view receiver.header
    receiver.located receiver.resolved
  intro _
  exact receiver.writable

theorem Receiver.resolve (s : Context) (object : ObjectRef) (ty : Ty) (receiver : Receiver s object ty)
    (expressions : List (NExpr × Int)) (ready : Ready s ty expressions) :
    ∃ last, resolveArguments s ty
      (.vector ty true :: .scalar ty true true :: .scalar ty false true :: parameters ty expressions)
      (.vectorReference object.vectorSlot :: .scalarReference receiver.counter.slot ::
        .value (.variable ty receiver.size.slot) :: arguments expressions) =
      some (last,Proofs.CppMoveReceiverLayout.receiverArguments ⟨receiver.view.header,true⟩ ty
        receiver.counter.address true (receiver.size.value::values expressions)) := by
  exact resolve_fields s ty object.vectorSlot receiver.counter.slot receiver.size.slot ⟨receiver.view.header,true⟩
    ⟨receiver.counter.address,receiver.counter.writable⟩ ⟨receiver.size.address,receiver.size.writable⟩
    receiver.counter.value receiver.size.value (Receiver.capture s object ty receiver) (Field.cell s ty receiver.counter)
    (Field.cell s ty receiver.size) receiver.counterWritable expressions ready

end Proofs.CppMoveObjectReceiver
