import Proofs.CppMoveObjectReceiver

namespace Proofs.CppMoveReadReceiver
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppConstructorFinish Proofs.CppScalar

-- Reading and copying require valid loads, not permission to mutate the source.
structure ReadReceiver (s : Context) (object : ObjectRef) (ty : Ty) where
  counter : Field s ty
  size : Field s ty
  fields : object.scalarSlots = [counter.slot,size.slot]
  viewSlot : Nat
  view : Proofs.CppMoveViews.View
  header : Proofs.CppMoveHeaders.Header
  located : vectorView s object.vectorSlot = some viewSlot
  resolved : Proofs.CppMoveViews.resolve s.objects viewSlot = some (view,header)

def of_mutable (s : Context) (object : ObjectRef) (ty : Ty) (receiver : Receiver s object ty) : ReadReceiver s object ty :=
  ⟨receiver.counter,receiver.size,receiver.fields,receiver.viewSlot,receiver.view,receiver.header,receiver.located,receiver.resolved⟩

theorem project_ready (s : Context) (object : ObjectRef) (ty : Ty) (receiver : ReadReceiver s object ty)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header ty.valid = true)
    (unique : Proofs.CppMoveHeaders.Unique s.objects.heap) (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap)
    (supported : Proofs.CppVectorBindings.supported ty) (valid : Proofs.CppMoveFrame.AllocationsValid s.objects.heap ty) :
    ∃ buffer, Proofs.CppMoveFrame.currentBuffer s.objects.heap receiver.view.header receiver.header = some buffer ∧
      (project s ty).vectorSlot object.vectorSlot = some (s.objects.heap.grants.length+receiver.viewSlot) ∧
      (project s ty).frame.resolve (s.objects.heap.grants.length+receiver.viewSlot) (.integer ty) =
        some (⟨buffer.owner,.integer ty,receiver.view.writable,.root receiver.header.scope⟩,Proofs.CppMoveFrame.box buffer) :=
  project_view_ready s ty object.vectorSlot receiver.viewSlot receiver.view receiver.header receiver.located receiver.resolved
    readable unique covered supported valid

end Proofs.CppMoveReadReceiver
