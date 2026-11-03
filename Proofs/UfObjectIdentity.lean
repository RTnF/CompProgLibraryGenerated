import Proofs.UfObjectValues

namespace Proofs.UfObjectIdentity
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppMoveCallLayout
open Proofs.CppConstructorFinish Proofs.CppScalar Proofs.CppNestedProgram Proofs.DoublingNested

theorem field_address (s out : Context) (ty : Ty) (before : Field s ty) (after : Field out ty)
    (layout : Layout s out) (slot : before.slot = after.slot) : after.address = before.address := by
  have oldLocated : scalarSlot out before.slot = some before.index := by
    simpa only [scalarSlot,layout.slots] using before.located
  rw [slot] at oldLocated
  have sameIndex := Option.some.inj (oldLocated.symm.trans after.located)
  have oldBound : out.scalars.bindings[before.index]? = some ⟨before.address,before.writable⟩ := by
    rw [layout.bindings]
    exact before.bound
  rw [sameIndex] at oldBound
  have sameBinding := Option.some.inj (oldBound.symm.trans after.bound)
  exact (congrArg Proofs.CppState.Binding.address sameBinding).symm

theorem receiver (s out : Context) (object : ObjectRef) (ty : Ty)
    (before : Receiver s object ty) (after : Receiver out object ty) (layout : Layout s out) :
    after.counter.address = before.counter.address ∧ after.size.address = before.size.address ∧
      after.view = before.view ∧ after.header = before.header := by
  have fields := List.cons.inj (before.fields.symm.trans after.fields)
  have counter := field_address s out ty before.counter after.counter layout fields.1
  have size := field_address s out ty before.size after.size layout (List.cons.inj fields.2).1
  have oldLocated : vectorView out object.vectorSlot = some before.viewSlot := by
    simpa only [vectorView,layout.slots] using before.located
  have sameSlot := Option.some.inj (oldLocated.symm.trans after.located)
  have oldResolved : Proofs.CppMoveViews.resolve out.objects before.viewSlot = some (before.view,before.header) := by
    simpa only [Proofs.CppMoveViews.resolve,Proofs.CppMoveHeaders.Heap.header,layout.views,layout.headers] using before.resolved
  rw [sameSlot] at oldResolved
  have samePair := Prod.mk.inj (Option.some.inj (oldResolved.symm.trans after.resolved))
  exact ⟨counter,size,samePair.1.symm,samePair.2.symm⟩

theorem state (s out : Context) (object : ObjectRef)
    (before : Proofs.UfObjectState.State s object) (after : Proofs.UfObjectState.State out object)
    (layout : Layout s out) :
    after.data.owner = before.data.owner ∧ after.receiver.counter.address = before.receiver.counter.address ∧
      after.receiver.size.address = before.receiver.size.address := by
  have identity := receiver s out object i32 before.receiver after.receiver layout
  have oldHeader := (Proofs.CppMoveViews.resolve_parts s.objects before.receiver.viewSlot before.receiver.view before.receiver.header before.receiver.resolved).2.1
  have newHeader := (Proofs.CppMoveViews.resolve_parts out.objects after.receiver.viewSlot after.receiver.view after.receiver.header after.receiver.resolved).2.1
  obtain ⟨oldData,oldCurrent,oldEntry,oldValid,oldLimit,oldOwner⟩ := Proofs.CppMoveReceiverFrame.current_entry s.objects.heap i32
    before.receiver.view.header before.receiver.header oldHeader before.readable before.unique before.covered
  obtain ⟨newData,newCurrent,newEntry,newValid,newLimit,newOwner⟩ := Proofs.CppMoveReceiverFrame.current_entry out.objects.heap i32
    after.receiver.view.header after.receiver.header newHeader after.readable after.unique after.covered
  have oldEq := Option.some.inj (oldCurrent.symm.trans before.current)
  have newEq := Option.some.inj (newCurrent.symm.trans after.current)
  subst oldData
  subst newData
  refine ⟨?_,identity.1,identity.2.1⟩
  rw [newOwner,oldOwner,identity.2.2.1,identity.2.2.2,layout.allocations]

end Proofs.UfObjectIdentity
