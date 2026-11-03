import Proofs.CppMoveObjectReceiver
import Proofs.CppMoveCallBindings

namespace Proofs.CppMoveCallLayout
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppMoveRestore
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppScalar Proofs.CppLoop
open Proofs.CppConstructorFinish Proofs.DynamicResultValid

structure Layout (before after : Context) : Prop where
  slots : after.slots = before.slots
  scope : after.scope = before.scope
  bindings : after.scalars.bindings = before.scalars.bindings
  baseline : after.scalars.baseMemory = before.scalars.baseMemory
  memoryLength : after.scalars.memory.length = before.scalars.memory.length
  headers : after.objects.heap.headers = before.objects.heap.headers
  grants : after.objects.heap.grants = before.objects.heap.grants
  views : after.objects.views = before.objects.views
  allocations : after.objects.heap.allocations.length = before.objects.heap.allocations.length
  heapBaseline : after.objects.heap.baseSpace = before.objects.heap.baseSpace

theorem restore_layout (s out : Context) (ty : Ty) (after : NState)
    (restored : restoreContext s ty after = some out) : Layout s out := by
  unfold restoreContext at restored
  split at restored
  next good =>
    obtain ⟨objects,run,done⟩ := bind_some _ _ _ restored
    have equal := Option.some.inj done
    subst out
    obtain ⟨headers,grants,views,len,work,peak,base,same⟩ := restore_metadata s.objects objects ty after.frame run
    exact ⟨rfl,rfl,good.2.2.2.1,good.2.2.2.2.2,good.2.2.2.2.1,
      headers,grants,views,len,base.trans (congrArg Shape.base same)⟩
  next => simp at restored

theorem outcome_bind_finished {α β : Type} (first : Outcome α) (next : α → Outcome β) (out : β)
    (run : Outcome.bind first next = .finished out) :
    ∃ value, first = .finished value ∧ next value = .finished out := by
  cases first with
  | fault => simp [Outcome.bind] at run
  | exhausted => simp [Outcome.bind] at run
  | finished value => exact ⟨value,rfl,run⟩

theorem checked_bind_finished {α β : Type} (first : Option α) (next : α → Outcome β) (out : β)
    (run : Outcome.bind (liftChecked first) next = .finished out) :
    ∃ value, first = some value ∧ next value = .finished out := by
  cases first with
  | none => simp [liftChecked,Outcome.bind] at run
  | some value => exact ⟨value,rfl,run⟩

-- Successful calls expose the actual checked restoration, including failure guards.
theorem call_restored (program : NProgram) (fuel : Nat) (s out : Context) (ty : Ty)
    (arguments : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result)) : ∃ after, restoreContext s ty after = some out := by
  unfold Proofs.CppMoveCallBindings.callFuel at run
  split at run
  next =>
    obtain ⟨prepared,_,rest⟩ := checked_bind_finished _ _ _ run
    obtain ⟨initial,_,rest⟩ := checked_bind_finished _ _ _ rest
    obtain ⟨step,_,rest⟩ := outcome_bind_finished _ _ _ rest
    split at rest
    next => simp at rest
    next =>
      obtain ⟨pair,_,rest⟩ := checked_bind_finished _ _ _ rest
      rcases pair with ⟨after,value⟩
      obtain ⟨actual,restored,done⟩ := checked_bind_finished _ _ _ rest
      have equal : (actual,value) = (out,result) := Outcome.finished.inj done
      have state := (Prod.mk.inj equal).1
      subst actual
      exact ⟨after,restored⟩
  next => simp at run

-- These are effects of a completed call. Normal termination is still derived
-- separately from the source receiver/heap/algorithm conditions.
theorem call_layout (program : NProgram) (fuel : Nat) (s out : Context) (ty : Ty)
    (arguments : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result)) : Layout s out := by
  obtain ⟨after,restored⟩ := call_restored program fuel s out ty arguments result run
  exact restore_layout s out ty after restored

theorem restore_objects (s out : Context) (ty : Ty) (after : NState)
    (restored : restoreContext s ty after = some out) : restore s.objects ty after.frame = some out.objects := by
  unfold restoreContext at restored
  split at restored
  next =>
    obtain ⟨objects,run,done⟩ := bind_some _ _ _ restored
    have equal := Option.some.inj done
    subst out
    exact run
  next => simp at restored

theorem call_objects (program : NProgram) (fuel : Nat) (s out : Context) (ty : Ty)
    (arguments : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result)) :
    ∃ (after : NState), restore s.objects ty after.frame = some out.objects := by
  obtain ⟨after,restored⟩ := call_restored program fuel s out ty arguments result run
  exact ⟨after,restore_objects s out ty after restored⟩

theorem call_allocationsValid (program : NProgram) (fuel : Nat) (s out : Context) (ty : Ty)
    (arguments : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result)) :
    Proofs.CppMoveFrame.AllocationsValid out.objects.heap ty := by
  obtain ⟨after,restored⟩ := call_objects program fuel s out ty arguments result run
  exact restore_allocationsValid s.objects out.objects ty after.frame restored

theorem call_unique (program : NProgram) (fuel : Nat) (s out : Context) (ty : Ty)
    (arguments : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result))
    (unique : Proofs.CppMoveHeaders.Unique s.objects.heap) : Proofs.CppMoveHeaders.Unique out.objects.heap := by
  obtain ⟨after,restored⟩ := call_objects program fuel s out ty arguments result run
  exact restore_unique s.objects out.objects ty after.frame restored unique

theorem call_ownsAll (program : NProgram) (fuel : Nat) (s out : Context) (ty : Ty)
    (arguments : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result))
    (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap) : Proofs.CppMoveHeaders.OwnsAll out.objects.heap := by
  obtain ⟨after,restored⟩ := call_objects program fuel s out ty arguments result run
  exact restore_ownsAll s.objects out.objects ty after.frame restored covered

theorem restore_readable (s out : Proofs.CppMoveViews.State Int) (ty : Ty)
    (after : Proofs.CppNestedVectorBindings.Frame) (restored : restore s ty after = some out)
    (header : Proofs.CppMoveHeaders.Header)
    (readable : Proofs.CppMoveHeaders.readable s.heap header ty.valid = true) :
    Proofs.CppMoveHeaders.readable out.heap header ty.valid = true := by
  cases owns : header.allocation with
  | none => simp [Proofs.CppMoveHeaders.readable,owns]
  | some owner =>
    cases found : s.heap.allocation owner with
    | none => simp [Proofs.CppMoveHeaders.readable,owns,found] at readable
    | some old =>
      have oldValid : old.buffer.owner = owner ∧ old.buffer.limit = header.limit ∧ old.buffer.Valid ty.valid := by
        simpa [Proofs.CppMoveHeaders.readable,owns,found] using readable
      obtain ⟨next,nextFound,lookup,signature,ownerEq,valid,generation⟩ := restore_allocation s out ty after restored owner old found
      have limit := congrArg Proofs.CppBufferHeaders.Signature.limit signature
      change next.buffer.limit = old.buffer.limit at limit
      simp [Proofs.CppMoveHeaders.readable,owns,nextFound,ownerEq,limit,oldValid.2.1,valid]

theorem call_readable (program : NProgram) (fuel : Nat) (s out : Context) (ty : Ty)
    (arguments : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result))
    (header : Proofs.CppMoveHeaders.Header)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap header ty.valid = true) :
    Proofs.CppMoveHeaders.readable out.objects.heap header ty.valid = true := by
  obtain ⟨after,restored⟩ := call_objects program fuel s out ty arguments result run
  exact restore_readable s.objects out.objects ty after.frame restored header readable

theorem call_contexts (program : NProgram) (fuel : Nat) (s out : Context) (ty : Ty)
    (arguments : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result))
    (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap)
    (contexts : ∀ owner sc, (project s ty).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∀ owner sc, (project out ty).frame.state.forest.context owner = some sc → sc ≤ out.scope := by
  obtain ⟨after,restored⟩ := call_objects program fuel s out ty arguments result run
  have forest := restore_forest s.objects out.objects ty after.frame restored covered
  have layout := call_layout program fuel s out ty arguments result run
  intro owner sc found
  change (Proofs.CppMoveFrame.materialize out.objects ty).frame.state.forest.context owner = some sc at found
  rw [forest] at found
  rw [layout.scope]
  exact contexts owner sc found

theorem Layout.prefix_length (s out : Context) (layout : Layout s out) :
    (Proofs.CppMoveReceiverLayout.receiverPrefix out).length =
      (Proofs.CppMoveReceiverLayout.receiverPrefix s).length := by
  simp [Proofs.CppMoveReceiverLayout.receiverPrefix,layout.memoryLength,layout.slots]

theorem Layout.baseline_fits (s out : Context) (layout : Layout s out)
    (fits : s.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix s).length) :
    out.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix out).length := by
  rw [layout.baseline,Layout.prefix_length s out layout]
  exact fits

def Field.update (s out : Context) (ty : Ty) (field : Field s ty) (layout : Layout s out)
    (value : Int) (found : out.scalars.memory[field.address]? = some ⟨ty,value⟩)
    (valid : ty.valid value = true) : Field out ty :=
  ⟨field.slot,field.index,field.address,field.writable,value,
    by simpa only [scalarSlot,layout.slots] using field.located,
    by rw [layout.bindings]; exact field.bound,found,valid⟩

def Receiver.update (s out : Context) (object : ObjectRef) (ty : Ty) (receiver : Receiver s object ty)
    (layout : Layout s out) (count size : Int)
    (counter : out.scalars.memory[receiver.counter.address]? = some ⟨ty,count⟩)
    (countValid : ty.valid count = true)
    (sizeCell : out.scalars.memory[receiver.size.address]? = some ⟨ty,size⟩)
    (sizeValid : ty.valid size = true) : Receiver out object ty :=
  ⟨Field.update s out ty receiver.counter layout count counter countValid,
    Field.update s out ty receiver.size layout size sizeCell sizeValid,receiver.fields,
    receiver.counterWritable,receiver.viewSlot,receiver.view,receiver.header,
    by simpa only [vectorView,layout.slots] using receiver.located,
    by simpa only [Proofs.CppMoveViews.resolve,Proofs.CppMoveHeaders.Heap.header,layout.views,layout.headers]
      using receiver.resolved,receiver.writable⟩

end Proofs.CppMoveCallLayout
