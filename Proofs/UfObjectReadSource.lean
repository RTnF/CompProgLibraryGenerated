import Proofs.CppMoveReadReceiver
import Proofs.UfAssignmentView
import Proofs.UfCopyReceiver
import Proofs.CppMoveReceiverFrame

namespace Proofs.UfObjectReadSource
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppConstructorFinish Proofs.CppNestedProgram
open Proofs.CppMoveFrame Proofs.CppMoveHeaders Proofs.CppVector Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppMoveReadReceiver Proofs.UfReceiverState Proofs.UfAssignmentView Proofs.DoublingNested
open Proofs.CppFrameCopy Proofs.UfCopyFields Proofs.CppNestedCopy Proofs.CppNestedConstruct

def layout (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32) (data : Buffer Int) : Layout :=
  ⟨object.vectorSlot,s.objects.heap.grants.length+receiver.viewSlot,data.owner,receiver.header.scope,receiver.counter.slot,receiver.size.slot⟩

theorem source_view (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (rank : Nat → Nat)
    (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (math : Proofs.UfClassInvariant.Valid data.items receiver.counter.value rank)
    (size : receiver.size.value = (data.items.length : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32) :
    SourceView (project s i32) (layout s object receiver data) data.items receiver.counter.value rank (box data)
      ⟨data.owner,.integer i32,receiver.view.writable,.root receiver.header.scope⟩
      ⟨receiver.counter.address,receiver.counter.writable⟩ ⟨receiver.size.address,receiver.size.writable⟩ := by
  obtain ⟨actual,actualCurrent,slot,resolved⟩ := project_ready s object i32 receiver readable unique covered (by decide +kernel) allocations
  have same := Option.some.inj (actualCurrent.symm.trans current)
  subst actual
  have headerFound := (Proofs.CppMoveViews.resolve_parts s.objects receiver.viewSlot receiver.view receiver.header receiver.resolved).2.1
  obtain ⟨actual,actualCurrent,entry,bufferValid,bufferLimit,owner⟩ := Proofs.CppMoveReceiverFrame.current_entry s.objects.heap i32
    receiver.view.header receiver.header headerFound readable unique covered
  have same := Option.some.inj (actualCurrent.symm.trans current)
  subst actual
  refine ⟨slot,resolved,rfl,box_valid data i32 bufferValid,bufferLimit.trans limit,math,Field.cell s i32 receiver.counter,?_⟩
  have cell := Field.cell s i32 receiver.size
  rw [size] at cell
  exact cell

theorem copy_raw (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (allocations : AllocationsValid s.objects.heap i32) :
    Proofs.CppClassCopy.copyClass (project s i32) object Proofs.UfClassCopyBridge.profile =
      some (Proofs.UfCopyReceiver.state (project s i32) (box data) receiver.counter.value receiver.size.value,
        reference (project s i32) 2) := by
  obtain ⟨actual,actualCurrent,slot,resolved⟩ := project_ready s object i32 receiver readable unique covered (by decide +kernel) allocations
  have same := Option.some.inj (actualCurrent.symm.trans current)
  subst actual
  have lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length := by
    simp [project,materialize]
  have copied := copy_vector_runs (project s i32).frame (s.objects.heap.grants.length+receiver.viewSlot) i32 s.scope true
    _ (box data) lengths (by decide +kernel) resolved
  have captured := Proofs.CppClassCopy.capture_two (project s i32) receiver.counter.slot receiver.size.slot
    (i32,true) (i32,true) ⟨receiver.counter.address,receiver.counter.writable⟩ ⟨receiver.size.address,receiver.size.writable⟩
    ⟨i32,receiver.counter.value⟩ ⟨i32,receiver.size.value⟩ (Field.cell s i32 receiver.counter) (Field.cell s i32 receiver.size)
  have capturedAll : Proofs.CppClassCopy.captureAll (project s i32) object.scalarSlots Proofs.UfClassCopyBridge.profile.scalarFields =
      some [(⟨i32,receiver.counter.value⟩,true),(⟨i32,receiver.size.value⟩,true)] := by
    rw [receiver.fields]
    exact captured
  have actual := Proofs.CppClassCopy.copy_runs (project s i32) object Proofs.UfClassCopyBridge.profile
    _ _ _ _ slot copied capturedAll
  simp only [List.length_cons,List.length_nil] at actual
  rw [Proofs.UfClassCopyBridge.finish_two] at actual
  exact actual

theorem new_ok (s : NState) (buffer : Buffer Value) (count n : Int)
    (valid : s.frame.state.wellFormed = true)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (payload : buffer.Valid (accepts (.integer i32))) :
    Proofs.UfFindCall.VOKWF (Proofs.UfCopyReceiver.state s buffer count n)
      (layoutOf s).vectorSlot (layoutOf s).vectorBinding (layoutOf s).owner (layoutOf s).scope
      (Proofs.CppVectorCopy.copied buffer s.frame.state.storage.objects.length) := by
  have extension := copied_frame_extends s.frame buffer i32 s.scope true valid lengths (by decide +kernel) payload
  have sf := (wellFormed_parts s.frame.state valid).1
  refine ⟨extension.newValid,fields_vector s _ count n,?_,?_,
    clone_storage_new s.frame.state buffer i32 s.scope,extension.newLengths,?_,?_,?_⟩
  · simp [Proofs.UfCopyReceiver.state,fields,NState.observe,copiedFrame,layoutOf,copyBinding]
  · have tag := declareRoot_new s.frame.state.forest i32 s.scope
    rw [sf] at tag
    exact tag
  · simp [Proofs.UfCopyReceiver.state,fields,NState.observe,copiedFrame,layoutOf,lengths,sf]
  · exact Proofs.UfCopyReceiver.context_bound s buffer valid contexts
  · simp only [Proofs.UfCopyReceiver.state,fields,NState.observe,Proofs.CppState.State.observe,List.length_append,
      List.length_cons,List.length_nil]
    omega

theorem copy_represents (s : NState) (source : Layout) (parents : List Int) (count : Int) (rank : Nat → Nat)
    (buffer : Buffer Value) (binding : Binding) (cb nb : Proofs.CppState.Binding)
    (view : SourceView s source parents count rank buffer binding cb nb)
    (valid : s.frame.state.wellFormed = true)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length) :
    Represents (Proofs.UfCopyReceiver.state s buffer count parents.length) (layoutOf s) parents count rank := by
  refine ⟨Proofs.CppVectorCopy.copied buffer s.frame.state.storage.objects.length,
    ⟨s.scalars.memory.length,true⟩,⟨s.scalars.memory.length+1,true⟩,
    new_ok s buffer count parents.length valid lengths contexts base view.valid,?_,
    Proofs.CppVectorCopy.copied_valid buffer _ _ view.valid,view.limit,rfl,view.math,?_,rfl,?_,by dsimp; omega⟩
  · exact view.items
  · exact fields_count s _ count parents.length (scalar_valid s source.countSlot i32 cb ⟨i32,count⟩ view.countCell)
  · exact fields_n s _ count parents.length (scalar_valid s source.nSlot i32 nb ⟨i32,parents.length⟩ view.nCell)

theorem copy_correct (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (rank : Nat → Nat)
    (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (math : Proofs.UfClassInvariant.Valid data.items receiver.counter.value rank)
    (size : receiver.size.value = (data.items.length : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (contexts : ∀ owner scope, (project s i32).frame.state.forest.context owner = some scope → scope ≤ s.scope) :
    let p := project s i32
    let out := Proofs.UfCopyReceiver.state p (box data) receiver.counter.value data.items.length
    Proofs.CppClassCopy.copyClass p object Proofs.UfClassCopyBridge.profile = some (out,reference p 2) ∧
      Represents out (layoutOf p) data.items receiver.counter.value rank ∧
      Proofs.CppFrameExtension.Extends p.frame out.frame ∧ out.work = work s+data.items.length+4 := by
  dsimp only
  have view := source_view s object receiver data rank current math size readable unique covered allocations limit
  have valid := materialize_ready s.objects i32 (by decide +kernel) allocations
  have lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length := by
    simp [project,materialize]
  have representation := copy_represents (project s i32) (layout s object receiver data) data.items receiver.counter.value rank
    (box data) _ _ _ view valid lengths contexts base
  have extension := copied_frame_extends (project s i32).frame (box data) i32 s.scope true valid lengths (by decide +kernel) view.valid
  have costs := Proofs.UfCopyReceiver.state_cost (project s i32) (box data) receiver.counter.value data.items.length
    (wellFormed_parts (project s i32).frame.state valid).1
  have cost : (Proofs.UfCopyReceiver.state (project s i32) (box data) receiver.counter.value data.items.length).work =
      work s+data.items.length+4 := by
    simpa only [box,List.length_map,project_work] using costs.1
  exact ⟨(by simpa only [size] using copy_raw s object receiver data current readable unique covered allocations),
    representation,extension,cost⟩

end Proofs.UfObjectReadSource
