import Proofs.UfPublicSource
import Proofs.UfObjectReadSource
import Proofs.UfObjectConstructionPreserve

namespace Proofs.UfCopyContext
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.CppMoveReadReceiver Proofs.CppMoveObjectReceiver Proofs.CppMoveFrame
open Proofs.CppMoveHeaders Proofs.CppVector Proofs.CppNestedVectorStore
open Proofs.CppClassCopy Proofs.CppFrameCopy Proofs.DoublingNested

def profile (writable : Bool) : Profile :=
  ⟨i32,writable,[(i32,writable),(i32,writable)]⟩

def state (s : NState) (data : Buffer Int) (count n : Int) (writable : Bool) : NState :=
  finish s (copiedFrame s.frame (box data) i32 s.scope writable) s.frame.bindings.length
    [(⟨i32,count⟩,writable),(⟨i32,n⟩,writable)]

-- Copy the values and n independently: moved-from objects need not have n=len.
def payload (data : Buffer Int) : Buffer Int :=
  {data with owner := 0, capacity := data.items.length, epoch := 0}

def heap (s : Context) (after : NState) (data : Buffer Int) (writable : Bool) : Heap Int :=
  {Proofs.CppMoveAppendOwned.appended s.objects.heap (payload data) s.scope writable with
    work := after.frame.state.storage.work,
    peak := after.frame.state.storage.peak,
    baseSpace := after.frame.state.storage.baseSpace}

def exported (s : Context) (after : NState) (data : Buffer Int) (writable : Bool) : Context :=
  ⟨⟨heap s after data writable,s.objects.views++[⟨s.objects.heap.headers.length,writable⟩]⟩,
    after.scalars,after.slots.map (Proofs.UfObjectConstructionContext.unlocation s.objects.heap.grants.length),
    after.scope,after.peak⟩

-- The source payload is resolved from the source object, not supplied by callers.
def copy (s : Context) (object : ObjectRef) (writable : Bool) : Option (Context × ObjectRef) := do
  let index ← vectorView s object.vectorSlot
  let (view,header) ← Proofs.CppMoveViews.resolve s.objects index
  let data ← currentBuffer s.objects.heap view.header header
  let (after,result) ← copyClass (project s i32) object (profile writable)
  some (exported s after data writable,result)

theorem source_profile (targetConst : Bool) :
    Proofs.UnionFindPublicCompatInstance.Construction.profileFor targetConst = profile (!targetConst) := by
  cases targetConst <;> rfl

theorem source_copy (s : NState) (object : ObjectRef) (targetConst : Bool) :
    copyClass s object (profile (!targetConst)) =
      if targetConst then Proofs.UnionFindPublicCompatInstance.Construction.copyConst s object
      else Proofs.UnionFindPublicCompatInstance.Construction.copy s object := by
  cases targetConst <;> rfl

theorem raw (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (writable : Bool) :
    copyClass (project s i32) object (profile writable) =
      some (state (project s i32) data receiver.counter.value receiver.size.value writable,
        reference (project s i32) 2) := by
  obtain ⟨actual,actualCurrent,slot,resolved⟩ :=
    project_ready s object i32 receiver readable unique covered (by decide +kernel) allocations
  have same := Option.some.inj (actualCurrent.symm.trans current)
  subst actual
  have lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length := by
    simp [project,materialize]
  have copied := copy_vector_runs (project s i32).frame (s.objects.heap.grants.length+receiver.viewSlot) i32 s.scope writable
    _ (box data) lengths (by decide +kernel) resolved
  have captured := capture_two (project s i32) receiver.counter.slot receiver.size.slot
    (i32,writable) (i32,writable) ⟨receiver.counter.address,receiver.counter.writable⟩
    ⟨receiver.size.address,receiver.size.writable⟩ ⟨i32,receiver.counter.value⟩ ⟨i32,receiver.size.value⟩
    (Field.cell s i32 receiver.counter) (Field.cell s i32 receiver.size)
  have all : captureAll (project s i32) object.scalarSlots (profile writable).scalarFields =
      some [(⟨i32,receiver.counter.value⟩,writable),(⟨i32,receiver.size.value⟩,writable)] := by
    rw [receiver.fields]
    exact captured
  simpa only [state,project,List.length_cons,List.length_nil,Nat.reduceAdd] using
    copy_runs (project s i32) object (profile writable) _ _ _ _ slot copied all

theorem copied (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (writable : Bool) :
    copy s object writable = some (
      exported s (state (project s i32) data receiver.counter.value receiver.size.value writable) data writable,
      reference (project s i32) 2) := by
  simp [copy,receiver.located,receiver.resolved,current,
    raw s object receiver data current readable unique covered allocations writable]

theorem layout (s : NState) (data : Buffer Int) (count n : Int) (writable : Bool) :
    Proofs.CppConstructorLayout.Layout s (state s data count n writable) (reference s 2) := by
  refine ⟨s.scalars.memory,[(⟨i32,count⟩,writable),(⟨i32,n⟩,writable)],rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl⟩
  simp only [state,CppClassCopy.finish,NState.observe,List.append_assoc,List.singleton_append]

theorem payload_valid (data : Buffer Int) (valid : data.Valid i32.valid) :
    (payload data).Valid i32.valid := by
  exact ⟨by simp [payload],valid.1.trans valid.2.1,valid.2.2⟩

theorem heap_invariants (s : Context) (after : NState) (data : Buffer Int) (writable : Bool)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (valid : data.Valid i32.valid) :
    Unique (heap s after data writable) ∧ OwnsAll (heap s after data writable) ∧
      Proofs.CppMoveSpace.HeadersLive (heap s after data writable) ∧ AllocationsValid (heap s after data writable) i32 := by
  exact ⟨Proofs.CppMoveAppendOwned.appended_unique s.objects.heap (payload data) s.scope writable unique live,
    Proofs.CppMoveAppendOwned.appended_ownsAll s.objects.heap (payload data) s.scope writable covered,
    Proofs.CppMoveAppendOwned.appended_headersLive s.objects.heap (payload data) s.scope writable live,
    Proofs.CppMoveAppendOwned.appended_valid s.objects.heap (payload data) s.scope writable i32 allocations (payload_valid data valid)⟩

theorem current_buffer (s : Context) (after : NState) (data : Buffer Int) (writable : Bool) :
    currentBuffer (heap s after data writable) s.objects.heap.headers.length
      ⟨some s.objects.heap.allocations.length,s.scope,writable,data.limit⟩ =
      some {(payload data) with owner := s.objects.heap.allocations.length} :=
  Proofs.CppMoveAppendOwned.current_buffer s.objects.heap (payload data) s.scope writable

theorem old_read (s : Context) (after : NState) (data : Buffer Int) (writable : Bool)
    (id : Nat) (grant : Grant) (found : s.objects.heap.grants[id]? = some grant)
    (inside : grant.reference.element.owner < s.objects.heap.allocations.length) :
    Proofs.CppMoveHeaders.read (heap s after data writable) i32.valid id =
      Proofs.CppMoveHeaders.read s.objects.heap i32.valid id :=
  Proofs.CppMoveAppendOwned.old_read s.objects.heap (payload data) s.scope writable i32.valid id grant found inside

theorem liveSpace (s : Context) (after : NState) (data : Buffer Int) (writable : Bool) :
    (heap s after data writable).liveSpace = s.objects.heap.liveSpace+1+data.items.length :=
  Proofs.CppMoveAppendOwned.liveSpace s.objects.heap (payload data) s.scope writable

theorem count_cell (s : NState) (data : Buffer Int) (count n : Int) (writable : Bool)
    (valid : i32.valid count = true) :
    (state s data count n writable).scalarCell (s.slots.length+1) i32 =
      some (⟨s.scalars.memory.length,writable⟩,⟨i32,count⟩) := by
  simp [state,CppClassCopy.finish,NState.observe,Proofs.CppState.State.observe,
    NState.scalarCell,NState.scalarSlot,scalarBindings,scalarLocations,
    valid]

theorem size_cell (s : NState) (data : Buffer Int) (count n : Int) (writable : Bool)
    (valid : i32.valid n = true) :
    (state s data count n writable).scalarCell (s.slots.length+2) i32 =
      some (⟨s.scalars.memory.length+1,writable⟩,⟨i32,n⟩) := by
  simp [state,CppClassCopy.finish,NState.observe,Proofs.CppState.State.observe,
    NState.scalarCell,NState.scalarSlot,scalarBindings,scalarLocations,
    valid]

theorem scalar_slot (s : Context) (after : NState) (data : Buffer Int) (writable : Bool) (slot : Nat) :
    Proofs.CppMoveContext.scalarSlot (exported s after data writable) slot = after.scalarSlot slot := by
  unfold Proofs.CppMoveContext.scalarSlot NState.scalarSlot
  simp only [exported,List.getElem?_map]
  cases entry : after.slots[slot]? with
  | none => rfl
  | some loc => cases loc <;> rfl

theorem field_of_cell (s : Context) (after : NState) (data : Buffer Int) (permission : Bool)
    (slot address : Nat) (writable : Bool) (value : Int)
    (cell : after.scalarCell slot i32 = some (⟨address,writable⟩,⟨i32,value⟩)) :
    ∃ field : Field (exported s after data permission) i32,
      field.slot = slot ∧ field.address = address ∧ field.writable = writable ∧ field.value = value := by
  unfold NState.scalarCell at cell
  obtain ⟨index,located,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ cell
  obtain ⟨binding,bound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨actual,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  split at rest
  · rename_i typed
    obtain ⟨bindingEq,actualEq⟩ := Prod.mk.inj (Option.some.inj rest)
    subst binding
    subst actual
    refine ⟨⟨slot,index,address,writable,value,?_,bound,found,typed.2⟩,rfl,rfl,rfl,rfl⟩
    rw [scalar_slot]
    exact located
  · simp at rest

theorem located_vector (s : Context) (after : NState) (data : Buffer Int) (writable : Bool) (object : ObjectRef)
    (shape : Proofs.CppConstructorLayout.Layout (project s i32) after object) :
    vectorView (exported s after data writable) object.vectorSlot = some s.objects.views.length := by
  obtain ⟨oldCells,values,oldLength,oldTypes,memory,bindings,slots,scope,base,objectEq⟩ := shape
  have entry : after.slots[(project s i32).slots.length]? = some (.vector (project s i32).frame.bindings.length) := by
    rw [slots,List.append_assoc]
    simp
  simp only [project,List.length_map] at entry
  rw [objectEq]
  simp [vectorView,Proofs.CppConstructorFinish.reference,exported,List.getElem?_map,entry,
    Proofs.UfObjectConstructionContext.unlocation,project,materialize]

theorem resolved_vector (s : Context) (after : NState) (data : Buffer Int) (writable : Bool) :
    Proofs.CppMoveViews.resolve (exported s after data writable).objects s.objects.views.length =
      some (⟨s.objects.heap.headers.length,writable⟩,
        ⟨some s.objects.heap.allocations.length,s.scope,writable,data.limit⟩) := by
  simp [Proofs.CppMoveViews.resolve,exported,heap,Proofs.CppMoveAppendOwned.appended,
    Proofs.CppMoveHeaders.Heap.header,payload]

theorem receiver (s : Context) (data : Buffer Int) (count n : Int) (writable : Bool)
    (cv : i32.valid count = true) (nv : i32.valid n = true) :
    let after := state (project s i32) data count n writable
    ∃ r : ReadReceiver (exported s after data writable) (reference (project s i32) 2) i32,
      r.counter.address = s.scalars.memory.length ∧ r.size.address = s.scalars.memory.length+1 ∧
      r.counter.value = count ∧ r.size.value = n ∧
      r.counter.writable = writable ∧ r.size.writable = writable ∧
      r.header = ⟨some s.objects.heap.allocations.length,s.scope,writable,data.limit⟩ ∧
      r.view = ⟨s.objects.heap.headers.length,writable⟩ := by
  dsimp only
  let after := state (project s i32) data count n writable
  obtain ⟨counter,slotC,addressC,writableC,valueC⟩ := field_of_cell s after data writable _ _ writable count
    (count_cell (project s i32) data count n writable cv)
  obtain ⟨size,slotS,addressS,writableS,valueS⟩ := field_of_cell s after data writable _ _ writable n
    (size_cell (project s i32) data count n writable nv)
  refine ⟨⟨counter,size,?_,s.objects.views.length,⟨s.objects.heap.headers.length,writable⟩,
    ⟨some s.objects.heap.allocations.length,s.scope,writable,data.limit⟩,
    located_vector s after data writable _ (layout (project s i32) data count n writable),
    resolved_vector s after data writable⟩,addressC,addressS,valueC,valueS,writableC,writableS,rfl,rfl⟩
  rw [slotC,slotS]
  simp [Proofs.CppConstructorFinish.reference,List.range_succ,Nat.add_assoc]

theorem work_eq (s : Context) (data : Buffer Int) (count n : Int) (writable : Bool) :
    Proofs.CppMoveContext.work
      (exported s (state (project s i32) data count n writable) data writable) =
      Proofs.CppMoveContext.work s+data.items.length+4 := by
  simp [Proofs.CppMoveContext.work,exported,heap,state,CppClassCopy.finish,NState.observe,
    Proofs.CppState.State.observe,copiedFrame,Proofs.CppNestedCopy.cloned,box,project,materialize]
  omega

theorem scalar_metadata (s : Context) (data : Buffer Int) (count n : Int) (writable : Bool) :
    let out := exported s (state (project s i32) data count n writable) data writable
    out.scalars.memory = s.scalars.memory++[⟨i32,count⟩,⟨i32,n⟩] ∧
      out.scalars.bindings = s.scalars.bindings++[⟨s.scalars.memory.length,writable⟩,⟨s.scalars.memory.length+1,writable⟩] ∧
      out.scalars.baseMemory = s.scalars.baseMemory := by
  exact ⟨rfl,rfl,rfl⟩

theorem peaks (s : Context) (data : Buffer Int) (count n : Int) (writable : Bool)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap) :
    let out := exported s (state (project s i32) data count n writable) data writable
    let S := max s.scalars.peak (scalarLive s+4)
    let H := max s.objects.heap.peak (s.objects.heap.liveSpace+data.items.length+2-s.objects.heap.baseSpace)
    out.scalars.peak ≤ S ∧ out.objects.heap.peak = H ∧ out.peak ≤ max s.peak (S+H) := by
  dsimp only
  have space := Proofs.CppMoveSpace.materialize_liveSpace s.objects i32 unique covered live
  have storage : (heap s (state (project s i32) data count n writable) data writable).peak =
      max s.objects.heap.peak (s.objects.heap.liveSpace+data.items.length+2-s.objects.heap.baseSpace) := by
    simpa only [heap,state,CppClassCopy.finish,NState.observe,copiedFrame,Proofs.CppNestedCopy.cloned,
      box,List.length_map,project,materialize] using congrArg (fun k => max s.objects.heap.peak
        (k+data.items.length+2-s.objects.heap.baseSpace)) space
  have scalar : (state (project s i32) data count n writable).scalars.peak ≤
      max s.scalars.peak (scalarLive s+4) := by
    simp only [state,CppClassCopy.finish,NState.observe,Proofs.CppState.State.observe,project,
      List.length_append,List.length_map,List.length_cons,List.length_nil,scalarBindings]
    unfold scalarLive
    omega
  have outer : (state (project s i32) data count n writable).peak =
      max s.peak ((state (project s i32) data count n writable).scalars.peak+
        (heap s (state (project s i32) data count n writable) data writable).peak) := rfl
  refine ⟨scalar,storage,?_⟩
  change (state (project s i32) data count n writable).peak ≤ _
  rw [outer,storage]
  exact max_le_max (Nat.le_refl _) (Nat.add_le_add_right scalar _)

end Proofs.UfCopyContext
