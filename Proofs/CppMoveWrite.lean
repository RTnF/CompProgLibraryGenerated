import Proofs.CppMoveSpace

namespace Proofs.CppMoveWrite
open Proofs.CppScalar Proofs.CppVector Proofs.CppMoveHeaders
open Proofs.CppNestedVectorStore Proofs.CppMoveFrame

-- Decode only flat integer payloads; nested children are not silently dropped.
def decode : List Value → Option (List Int)
  | [] => some []
  | .integer value :: tail => do
    let values ← decode tail
    some (value::values)
  | .child _ :: _ => none

def unbox (buffer : Buffer Value) : Option (Buffer Int) := do
  let values ← decode buffer.items
  some ⟨buffer.owner,values,buffer.capacity,buffer.limit,buffer.epoch⟩

theorem decode_box (values : List Int) : decode (values.map Value.integer) = some values := by
  induction values with
  | nil => rfl
  | cons value tail ih => simp [decode,ih]

theorem unbox_box (buffer : Buffer Int) : unbox (box buffer) = some buffer := by
  simp [unbox,box,decode_box]

-- Execute the existing typed Frame write, then return its actual payload and
-- resource counters to the high-level heap. Header/view/grant identities stay
-- in the high-level state. This adapter is specific to fixed element writes;
-- allocation, resizing and moving headers require their own finish adapters.
def restoreWrite (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int) :
    Option (Proofs.CppMoveViews.State Int) := do
  let grant ← s.heap.grants[id]?
  let ref ← reference s.heap ty id
  let written ← Proofs.CppFrameCopyAssign.write (materialize s ty) ref value
  let buffer ← written.frame.state.storage.lookup grant.reference.element.owner
  let actual ← unbox buffer
  let _ ← s.heap.allocation grant.reference.element.owner
  if actual.owner = grant.reference.element.owner then
    some ⟨{s.heap with
      allocations := s.heap.allocations.set grant.reference.element.owner
        (some ⟨actual,written.generation grant.reference.element.owner⟩)
      work := written.frame.state.storage.work
      peak := written.frame.state.storage.peak
      baseSpace := written.frame.state.storage.baseSpace},s.views⟩
  else none

-- Event budget corresponding to a single existing Frame.write primitive.
-- CppMoveHeaders.write alone is a data helper and does not charge this event.
def writeEvent (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int) :
    Option (Proofs.CppMoveViews.State Int) := do
  let heap ← Proofs.CppMoveHeaders.write s.heap ty.valid id value
  some ⟨{heap with work := s.heap.work+1, peak := max s.heap.peak (s.heap.liveSpace+1-s.heap.baseSpace)},s.views⟩


-- The typed primitive performs the same update, work and peak accounting.
theorem box_write (buffer : Buffer Int) (ty : Ty) (writable : Bool) (ref : ElementRef) (value : Int) :
    CppVector.writeRef (box buffer) (accepts (.integer ty)) writable ref (.integer value) =
      (CppVector.writeRef buffer ty.valid writable ref value).map
        (fun result => (⟨box result.buffer,result.value,result.work,result.peak⟩ : Result Value Unit)) := by
  simp [CppVector.writeRef,box,Buffer.Valid,List.all_map,accepts,List.map_set]

theorem decode_success (values : List Value) (decoded : List Int) (run : decode values = some decoded) :
    values = decoded.map Value.integer := by
  induction values generalizing decoded with
  | nil => simp [decode] at run; subst decoded; rfl
  | cons value tail ih =>
    cases value with
    | child owner => simp [decode] at run
    | integer value =>
      cases rest : decode tail with
      | none => simp [decode,rest] at run
      | some items =>
        simp only [decode,rest,Bind.bind,Option.bind,Option.some.injEq] at run
        subst decoded
        simp [ih items rest]

theorem unbox_success (buffer : Buffer Value) (decoded : Buffer Int)
    (run : unbox buffer = some decoded) : box decoded = buffer := by
  unfold unbox at run
  cases items : decode buffer.items with
  | none => simp [items] at run
  | some values =>
    simp only [items,Bind.bind,Option.bind,Option.some.injEq] at run
    subst decoded
    have payload := decode_success buffer.items values items
    cases buffer
    simp_all [box]


theorem restoreWrite_metadata (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (run : restoreWrite s ty id value = some out) :
    out.heap.headers = s.heap.headers ∧ out.heap.grants = s.heap.grants ∧ out.views = s.views := by
  unfold restoreWrite at run
  obtain ⟨grant,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  obtain ⟨ref,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨written,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨buffer,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨actual,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨old,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  dsimp only at rest
  split at rest
  · have eq := Option.some.inj rest
    subst out
    exact ⟨rfl,rfl,rfl⟩
  · simp at rest

theorem frame_write_generations (s out : Proofs.CppFrameCopyAssign.TrackedFrame)
    (ref : Proofs.CppFrameCopyAssign.TrackedReference) (value : Int)
    (run : Proofs.CppFrameCopyAssign.write s ref value = some out) : out.generation = s.generation := by
  unfold Proofs.CppFrameCopyAssign.write at run
  split at run
  · cases written : s.frame.write ref.original value with
    | none => simp [written] at run
    | some frame =>
      simp only [written,Bind.bind,Option.bind,Option.some.injEq] at run
      subst out
      rfl
  · simp at run


theorem write_parts (buffer : Buffer Int) (ty : Ty) (writable : Bool) (ref : ElementRef) (value : Int)
    (result : Result Int Unit) (run : CppVector.writeRef buffer ty.valid writable ref value = some result) :
    writable = true ∧ result.buffer.owner = buffer.owner ∧ result.buffer.capacity = buffer.capacity ∧
      result.buffer.Valid ty.valid ∧ result.work = 1 ∧ result.peak = buffer.capacity+2 := by
  unfold CppVector.writeRef at run
  split at run
  next good =>
    rcases good with ⟨valid,permission,_,_,_,accepted⟩
    have eq := Option.some.inj run
    rw [← eq]
    exact ⟨permission,rfl,rfl,writeRef_preserves_valid buffer ty.valid ref.index value valid accepted,rfl,rfl⟩
  next => simp at run

theorem materialized_write_runs (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (grant : Grant)
    (tracked : Proofs.CppVectorCopyAssign.Tracked Int) (value : Int) (result : Result Int Unit)
    (found : s.heap.grants[id]? = some grant)
    (live : s.heap.allocation grant.reference.element.owner = some tracked)
    (covered : OwnsAll s.heap) (supported : Proofs.CppVectorBindings.supported ty)
    (valid : AllocationsValid s.heap ty)
    (generation : grant.reference.generation = tracked.generation grant.reference.element.index)
    (primitive : CppVector.writeRef tracked.buffer ty.valid grant.writable grant.reference.element value = some result) :
    Proofs.CppFrameCopyAssign.write (materialize s ty)
      ⟨⟨id,ty,grant.writable,grant.reference.element⟩,grant.reference.generation⟩ value =
      some ⟨(materialize s ty).frame.updated grant.reference.element.owner (box tracked.buffer)
        ⟨box result.buffer,result.value,result.work,result.peak⟩,(materialize s ty).generation⟩ := by
  open Proofs.CppNestedVectorBindings in
  obtain ⟨header,hf⟩ := ownerHeader_exists s.heap grant.reference.element.owner tracked covered live
  have entry := entries_allocation s.heap ty grant.reference.element.owner tracked header live hf
  have pair := materialize_entry s ty grant.reference.element.owner (box tracked.buffer) _ entry
  have wf := materialize_ready s ty supported valid
  have object := materialize_object s ty grant.reference.element.owner (box tracked.buffer)
    ⟨.integer ty,none,some header.scope,[]⟩ entry rfl wf
  have granted := materialize_live_grant s ty id grant tracked found live covered
  obtain ⟨permission,ownerEq,capacity,bufferValid,work,peak⟩ :=
    write_parts tracked.buffer ty grant.writable grant.reference.element value result primitive
  have owns := (valid grant.reference.element.owner tracked live).1
  have payload : payloadOK ⟨.integer ty,none,some header.scope,[]⟩ (box result.buffer) := by
    exact ⟨box_valid result.buffer ty bufferValid,True.intro⟩
  have oldPeak : (box tracked.buffer).capacity+1 ≤ result.peak := by simp only [box] at *; omega
  have newPeak : (box result.buffer).capacity+1 ≤ result.peak := by simp only [box] at *; omega
  have commit := Proofs.CppNestedVectorBindings.commit_runs (materialize s ty).frame
    grant.reference.element.owner (.integer ty) (box tracked.buffer) ⟨.integer ty,none,some header.scope,[]⟩
    ⟨box result.buffer,result.value,result.work,result.peak⟩ wf object pair.2 pair.1
    (ownerEq.trans owns) payload oldPeak newPeak
  have boxed := box_write tracked.buffer ty grant.writable grant.reference.element value
  rw [primitive] at boxed
  simp only [Option.map_some] at boxed
  rw [permission] at boxed granted
  have written : (materialize s ty).frame.write ⟨id,ty,grant.writable,grant.reference.element⟩ value =
      some ((materialize s ty).frame.updated grant.reference.element.owner (box tracked.buffer)
        ⟨box result.buffer,result.value,result.work,result.peak⟩) := by
    simp [Proofs.CppNestedVectorBindings.Frame.write,granted,permission,object,boxed,commit]
  apply Proofs.CppFrameCopyAssign.write_runs _ _ _ _ _ written
  simpa [materialize,live] using generation


theorem restoreWrite_primitive (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (grant : Grant)
    (tracked : Proofs.CppVectorCopyAssign.Tracked Int) (value : Int) (result : Result Int Unit)
    (found : s.heap.grants[id]? = some grant)
    (live : s.heap.allocation grant.reference.element.owner = some tracked)
    (unique : Unique s.heap) (covered : OwnsAll s.heap) (headersLive : Proofs.CppMoveSpace.HeadersLive s.heap)
    (supported : Proofs.CppVectorBindings.supported ty) (valid : AllocationsValid s.heap ty)
    (generation : grant.reference.generation = tracked.generation grant.reference.element.index)
    (primitive : CppVector.writeRef tracked.buffer ty.valid grant.writable grant.reference.element value = some result) :
    restoreWrite s ty id value = some ⟨{s.heap with
      allocations := s.heap.allocations.set grant.reference.element.owner (some ⟨result.buffer,tracked.generation⟩)
      work := s.heap.work+1
      peak := max s.heap.peak (s.heap.liveSpace+1-s.heap.baseSpace)},s.views⟩ := by
  have written := materialized_write_runs s ty id grant tracked value result found live covered supported valid generation primitive
  obtain ⟨header,hf⟩ := ownerHeader_exists s.heap grant.reference.element.owner tracked covered live
  have entry := entries_allocation s.heap ty grant.reference.element.owner tracked header live hf
  have pair := materialize_entry s ty grant.reference.element.owner (box tracked.buffer) _ entry
  have bound := Proofs.CppVectorStore.lookup_bound (materialize s ty).frame.state.storage _ _ pair.1
  have lookup := Proofs.CppNestedOps.updated_lookup_self (materialize s ty).frame grant.reference.element.owner
    (box tracked.buffer) ⟨box result.buffer,result.value,result.work,result.peak⟩ bound
  have genAt : (materialize s ty).generation grant.reference.element.owner = tracked.generation := by
    funext index
    simp [materialize,live]
  obtain ⟨_,ownerEq,_,_,work,peak⟩ := write_parts tracked.buffer ty grant.writable grant.reference.element value result primitive
  have owns : result.buffer.owner = grant.reference.element.owner := ownerEq.trans (valid _ _ live).1
  have resources := materialize_resources s ty
  have space := Proofs.CppMoveSpace.materialize_liveSpace s ty unique covered headersLive
  have difference : tracked.buffer.capacity+2-(tracked.buffer.capacity+1) = 1 := by omega
  simp only [restoreWrite,reference,found,Bind.bind,Option.bind,written,lookup,unbox_box,live,owns,ite_true]
  simp only [Proofs.CppNestedVectorBindings.Frame.updated,genAt,resources.1,resources.2.1,resources.2.2,
    space,box,work,peak,difference]


theorem restoreWrite_of_event (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (unique : Unique s.heap) (covered : OwnsAll s.heap) (headersLive : Proofs.CppMoveSpace.HeadersLive s.heap)
    (supported : Proofs.CppVectorBindings.supported ty) (valid : AllocationsValid s.heap ty)
    (run : writeEvent s ty id value = some out) : restoreWrite s ty id value = some out := by
  unfold writeEvent at run
  obtain ⟨heap,heapRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have outEq := Option.some.inj rest
  subst out
  unfold Proofs.CppMoveHeaders.write at heapRun
  obtain ⟨grant,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ heapRun
  obtain ⟨tracked,live,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  split at rest
  next generation =>
    obtain ⟨result,primitive,finish⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    have heapEq := Option.some.inj finish
    subst heap
    exact restoreWrite_primitive s ty id grant tracked value result found live unique covered headersLive
      supported valid generation primitive
  next => simp at rest


theorem materialized_write_primitive_none (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (grant : Grant)
    (tracked : Proofs.CppVectorCopyAssign.Tracked Int) (value : Int)
    (found : s.heap.grants[id]? = some grant)
    (live : s.heap.allocation grant.reference.element.owner = some tracked)
    (covered : OwnsAll s.heap) (supported : Proofs.CppVectorBindings.supported ty)
    (valid : AllocationsValid s.heap ty)
    (primitive : CppVector.writeRef tracked.buffer ty.valid grant.writable grant.reference.element value = none) :
    Proofs.CppFrameCopyAssign.write (materialize s ty)
      ⟨⟨id,ty,grant.writable,grant.reference.element⟩,grant.reference.generation⟩ value = none := by
  obtain ⟨header,hf⟩ := ownerHeader_exists s.heap grant.reference.element.owner tracked covered live
  have entry := entries_allocation s.heap ty grant.reference.element.owner tracked header live hf
  have object := materialize_object s ty grant.reference.element.owner (box tracked.buffer)
    ⟨.integer ty,none,some header.scope,[]⟩ entry rfl (materialize_ready s ty supported valid)
  have granted := materialize_live_grant s ty id grant tracked found live covered
  have boxed := box_write tracked.buffer ty grant.writable grant.reference.element value
  rw [primitive] at boxed
  simp only [Option.map_none] at boxed
  cases permission : grant.writable with
  | false => simp [Proofs.CppFrameCopyAssign.write,Proofs.CppNestedVectorBindings.Frame.write]
  | true =>
    rw [permission] at granted boxed
    simp [Proofs.CppFrameCopyAssign.write,Proofs.CppNestedVectorBindings.Frame.write,granted,object,boxed]

theorem materialized_write_dead (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (grant : Grant) (value : Int)
    (inside : grant.reference.element.owner < s.heap.allocations.length)
    (dead : s.heap.allocation grant.reference.element.owner = none) :
    Proofs.CppFrameCopyAssign.write (materialize s ty)
      ⟨⟨id,ty,grant.writable,grant.reference.element⟩,grant.reference.generation⟩ value = none := by
  have entry := entries_missing s.heap ty grant.reference.element.owner inside dead
  have object := materialize_missing_object s ty grant.reference.element.owner entry
  unfold Proofs.CppFrameCopyAssign.write
  split
  · unfold Proofs.CppNestedVectorBindings.Frame.write
    cases checked : (materialize s ty).frame.grant ⟨id,ty,grant.writable,grant.reference.element⟩ with
    | none => simp
    | some writable => simp [object]
  · rfl

-- All captured allocation IDs must belong to the existing allocation table.
-- This permits tombstones; it does not demand that every grant remains live.
def GrantBounds (s : Heap α) : Prop :=
  ∀ (id : Nat) (grant : Grant), s.grants[id]? = some grant → grant.reference.element.owner < s.allocations.length

theorem restoreWrite_eq_event (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (unique : Unique s.heap) (covered : OwnsAll s.heap) (headersLive : Proofs.CppMoveSpace.HeadersLive s.heap)
    (supported : Proofs.CppVectorBindings.supported ty) (valid : AllocationsValid s.heap ty)
    (bounds : GrantBounds s.heap) : restoreWrite s ty id value = writeEvent s ty id value := by
  cases found : s.heap.grants[id]? with
  | none => simp [restoreWrite,writeEvent,Proofs.CppMoveHeaders.write,found]
  | some grant =>
    cases live : s.heap.allocation grant.reference.element.owner with
    | none =>
      have rejected := materialized_write_dead s ty id grant value (bounds id grant found) live
      simp [restoreWrite,writeEvent,Proofs.CppMoveHeaders.write,reference,found,live,rejected]
    | some tracked =>
      have gen : (materialize s ty).generation grant.reference.element.owner grant.reference.element.index =
          tracked.generation grant.reference.element.index := by simp [materialize,live]
      by_cases generation : grant.reference.generation = tracked.generation grant.reference.element.index
      · cases primitive : CppVector.writeRef tracked.buffer ty.valid grant.writable grant.reference.element value with
        | none =>
          have rejected := materialized_write_primitive_none s ty id grant tracked value found live covered supported valid primitive
          rw [generation] at rejected
          simp [restoreWrite,writeEvent,Proofs.CppMoveHeaders.write,reference,found,live,generation,primitive,rejected]
        | some result =>
          rw [restoreWrite_primitive s ty id grant tracked value result found live unique covered headersLive
            supported valid generation primitive]
          simp [writeEvent,Proofs.CppMoveHeaders.write,found,live,generation,primitive]
      · have rejected : Proofs.CppFrameCopyAssign.write (materialize s ty)
            ⟨⟨id,ty,grant.writable,grant.reference.element⟩,grant.reference.generation⟩ value = none := by
          simp [Proofs.CppFrameCopyAssign.write,gen,generation]
        simp [restoreWrite,writeEvent,Proofs.CppMoveHeaders.write,reference,found,live,generation,rejected]



theorem grantBounds_metadata (s out : Heap α) (bounds : GrantBounds s)
    (grants : out.grants = s.grants) (lengths : out.allocations.length = s.allocations.length) : GrantBounds out := by
  intro id grant found
  rw [grants] at found
  rw [lengths]
  exact bounds id grant found

theorem assign_grantBounds (s out : Proofs.CppMoveViews.State Int) (accept : Int → Bool) (target source : Nat)
    (run : Proofs.CppMoveViews.assign s accept target source = some out) (bounds : GrantBounds s.heap) :
    GrantBounds out.heap := by
  obtain ⟨tv,th,sv,sh,_,_,_,_,core,_⟩ := Proofs.CppMoveViews.assign_success s out accept target source run
  obtain ⟨th,sh,_,_,heapEq⟩ := Proofs.CppMoveAssign.move_assign_success s.heap out.heap accept tv.header sv.header core
  apply grantBounds_metadata s.heap out.heap bounds
  · rw [heapEq]
    exact Proofs.CppMoveAssign.assigned_grants s.heap tv.header sv.header th sh
  · rw [heapEq]
    cases alloc : th.allocation <;>
      simp [Proofs.CppMoveAssign.assigned,Proofs.CppMoveAssign.retire,alloc,List.length_set]

theorem construct_grantBounds (s out : Proofs.CppMoveViews.State Int) (accept : Int → Bool)
    (source scope slot : Nat) (writable : Bool)
    (run : Proofs.CppMoveViews.construct s accept source scope writable = some (out,slot))
    (bounds : GrantBounds s.heap) : GrantBounds out.heap := by
  obtain ⟨view,header,destination,_,_,core,_,_⟩ := Proofs.CppMoveViews.construct_success s out accept source scope slot writable run
  obtain ⟨header,_,_,heapEq⟩ := move_construct_success s.heap out.heap accept view.header scope destination writable core
  apply grantBounds_metadata s.heap out.heap bounds <;> rw [heapEq] <;> rfl

theorem writeEvent_grantBounds (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (run : writeEvent s ty id value = some out) (bounds : GrantBounds s.heap) : GrantBounds out.heap := by
  unfold writeEvent at run
  obtain ⟨heap,heapRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have outEq := Option.some.inj rest
  subst out
  unfold Proofs.CppMoveHeaders.write at heapRun
  obtain ⟨grant,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ heapRun
  obtain ⟨tracked,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  split at rest
  · obtain ⟨result,_,finish⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    have heapEq := Option.some.inj finish
    subst heap
    apply grantBounds_metadata s.heap _ bounds
    · rfl
    · simp [List.length_set]
  · simp at rest


theorem captured_reference_owner (tracked : Proofs.CppVectorCopyAssign.Tracked α) (accept : α → Bool)
    (index : Int) (ref : Proofs.CppVectorCopyAssign.Reference)
    (run : Proofs.CppVectorCopyAssign.reference tracked accept index = some ref) :
    ref.element.owner = tracked.buffer.owner := by
  unfold Proofs.CppVectorCopyAssign.reference at run
  obtain ⟨element,elementRun,finish⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have eq := Option.some.inj finish
  subst ref
  unfold CppVector.elementRef at elementRun
  split at elementRun
  · have same := Option.some.inj elementRun
    rw [← same]
  · simp at elementRun

theorem capture_new_grant (s out : Heap α) (accept : α → Bool) (headerId : Nat) (index : Int)
    (writable : Bool) (reference : Nat)
    (run : Proofs.CppMoveHeaders.capture s accept headerId index writable = some (out,reference)) :
    ∃ grant : Grant, out = {s with grants := s.grants++[grant]} ∧
      grant.reference.element.owner < s.allocations.length := by
  unfold Proofs.CppMoveHeaders.capture at run
  obtain ⟨header,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  split at rest
  · obtain ⟨owner,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    obtain ⟨tracked,live,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    split at rest
    next compatible =>
      obtain ⟨ref,refRun,finish⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
      have pair := Prod.mk.inj (Option.some.inj finish)
      refine ⟨⟨ref,writable⟩,pair.1.symm,?_⟩
      rw [captured_reference_owner tracked accept index ref refRun,compatible.1]
      exact Proofs.CppMoveAssign.allocation_inside s owner tracked live
    next => simp at rest
  · simp at rest

theorem capture_core_grantBounds (s out : Heap α) (accept : α → Bool) (headerId : Nat) (index : Int)
    (writable : Bool) (reference : Nat)
    (run : Proofs.CppMoveHeaders.capture s accept headerId index writable = some (out,reference))
    (bounds : GrantBounds s) : GrantBounds out := by
  obtain ⟨new,heapEq,newBound⟩ := capture_new_grant s out accept headerId index writable reference run
  subst out
  intro id grant found
  change (s.grants++[new])[id]? = some grant at found
  change grant.reference.element.owner < s.allocations.length
  by_cases inside : id < s.grants.length
  · rw [List.getElem?_append_left inside] at found
    exact bounds id grant found
  · have outside : s.grants.length ≤ id := by omega
    rw [List.getElem?_append_right outside] at found
    cases offset : id-s.grants.length with
    | zero =>
      simp only [offset,List.getElem?_cons_zero,Option.some.injEq] at found
      subst grant
      exact newBound
    | succ n => simp [offset] at found

theorem capture_grantBounds (s out : Proofs.CppMoveViews.State Int) (accept : Int → Bool) (slot : Nat)
    (index : Int) (writable : Bool) (reference : Nat)
    (run : Proofs.CppMoveViews.capture s accept slot index writable = some (out,reference))
    (bounds : GrantBounds s.heap) : GrantBounds out.heap := by
  obtain ⟨view,header,_,_,core,_⟩ := Proofs.CppMoveViews.capture_success s out accept slot index writable reference run
  exact capture_core_grantBounds s.heap out.heap accept view.header index writable reference core bounds


theorem writeEvent_success (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (run : writeEvent s ty id value = some out) :
    ∃ grant tracked result, s.heap.grants[id]? = some grant ∧
      s.heap.allocation grant.reference.element.owner = some tracked ∧
      CppVector.writeRef tracked.buffer ty.valid grant.writable grant.reference.element value = some result ∧
      out = ⟨{s.heap with
        allocations := s.heap.allocations.set grant.reference.element.owner (some ⟨result.buffer,tracked.generation⟩)
        work := s.heap.work+1
        peak := max s.heap.peak (s.heap.liveSpace+1-s.heap.baseSpace)},s.views⟩ := by
  unfold writeEvent at run
  obtain ⟨heap,heapRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have outEq := Option.some.inj rest
  subst out
  unfold Proofs.CppMoveHeaders.write at heapRun
  obtain ⟨grant,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ heapRun
  obtain ⟨tracked,live,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  split at rest
  · obtain ⟨result,primitive,finish⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    have heapEq := Option.some.inj finish
    subst heap
    exact ⟨grant,tracked,result,found,live,primitive,rfl⟩
  · simp at rest

theorem writeEvent_allocationsValid (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (run : writeEvent s ty id value = some out) (valid : AllocationsValid s.heap ty) :
    AllocationsValid out.heap ty := by
  obtain ⟨grant,tracked,result,_,live,primitive,outEq⟩ := writeEvent_success s out ty id value run
  obtain ⟨_,ownerEq,_,bufferValid,_,_⟩ := write_parts tracked.buffer ty grant.writable grant.reference.element value result primitive
  have oldOwner := (valid _ _ live).1
  have inside := Proofs.CppMoveAssign.allocation_inside s.heap grant.reference.element.owner tracked live
  subst out
  intro owner actual found
  by_cases same : grant.reference.element.owner = owner
  · subst owner
    simp only [Heap.allocation,List.getElem?_set_self inside,Option.join_some,Option.some.injEq] at found
    subst actual
    exact ⟨ownerEq.trans oldOwner,bufferValid⟩
  · simp only [Heap.allocation,List.getElem?_set_ne same] at found
    exact valid owner actual found

theorem writeEvent_unique (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (run : writeEvent s ty id value = some out) (unique : Unique s.heap) : Unique out.heap := by
  obtain ⟨_,_,_,_,_,_,outEq⟩ := writeEvent_success s out ty id value run
  subst out
  exact unique

theorem writeEvent_ownsAll (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (run : writeEvent s ty id value = some out) (covered : OwnsAll s.heap) : OwnsAll out.heap := by
  obtain ⟨grant,tracked,result,_,live,_,outEq⟩ := writeEvent_success s out ty id value run
  subst out
  intro owner actual found
  by_cases same : grant.reference.element.owner = owner
  · subst owner
    obtain ⟨headerId,header,hf,owns⟩ := covered _ _ live
    exact ⟨headerId,header,hf,owns⟩
  · simp only [Heap.allocation,List.getElem?_set_ne same] at found
    obtain ⟨headerId,header,hf,owns⟩ := covered owner actual found
    exact ⟨headerId,header,hf,owns⟩

theorem writeEvent_headersLive (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (run : writeEvent s ty id value = some out) (headersLive : Proofs.CppMoveSpace.HeadersLive s.heap) :
    Proofs.CppMoveSpace.HeadersLive out.heap := by
  obtain ⟨grant,tracked,result,_,live,_,outEq⟩ := writeEvent_success s out ty id value run
  have inside := Proofs.CppMoveAssign.allocation_inside s.heap grant.reference.element.owner tracked live
  subst out
  intro headerId header owner hf owns
  by_cases same : grant.reference.element.owner = owner
  · subst owner
    simp [Heap.allocation,List.getElem?_set_self inside]
  · simp only [Heap.allocation,List.getElem?_set_ne same]
    exact headersLive headerId header owner hf owns

theorem writeEvent_other (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (grant : Grant) (other : Nat) (found : s.heap.grants[id]? = some grant)
    (different : grant.reference.element.owner ≠ other) (run : writeEvent s ty id value = some out) :
    out.heap.allocation other = s.heap.allocation other := by
  obtain ⟨actual,tracked,result,gf,_,_,outEq⟩ := writeEvent_success s out ty id value run
  have eq := Option.some.inj (found.symm.trans gf)
  subst actual
  subst out
  simp only [Heap.allocation,List.getElem?_set_ne different]


theorem capacity_set_sum (xs : List (Option (Proofs.CppVectorCopyAssign.Tracked α))) (id : Nat)
    (old actual : Proofs.CppVectorCopyAssign.Tracked α) (found : xs[id]? = some (some old))
    (capacity : actual.buffer.capacity = old.buffer.capacity) :
    ((xs.set id (some actual)).map Proofs.CppMoveAssign.capacity).sum =
      (xs.map Proofs.CppMoveAssign.capacity).sum := by
  induction xs generalizing id with
  | nil => simp at found
  | cons entry tail ih =>
    cases id with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst entry
      simp [Proofs.CppMoveAssign.capacity,capacity]
    | succ id =>
      simp only [List.getElem?_cons_succ] at found
      simp only [List.set_cons_succ,List.map_cons,List.sum_cons]
      rw [ih id found]

theorem writeEvent_resources (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (value : Int)
    (run : writeEvent s ty id value = some out) :
    out.heap.work = s.heap.work+1 ∧ out.heap.liveSpace = s.heap.liveSpace ∧
      out.heap.peak = max s.heap.peak (s.heap.liveSpace+1-s.heap.baseSpace) ∧ out.heap.baseSpace = s.heap.baseSpace := by
  obtain ⟨grant,tracked,result,_,live,primitive,outEq⟩ := writeEvent_success s out ty id value run
  obtain ⟨_,_,capacity,_,_,_⟩ := write_parts tracked.buffer ty grant.writable grant.reference.element value result primitive
  have slot := allocation_slot s.heap grant.reference.element.owner tracked live
  have raw := capacity_set_sum s.heap.allocations grant.reference.element.owner tracked
    ⟨result.buffer,tracked.generation⟩ slot capacity
  subst out
  refine ⟨rfl,?_,rfl,rfl⟩
  change s.heap.headers.countP (·.isSome) +
      ((s.heap.allocations.set grant.reference.element.owner (some ⟨result.buffer,tracked.generation⟩)).map Proofs.CppMoveAssign.capacity).sum =
    s.heap.headers.countP (·.isSome) + (s.heap.allocations.map Proofs.CppMoveAssign.capacity).sum
  rw [raw]

end Proofs.CppMoveWrite
