import Proofs.CppMoveViews
import Proofs.CppFrameCopyAssign

namespace Proofs.CppMoveFrame
open Proofs.CppScalar Proofs.CppVector Proofs.CppMoveHeaders
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings

-- A transient flat-integer Frame projection. Allocation IDs remain unchanged.
-- Empty-object placeholders carry header space only (capacity zero).
def ownerHeader (s : Heap Int) (owner : Nat) : Option Proofs.CppMoveHeaders.Header :=
  (s.headers.filterMap id).find? (fun h => h.allocation == some owner)

def box (b : Buffer Int) : Buffer Value :=
  ⟨b.owner,b.items.map Value.integer,b.capacity,b.limit,b.epoch⟩

def entries (s : Heap Int) (ty : Ty) : List (Option (Buffer Value × Tag)) :=
  (s.allocations.mapIdx fun owner entry => do
    let tracked ← entry
    let header ← ownerHeader s owner
    some (box tracked.buffer,⟨.integer ty,none,some header.scope,[]⟩)) ++
  (s.headers.mapIdx fun headerId entry => do
    let header ← entry
    if header.allocation = none then
      some (⟨s.allocations.length+headerId,[],0,header.limit,0⟩,
        ⟨.integer ty,none,some header.scope,[]⟩)
    else none)

def viewBinding (s : Proofs.CppMoveViews.State Int) (ty : Ty)
    (view : Proofs.CppMoveViews.View) : Binding :=
  match s.heap.header view.header with
  | none => ⟨s.heap.allocations.length+s.heap.headers.length,.integer ty,false,.root 0⟩
  | some header =>
    ⟨header.allocation.getD (s.heap.allocations.length+view.header),.integer ty,
      view.writable && header.writable,.root header.scope⟩

def materialize (s : Proofs.CppMoveViews.State Int) (ty : Ty) : Proofs.CppFrameCopyAssign.TrackedFrame :=
  let objects := entries s.heap ty
  let frame : Frame :=
    {state :=
      {forest := ⟨objects.map (fun entry => entry.map Prod.snd)⟩,
       storage := ⟨objects.map (fun entry => entry.map Prod.fst),s.heap.work,s.heap.peak,s.heap.baseSpace⟩},
     rootWritable := List.replicate objects.length true,
     bindings :=
       (s.heap.grants.map fun grant =>
         ⟨grant.reference.element.owner,.integer ty,grant.writable,.root 0⟩) ++
       (s.views.map (viewBinding s ty))}
  ⟨frame,fun owner index => ((s.heap.allocation owner).map (fun t => t.generation index)).getD 0⟩

def reference (s : Heap Int) (ty : Ty) (id : Nat) : Option Proofs.CppFrameCopyAssign.TrackedReference := do
  let grant ← s.grants[id]?
  some ⟨⟨id,ty,grant.writable,grant.reference.element⟩,grant.reference.generation⟩

-- Physical accounting must be proved for well-owned inputs: the Frame root
-- header for an allocation represents its unique owning object; empty-object
-- placeholders account for the remaining headers and have no element storage.
-- This projection is not yet a complete caller prepare/finish adapter. Newly
-- captured transient view bindings cannot escape as durable element grants;
-- capture must first append to the high-level immutable grant ledger.
theorem box_shape (b : Buffer Int) :
    (box b).owner = b.owner ∧ (box b).items.length = b.items.length ∧
    (box b).capacity = b.capacity ∧ (box b).limit = b.limit ∧ (box b).epoch = b.epoch := by
  simp [box]

theorem box_valid (b : Buffer Int) (ty : Ty) (valid : b.Valid ty.valid) :
    (box b).Valid (accepts (.integer ty)) := by
  simpa [Buffer.Valid,box,List.all_map,accepts] using valid


theorem allocation_slot (s : Heap Int) (owner : Nat) (tracked : Proofs.CppVectorCopyAssign.Tracked Int)
    (found : s.allocation owner = some tracked) : s.allocations[owner]? = some (some tracked) := by
  unfold Heap.allocation at found
  cases slot : s.allocations[owner]? with
  | none => simp [slot] at found
  | some entry =>
    cases entry with
    | none => simp [slot] at found
    | some actual =>
      simp only [slot,Option.join_some,Option.some.injEq] at found
      subst actual
      rfl

theorem entries_allocation (s : Heap Int) (ty : Ty) (owner : Nat)
    (tracked : Proofs.CppVectorCopyAssign.Tracked Int) (header : Proofs.CppMoveHeaders.Header)
    (found : s.allocation owner = some tracked) (headerFound : ownerHeader s owner = some header) :
    (entries s ty)[owner]? = some (some (box tracked.buffer,⟨.integer ty,none,some header.scope,[]⟩)) := by
  have slot := allocation_slot s owner tracked found
  have inside := (List.getElem?_eq_some_iff.mp slot).1
  unfold entries
  rw [List.getElem?_append_left (by simpa using inside)]
  simp [List.getElem?_mapIdx,slot,headerFound]

theorem entries_empty (s : Heap Int) (ty : Ty) (id : Nat) (header : Proofs.CppMoveHeaders.Header)
    (found : s.header id = some header) (empty : header.allocation = none) :
    (entries s ty)[s.allocations.length+id]? =
      some (some (⟨s.allocations.length+id,[],0,header.limit,0⟩,⟨.integer ty,none,some header.scope,[]⟩)) := by
  have slot := header_lookup s id header found
  simp [entries,List.getElem?_append,List.getElem?_mapIdx,slot,empty]

theorem materialize_resources (s : Proofs.CppMoveViews.State Int) (ty : Ty) :
    (materialize s ty).frame.state.storage.work = s.heap.work ∧
    (materialize s ty).frame.state.storage.peak = s.heap.peak ∧
    (materialize s ty).frame.state.storage.baseSpace = s.heap.baseSpace := ⟨rfl,rfl,rfl⟩

theorem materialize_entry (s : Proofs.CppMoveViews.State Int) (ty : Ty) (owner : Nat)
    (buffer : Buffer Value) (tag : Tag)
    (entry : (entries s.heap ty)[owner]? = some (some (buffer,tag))) :
    (materialize s ty).frame.state.storage.lookup owner = some buffer ∧
      (materialize s ty).frame.state.forest.lookup owner = some tag := by
  simp [materialize,Proofs.CppVectorStore.Store.lookup,Forest.lookup,List.getElem?_map,entry]

theorem materialize_object (s : Proofs.CppMoveViews.State Int) (ty : Ty) (owner : Nat)
    (buffer : Buffer Value) (tag : Tag)
    (entry : (entries s.heap ty)[owner]? = some (some (buffer,tag)))
    (typed : tag.element = .integer ty) (valid : (materialize s ty).frame.state.wellFormed = true) :
    (materialize s ty).frame.object owner (.integer ty) = some (buffer,tag) := by
  have pair := materialize_entry s ty owner buffer tag entry
  simp [Frame.object,valid,pair.1,pair.2,typed]


theorem materialize_maximum (s : Proofs.CppMoveViews.State Int) (ty : Ty) (owner scope : Nat)
    (buffer : Buffer Value)
    (entry : (entries s.heap ty)[owner]? = some (some (buffer,⟨.integer ty,none,some scope,[]⟩))) :
    (materialize s ty).frame.maximum owner = some true := by
  have pair := materialize_entry s ty owner buffer _ entry
  have root : (materialize s ty).frame.state.forest.rootOwner owner = some owner := by
    rw [Forest.rootOwner,pair.2]
    rfl
  have inside := (List.getElem?_eq_some_iff.mp entry).1
  have lengths : (materialize s ty).frame.rootWritable.length =
      (materialize s ty).frame.state.forest.objects.length := by simp [materialize]
  unfold Frame.maximum
  simp only [lengths,ite_true,root,Bind.bind,Option.bind]
  simp [materialize,inside]


theorem ownerHeader_parts (s : Heap Int) (owner : Nat) (header : Proofs.CppMoveHeaders.Header)
    (found : ownerHeader s owner = some header) :
    ∃ id, s.header id = some header ∧ header.allocation = some owner := by
  have member := List.mem_of_find?_eq_some found
  obtain ⟨entry,mem,eq⟩ := List.mem_filterMap.mp member
  change entry = some header at eq
  subst entry
  obtain ⟨id,slot⟩ := List.mem_iff_getElem?.mp mem
  refine ⟨id,?_,?_⟩
  · simp [Heap.header,slot]
  · have matched := List.find?_some found
    simpa using matched

theorem ownerHeader_exists (s : Heap Int) (owner : Nat) (tracked : Proofs.CppVectorCopyAssign.Tracked Int)
    (covered : OwnsAll s) (found : s.allocation owner = some tracked) :
    ∃ header, ownerHeader s owner = some header := by
  obtain ⟨id,header,hf,owns⟩ := covered owner tracked found
  have member : header ∈ s.headers.filterMap (fun entry => entry) := by
    apply List.mem_filterMap.mpr
    exact ⟨some header,List.mem_iff_getElem?.mpr ⟨id,header_lookup s id header hf⟩,rfl⟩
  have live : (ownerHeader s owner).isSome := List.find?_isSome.mpr ⟨header,member,by simp [owns]⟩
  cases actual : ownerHeader s owner with
  | none => simp [actual] at live
  | some header => exact ⟨header,rfl⟩

theorem ownerHeader_unique (s : Heap Int) (owner id : Nat) (header : Proofs.CppMoveHeaders.Header)
    (unique : Unique s) (found : s.header id = some header) (owns : header.allocation = some owner)
    (existsOwner : ∃ actual, ownerHeader s owner = some actual) : ownerHeader s owner = some header := by
  obtain ⟨actual,actualFound⟩ := existsOwner
  obtain ⟨other,otherFound,otherOwns⟩ := ownerHeader_parts s owner actual actualFound
  have same := unique id other header actual owner found otherFound owns otherOwns
  subst other
  have sameHeader := Option.some.inj (found.symm.trans otherFound)
  subst actual
  exact actualFound


-- A local, checkable condition on the projected entries, not a premise that
-- the completed Frame is already well formed.
def EntriesValid (s : Heap Int) (ty : Ty) : Prop :=
  ∀ (owner : Nat) (buffer : Buffer Value) (tag : Tag), (entries s ty)[owner]? = some (some (buffer,tag)) →
    ∃ scope, tag = ⟨.integer ty,none,some scope,[]⟩ ∧ buffer.owner = owner ∧
      buffer.Valid (accepts (.integer ty))

theorem materialize_wellFormed (s : Proofs.CppMoveViews.State Int) (ty : Ty)
    (supported : Proofs.CppVectorBindings.supported ty) (valid : EntriesValid s.heap ty) :
    (materialize s ty).frame.state.wellFormed = true := by
  have each : ∀ owner, (materialize s ty).frame.state.forest.check owner = true ∧
      (materialize s ty).frame.state.check owner = true := by
    intro owner
    cases slot : (entries s.heap ty)[owner]? with
    | none =>
      simp [materialize,Forest.check,Forest.lookup,State.check,Proofs.CppVectorStore.Store.lookup,
        List.getElem?_map,slot]
    | some entry =>
      cases entry with
      | none =>
        simp [materialize,Forest.check,Forest.lookup,State.check,Proofs.CppVectorStore.Store.lookup,
          List.getElem?_map,slot]
      | some pair =>
        rcases pair with ⟨buffer,tag⟩
        obtain ⟨scope,tagEq,ownerEq,bufferValid⟩ := valid owner buffer tag slot
        subst tag
        simp [materialize,Forest.check,Forest.lookup,State.check,Proofs.CppVectorStore.Store.lookup,
          List.getElem?_map,slot,Forest.tagOK,Forest.parentOK,Element.supported,supported,
          ownerEq,payloadOK,bufferValid]
  simp only [State.wellFormed,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp [materialize]
  · apply List.all_eq_true.mpr
    intro owner _
    exact (each owner).1
  · apply List.all_eq_true.mpr
    intro owner _
    exact (each owner).2


def AllocationsValid (s : Heap Int) (ty : Ty) : Prop :=
  ∀ owner tracked, s.allocation owner = some tracked →
    tracked.buffer.owner = owner ∧ tracked.buffer.Valid ty.valid

theorem entries_valid (s : Heap Int) (ty : Ty) (valid : AllocationsValid s ty) : EntriesValid s ty := by
  intro owner buffer tag found
  by_cases inside : owner < s.allocations.length
  · unfold entries at found
    rw [List.getElem?_append_left (by simpa using inside)] at found
    simp only [List.getElem?_mapIdx] at found
    cases slot : s.allocations[owner]? with
    | none => simp [slot] at found
    | some entry =>
      cases entry with
      | none => simp [slot] at found
      | some tracked =>
        cases hf : ownerHeader s owner with
        | none => simp [slot,hf] at found
        | some header =>
          simp only [slot,Option.map_some,Bind.bind,Option.bind,hf,Option.some.injEq,Prod.mk.injEq] at found
          rcases found with ⟨bufferEq,tagEq⟩
          subst buffer
          subst tag
          have actual : s.allocation owner = some tracked := by simp [Heap.allocation,slot]
          have good := valid owner tracked actual
          exact ⟨header.scope,rfl,good.1,box_valid tracked.buffer ty good.2⟩
  · unfold entries at found
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt inside)] at found
    simp only [List.length_mapIdx,List.getElem?_mapIdx] at found
    cases slot : s.headers[owner-s.allocations.length]? with
    | none => simp [slot] at found
    | some entry =>
      cases entry with
      | none => simp [slot] at found
      | some header =>
        simp only [slot,Option.map_some,Bind.bind,Option.bind] at found
        split at found
        next empty =>
          have pair := Prod.mk.inj (Option.some.inj (Option.some.inj found))
          rcases pair with ⟨bufferEq,tagEq⟩
          subst buffer
          subst tag
          refine ⟨header.scope,rfl,?_,?_⟩
          · dsimp only
            omega
          · simp [Buffer.Valid]
        next => simp at found

theorem materialize_ready (s : Proofs.CppMoveViews.State Int) (ty : Ty)
    (supported : Proofs.CppVectorBindings.supported ty) (valid : AllocationsValid s.heap ty) :
    (materialize s ty).frame.state.wellFormed = true :=
  materialize_wellFormed s ty supported (entries_valid s.heap ty valid)


theorem assign_allocationsValid (s out : Proofs.CppMoveViews.State Int) (ty : Ty)
    (accept : Int → Bool) (target source : Nat)
    (run : Proofs.CppMoveViews.assign s accept target source = some out)
    (valid : AllocationsValid s.heap ty) : AllocationsValid out.heap ty := by
  obtain ⟨tv,th,sv,sh,_,_,_,_,core,_⟩ :=
    Proofs.CppMoveViews.assign_success s out accept target source run
  obtain ⟨th,sh,_,_,heapEq⟩ :=
    Proofs.CppMoveAssign.move_assign_success s.heap out.heap accept tv.header sv.header core
  intro owner tracked found
  rw [heapEq] at found
  exact valid owner tracked (Proofs.CppMoveAssign.assigned_sub s.heap tv.header sv.header th sh owner tracked found)

theorem construct_allocationsValid (s out : Proofs.CppMoveViews.State Int) (ty : Ty)
    (accept : Int → Bool) (source scope slot : Nat) (writable : Bool)
    (run : Proofs.CppMoveViews.construct s accept source scope writable = some (out,slot))
    (valid : AllocationsValid s.heap ty) : AllocationsValid out.heap ty := by
  obtain ⟨view,header,destination,_,_,core,_,_⟩ :=
    Proofs.CppMoveViews.construct_success s out accept source scope slot writable run
  obtain ⟨header,_,_,heapEq⟩ :=
    move_construct_success s.heap out.heap accept view.header scope destination writable core
  intro owner tracked found
  rw [heapEq] at found
  exact valid owner tracked found


theorem box_valid_iff (b : Buffer Int) (ty : Ty) :
    (box b).Valid (accepts (.integer ty)) ↔ b.Valid ty.valid := by
  simp [box,Buffer.Valid,List.all_map,accepts]

theorem box_read (b : Buffer Int) (ty : Ty) (ref : ElementRef) :
    (CppVector.readRef (box b) (accepts (.integer ty)) ref).bind (fun r => match r.value with | .integer v => some v | .child _ => none) =
      (CppVector.readRef b ty.valid ref).map (fun r => r.value) := by
  unfold CppVector.readRef
  simp only [box_valid_iff]
  by_cases good : b.Valid ty.valid ∧ ref.owner = b.owner ∧ ref.epoch = b.epoch
  · cases itemFound : b.items[ref.index]? <;>
      simp [box,good,List.getElem?_map,itemFound]
  · simp [box,good]

theorem materialize_binding (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (grant : Grant)
    (found : s.heap.grants[id]? = some grant) :
    (materialize s ty).frame.bindings[id]? =
      some ⟨grant.reference.element.owner,.integer ty,grant.writable,.root 0⟩ := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  change ((s.heap.grants.map fun g => (⟨g.reference.element.owner,.integer ty,g.writable,.root 0⟩ : Binding)) ++
    (s.views.map (viewBinding s ty)))[id]? = _
  rw [List.getElem?_append_left (by simpa using inside)]
  simp [List.getElem?_map,found]

theorem materialize_live_grant (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (grant : Grant)
    (tracked : Proofs.CppVectorCopyAssign.Tracked Int)
    (found : s.heap.grants[id]? = some grant)
    (live : s.heap.allocation grant.reference.element.owner = some tracked) (covered : OwnsAll s.heap) :
    (materialize s ty).frame.grant ⟨id,ty,grant.writable,grant.reference.element⟩ = some grant.writable := by
  obtain ⟨header,hf⟩ := ownerHeader_exists s.heap grant.reference.element.owner tracked covered live
  have entry := entries_allocation s.heap ty grant.reference.element.owner tracked header live hf
  have maximum := materialize_maximum s ty grant.reference.element.owner header.scope (box tracked.buffer) entry
  have binding := materialize_binding s ty id grant found
  simp [Frame.grant,binding,maximum]


theorem materialize_live_read (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (grant : Grant)
    (tracked : Proofs.CppVectorCopyAssign.Tracked Int)
    (found : s.heap.grants[id]? = some grant)
    (live : s.heap.allocation grant.reference.element.owner = some tracked)
    (covered : OwnsAll s.heap) (supported : Proofs.CppVectorBindings.supported ty)
    (valid : AllocationsValid s.heap ty) :
    (reference s.heap ty id).bind (Proofs.CppFrameCopyAssign.read (materialize s ty)) =
      Proofs.CppMoveHeaders.read s.heap ty.valid id := by
  obtain ⟨header,hf⟩ := ownerHeader_exists s.heap grant.reference.element.owner tracked covered live
  have entry := entries_allocation s.heap ty grant.reference.element.owner tracked header live hf
  have object := materialize_object s ty grant.reference.element.owner (box tracked.buffer)
    ⟨.integer ty,none,some header.scope,[]⟩ entry rfl (materialize_ready s ty supported valid)
  have granted := materialize_live_grant s ty id grant tracked found live covered
  have generation : (materialize s ty).generation grant.reference.element.owner grant.reference.element.index =
      tracked.generation grant.reference.element.index := by simp [materialize,live]
  unfold Proofs.CppMoveHeaders.read
  simp only [reference,found,live,Bind.bind,Option.bind]
  unfold Proofs.CppFrameCopyAssign.read Proofs.CppVectorCopyAssign.read
  simp only [generation]
  by_cases equal : grant.reference.generation = tracked.generation grant.reference.element.index
  · simp only [equal,ite_true,Frame.read,granted,object,Bind.bind,Option.bind]
    have correct := box_read tracked.buffer ty grant.reference.element
    cases boxed : CppVector.readRef (box tracked.buffer) (accepts (.integer ty)) grant.reference.element with
    | none =>
      cases plain : CppVector.readRef tracked.buffer ty.valid grant.reference.element <;> simp_all
    | some result =>
      cases itemEq : result.value <;>
        cases plain : CppVector.readRef tracked.buffer ty.valid grant.reference.element <;> simp_all
  · simp [equal]


theorem entries_missing (s : Heap Int) (ty : Ty) (owner : Nat)
    (inside : owner < s.allocations.length) (dead : s.allocation owner = none) :
    (entries s ty)[owner]? = some none := by
  unfold entries
  rw [List.getElem?_append_left (by simpa using inside)]
  simp only [List.getElem?_mapIdx]
  cases slot : s.allocations[owner]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp slot
    omega
  | some entry =>
    cases entry with
    | none => simp
    | some tracked => simp [Heap.allocation,slot] at dead

theorem materialize_missing_object (s : Proofs.CppMoveViews.State Int) (ty : Ty) (owner : Nat)
    (entry : (entries s.heap ty)[owner]? = some none) :
    (materialize s ty).frame.object owner (.integer ty) = none := by
  simp [Frame.object,materialize,Proofs.CppVectorStore.Store.lookup,Forest.lookup,List.getElem?_map,entry]

theorem materialize_dead_read (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (grant : Grant)
    (found : s.heap.grants[id]? = some grant) (inside : grant.reference.element.owner < s.heap.allocations.length)
    (dead : s.heap.allocation grant.reference.element.owner = none) :
    (reference s.heap ty id).bind (Proofs.CppFrameCopyAssign.read (materialize s ty)) = none := by
  have entry := entries_missing s.heap ty grant.reference.element.owner inside dead
  have object := materialize_missing_object s ty grant.reference.element.owner entry
  have gen : (materialize s ty).generation grant.reference.element.owner grant.reference.element.index = 0 := by
    simp [materialize,dead]
  simp only [reference,found,Bind.bind,Option.bind]
  unfold Proofs.CppFrameCopyAssign.read
  simp only [gen]
  by_cases equal : grant.reference.generation = 0
  · simp only [equal,ite_true]
    cases checked : (materialize s ty).frame.grant ⟨id,ty,grant.writable,grant.reference.element⟩ <;>
      simp [Frame.read,checked,object]
  · simp [equal]

theorem materialize_read (s : Proofs.CppMoveViews.State Int) (ty : Ty) (id : Nat) (grant : Grant)
    (found : s.heap.grants[id]? = some grant) (inside : grant.reference.element.owner < s.heap.allocations.length)
    (covered : OwnsAll s.heap) (supported : Proofs.CppVectorBindings.supported ty)
    (valid : AllocationsValid s.heap ty) :
    (reference s.heap ty id).bind (Proofs.CppFrameCopyAssign.read (materialize s ty)) =
      Proofs.CppMoveHeaders.read s.heap ty.valid id := by
  cases live : s.heap.allocation grant.reference.element.owner with
  | none =>
    rw [materialize_dead_read s ty id grant found inside live]
    simp [Proofs.CppMoveHeaders.read,found,live]
  | some tracked => exact materialize_live_read s ty id grant tracked found live covered supported valid


theorem materialize_view_binding (s : Proofs.CppMoveViews.State Int) (ty : Ty) (slot : Nat)
    (view : Proofs.CppMoveViews.View) (found : s.views[slot]? = some view) :
    (materialize s ty).frame.bindings[s.heap.grants.length+slot]? = some (viewBinding s ty view) := by
  change ((s.heap.grants.map _) ++ (s.views.map (viewBinding s ty)))[s.heap.grants.length+slot]? = _
  simp [List.getElem?_append,List.getElem?_map,found]

theorem materialize_root_resolve (s : Proofs.CppMoveViews.State Int) (ty : Ty)
    (slot owner scope : Nat) (writable : Bool) (buffer : Buffer Value)
    (binding : (materialize s ty).frame.bindings[slot]? = some ⟨owner,.integer ty,writable,.root scope⟩)
    (entry : (entries s.heap ty)[owner]? = some (some (buffer,⟨.integer ty,none,some scope,[]⟩)))
    (supported : Proofs.CppVectorBindings.supported ty) (valid : AllocationsValid s.heap ty) :
    (materialize s ty).frame.resolve slot (.integer ty) =
      some (⟨owner,.integer ty,writable,.root scope⟩,buffer) := by
  have object := materialize_object s ty owner buffer _ entry rfl (materialize_ready s ty supported valid)
  have maximum := materialize_maximum s ty owner scope buffer entry
  have header : (materialize s ty).frame.headerOwner ⟨owner,.integer ty,writable,.root scope⟩ = some owner := by
    simp [Frame.headerOwner,object]
  simp [Frame.resolve,binding,header,object,maximum]

theorem view_writable (view : Proofs.CppMoveViews.View) (header : Proofs.CppMoveHeaders.Header)
    (permission : view.writable = true → header.writable = true) :
    (view.writable && header.writable) = view.writable := by
  cases vw : view.writable <;> simp_all

theorem materialize_live_view (s : Proofs.CppMoveViews.State Int) (ty : Ty) (slot owner : Nat)
    (view : Proofs.CppMoveViews.View) (header : Proofs.CppMoveHeaders.Header)
    (tracked : Proofs.CppVectorCopyAssign.Tracked Int)
    (resolved : Proofs.CppMoveViews.resolve s slot = some (view,header))
    (owns : header.allocation = some owner) (live : s.heap.allocation owner = some tracked)
    (unique : Unique s.heap) (covered : OwnsAll s.heap)
    (supported : Proofs.CppVectorBindings.supported ty) (valid : AllocationsValid s.heap ty) :
    (materialize s ty).frame.resolve (s.heap.grants.length+slot) (.integer ty) =
      some (⟨owner,.integer ty,view.writable,.root header.scope⟩,box tracked.buffer) := by
  have parts := Proofs.CppMoveViews.resolve_parts s slot view header resolved
  have ownerFound := ownerHeader_unique s.heap owner view.header header unique parts.2.1 owns
    (ownerHeader_exists s.heap owner tracked covered live)
  have entry := entries_allocation s.heap ty owner tracked header live ownerFound
  have binding := materialize_view_binding s ty slot view parts.1
  have permission := view_writable view header parts.2.2
  simp only [viewBinding,parts.2.1,owns,Option.getD_some] at binding
  rw [permission] at binding
  exact materialize_root_resolve s ty _ owner header.scope view.writable _ binding entry supported valid

theorem materialize_empty_view (s : Proofs.CppMoveViews.State Int) (ty : Ty) (slot : Nat)
    (view : Proofs.CppMoveViews.View) (header : Proofs.CppMoveHeaders.Header)
    (resolved : Proofs.CppMoveViews.resolve s slot = some (view,header))
    (empty : header.allocation = none)
    (supported : Proofs.CppVectorBindings.supported ty) (valid : AllocationsValid s.heap ty) :
    (materialize s ty).frame.resolve (s.heap.grants.length+slot) (.integer ty) =
      some (⟨s.heap.allocations.length+view.header,.integer ty,view.writable,.root header.scope⟩,
        ⟨s.heap.allocations.length+view.header,[],0,header.limit,0⟩) := by
  have parts := Proofs.CppMoveViews.resolve_parts s slot view header resolved
  have entry := entries_empty s.heap ty view.header header parts.2.1 empty
  have binding := materialize_view_binding s ty slot view parts.1
  have permission := view_writable view header parts.2.2
  simp only [viewBinding,parts.2.1,empty,Option.getD_none] at binding
  rw [permission] at binding
  exact materialize_root_resolve s ty _ _ header.scope view.writable _ binding entry supported valid


def currentBuffer (s : Heap Int) (headerId : Nat) (header : Proofs.CppMoveHeaders.Header) : Option (Buffer Int) :=
  match header.allocation with
  | none => some ⟨s.allocations.length+headerId,[],0,header.limit,0⟩
  | some owner => (s.allocation owner).map (fun tracked => tracked.buffer)

theorem materialize_view_ready (s : Proofs.CppMoveViews.State Int) (ty : Ty) (slot : Nat)
    (view : Proofs.CppMoveViews.View) (header : Proofs.CppMoveHeaders.Header)
    (resolved : Proofs.CppMoveViews.resolve s slot = some (view,header))
    (readable : Proofs.CppMoveHeaders.readable s.heap header ty.valid = true)
    (unique : Unique s.heap) (covered : OwnsAll s.heap)
    (supported : Proofs.CppVectorBindings.supported ty) (valid : AllocationsValid s.heap ty) :
    ∃ buffer, currentBuffer s.heap view.header header = some buffer ∧
      (materialize s ty).frame.resolve (s.heap.grants.length+slot) (.integer ty) =
        some (⟨buffer.owner,.integer ty,view.writable,.root header.scope⟩,box buffer) := by
  cases owns : header.allocation with
  | none =>
    refine ⟨⟨s.heap.allocations.length+view.header,[],0,header.limit,0⟩,?_,?_⟩
    · simp [currentBuffer,owns]
    · exact materialize_empty_view s ty slot view header resolved owns supported valid
  | some owner =>
    cases live : s.heap.allocation owner with
    | none => simp [Proofs.CppMoveHeaders.readable,owns,live] at readable
    | some tracked =>
      refine ⟨tracked.buffer,?_,?_⟩
      · simp [currentBuffer,owns,live]
      · have ownerEq := (valid owner tracked live).1
        simpa only [ownerEq] using
          materialize_live_view s ty slot owner view header tracked resolved owns live unique covered supported valid

end Proofs.CppMoveFrame
