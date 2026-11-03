import Proofs.CppMoveClass
import Proofs.CppNoResizeRun

namespace Proofs.CppMoveRestore
open Proofs.CppScalar Proofs.CppVector Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveWrite
open Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppBufferHeaders

structure Shape where
  forest : Forest
  maximum : List Bool
  buffers : List (Option Signature)
  base : Nat
  deriving DecidableEq, Repr

-- A finite executable check. Payload values, work and historical peak may vary.
def shape (f : Frame) : Shape :=
  ⟨f.state.forest,f.rootWritable,(List.range f.state.storage.objects.length).map (fun owner => (f.state.storage.lookup owner).map signature),f.state.storage.baseSpace⟩

def restoreEntry (store : Store Value) (ty : Ty) (owner : Nat)
    (entry : Option (Proofs.CppVectorCopyAssign.Tracked Int)) :
    Option (Option (Proofs.CppVectorCopyAssign.Tracked Int)) :=
  match entry with
  | none => some none
  | some old => do
    let actual ← store.lookup owner
    let decoded ← unbox actual
    if signature (box decoded) = signature (box old.buffer) ∧ decoded.owner = owner ∧ decoded.Valid ty.valid then
      some (some ⟨decoded,old.generation⟩)
    else none

def restoreEntries (store : Store Value) (ty : Ty) : Nat →
    List (Option (Proofs.CppVectorCopyAssign.Tracked Int)) →
    Option (List (Option (Proofs.CppVectorCopyAssign.Tracked Int)))
  | _,[] => some []
  | owner,entry::tail => do
    let next ← restoreEntry store ty owner entry
    let rest ← restoreEntries store ty (owner+1) tail
    some (next::rest)

-- Table scans are ghost interpreter work, not additional C++ operations.
-- No allocation ID, header ID, immutable grant or lifetime generation is replaced.
def restore (s : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame) :
    Option (Proofs.CppMoveViews.State Int) := do
  if shape after = shape (materialize s ty).frame then
    let allocations ← restoreEntries after.state.storage ty 0 s.heap.allocations
    some ⟨{s.heap with allocations := allocations,work := after.state.storage.work,peak := after.state.storage.peak,baseSpace := after.state.storage.baseSpace},s.views⟩
  else none


theorem shape_of_sameHeaders (before after : Frame) (same : SameHeaders before.state after.state)
    (maximum : after.rootWritable = before.rootWritable) : shape after = shape before := by
  unfold shape
  rw [same.forest,maximum,same.count,same.base]
  congr 1
  exact List.map_congr_left (fun owner _ => same.buffers owner)



theorem context_of_root (forest : Forest) (owner : Nat) (tag : Tag)
    (found : forest.lookup owner = some tag) (root : tag.parent = none) : forest.context owner = tag.scope := by
  have ownerRun : forest.rootOwner owner = some owner := by
    rw [Forest.rootOwner,found]
    simp [root]
  rw [Forest.context,ownerRun]
  simp [found]

theorem context_of_none (forest : Forest) (owner : Nat) (found : forest.lookup owner = none) :
    forest.context owner = none := by
  have dead : forest.rootOwner owner = none := by rw [Forest.rootOwner,found]; rfl
  rw [Forest.context,dead]
  rfl


theorem decode_ready (values : List Value) (ty : Ty)
    (valid : values.all (accepts (.integer ty)) = true) :
    ∃ decoded, decode values = some decoded ∧ decoded.all ty.valid = true := by
  induction values with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons value tail ih =>
    cases value with
    | child owner => simp [accepts] at valid
    | integer value =>
      have parts : ty.valid value = true ∧ tail.all (accepts (.integer ty)) = true := by simpa [accepts] using valid
      obtain ⟨decoded,run,validTail⟩ := ih parts.2
      exact ⟨value::decoded,by simp [decode,run],by simp [parts.1,validTail]⟩

theorem unbox_ready (buffer : Buffer Value) (ty : Ty) (valid : buffer.Valid (accepts (.integer ty))) :
    ∃ decoded, unbox buffer = some decoded ∧ box decoded = buffer ∧ decoded.Valid ty.valid := by
  obtain ⟨values,run,accepted⟩ := decode_ready buffer.items ty valid.2.2
  have eq := decode_success buffer.items values run
  refine ⟨⟨buffer.owner,values,buffer.capacity,buffer.limit,buffer.epoch⟩,?_,?_,?_⟩
  · simp [unbox,run]
  · simp only [box]
    rw [← eq]
  · have lengths : values.length = buffer.items.length := by rw [eq,List.length_map]
    exact ⟨by simpa [lengths] using valid.1,valid.2.1,accepted⟩

theorem restoreEntry_ready (store : Store Value) (ty : Ty) (owner : Nat)
    (old : Proofs.CppVectorCopyAssign.Tracked Int) (actual : Buffer Value)
    (found : store.lookup owner = some actual) (same : signature actual = signature (box old.buffer))
    (owns : actual.owner = owner) (valid : actual.Valid (accepts (.integer ty))) :
    ∃ next, restoreEntry store ty owner (some old) = some (some next) ∧
      box next.buffer = actual ∧ next.generation = old.generation := by
  obtain ⟨decoded,decodedRun,boxed,decodedValid⟩ := unbox_ready actual ty valid
  have decodedOwner : decoded.owner = owner := by
    have ownerEq := congrArg Buffer.owner boxed
    exact ownerEq.trans owns
  refine ⟨⟨decoded,old.generation⟩,?_,boxed,rfl⟩
  simp [restoreEntry,found,decodedRun,boxed,same,decodedOwner,decodedValid]

theorem restoreEntry_success (store : Store Value) (ty : Ty) (owner : Nat)
    (old next : Proofs.CppVectorCopyAssign.Tracked Int)
    (run : restoreEntry store ty owner (some old) = some (some next)) :
    store.lookup owner = some (box next.buffer) ∧
      signature (box next.buffer) = signature (box old.buffer) ∧
      next.buffer.owner = owner ∧ next.buffer.Valid ty.valid ∧ next.generation = old.generation := by
  unfold restoreEntry at run
  obtain ⟨actual,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  obtain ⟨decoded,decodedRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  split at rest
  next guard =>
    have eq := Option.some.inj (Option.some.inj rest)
    subst next
    have boxed := unbox_success actual decoded decodedRun
    exact ⟨by simpa only [boxed] using found,guard.1,guard.2.1,guard.2.2,rfl⟩
  next => simp at rest

theorem restoreEntry_presence (store : Store Value) (ty : Ty) (owner : Nat)
    (old next : Option (Proofs.CppVectorCopyAssign.Tracked Int))
    (run : restoreEntry store ty owner old = some next) : next.isSome = old.isSome := by
  cases old with
  | none => cases Option.some.inj run; rfl
  | some old =>
    unfold restoreEntry at run
    obtain ⟨_,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    obtain ⟨_,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    split at rest
    · cases Option.some.inj rest; rfl
    · simp at rest


theorem restoreEntries_length (store : Store Value) (ty : Ty) (start : Nat)
    (entries next : List (Option (Proofs.CppVectorCopyAssign.Tracked Int)))
    (run : restoreEntries store ty start entries = some next) : next.length = entries.length := by
  induction entries generalizing start next with
  | nil => cases Option.some.inj run; rfl
  | cons entry tail ih =>
    simp only [restoreEntries] at run
    obtain ⟨head,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    obtain ⟨remaining,tailRun,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    have eq := Option.some.inj done
    rw [← eq,List.length_cons,List.length_cons,ih (start+1) remaining tailRun]

theorem restoreEntries_lookup (store : Store Value) (ty : Ty) (start : Nat)
    (entries next : List (Option (Proofs.CppVectorCopyAssign.Tracked Int)))
    (run : restoreEntries store ty start entries = some next) (index : Nat)
    (entry : Option (Proofs.CppVectorCopyAssign.Tracked Int)) (found : entries[index]? = some entry) :
    ∃ actual, next[index]? = some actual ∧ restoreEntry store ty (start+index) entry = some actual := by
  induction entries generalizing start next index with
  | nil => simp at found
  | cons head tail ih =>
    simp only [restoreEntries] at run
    obtain ⟨actual,headRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    obtain ⟨remaining,tailRun,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    have eq := Option.some.inj done
    rw [← eq]
    cases index with
    | zero =>
      have same := Option.some.inj found
      subst entry
      exact ⟨actual,rfl,by simpa using headRun⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      obtain ⟨value,slot,ran⟩ := ih (start+1) remaining tailRun index found
      exact ⟨value,slot,by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ran⟩

def ReadyEntries (store : Store Value) (ty : Ty) (start : Nat)
    (entries : List (Option (Proofs.CppVectorCopyAssign.Tracked Int))) : Prop :=
  ∀ index old, entries[index]? = some (some old) →
    ∃ actual, store.lookup (start+index) = some actual ∧ signature actual = signature (box old.buffer) ∧
      actual.owner = start+index ∧ actual.Valid (accepts (.integer ty))

theorem restoreEntries_ready (store : Store Value) (ty : Ty) (start : Nat)
    (entries : List (Option (Proofs.CppVectorCopyAssign.Tracked Int))) (ready : ReadyEntries store ty start entries) :
    ∃ next, restoreEntries store ty start entries = some next := by
  induction entries generalizing start with
  | nil => exact ⟨[],rfl⟩
  | cons head tail ih =>
    have first : ∃ next, restoreEntry store ty start head = some next := by
      cases head with
      | none => exact ⟨none,rfl⟩
      | some old =>
        obtain ⟨actual,found,same,owns,valid⟩ := ready 0 old rfl
        obtain ⟨next,run,_,_⟩ := restoreEntry_ready store ty start old actual (by simpa using found) same (by simpa using owns) valid
        exact ⟨some next,run⟩
    obtain ⟨next,firstRun⟩ := first
    have tailReady : ReadyEntries store ty (start+1) tail := by
      intro index old found
      have whole : (head::tail)[index+1]? = some (some old) := found
      obtain ⟨actual,slot,same,owns,valid⟩ := ready (index+1) old whole
      exact ⟨actual,by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using slot,same,
        by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using owns,valid⟩
    obtain ⟨rest,tailRun⟩ := ih (start+1) tailReady
    exact ⟨next::rest,by simp [restoreEntries,firstRun,tailRun]⟩

theorem restore_ready (s : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (same : shape after = shape (materialize s ty).frame)
    (ready : ReadyEntries after.state.storage ty 0 s.heap.allocations) :
    ∃ out, restore s ty after = some out := by
  obtain ⟨allocations,run⟩ := restoreEntries_ready after.state.storage ty 0 s.heap.allocations ready
  exact ⟨⟨{s.heap with allocations := allocations,work := after.state.storage.work,peak := after.state.storage.peak,baseSpace := after.state.storage.baseSpace},s.views⟩,by simp [restore,same,run]⟩

theorem restore_metadata (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) :
    out.heap.headers = s.heap.headers ∧ out.heap.grants = s.heap.grants ∧ out.views = s.views ∧
      out.heap.allocations.length = s.heap.allocations.length ∧
      out.heap.work = after.state.storage.work ∧ out.heap.peak = after.state.storage.peak ∧
      out.heap.baseSpace = after.state.storage.baseSpace ∧ shape after = shape (materialize s ty).frame := by
  unfold restore at run
  split at run
  next same =>
    obtain ⟨allocations,entriesRun,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj done
    subst out
    exact ⟨rfl,rfl,rfl,restoreEntries_length _ _ _ _ _ entriesRun,rfl,rfl,rfl,same⟩
  next => simp at run



theorem ready_of_sameHeaders (s : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (same : SameHeaders (materialize s ty).frame.state after.state)
    (covered : OwnsAll s.heap) (valid : after.state.wellFormed = true) :
    ReadyEntries after.state.storage ty 0 s.heap.allocations := by
  intro owner old found
  simp only [Nat.zero_add]
  have live : s.heap.allocation owner = some old := by simp [Heap.allocation,found]
  obtain ⟨header,headerFound⟩ := ownerHeader_exists s.heap owner old covered live
  have before := materialize_entry s ty owner (box old.buffer) ⟨.integer ty,none,some header.scope,[]⟩
    (entries_allocation s.heap ty owner old header live headerFound)
  have signatures := same.buffers owner
  rw [before.1] at signatures
  cases actualFound : after.state.storage.lookup owner with
  | none => simp [actualFound] at signatures
  | some actual =>
    simp only [actualFound,Option.map_some,Option.some.injEq] at signatures
    obtain ⟨tag,tagFound,owns,payload⟩ := Proofs.CppNestedVectorStore.wellFormed_buffer after.state owner actual valid actualFound
    have nextTag : after.state.forest.lookup owner = some ⟨.integer ty,none,some header.scope,[]⟩ := by
      rw [same.forest]
      exact before.2
    have tagEq := Option.some.inj (tagFound.symm.trans nextTag)
    subst tag
    exact ⟨actual,rfl,signatures,owns,payload.1⟩

theorem restore_of_sameHeaders (s : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (same : SameHeaders (materialize s ty).frame.state after.state)
    (maximum : after.rootWritable = (materialize s ty).frame.rootWritable)
    (covered : OwnsAll s.heap) (valid : after.state.wellFormed = true) :
    ∃ out, restore s ty after = some out :=
  restore_ready s ty after (shape_of_sameHeaders _ _ same maximum) (ready_of_sameHeaders s ty after same covered valid)

theorem command_restore_ready (s : Proofs.CppMoveContext.Context) (ty : Ty)
    (fuel : Nat) (command : Proofs.CppNestedProgram.Command) (out : Proofs.CppNestedProgram.NStep)
    (allowed : Proofs.CppNoResizeScope.Allowed command = true)
    (contexts : ∀ owner scope, (Proofs.CppMoveContext.project s ty).frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : Proofs.CppNestedProgram.runFuel fuel command (Proofs.CppMoveContext.project s ty) = .finished out)
    (covered : OwnsAll s.objects.heap) (valid : out.state.frame.state.wellFormed = true) :
    ∃ objects, restore s.objects ty out.state.frame = some objects := by
  have effects := Proofs.CppNoResizeRun.run_headers fuel command (Proofs.CppMoveContext.project s ty) out allowed contexts actual
  exact restore_of_sameHeaders s.objects ty out.state.frame effects.headers effects.flags covered valid



-- Completed non-resizing calls restore the caller metadata. The actual scalar
-- cells, allocation payloads and resource counters all come from the result.
def restoreContext (s : Proofs.CppMoveContext.Context) (ty : Ty) (after : Proofs.CppNestedProgram.NState) :
    Option Proofs.CppMoveContext.Context := do
  if after.slots = (Proofs.CppMoveContext.project s ty).slots ∧ after.scope = s.scope ∧
      after.frame.bindings = (Proofs.CppMoveContext.project s ty).frame.bindings ∧
      after.scalars.bindings = s.scalars.bindings ∧ after.scalars.memory.length = s.scalars.memory.length ∧
      after.scalars.baseMemory = s.scalars.baseMemory then
    let objects ← restore s.objects ty after.frame
    some {s with objects := objects,scalars := after.scalars,peak := after.peak}
  else none

theorem restoreContext_metadata (s out : Proofs.CppMoveContext.Context) (ty : Ty)
    (after : Proofs.CppNestedProgram.NState) (run : restoreContext s ty after = some out) :
    out.scalars = after.scalars ∧ out.peak = after.peak ∧ out.slots = s.slots ∧ out.scope = s.scope ∧
      out.objects.heap.headers = s.objects.heap.headers ∧ out.objects.heap.grants = s.objects.heap.grants ∧
      Proofs.CppMoveContext.work out = after.work := by
  unfold restoreContext at run
  split at run
  · obtain ⟨objects,restored,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj done
    subst out
    have metadata := restore_metadata s.objects objects ty after.frame restored
    refine ⟨rfl,rfl,rfl,rfl,metadata.1,metadata.2.1,?_⟩
    change after.scalars.work+objects.heap.work = after.work
    rw [metadata.2.2.2.2.1]
    rfl
  · simp at run



theorem restore_allocation (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (owner : Nat) (old : Proofs.CppVectorCopyAssign.Tracked Int)
    (found : s.heap.allocation owner = some old) :
    ∃ actual, out.heap.allocation owner = some actual ∧ after.state.storage.lookup owner = some (box actual.buffer) ∧
      signature (box actual.buffer) = signature (box old.buffer) ∧ actual.buffer.owner = owner ∧
      actual.buffer.Valid ty.valid ∧ actual.generation = old.generation := by
  unfold restore at run
  split at run
  · obtain ⟨allocations,entriesRun,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj done
    subst out
    obtain ⟨entry,slot,entryRun⟩ := restoreEntries_lookup after.state.storage ty 0 s.heap.allocations allocations
      entriesRun owner (some old) (allocation_slot s.heap owner old found)
    simp only [Nat.zero_add] at entryRun
    cases entry with
    | none =>
      have presence := restoreEntry_presence after.state.storage ty owner (some old) none entryRun
      contradiction
    | some actual =>
      have facts := restoreEntry_success after.state.storage ty owner old actual entryRun
      exact ⟨actual,by simp [Heap.allocation,slot],facts⟩
  · simp at run

theorem restore_dead (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (owner : Nat) (dead : s.heap.allocation owner = none) :
    out.heap.allocation owner = none := by
  unfold restore at run
  split at run
  · obtain ⟨allocations,entriesRun,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj done
    subst out
    cases slot : s.heap.allocations[owner]? with
    | none =>
      have outside := List.getElem?_eq_none_iff.mp slot
      have lengths := restoreEntries_length after.state.storage ty 0 s.heap.allocations allocations entriesRun
      have nextSlot : allocations[owner]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      simp [Heap.allocation,nextSlot]
    | some entry =>
      cases entry with
      | some old => simp [Heap.allocation,slot] at dead
      | none =>
        obtain ⟨entry,nextSlot,entryRun⟩ := restoreEntries_lookup after.state.storage ty 0 s.heap.allocations allocations
          entriesRun owner none slot
        have entryEq := Option.some.inj entryRun
        change none = entry at entryEq
        subst entry
        simp [Heap.allocation,nextSlot]
  · simp at run

theorem restore_allocationsValid (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) : AllocationsValid out.heap ty := by
  intro owner actual found
  cases previous : s.heap.allocation owner with
  | none => rw [restore_dead s out ty after run owner previous] at found; contradiction
  | some old =>
    obtain ⟨next,nextFound,_,_,owns,valid,_⟩ := restore_allocation s out ty after run owner old previous
    have eq := Option.some.inj (nextFound.symm.trans found)
    subst actual
    exact ⟨owns,valid⟩

theorem restore_unique (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (unique : Unique s.heap) : Unique out.heap := by
  have headers := (restore_metadata s out ty after run).1
  intro a b ha hb owner aFound bFound aOwns bOwns
  have first : s.heap.header a = some ha := by simpa [Heap.header,headers] using aFound
  have second : s.heap.header b = some hb := by simpa [Heap.header,headers] using bFound
  exact unique a b ha hb owner first second aOwns bOwns

theorem restore_ownsAll (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (covered : OwnsAll s.heap) : OwnsAll out.heap := by
  have headers := (restore_metadata s out ty after run).1
  intro owner actual found
  cases previous : s.heap.allocation owner with
  | none => rw [restore_dead s out ty after run owner previous] at found; contradiction
  | some old =>
    obtain ⟨id,header,headerFound,owns⟩ := covered owner old previous
    exact ⟨id,header,by simpa [Heap.header,headers] using headerFound,owns⟩

theorem restore_headersLive (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (live : Proofs.CppMoveSpace.HeadersLive s.heap) :
    Proofs.CppMoveSpace.HeadersLive out.heap := by
  have headers := (restore_metadata s out ty after run).1
  intro id header owner found owns
  have oldHeader : s.heap.header id = some header := by simpa [Heap.header,headers] using found
  have oldLive := live id header owner oldHeader owns
  cases oldFound : s.heap.allocation owner with
  | none => simp [oldFound] at oldLive
  | some old =>
    obtain ⟨actual,actualFound,_⟩ := restore_allocation s out ty after run owner old oldFound
    simp [actualFound]

theorem restore_grantBounds (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (bounds : GrantBounds s.heap) : GrantBounds out.heap := by
  have metadata := restore_metadata s out ty after run
  exact grantBounds_metadata s.heap out.heap bounds metadata.2.1 metadata.2.2.2.1



theorem restoreEntry_capacity (store : Store Value) (ty : Ty) (owner : Nat)
    (old next : Option (Proofs.CppVectorCopyAssign.Tracked Int))
    (run : restoreEntry store ty owner old = some next) :
    Proofs.CppMoveAssign.capacity next = Proofs.CppMoveAssign.capacity old := by
  cases old with
  | none => cases Option.some.inj run; rfl
  | some old =>
    cases next with
    | none =>
      have presence := restoreEntry_presence store ty owner (some old) none run
      contradiction
    | some next =>
      have same := (restoreEntry_success store ty owner old next run).2.1
      exact congrArg Signature.capacity same

theorem restoreEntries_capacity (store : Store Value) (ty : Ty) (start : Nat)
    (entries next : List (Option (Proofs.CppVectorCopyAssign.Tracked Int)))
    (run : restoreEntries store ty start entries = some next) :
    (next.map Proofs.CppMoveAssign.capacity).sum = (entries.map Proofs.CppMoveAssign.capacity).sum := by
  induction entries generalizing start next with
  | nil => cases Option.some.inj run; rfl
  | cons head tail ih =>
    simp only [restoreEntries] at run
    obtain ⟨actual,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    obtain ⟨remaining,tailRun,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    have eq := Option.some.inj done
    rw [← eq,List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,
      restoreEntry_capacity store ty start head actual first,ih (start+1) remaining tailRun]

theorem restore_liveSpace (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) : out.heap.liveSpace = s.heap.liveSpace := by
  unfold restore at run
  split at run
  · obtain ⟨allocations,entriesRun,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj done
    subst out
    have capacity := restoreEntries_capacity after.state.storage ty 0 s.heap.allocations allocations entriesRun
    change s.heap.headers.countP (·.isSome)+(allocations.map Proofs.CppMoveAssign.capacity).sum =
      s.heap.headers.countP (·.isSome)+(s.heap.allocations.map Proofs.CppMoveAssign.capacity).sum
    rw [capacity]
  · simp at run

theorem restore_baseSpace (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) : out.heap.baseSpace = s.heap.baseSpace := by
  have metadata := restore_metadata s out ty after run
  have same := congrArg Shape.base metadata.2.2.2.2.2.2.2
  exact metadata.2.2.2.2.2.2.1.trans same



theorem readRef_none (old next : Buffer Int) (ty : Ty) (reference : ElementRef)
    (same : signature (box next) = signature (box old))
    (oldValid : old.Valid ty.valid) (nextValid : next.Valid ty.valid)
    (dead : CppVector.readRef old ty.valid reference = none) :
    CppVector.readRef next ty.valid reference = none := by
  have owner := congrArg Signature.owner same
  have epoch := congrArg Signature.epoch same
  have size : next.items.length = old.items.length := by
    have lengths := congrArg Signature.size same
    simpa only [signature,box,List.length_map] using lengths
  change next.owner = old.owner at owner
  change next.epoch = old.epoch at epoch
  unfold CppVector.readRef at dead ⊢
  simp only [oldValid,nextValid,true_and,owner,epoch] at dead ⊢
  split at dead
  next allowed =>
    rw [ite_eq_left allowed]
    have oldMissing : old.items[reference.index]? = none := by
      cases found : old.items[reference.index]? with
      | none => rfl
      | some value => simp [found] at dead
    have nextMissing : next.items[reference.index]? = none :=
      List.getElem?_eq_none_iff.mpr (by rw [size]; exact List.getElem?_eq_none_iff.mp oldMissing)
    simp [nextMissing]
  next forbidden => simp [forbidden]

theorem tracked_read_none (old next : Proofs.CppVectorCopyAssign.Tracked Int) (ty : Ty)
    (reference : Proofs.CppVectorCopyAssign.Reference)
    (same : signature (box next.buffer) = signature (box old.buffer)) (generation : next.generation = old.generation)
    (oldValid : old.buffer.Valid ty.valid) (nextValid : next.buffer.Valid ty.valid)
    (dead : Proofs.CppVectorCopyAssign.read old ty.valid reference = none) :
    Proofs.CppVectorCopyAssign.read next ty.valid reference = none := by
  unfold Proofs.CppVectorCopyAssign.read at dead ⊢
  rw [generation]
  by_cases alive : reference.generation = old.generation reference.element.index
  · simp only [alive,ite_true] at dead ⊢
    exact readRef_none old.buffer next.buffer ty reference.element same oldValid nextValid dead
  · simp [alive]

theorem restore_no_resurrection (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (valid : AllocationsValid s.heap ty) (reference : Nat)
    (dead : Proofs.CppMoveHeaders.read s.heap ty.valid reference = none) :
    Proofs.CppMoveHeaders.read out.heap ty.valid reference = none := by
  have grants := (restore_metadata s out ty after run).2.1
  cases grantFound : s.heap.grants[reference]? with
  | none => simp [Proofs.CppMoveHeaders.read,grants,grantFound]
  | some grant =>
    cases found : s.heap.allocation grant.reference.element.owner with
    | none =>
      have missing := restore_dead s out ty after run grant.reference.element.owner found
      simp [Proofs.CppMoveHeaders.read,grants,grantFound,missing]
    | some old =>
      obtain ⟨next,nextFound,_,same,_,nextValid,generation⟩ :=
        restore_allocation s out ty after run grant.reference.element.owner old found
      have oldRead : Proofs.CppVectorCopyAssign.read old ty.valid grant.reference = none := by
        cases previous : Proofs.CppVectorCopyAssign.read old ty.valid grant.reference with
        | none => rfl
        | some value => simp [Proofs.CppMoveHeaders.read,grantFound,found,previous] at dead
      have nextRead := tracked_read_none old next ty grant.reference same generation (valid _ _ found).2 nextValid oldRead
      simp [Proofs.CppMoveHeaders.read,grants,grantFound,nextFound,nextRead]



theorem restoreContext_ready (s : Proofs.CppMoveContext.Context) (ty : Ty) (after : Proofs.CppNestedProgram.NState)
    (slots : after.slots = (Proofs.CppMoveContext.project s ty).slots) (scope : after.scope = s.scope)
    (bindings : after.frame.bindings = (Proofs.CppMoveContext.project s ty).frame.bindings)
    (scalars : after.scalars.bindings = s.scalars.bindings)
    (memory : after.scalars.memory.length = s.scalars.memory.length) (base : after.scalars.baseMemory = s.scalars.baseMemory)
    (same : SameHeaders (materialize s.objects ty).frame.state after.frame.state)
    (maximum : after.frame.rootWritable = (materialize s.objects ty).frame.rootWritable)
    (covered : OwnsAll s.objects.heap) (valid : after.frame.state.wellFormed = true) :
    ∃ out, restoreContext s ty after = some out := by
  obtain ⟨objects,run⟩ := restore_of_sameHeaders s.objects ty after.frame same maximum covered valid
  exact ⟨{s with objects := objects,scalars := after.scalars,peak := after.peak},
    by simp [restoreContext,slots,scope,bindings,scalars,memory,base,run]⟩



theorem sameHeaders_of_shape (before after : Frame) (same : shape after = shape before) :
    SameHeaders before.state after.state ∧ after.rootWritable = before.rootWritable := by
  have count : after.state.storage.objects.length = before.state.storage.objects.length := by
    have lengths := congrArg (fun s : Shape => s.buffers.length) same
    simpa only [shape,List.length_map,List.length_range] using lengths
  refine ⟨⟨congrArg Shape.forest same,count,congrArg Shape.base same,?_⟩,congrArg Shape.maximum same⟩
  intro owner
  by_cases inside : owner < before.state.storage.objects.length
  · have afterInside : owner < after.state.storage.objects.length := by rw [count]; exact inside
    have a := List.getElem?_range afterInside
    have b := List.getElem?_range inside
    have slot := congrArg (fun s : Shape => s.buffers[owner]?) same
    simp only [shape,List.getElem?_map,a,b,Option.map_some] at slot
    exact Option.some.inj slot
  · have oldDead := lookup_past_end before.state.storage owner (Nat.le_of_not_gt inside)
    have nextDead := lookup_past_end after.state.storage owner (by rw [count]; exact Nat.le_of_not_gt inside)
    simp [oldDead,nextDead]

theorem restore_ownerHeader (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (owner : Nat) : ownerHeader out.heap owner = ownerHeader s.heap owner := by
  unfold ownerHeader
  rw [(restore_metadata s out ty after run).1]

theorem restore_viewBinding (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (view : Proofs.CppMoveViews.View) :
    viewBinding out ty view = viewBinding s ty view := by
  have metadata := restore_metadata s out ty after run
  simp [viewBinding,Heap.header,metadata.1,metadata.2.2.2.1]

theorem restore_bindings (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) : (materialize out ty).frame.bindings = (materialize s ty).frame.bindings := by
  have metadata := restore_metadata s out ty after run
  simp only [materialize,metadata.2.1,metadata.2.2.1]
  congr 1
  exact List.map_congr_left (fun view _ => restore_viewBinding s out ty after run view)

theorem entries_dead (s : Heap Int) (ty : Ty) (owner : Nat) (inside : owner < s.allocations.length)
    (dead : s.allocation owner = none) : (entries s ty)[owner]? = some none := by
  have slot : s.allocations[owner]? = some none := by
    cases found : s.allocations[owner]? with
    | none => have outside := List.getElem?_eq_none_iff.mp found; omega
    | some entry =>
      cases entry with
      | none => rfl
      | some old => simp [Heap.allocation,found] at dead
  unfold entries
  rw [List.getElem?_append_left (by simpa using inside)]
  simp [List.getElem?_mapIdx,slot]

theorem materialize_dead (s : Proofs.CppMoveViews.State Int) (ty : Ty) (owner : Nat)
    (inside : owner < s.heap.allocations.length) (dead : s.heap.allocation owner = none) :
    (materialize s ty).frame.state.storage.lookup owner = none := by
  have slot := entries_dead s.heap ty owner inside dead
  simp [materialize,Store.lookup,List.getElem?_map,slot]

theorem restore_materialize_allocation (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (covered : OwnsAll s.heap) (owner : Nat)
    (inside : owner < s.heap.allocations.length) :
    (materialize out ty).frame.state.storage.lookup owner = after.state.storage.lookup owner := by
  have metadata := restore_metadata s out ty after run
  have same := (sameHeaders_of_shape (materialize s ty).frame after metadata.2.2.2.2.2.2.2).1
  cases previous : s.heap.allocation owner with
  | none =>
    have missing := restore_dead s out ty after run owner previous
    have nextInside : owner < out.heap.allocations.length := by rw [metadata.2.2.2.1]; exact inside
    rw [materialize_dead out ty owner nextInside missing]
    have beforeDead := materialize_dead s ty owner inside previous
    have signatures := same.buffers owner
    rw [beforeDead] at signatures
    cases actual : after.state.storage.lookup owner with
    | none => rfl
    | some value => simp [actual] at signatures
  | some old =>
    obtain ⟨actual,found,lookup,_,_,_,_⟩ := restore_allocation s out ty after run owner old previous
    obtain ⟨header,headerFound⟩ := ownerHeader_exists s.heap owner old covered previous
    have nextHeader : ownerHeader out.heap owner = some header := by rw [restore_ownerHeader s out ty after run owner]; exact headerFound
    have projected := materialize_entry out ty owner (box actual.buffer) ⟨.integer ty,none,some header.scope,[]⟩
      (entries_allocation out.heap ty owner actual header found nextHeader)
    exact projected.1.trans lookup.symm



theorem restore_generations (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) : (materialize out ty).generation = (materialize s ty).generation := by
  funext owner index
  change ((out.heap.allocation owner).map (fun t => t.generation index)).getD 0 =
    ((s.heap.allocation owner).map (fun t => t.generation index)).getD 0
  cases previous : s.heap.allocation owner with
  | none =>
    have missing := restore_dead s out ty after run owner previous
    simp [missing]
  | some old =>
    obtain ⟨actual,found,_,_,_,_,generation⟩ := restore_allocation s out ty after run owner old previous
    simp [found,generation]



theorem entries_tail (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (owner : Nat) (outside : s.heap.allocations.length ≤ owner) :
    (entries out.heap ty)[owner]? = (entries s.heap ty)[owner]? := by
  have metadata := restore_metadata s out ty after run
  unfold entries
  rw [List.getElem?_append_right (by simpa only [List.length_mapIdx,metadata.2.2.2.1] using outside),
    List.getElem?_append_right (by simpa only [List.length_mapIdx] using outside)]
  simp only [List.length_mapIdx,metadata.1,metadata.2.2.2.1]

theorem entries_tail_empty (s : Heap Int) (ty : Ty) (owner : Nat)
    (outside : s.allocations.length ≤ owner) (buffer : Buffer Value) (tag : Tag)
    (found : (entries s ty)[owner]? = some (some (buffer,tag))) : buffer.items = [] := by
  unfold entries at found
  rw [List.getElem?_append_right (by simpa only [List.length_mapIdx] using outside)] at found
  simp only [List.length_mapIdx,List.getElem?_mapIdx] at found
  cases slot : s.headers[owner-s.allocations.length]? with
  | none => simp [slot] at found
  | some entry =>
    cases entry with
    | none => simp [slot] at found
    | some header =>
      simp only [slot,Option.map_some,Bind.bind,Option.bind] at found
      split at found
      · have pair := Prod.mk.inj (Option.some.inj (Option.some.inj found))
        rcases pair with ⟨bufferEq,_⟩
        subst buffer
        rfl
      · simp at found

theorem materialize_buffer_entry (s : Proofs.CppMoveViews.State Int) (ty : Ty) (owner : Nat) (buffer : Buffer Value)
    (found : (materialize s ty).frame.state.storage.lookup owner = some buffer) :
    ∃ tag, (entries s.heap ty)[owner]? = some (some (buffer,tag)) := by
  simp only [materialize,Store.lookup,List.getElem?_map] at found
  cases slot : (entries s.heap ty)[owner]? with
  | none => simp [slot] at found
  | some entry =>
    cases entry with
    | none => simp [slot] at found
    | some pair =>
      rcases pair with ⟨actual,tag⟩
      simp only [slot,Option.map_some,Option.join_some,Option.some.injEq] at found
      subst buffer
      exact ⟨tag,rfl⟩

theorem signature_empty (actual old : Buffer Value) (same : signature actual = signature old)
    (empty : old.items = []) : actual = old := by
  cases actual with
  | mk owner items capacity limit epoch =>
    cases old with
    | mk oldOwner oldItems oldCapacity oldLimit oldEpoch =>
      simp only [signature,Signature.mk.injEq] at same
      obtain ⟨rfl,rfl,rfl,rfl,size⟩ := same
      dsimp only at empty size
      subst oldItems
      have nil : items = [] := List.length_eq_zero_iff.mp size
      subst items
      rfl

theorem restore_materialize_tail (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (owner : Nat) (outside : s.heap.allocations.length ≤ owner) :
    (materialize out ty).frame.state.storage.lookup owner = after.state.storage.lookup owner := by
  have metadata := restore_metadata s out ty after run
  have same := (sameHeaders_of_shape (materialize s ty).frame after metadata.2.2.2.2.2.2.2).1
  have original : (materialize out ty).frame.state.storage.lookup owner = (materialize s ty).frame.state.storage.lookup owner := by
    simp only [materialize,Store.lookup,List.getElem?_map]
    rw [entries_tail s out ty after run owner outside]
  rw [original]
  have signatures := same.buffers owner
  cases oldFound : (materialize s ty).frame.state.storage.lookup owner with
  | none =>
    rw [oldFound] at signatures
    cases nextFound : after.state.storage.lookup owner with
    | none => rfl
    | some value => simp [nextFound] at signatures
  | some old =>
    obtain ⟨tag,entry⟩ := materialize_buffer_entry s ty owner old oldFound
    have empty := entries_tail_empty s.heap ty owner outside old tag entry
    rw [oldFound] at signatures
    cases nextFound : after.state.storage.lookup owner with
    | none => simp [nextFound] at signatures
    | some actual =>
      simp only [nextFound,Option.map_some,Option.some.injEq] at signatures
      rw [signature_empty actual old signatures empty]

theorem option_list_ext {α : Type} (before after : List (Option α))
    (count : after.length = before.length)
    (lookup : ∀ owner : Nat, (after[owner]?).join = (before[owner]?).join) : after = before := by
  apply List.ext_getElem?
  intro owner
  by_cases inside : owner < before.length
  · have afterInside : owner < after.length := by rw [count]; exact inside
    have a : after[owner]? = some (after[owner]'afterInside) := List.getElem?_eq_some_iff.mpr ⟨afterInside,rfl⟩
    have b : before[owner]? = some (before[owner]'inside) := List.getElem?_eq_some_iff.mpr ⟨inside,rfl⟩
    have same := lookup owner
    rw [a,b] at same
    change after[owner]'afterInside = before[owner]'inside at same
    rw [a,b,same]
  · have beforeDead : before[owner]? = none := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt inside)
    have afterDead : after[owner]? = none := List.getElem?_eq_none_iff.mpr (by rw [count]; exact Nat.le_of_not_gt inside)
    rw [beforeDead,afterDead]



theorem restore_materialize_lookup (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (covered : OwnsAll s.heap) (owner : Nat) :
    (materialize out ty).frame.state.storage.lookup owner = after.state.storage.lookup owner := by
  by_cases inside : owner < s.heap.allocations.length
  · exact restore_materialize_allocation s out ty after run covered owner inside
  · exact restore_materialize_tail s out ty after run owner (Nat.le_of_not_gt inside)

theorem restore_storage (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (covered : OwnsAll s.heap) :
    (materialize out ty).frame.state.storage = after.state.storage := by
  have metadata := restore_metadata s out ty after run
  have same := (sameHeaders_of_shape (materialize s ty).frame after metadata.2.2.2.2.2.2.2).1
  have lengths : (materialize out ty).frame.state.storage.objects.length = (materialize s ty).frame.state.storage.objects.length := by
    simp [materialize,entries,metadata.1,metadata.2.2.2.1]
  have count := lengths.trans same.count.symm
  have objects := option_list_ext after.state.storage.objects (materialize out ty).frame.state.storage.objects count
    (fun owner => restore_materialize_lookup s out ty after run covered owner)
  change (⟨(materialize out ty).frame.state.storage.objects,out.heap.work,out.heap.peak,out.heap.baseSpace⟩ : Store Value) =
    ⟨after.state.storage.objects,after.state.storage.work,after.state.storage.peak,after.state.storage.baseSpace⟩
  rw [objects,metadata.2.2.2.2.1,metadata.2.2.2.2.2.1,metadata.2.2.2.2.2.2.1]

theorem materialize_forest_dead (s : Proofs.CppMoveViews.State Int) (ty : Ty) (owner : Nat)
    (inside : owner < s.heap.allocations.length) (dead : s.heap.allocation owner = none) :
    (materialize s ty).frame.state.forest.lookup owner = none := by
  have slot := entries_dead s.heap ty owner inside dead
  simp [materialize,Forest.lookup,List.getElem?_map,slot]

theorem restore_forest_lookup (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (covered : OwnsAll s.heap) (owner : Nat) :
    (materialize out ty).frame.state.forest.lookup owner = (materialize s ty).frame.state.forest.lookup owner := by
  have metadata := restore_metadata s out ty after run
  by_cases inside : owner < s.heap.allocations.length
  · cases previous : s.heap.allocation owner with
    | none =>
      have missing := restore_dead s out ty after run owner previous
      have nextInside : owner < out.heap.allocations.length := by rw [metadata.2.2.2.1]; exact inside
      rw [materialize_forest_dead out ty owner nextInside missing,materialize_forest_dead s ty owner inside previous]
    | some old =>
      obtain ⟨actual,found,_,_,_,_,_⟩ := restore_allocation s out ty after run owner old previous
      obtain ⟨header,headerFound⟩ := ownerHeader_exists s.heap owner old covered previous
      have nextHeader : ownerHeader out.heap owner = some header := by rw [restore_ownerHeader s out ty after run owner]; exact headerFound
      have next := materialize_entry out ty owner (box actual.buffer) ⟨.integer ty,none,some header.scope,[]⟩
        (entries_allocation out.heap ty owner actual header found nextHeader)
      have oldEntry := materialize_entry s ty owner (box old.buffer) ⟨.integer ty,none,some header.scope,[]⟩
        (entries_allocation s.heap ty owner old header previous headerFound)
      exact next.2.trans oldEntry.2.symm
  · simp only [materialize,Forest.lookup,List.getElem?_map]
    rw [entries_tail s out ty after run owner (Nat.le_of_not_gt inside)]

theorem restore_forest (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (covered : OwnsAll s.heap) :
    (materialize out ty).frame.state.forest = (materialize s ty).frame.state.forest := by
  have metadata := restore_metadata s out ty after run
  have count : (materialize out ty).frame.state.forest.objects.length = (materialize s ty).frame.state.forest.objects.length := by
    simp [materialize,entries,metadata.1,metadata.2.2.2.1]
  have objects := option_list_ext (materialize s ty).frame.state.forest.objects (materialize out ty).frame.state.forest.objects count
    (fun owner => restore_forest_lookup s out ty after run covered owner)
  exact congrArg Forest.mk objects

theorem restore_state (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (covered : OwnsAll s.heap) :
    (materialize out ty).frame.state = after.state := by
  have metadata := restore_metadata s out ty after run
  have same := (sameHeaders_of_shape (materialize s ty).frame after metadata.2.2.2.2.2.2.2).1
  have forest := (restore_forest s out ty after run covered).trans same.forest.symm
  have storage := restore_storage s out ty after run covered
  change (⟨(materialize out ty).frame.state.forest,(materialize out ty).frame.state.storage⟩ : Proofs.CppNestedVectorStore.State) =
    ⟨after.state.forest,after.state.storage⟩
  rw [forest,storage]

theorem restore_frame (s out : Proofs.CppMoveViews.State Int) (ty : Ty) (after : Frame)
    (run : restore s ty after = some out) (covered : OwnsAll s.heap)
    (bindings : after.bindings = (materialize s ty).frame.bindings) : (materialize out ty).frame = after := by
  have metadata := restore_metadata s out ty after run
  have same := sameHeaders_of_shape (materialize s ty).frame after metadata.2.2.2.2.2.2.2
  have maximum : (materialize out ty).frame.rootWritable = (materialize s ty).frame.rootWritable := by
    simp [materialize,entries,metadata.1,metadata.2.2.2.1]
  have flags := maximum.trans same.2.symm
  have slots := (restore_bindings s out ty after run).trans bindings.symm
  change (⟨(materialize out ty).frame.state,(materialize out ty).frame.rootWritable,(materialize out ty).frame.bindings⟩ : Frame) =
    ⟨after.state,after.rootWritable,after.bindings⟩
  rw [restore_state s out ty after run covered,flags,slots]

theorem restoreContext_project (s out : Proofs.CppMoveContext.Context) (ty : Ty) (after : Proofs.CppNestedProgram.NState)
    (run : restoreContext s ty after = some out) (covered : OwnsAll s.objects.heap) :
    Proofs.CppMoveContext.project out ty = after := by
  unfold restoreContext at run
  split at run
  next guard =>
    obtain ⟨objects,restored,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    have eq := Option.some.inj done
    subst out
    have metadata := restore_metadata s.objects objects ty after.frame restored
    have frame := restore_frame s.objects objects ty after.frame restored covered guard.2.2.1
    have slots : s.slots.map (Proofs.CppMoveContext.location objects.heap.grants.length) = after.slots := by
      rw [metadata.2.1]
      exact guard.1.symm
    change (⟨after.scalars,(materialize objects ty).frame,s.slots.map (Proofs.CppMoveContext.location objects.heap.grants.length),s.scope,after.peak⟩ : Proofs.CppNestedProgram.NState) =
      ⟨after.scalars,after.frame,after.slots,after.scope,after.peak⟩
    rw [frame,slots,guard.2.1]
  next => simp at run


end Proofs.CppMoveRestore
