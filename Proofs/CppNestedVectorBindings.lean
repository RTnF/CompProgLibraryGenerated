import Proofs.CppNestedVectorStore
import Proofs.StlContracts

namespace Proofs.CppNestedVectorBindings
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore

inductive Header where
  | root (scope : Nat)
  | child (address : ElementRef)
deriving DecidableEq, Repr

structure Binding where
  owner : Nat
  element : Element
  writable : Bool
  header : Header
deriving DecidableEq, Repr

structure Reference where
  slot : Nat
  element : Ty
  writable : Bool
  address : ElementRef
deriving DecidableEq, Repr

-- Binding slots are immutable grants and are never recycled. Reading a
-- captured integer reference uses its grant, NOT the lifetime of the header
-- through which it was acquired. Outer reserve may move that header while
-- the integer allocation and the captured integer reference remain alive.
structure Frame where
  state : State
  rootWritable : List Bool
  bindings : List Binding := []
deriving DecidableEq, Repr

def Frame.object (f : Frame) (owner : Nat) (expected : Element) : Option (Buffer Value × Tag) := do
  if f.state.wellFormed then
    let buffer ← f.state.storage.lookup owner
    let tag ← f.state.forest.lookup owner
    if tag.element = expected then some (buffer,tag) else none
  else none

def Frame.maximum (f : Frame) (owner : Nat) : Option Bool := do
  if f.rootWritable.length = f.state.forest.objects.length then
    let root ← f.state.forest.rootOwner owner
    f.rootWritable[root]?
  else none

def Frame.headerOwner (f : Frame) (binding : Binding) : Option Nat := do
  match binding.header with
  | .root scope =>
    let (_,tag) ← f.object binding.owner binding.element
    if tag.parent = none ∧ tag.scope = some scope then some binding.owner else none
  | .child address =>
    let (parent,_) ← f.object address.owner (.vector binding.element)
    let result ← readRef parent (accepts (.vector binding.element)) address
    match result.value with
    | .child owner => some owner
    | .integer _ => none

def Frame.resolve (f : Frame) (slot : Nat) (expected : Element) : Option (Binding × Buffer Value) := do
  let binding ← f.bindings[slot]?
  let owner ← f.headerOwner binding
  let (buffer,_) ← f.object owner expected
  let maximum ← f.maximum owner
  if binding.owner = owner ∧ binding.element = expected ∧
      (binding.writable = true → maximum = true) then some (binding,buffer) else none

def Frame.addBinding (f : Frame) (binding : Binding) : Frame × Nat :=
  ({f with bindings := f.bindings ++ [binding]},f.bindings.length)

-- Root bindings apply only while the root object has not been moved.
-- Logical State.transfer is not a C++ move / source-header lifetime adapter.
def Frame.bindRoot (f : Frame) (owner : Nat) (expected : Element) (scope : Nat)
    (writable : Bool) : Option (Frame × Nat) := do
  let (_,tag) ← f.object owner expected
  let maximum ← f.maximum owner
  if tag.parent = none ∧ tag.scope = some scope ∧ (writable = true → maximum = true) then
    some (f.addBinding ⟨owner,expected,writable,.root scope⟩)
  else none

def Frame.bindChild (f : Frame) (slot : Nat) (expected : Element) (index : Int)
    (writable : Bool) : Option (Frame × Nat) := do
  let (origin,parent) ← f.resolve slot (.vector expected)
  if writable = true → origin.writable = true then
    let address ← CppVector.elementRef parent (accepts (.vector expected)) index
    let result ← readRef parent (accepts (.vector expected)) address
    match result.value with
    | .child owner =>
      let (_,tag) ← f.object owner expected
      if tag.parent = some origin.owner then
        some (f.addBinding ⟨owner,expected,writable,.child address⟩)
      else none
    | .integer _ => none
  else none

def Frame.elementRef (f : Frame) (slot : Nat) (expected : Ty) (index : Int) : Option Reference := do
  let (binding,buffer) ← f.resolve slot (.integer expected)
  let address ← CppVector.elementRef buffer (accepts (.integer expected)) index
  some ⟨slot,expected,binding.writable,address⟩

-- This validates the immutable grant without dereferencing the saved header.
def Frame.grant (f : Frame) (reference : Reference) : Option Bool := do
  let binding ← f.bindings[reference.slot]?
  let maximum ← f.maximum binding.owner
  if binding.owner = reference.address.owner ∧ binding.element = .integer reference.element ∧
      (reference.writable = true → binding.writable = true) ∧
      (binding.writable = true → maximum = true) then some binding.writable else none

def Frame.read (f : Frame) (reference : Reference) : Option Int := do
  let _ ← f.grant reference
  let (buffer,_) ← f.object reference.address.owner (.integer reference.element)
  let result ← readRef buffer (accepts (.integer reference.element)) reference.address
  match result.value with | .integer value => some value | .child _ => none

-- Commit uses the NESTED live-space baseline. The flat Store.liveSpace
-- counts child headers again and must not be used for this accounting.
def Frame.updated (f : Frame) (owner : Nat) (old : Buffer Value) (result : Result Value Unit) : Frame :=
  {f with state := {f.state with storage := {f.state.storage with
    objects := f.state.storage.objects.set owner (some result.buffer),
    work := f.state.storage.work+result.work,
    peak := max f.state.storage.peak
      (f.state.liveSpace+(result.peak-(old.capacity+1))-f.state.storage.baseSpace)}}}

def Frame.commit (f : Frame) (owner : Nat) (expected : Element)
    (result : Result Value Unit) : Option Frame :=
  match f.object owner expected with
  | none => none
  | some (old,tag) =>
    if result.buffer.owner = owner ∧ payloadOK tag result.buffer ∧
        old.capacity+1 ≤ result.peak ∧ result.buffer.capacity+1 ≤ result.peak then
      let next := f.updated owner old result
      if next.state.wellFormed then some next else none
    else none

def Frame.write (f : Frame) (reference : Reference) (value : Int) : Option Frame := do
  let writable ← f.grant reference
  if reference.writable = true ∧ writable = true then
    let (buffer,_) ← f.object reference.address.owner (.integer reference.element)
    let result ← writeRef buffer (accepts (.integer reference.element)) true reference.address (.integer value)
    f.commit reference.address.owner (.integer reference.element) result
  else none

def Frame.reserve (f : Frame) (slot : Nat) (expected : Element) (requested : Nat) : Option Frame := do
  let (binding,buffer) ← f.resolve slot expected
  let result ← CppVector.reserve buffer (accepts expected) binding.writable requested
  f.commit binding.owner expected result

/-- The integer payload of a buffer element. -/
def Value.intOf : Value → Option Int
  | .integer value => some value
  | .child _ => none

/-- `std::sort(v.begin(), v.end())` on a writable flat integer vector: the contents become the sorted permutation
(the result of the operation is *defined* here; only its cost, `sortComparisons`, is a contract). Iterators and
references stay valid (no reallocation), so the epoch is kept. -/
def sortFlat (b : Buffer Value) (accept : Value → Bool) (writable : Bool) : Option (Result Value Unit) :=
  if b.Valid accept ∧ writable = true then
    match b.items.mapM Value.intOf with
    | some ints =>
        some ⟨{b with items := (ints.mergeSort (fun x y => decide (x ≤ y))).map Value.integer},(),
          Proofs.StlContracts.sortComparisons ints.length + ints.length,b.capacity+2⟩
    | none => none
  else none

def Frame.sortAll (f : Frame) (slot : Nat) (expected : Ty) : Option Frame := do
  let (binding,buffer) ← f.resolve slot (.integer expected)
  let result ← sortFlat buffer (accepts (.integer expected)) binding.writable
  f.commit binding.owner (.integer expected) result

/-- `std::unique` followed by the matching `erase`: adjacent equal elements collapse to the first of each run. -/
def uniqAdjAux : Int → List Int → List Int
  | _, [] => []
  | p, x :: t => if x = p then uniqAdjAux p t else x :: uniqAdjAux x t

def uniqAdj : List Int → List Int
  | [] => []
  | a :: t => a :: uniqAdjAux a t

theorem uniqAdjAux_mem : ∀ (t : List Int) (p x : Int), x ∈ uniqAdjAux p t → x ∈ t
  | [], _, _, h => by simp [uniqAdjAux] at h
  | y :: t, p, x, h => by
    by_cases hy : y = p
    · simp only [uniqAdjAux, hy, if_true] at h
      exact List.mem_cons_of_mem _ (uniqAdjAux_mem t p x h)
    · simp only [uniqAdjAux, hy, if_false, List.mem_cons] at h
      rcases h with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem _ (uniqAdjAux_mem t y x h)

theorem uniqAdjAux_length : ∀ (t : List Int) (p : Int), (uniqAdjAux p t).length ≤ t.length
  | [], _ => by simp [uniqAdjAux]
  | y :: t, p => by
    by_cases hy : y = p
    · simp only [uniqAdjAux, hy, if_true]
      have := uniqAdjAux_length t p
      simp; omega
    · simp only [uniqAdjAux, hy, if_false, List.length_cons]
      have := uniqAdjAux_length t y
      omega

theorem uniqAdj_mem (l : List Int) (x : Int) (h : x ∈ uniqAdj l) : x ∈ l := by
  cases l with
  | nil => simp [uniqAdj] at h
  | cons a t =>
    simp only [uniqAdj, List.mem_cons] at h
    rcases h with h | h
    · simp [h]
    · exact List.mem_cons_of_mem _ (uniqAdjAux_mem t a x h)

theorem uniqAdj_length (l : List Int) : (uniqAdj l).length ≤ l.length := by
  cases l with
  | nil => simp [uniqAdj]
  | cons a t =>
    simp only [uniqAdj, List.length_cons]
    have := uniqAdjAux_length t a
    omega

/-- `v.erase(std::unique(v.begin(), v.end()), v.end())` on a writable flat integer vector. Erasing invalidates
iterators and references from the first erased position on, so the epoch advances. -/
def dedupFlat (b : Buffer Value) (accept : Value → Bool) (writable : Bool) : Option (Result Value Unit) :=
  if b.Valid accept ∧ writable = true then
    match b.items.mapM Value.intOf with
    | some ints => some ⟨{b with items := (uniqAdj ints).map Value.integer, epoch := b.epoch+1},(),
        ints.length + ints.length,b.capacity+2⟩
    | none => none
  else none

def Frame.dedupAll (f : Frame) (slot : Nat) (expected : Ty) : Option Frame := do
  let (binding,buffer) ← f.resolve slot (.integer expected)
  let result ← dedupFlat buffer (accepts (.integer expected)) binding.writable
  f.commit binding.owner (.integer expected) result

theorem object_runs (f : Frame) (owner : Nat) (expected : Element) (buffer : Buffer Value) (tag : Tag)
    (valid : f.state.wellFormed = true) (found : f.state.storage.lookup owner = some buffer)
    (tagFound : f.state.forest.lookup owner = some tag) (type : tag.element = expected) :
    f.object owner expected = some (buffer,tag) := by
  simp [Frame.object,valid,found,tagFound,type]

theorem object_invalid (f : Frame) (owner : Nat) (expected : Element)
    (invalid : f.state.wellFormed = false) : f.object owner expected = none := by
  simp [Frame.object,invalid]

theorem object_dead (f : Frame) (owner : Nat) (expected : Element)
    (dead : f.state.storage.lookup owner = none) : f.object owner expected = none := by
  simp [Frame.object,dead]

theorem header_root_runs (f : Frame) (binding : Binding) (scope : Nat) (buffer : Buffer Value) (tag : Tag)
    (header : binding.header = .root scope) (object : f.object binding.owner binding.element = some (buffer,tag))
    (root : tag.parent = none) (context : tag.scope = some scope) :
    f.headerOwner binding = some binding.owner := by
  simp [Frame.headerOwner,header,object,root,context]

theorem header_child_runs (f : Frame) (binding : Binding) (address : ElementRef)
    (parent : Buffer Value) (tag : Tag) (result : Result Value Value) (owner : Nat)
    (header : binding.header = .child address)
    (object : f.object address.owner (.vector binding.element) = some (parent,tag))
    (read : readRef parent (accepts (.vector binding.element)) address = some result)
    (child : result.value = .child owner) : f.headerOwner binding = some owner := by
  simp [Frame.headerOwner,header,object,read,child]

theorem header_child_stale (f : Frame) (binding : Binding) (address : ElementRef)
    (parent : Buffer Value) (tag : Tag) (header : binding.header = .child address)
    (object : f.object address.owner (.vector binding.element) = some (parent,tag))
    (stale : address.epoch ≠ parent.epoch) : f.headerOwner binding = none := by
  simp [Frame.headerOwner,header,object,readRef_stale parent _ address stale]

theorem bindChild_readonly (f : Frame) (slot : Nat) (expected : Element) (index : Int)
    (binding : Binding) (parent : Buffer Value)
    (resolved : f.resolve slot (.vector expected) = some (binding,parent))
    (readonly : binding.writable = false) : f.bindChild slot expected index true = none := by
  simp [Frame.bindChild,resolved,readonly]

theorem elementRef_runs (f : Frame) (slot : Nat) (expected : Ty) (index : Int)
    (binding : Binding) (buffer : Buffer Value) (address : ElementRef)
    (resolved : f.resolve slot (.integer expected) = some (binding,buffer))
    (captured : CppVector.elementRef buffer (accepts (.integer expected)) index = some address) :
    f.elementRef slot expected index = some ⟨slot,expected,binding.writable,address⟩ := by
  simp [Frame.elementRef,resolved,captured]

theorem grant_runs (f : Frame) (reference : Reference) (binding : Binding)
    (found : f.bindings[reference.slot]? = some binding) (owner : binding.owner = reference.address.owner)
    (type : binding.element = .integer reference.element)
    (permission : reference.writable = true → binding.writable = true) (maximum : Bool)
    (maxFound : f.maximum binding.owner = some maximum)
    (cap : binding.writable = true → maximum = true) :
    f.grant reference = some binding.writable := by
  simp only [Frame.grant,found,Bind.bind,Option.bind]
  simp only [maxFound]
  simp [owner,type]
  exact ⟨permission,cap⟩

theorem grant_wrong_owner (f : Frame) (reference : Reference) (binding : Binding)
    (found : f.bindings[reference.slot]? = some binding) (wrong : binding.owner ≠ reference.address.owner) :
    f.grant reference = none := by simp [Frame.grant,found,wrong]

theorem grant_wrong_type (f : Frame) (reference : Reference) (binding : Binding)
    (found : f.bindings[reference.slot]? = some binding) (wrong : binding.element ≠ .integer reference.element) :
    f.grant reference = none := by simp [Frame.grant,found,wrong]

theorem grant_no_escalation (f : Frame) (reference : Reference) (binding : Binding)
    (found : f.bindings[reference.slot]? = some binding) (readonly : binding.writable = false)
    (forged : reference.writable = true) : f.grant reference = none := by
  simp [Frame.grant,found,readonly,forged]

theorem read_runs (f : Frame) (reference : Reference) (binding : Binding) (buffer : Buffer Value) (tag : Tag)
    (result : Result Value Value) (value : Int) (grant : f.grant reference = some binding.writable)
    (object : f.object reference.address.owner (.integer reference.element) = some (buffer,tag))
    (read : readRef buffer (accepts (.integer reference.element)) reference.address = some result)
    (integer : result.value = .integer value) : f.read reference = some value := by
  simp [Frame.read,grant,object,read,integer]

theorem read_stale (f : Frame) (reference : Reference) (binding : Binding) (buffer : Buffer Value) (tag : Tag)
    (grant : f.grant reference = some binding.writable)
    (object : f.object reference.address.owner (.integer reference.element) = some (buffer,tag))
    (stale : reference.address.epoch ≠ buffer.epoch) : f.read reference = none := by
  simp [Frame.read,grant,object,readRef_stale buffer _ reference.address stale]

theorem write_readonly (f : Frame) (reference : Reference) (value : Int)
    (readonly : reference.writable = false) : f.write reference value = none := by
  simp [Frame.write,readonly]

theorem write_wrong_grant (f : Frame) (reference : Reference) (value : Int)
    (rejected : f.grant reference = none) : f.write reference value = none := by
  simp [Frame.write,rejected]

theorem read_header_independent (f : Frame) (reference : Reference) (binding : Binding) (header : Header)
    (found : f.bindings[reference.slot]? = some binding) :
    ({f with bindings := f.bindings.set reference.slot {binding with header := header}} : Frame).read reference =
      f.read reference := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simp [Frame.read,Frame.grant,Frame.object,Frame.maximum,List.getElem?_set_self bound,found]

theorem reserve_readonly (f : Frame) (slot : Nat) (expected : Element) (requested : Nat)
    (binding : Binding) (buffer : Buffer Value) (resolved : f.resolve slot expected = some (binding,buffer))
    (readonly : binding.writable = false) : f.reserve slot expected requested = none := by
  simp [Frame.reserve,resolved,readonly,CppVector.reserve_readonly]

theorem updated_wellFormed (f : Frame) (owner : Nat) (old : Buffer Value) (tag : Tag)
    (result : Result Value Unit) (valid : f.state.wellFormed = true)
    (tagFound : f.state.forest.lookup owner = some tag) (bound : owner < f.state.storage.objects.length)
    (owns : result.buffer.owner = owner) (payload : payloadOK tag result.buffer) :
    (f.updated owner old result).state.wellFormed = true := by
  obtain ⟨lengths,forest,checks⟩ := wellFormed_parts f.state valid
  have nextChecks : (List.range (f.updated owner old result).state.storage.objects.length).all
      (f.updated owner old result).state.check = true := by
    simp only [Frame.updated,List.length_set]
    apply List.all_eq_true.mpr
    intro other member
    by_cases same : owner = other
    · subst other
      simp [State.check,Store.lookup,List.getElem?_set_self bound,tagFound,owns,payload]
    · have good := List.all_eq_true.mp checks other member
      simpa [State.check,Frame.updated,Store.lookup,List.getElem?_set_ne same] using good
  simp only [State.wellFormed,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨by simpa [Frame.updated] using lengths,forest⟩,nextChecks⟩

theorem commit_runs (f : Frame) (owner : Nat) (expected : Element) (old : Buffer Value) (tag : Tag)
    (result : Result Value Unit) (valid : f.state.wellFormed = true)
    (object : f.object owner expected = some (old,tag))
    (tagFound : f.state.forest.lookup owner = some tag) (found : f.state.storage.lookup owner = some old)
    (owns : result.buffer.owner = owner) (payload : payloadOK tag result.buffer)
    (oldPeak : old.capacity+1 ≤ result.peak) (newPeak : result.buffer.capacity+1 ≤ result.peak) :
    f.commit owner expected result = some (f.updated owner old result) := by
  have bound := lookup_bound f.state.storage owner old found
  have nextValid := updated_wellFormed f owner old tag result valid tagFound bound owns payload
  simp [Frame.commit,object,owns,payload,oldPeak,newPeak,nextValid]

theorem reserve_runs (f : Frame) (slot : Nat) (expected : Element) (requested : Nat)
    (binding : Binding) (buffer : Buffer Value) (result : Result Value Unit)
    (resolved : f.resolve slot expected = some (binding,buffer))
    (reserved : CppVector.reserve buffer (accepts expected) binding.writable requested = some result) :
    f.reserve slot expected requested = f.commit binding.owner expected result := by
  simp [Frame.reserve,resolved,reserved]

theorem write_runs (f : Frame) (reference : Reference) (value : Int) (binding : Binding)
    (buffer : Buffer Value) (tag : Tag) (result : Result Value Unit)
    (grant : f.grant reference = some binding.writable) (permission : reference.writable = true)
    (bindingPermission : binding.writable = true)
    (object : f.object reference.address.owner (.integer reference.element) = some (buffer,tag))
    (written : writeRef buffer (accepts (.integer reference.element)) true reference.address (.integer value) = some result) :
    f.write reference value = f.commit reference.address.owner (.integer reference.element) result := by
  simp [Frame.write,grant,permission,bindingPermission,object,written]

theorem commit_success_valid (f next : Frame) (owner : Nat) (expected : Element) (result : Result Value Unit)
    (ran : f.commit owner expected result = some next) : next.state.wellFormed = true := by
  unfold Frame.commit at ran
  cases object : f.object owner expected with
  | none => simp [object] at ran
  | some pair =>
    rcases pair with ⟨old,tag⟩
    simp only [object] at ran
    split at ran
    · split at ran
      · cases ran; assumption
      · simp at ran
    · simp at ran

end Proofs.CppNestedVectorBindings
