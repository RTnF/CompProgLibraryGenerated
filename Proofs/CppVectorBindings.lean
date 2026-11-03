import Proofs.CppVectorStore

namespace Proofs.CppVectorBindings
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorRange Proofs.CppVectorStore

structure ObjectType where
  element : Ty
  writable : Bool
deriving DecidableEq, Repr
structure Binding where
  owner : Nat
  element : Ty
  writable : Bool
deriving DecidableEq, Repr
structure Reference where
  slot : Nat
  element : Ty
  writable : Bool
  address : ElementRef
deriving DecidableEq, Repr
structure Frame where
  store : Store Int
  types : List ObjectType
  bindings : List Binding := []
  peak : Nat := 0
deriving DecidableEq, Repr
inductive Parameter where
  | scalar (element : Ty) (reference writable : Bool)
  | vector (element : Ty) (writable : Bool)
  | nested (element : Ty) (writable : Bool)
deriving DecidableEq, Repr

def supported (ty : Ty) : Prop := (ty.width = 32 ∨ ty.width = 64) ∧ ty.boolean = false
instance (ty : Ty) : Decidable (supported ty) := inferInstanceAs (Decidable (_ ∧ _))
-- LP64 libstdc++ limits the element count by PTRDIFF_MAX / sizeof(T).
def sizeLimit (ty : Ty) : Nat := (2^63-1)/(ty.width/8)

def Frame.observe (f : Frame) (temporaries : Nat) : Frame :=
  {f with peak := max f.peak (f.store.peak+f.bindings.length+temporaries)}

def Frame.object (f : Frame) (owner : Nat) (expected : Ty) : Option (Buffer Int × ObjectType) := do
  let buffer ← f.store.lookup owner
  let tag ← f.types[owner]?
  if supported expected ∧ tag.element = expected ∧ buffer.owner = owner ∧
      buffer.Valid expected.valid ∧ buffer.limit ≤ sizeLimit expected then
    some (buffer,tag)
  else none

def Frame.resolve (f : Frame) (slot : Nat) (expected : Ty) : Option (Binding × Buffer Int) := do
  let binding ← f.bindings[slot]?
  let (buffer,tag) ← f.object binding.owner expected
  if binding.element = expected ∧ (binding.writable = true → tag.writable = true) then
    some (binding,buffer)
  else none

def Frame.bind (f : Frame) (owner : Nat) (expected : Ty) (writable : Bool) : Option Frame := do
  let (_,tag) ← f.object owner expected
  if writable = true → tag.writable = true then
    some (({f with bindings := f.bindings ++ [⟨owner,expected,writable⟩]} : Frame).observe 0)
  else none

def Frame.construct (f : Frame) (expected : Ty) (writable : Bool) (limit count : Nat) (value : Int) :
    Option (Frame × Nat) := do
  if supported expected ∧ limit ≤ sizeLimit expected ∧ f.types.length = f.store.objects.length then
    let (store,owner) ← f.store.construct expected.valid limit count value
    let next : Frame := {f with store := store,types := f.types ++ [⟨expected,writable⟩], bindings := f.bindings ++ [⟨owner,expected,writable⟩]}
    some (next.observe 0,f.bindings.length)
  else none

def Frame.size (f : Frame) (slot : Nat) (expected : Ty) : Option (Frame × Int) := do
  let (binding,buffer) ← f.resolve slot expected
  let value : Int := buffer.items.length
  if (⟨64,false,false⟩ : Ty).valid value then
    let (store,value) ← f.store.commit binding.owner expected.valid
      (⟨buffer,value,1,buffer.capacity+2⟩ : Result Int Int)
    some (({f with store := store} : Frame).observe 1,value)
  else none

def Frame.elementRef (f : Frame) (slot : Nat) (expected : Ty) (index : Int) : Option Reference := do
  let (binding,buffer) ← f.resolve slot expected
  let address ← CppVector.elementRef buffer expected.valid index
  some ⟨slot,expected,binding.writable,address⟩

def Frame.read (f : Frame) (reference : Reference) : Option (Frame × Int) := do
  let (binding,_) ← f.resolve reference.slot reference.element
  if reference.address.owner = binding.owner then
    let (store,value) ← f.store.read reference.element.valid reference.address
    some (({f with store := store} : Frame).observe 1,value)
  else none

def Frame.write (f : Frame) (reference : Reference) (value : Int) : Option Frame := do
  let (binding,_) ← f.resolve reference.slot reference.element
  if reference.address.owner = binding.owner ∧ reference.writable = true ∧ binding.writable = true then
    let (store,_) ← f.store.writeReference reference.element.valid true reference.address value
    some (({f with store := store} : Frame).observe 1)
  else none

def Frame.reserve (f : Frame) (slot : Nat) (expected : Ty) (requested : Nat) : Option Frame := do
  let (binding,_) ← f.resolve slot expected
  let (store,_) ← f.store.reserve expected.valid binding.writable binding.owner requested
  some (({f with store := store} : Frame).observe 1)

def Frame.assign (f : Frame) (target source : Nat) (expected : Ty) (range : IteratorRange) : Option Frame := do
  let (destination,_) ← f.resolve target expected
  let (origin,_) ← f.resolve source expected
  if range.owner = origin.owner then
    let (store,_) ← f.store.assign expected.valid destination.writable destination.owner range
    some (({f with store := store} : Frame).observe 1)
  else none

def Frame.appendReserved (f : Frame) (slot : Nat) (expected : Ty) (value : Int) : Option Frame := do
  let (binding,_) ← f.resolve slot expected
  let (store,_) ← f.store.appendReserved expected.valid binding.writable binding.owner value
  some (({f with store := store} : Frame).observe 1)

-- Pure begin/end endpoints are captured in the same unmodified frame.
def Frame.iteratorRange (f : Frame) (first last : Nat) (expected : Ty)
    (firstEnd lastEnd : Bool) : Option IteratorRange := do
  let (origin,buffer) ← f.resolve first expected
  let (ending,other) ← f.resolve last expected
  if origin.owner = ending.owner ∧ buffer.epoch = other.epoch then
    CppVectorRange.rangeBetween buffer expected.valid
      (if firstEnd then Int.ofNat buffer.items.length else 0)
      (if lastEnd then Int.ofNat other.items.length else 0)
  else none

theorem iteratorRange_runs (f : Frame) (first last : Nat) (expected : Ty)
    (firstEnd lastEnd : Bool) (origin ending : Binding) (buffer other : Buffer Int)
    (resolvedFirst : f.resolve first expected = some (origin,buffer))
    (resolvedLast : f.resolve last expected = some (ending,other))
    (sameOwner : origin.owner = ending.owner) (sameEpoch : buffer.epoch = other.epoch) :
    f.iteratorRange first last expected firstEnd lastEnd =
      CppVectorRange.rangeBetween buffer expected.valid
        (if firstEnd then Int.ofNat buffer.items.length else 0)
        (if lastEnd then Int.ofNat other.items.length else 0) := by
  simp [Frame.iteratorRange,resolvedFirst,resolvedLast,sameOwner,sameEpoch]

theorem iteratorRange_wrong_owner (f : Frame) (first last : Nat) (expected : Ty)
    (firstEnd lastEnd : Bool) (origin ending : Binding) (buffer other : Buffer Int)
    (resolvedFirst : f.resolve first expected = some (origin,buffer))
    (resolvedLast : f.resolve last expected = some (ending,other))
    (different : origin.owner ≠ ending.owner) :
    f.iteratorRange first last expected firstEnd lastEnd = none := by
  simp [Frame.iteratorRange,resolvedFirst,resolvedLast,different]

theorem iteratorRange_wrong_epoch (f : Frame) (first last : Nat) (expected : Ty)
    (firstEnd lastEnd : Bool) (origin ending : Binding) (buffer other : Buffer Int)
    (resolvedFirst : f.resolve first expected = some (origin,buffer))
    (resolvedLast : f.resolve last expected = some (ending,other))
    (different : buffer.epoch ≠ other.epoch) :
    f.iteratorRange first last expected firstEnd lastEnd = none := by
  simp [Frame.iteratorRange,resolvedFirst,resolvedLast,different]

theorem object_runs (f : Frame) (owner : Nat) (expected : Ty) (buffer : Buffer Int) (tag : ObjectType)
    (lookup : f.store.lookup owner = some buffer) (typeLookup : f.types[owner]? = some tag)
    (profile : supported expected) (same : tag.element = expected) (owns : buffer.owner = owner)
    (valid : buffer.Valid expected.valid) (limit : buffer.limit ≤ sizeLimit expected) :
    f.object owner expected = some (buffer,tag) := by
  simp [Frame.object,lookup,typeLookup,profile,same,owns,valid,limit]

theorem resolve_runs (f : Frame) (slot : Nat) (expected : Ty) (binding : Binding)
    (buffer : Buffer Int) (tag : ObjectType) (lookup : f.bindings[slot]? = some binding)
    (object : f.object binding.owner expected = some (buffer,tag)) (same : binding.element = expected)
    (permission : binding.writable = true → tag.writable = true) :
    f.resolve slot expected = some (binding,buffer) := by
  simp [Frame.resolve,lookup,object,same]
  exact permission

theorem resolve_wrong_type (f : Frame) (slot : Nat) (expected : Ty) (binding : Binding)
    (lookup : f.bindings[slot]? = some binding) (wrong : binding.element ≠ expected) :
    f.resolve slot expected = none := by simp [Frame.resolve,lookup,wrong]

theorem bind_runs (f : Frame) (owner : Nat) (expected : Ty) (writable : Bool)
    (buffer : Buffer Int) (tag : ObjectType) (object : f.object owner expected = some (buffer,tag))
    (permission : writable = true → tag.writable = true) :
    f.bind owner expected writable = some (({f with bindings := f.bindings ++ [⟨owner,expected,writable⟩]} : Frame).observe 0) := by
  simp [Frame.bind,object]
  exact permission

theorem bind_cannot_escalate (f : Frame) (owner : Nat) (expected : Ty)
    (buffer : Buffer Int) (tag : ObjectType) (object : f.object owner expected = some (buffer,tag))
    (readonly : tag.writable = false) : f.bind owner expected true = none := by
  simp [Frame.bind,object,readonly]

theorem elementRef_runs (f : Frame) (slot : Nat) (expected : Ty) (index : Int)
    (binding : Binding) (buffer : Buffer Int) (address : ElementRef)
    (resolved : f.resolve slot expected = some (binding,buffer))
    (reference : CppVector.elementRef buffer expected.valid index = some address) :
    f.elementRef slot expected index = some ⟨slot,expected,binding.writable,address⟩ := by
  simp [Frame.elementRef,resolved,reference]

theorem readonly_reference_stays_readonly (f : Frame) (slot : Nat) (expected : Ty) (index : Int)
    (binding : Binding) (buffer : Buffer Int) (address : ElementRef)
    (resolved : f.resolve slot expected = some (binding,buffer)) (readonly : binding.writable = false)
    (reference : CppVector.elementRef buffer expected.valid index = some address) :
    f.elementRef slot expected index = some ⟨slot,expected,false,address⟩ := by
  simpa [readonly] using elementRef_runs f slot expected index binding buffer address resolved reference

theorem write_readonly_reference (f : Frame) (reference : Reference) (value : Int)
    (readonly : reference.writable = false) : f.write reference value = none := by
  simp [Frame.write,readonly]

theorem write_readonly_binding (f : Frame) (reference : Reference) (value : Int)
    (binding : Binding) (buffer : Buffer Int)
    (resolved : f.resolve reference.slot reference.element = some (binding,buffer))
    (readonly : binding.writable = false) : f.write reference value = none := by
  simp [Frame.write,resolved,readonly]

theorem read_wrong_owner (f : Frame) (reference : Reference) (binding : Binding) (buffer : Buffer Int)
    (resolved : f.resolve reference.slot reference.element = some (binding,buffer))
    (wrong : reference.address.owner ≠ binding.owner) : f.read reference = none := by
  simp [Frame.read,resolved,wrong]

theorem write_wrong_owner (f : Frame) (reference : Reference) (value : Int)
    (binding : Binding) (buffer : Buffer Int)
    (resolved : f.resolve reference.slot reference.element = some (binding,buffer))
    (wrong : reference.address.owner ≠ binding.owner) : f.write reference value = none := by
  simp [Frame.write,resolved,wrong]

theorem observe_preserves (f : Frame) (temporaries : Nat) :
    (f.observe temporaries).store = f.store ∧ (f.observe temporaries).types = f.types ∧
    (f.observe temporaries).bindings = f.bindings := by exact ⟨rfl,rfl,rfl⟩

theorem observe_bounds (f : Frame) (temporaries : Nat) :
    f.peak ≤ (f.observe temporaries).peak ∧
    f.store.peak+f.bindings.length+temporaries ≤ (f.observe temporaries).peak := by
  exact ⟨Nat.le_max_left _ _,Nat.le_max_right _ _⟩

theorem object_wrong_type (f : Frame) (owner : Nat) (expected : Ty) (tag : ObjectType)
    (lookup : f.types[owner]? = some tag) (wrong : tag.element ≠ expected) :
    f.object owner expected = none := by simp [Frame.object,lookup,wrong]

theorem object_dead (f : Frame) (owner : Nat) (expected : Ty)
    (dead : f.store.lookup owner = none) : f.object owner expected = none := by
  simp [Frame.object,dead]

theorem construct_misaligned (f : Frame) (expected : Ty) (writable : Bool) (limit count : Nat)
    (value : Int) (wrong : f.types.length ≠ f.store.objects.length) :
    f.construct expected writable limit count value = none := by simp [Frame.construct,wrong]

theorem construct_runs (f : Frame) (expected : Ty) (writable : Bool) (limit count : Nat) (value : Int)
    (profile : supported expected) (maxSize : limit ≤ sizeLimit expected)
    (aligned : f.types.length = f.store.objects.length) (bounded : count ≤ limit)
    (accepted : expected.valid value = true) :
    f.construct expected writable limit count value = some
      (({f with store := f.store.allocate ⟨f.store.objects.length,List.replicate count value,count,limit,0⟩ (count+1) (count+2), types := f.types ++ [⟨expected,writable⟩],bindings := f.bindings ++ [⟨f.store.objects.length,expected,writable⟩]} : Frame).observe 0,
       f.bindings.length) := by
  simp [Frame.construct,profile,maxSize,aligned,Proofs.CppVectorStore.construct_runs _ _ _ _ _ bounded accepted]

end Proofs.CppVectorBindings
