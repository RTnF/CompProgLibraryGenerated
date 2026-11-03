import Proofs.CppNestedConstruct
import Proofs.CppNestedGrowth

namespace Proofs.CppNestedOps
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppVectorRange Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings

-- Operations on integer vectors owned through the nested forest. They follow
-- the flat `CppVectorBindings.Frame` operations but commit through the
-- nested Frame, which also checks parent / child payloads and epochs.

def _root_.Proofs.CppNestedVectorBindings.Frame.size (f : Frame) (slot : Nat) (expected : Element) :
    Option (Frame × Int) := do
  let (_,buffer) ← f.resolve slot expected
  let value : Int := buffer.items.length
  if (⟨64,false,false⟩ : Ty).valid value then some (f,value) else none

def _root_.Proofs.CppNestedVectorBindings.Frame.append (f : Frame) (slot : Nat) (ty : Ty) (value : Int) :
    Option Frame := do
  f.appendGrowing slot ty value

def _root_.Proofs.CppNestedVectorBindings.Frame.iteratorRange (f : Frame) (first last : Nat) (ty : Ty)
    (firstEnd lastEnd : Bool) : Option IteratorRange := do
  let (origin,buffer) ← f.resolve first (.integer ty)
  let (ending,other) ← f.resolve last (.integer ty)
  if origin.owner = ending.owner ∧ buffer.epoch = other.epoch then
    rangeBetween buffer (accepts (.integer ty))
      (if firstEnd then Int.ofNat buffer.items.length else 0)
      (if lastEnd then Int.ofNat other.items.length else 0)
  else none

def _root_.Proofs.CppNestedVectorBindings.Frame.assign (f : Frame) (target source : Nat) (ty : Ty)
    (range : IteratorRange) : Option Frame := do
  let (destination,targetBuffer) ← f.resolve target (.integer ty)
  let (origin,sourceBuffer) ← f.resolve source (.integer ty)
  if range.owner = origin.owner then
    let result ← assignRange targetBuffer sourceBuffer (accepts (.integer ty)) destination.writable range
    f.commit destination.owner (.integer ty) result
  else none

-- `container[index]` on a vector of vectors: the child binding inherits the
-- container binding's permission, so a const container yields const rows.
def _root_.Proofs.CppNestedVectorBindings.Frame.child (f : Frame) (slot : Nat) (expected : Element)
    (index : Int) : Option (Frame × Nat) := do
  let (origin,_) ← f.resolve slot (.vector expected)
  f.bindChild slot expected index origin.writable

-- A declared local vector root: `rootWritable` is indexed by owner ID, so the
-- new root's permission and its children's unused entries are appended.
def _root_.Proofs.CppNestedVectorBindings.Frame.retireScope (f : Frame) (scope : Nat) : Option Frame := do
  let state ← f.state.retireScope scope
  some {f with state := state}

def _root_.Proofs.CppNestedVectorBindings.Frame.transferRoot (f : Frame) (owner : Nat) (expected : Element)
    (fromScope toScope : Nat) : Option Frame := do
  let state ← f.state.transfer owner expected fromScope toScope
  some {f with state := state}

theorem updated_lookup_self (f : Frame) (owner : Nat) (old : Buffer Value) (result : Result Value Unit)
    (bound : owner < f.state.storage.objects.length) :
    (f.updated owner old result).state.storage.lookup owner = some result.buffer := by
  simp [Frame.updated,Store.lookup,List.getElem?_set_self bound]

theorem updated_lookup_other (f : Frame) (owner other : Nat) (old : Buffer Value) (result : Result Value Unit)
    (different : owner ≠ other) :
    (f.updated owner old result).state.storage.lookup other = f.state.storage.lookup other := by
  simp [Frame.updated,Store.lookup,List.getElem?_set_ne different]

theorem updated_forest (f : Frame) (owner : Nat) (old : Buffer Value) (result : Result Value Unit) :
    (f.updated owner old result).state.forest = f.state.forest := rfl

theorem updated_bindings (f : Frame) (owner : Nat) (old : Buffer Value) (result : Result Value Unit) :
    (f.updated owner old result).bindings = f.bindings ∧
    (f.updated owner old result).rootWritable = f.rootWritable := ⟨rfl,rfl⟩

theorem append_runs (f : Frame) (slot : Nat) (ty : Ty) (value : Int) (binding : Binding)
    (buffer : Buffer Value) (result : Result Value Unit)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (appended : CppVector.appendReserved buffer (accepts (.integer ty)) binding.writable (.integer value) = some result) :
    f.append slot ty value = f.commit binding.owner (.integer ty) result := by
  exact CppNestedGrowth.append_reserved f slot ty value binding buffer result resolved appended

theorem append_readonly (f : Frame) (slot : Nat) (ty : Ty) (value : Int) (binding : Binding)
    (buffer : Buffer Value) (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (readonly : binding.writable = false) : f.append slot ty value = none := by
  exact CppNestedGrowth.append_readonly f slot ty value binding buffer resolved readonly

theorem size_runs (f : Frame) (slot : Nat) (expected : Element) (binding : Binding) (buffer : Buffer Value)
    (resolved : f.resolve slot expected = some (binding,buffer))
    (valid : (⟨64,false,false⟩ : Ty).valid (buffer.items.length : Int) = true) :
    f.size slot expected = some (f,(buffer.items.length : Int)) := by
  have enough : (⟨64,false,false⟩ : Ty).valid (buffer.items.length : Int) = true := valid
  simp only [Frame.size,resolved,Bind.bind,Option.bind,enough,if_true]

theorem assign_runs (f : Frame) (target source : Nat) (ty : Ty) (range : IteratorRange)
    (destination origin : Binding) (targetBuffer sourceBuffer : Buffer Value) (result : Result Value Unit)
    (resolvedTarget : f.resolve target (.integer ty) = some (destination,targetBuffer))
    (resolvedSource : f.resolve source (.integer ty) = some (origin,sourceBuffer))
    (sameOwner : range.owner = origin.owner)
    (assigned : assignRange targetBuffer sourceBuffer (accepts (.integer ty)) destination.writable range = some result) :
    f.assign target source ty range = f.commit destination.owner (.integer ty) result := by
  simp [Frame.assign,resolvedTarget,resolvedSource,sameOwner,assigned]

theorem assign_readonly (f : Frame) (target source : Nat) (ty : Ty) (range : IteratorRange)
    (destination origin : Binding) (targetBuffer sourceBuffer : Buffer Value)
    (resolvedTarget : f.resolve target (.integer ty) = some (destination,targetBuffer))
    (resolvedSource : f.resolve source (.integer ty) = some (origin,sourceBuffer))
    (readonly : destination.writable = false) : f.assign target source ty range = none := by
  simp [Frame.assign,resolvedTarget,resolvedSource,readonly,assignRange]

end Proofs.CppNestedOps
