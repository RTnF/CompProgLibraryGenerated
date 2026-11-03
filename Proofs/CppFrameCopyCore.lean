import Proofs.CppNestedCopy

namespace Proofs.CppFrameCopy
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct
open Proofs.CppNestedCopy

-- Source permission governs reading; the newly constructed root has its own
-- permission. In particular a const source can produce a writable copy.
def copyBinding (f : Frame) (ty : Ty) (scope : Nat) (writable : Bool) : Binding :=
  ⟨f.state.storage.objects.length,.integer ty,writable,.root scope⟩

def copiedFrame (f : Frame) (source : Buffer Value) (ty : Ty) (scope : Nat) (writable : Bool) : Frame :=
  ⟨cloned f.state source ty scope,f.rootWritable++[writable],
    f.bindings++[copyBinding f ty scope writable]⟩

def copyVector (f : Frame) (slot : Nat) (ty : Ty) (scope : Nat) (writable : Bool) :
    Option (Frame × Nat) := do
  if f.rootWritable.length = f.state.forest.objects.length then
    let (binding,source) ← f.resolve slot (.integer ty)
    let _ ← copyRoot f.state binding.owner ty scope
    some (copiedFrame f source ty scope writable,f.bindings.length)
  else none

-- A statement first resolves its source expression, then releases temporary
-- bindings. The owner's object survives that release and can be copied here.
def copyOwner (f : Frame) (owner : Nat) (ty : Ty) (scope : Nat) (writable : Bool) :
    Option (Frame × Nat) := do
  if f.rootWritable.length = f.state.forest.objects.length then
    let (source,_) ← f.object owner (.integer ty)
    let _ ← copyRoot f.state owner ty scope
    some (copiedFrame f source ty scope writable,f.bindings.length)
  else none

end Proofs.CppFrameCopy
