import Proofs.CppFrameCopyCore
import Proofs.CppFrameExtension
import Proofs.CppNestedFacts
import Proofs.CppFixedWrite

namespace Proofs.CppFrameCopy
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct
open Proofs.CppNestedCopy Proofs.CppFrameExtension Proofs.DynamicResultValid

theorem resolve_object (f : Frame) (slot : Nat) (ty : Ty) (binding : Binding) (source : Buffer Value)
    (resolved : f.resolve slot (.integer ty) = some (binding,source)) :
    ∃ tag, f.object binding.owner (.integer ty) = some (source,tag) := by
  unfold Frame.resolve at resolved
  obtain ⟨b,_,rest⟩ := bind_some _ _ _ resolved
  obtain ⟨owner,_,rest⟩ := bind_some _ _ _ rest
  obtain ⟨⟨buffer,tag⟩,object,rest⟩ := bind_some _ _ _ rest
  obtain ⟨maximum,_,rest⟩ := bind_some _ _ _ rest
  try dsimp only at rest
  split at rest
  · rename_i good
    obtain ⟨sameB,sameBuffer⟩ := Prod.mk.inj (Option.some.inj rest)
    subst b
    subst buffer
    exact ⟨tag,by rw [good.1]; exact object⟩
  · simp at rest

theorem object_parts (f : Frame) (owner : Nat) (ty : Ty) (source : Buffer Value) (tag : Tag)
    (object : f.object owner (.integer ty) = some (source,tag)) :
    f.state.wellFormed = true ∧ f.state.storage.lookup owner = some source ∧
      f.state.forest.lookup owner = some tag ∧ tag.element = .integer ty := by
  unfold Frame.object at object
  split at object
  · rename_i valid
    obtain ⟨buffer,found,rest⟩ := bind_some _ _ _ object
    obtain ⟨actual,tagFound,rest⟩ := bind_some _ _ _ rest
    split at rest
    · rename_i typed
      obtain ⟨sameBuffer,sameTag⟩ := Prod.mk.inj (Option.some.inj rest)
      subst buffer
      subst actual
      exact ⟨valid,found,tagFound,typed⟩
    · simp at rest
  · simp at object

theorem copy_vector_runs (f : Frame) (slot : Nat) (ty : Ty) (scope : Nat) (writable : Bool)
    (binding : Binding) (source : Buffer Value)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (supported : CppVectorBindings.supported ty)
    (resolved : f.resolve slot (.integer ty) = some (binding,source)) :
    copyVector f slot ty scope writable = some (copiedFrame f source ty scope writable,f.bindings.length) := by
  obtain ⟨tag,object⟩ := resolve_object f slot ty binding source resolved
  obtain ⟨valid,storage,forest,typed⟩ := object_parts f binding.owner ty source tag object
  simp [copyVector,lengths,resolved,Proofs.CppNestedCopy.copy_runs f.state source tag binding.owner ty scope
    valid supported forest storage typed]

theorem copied_frame_extends (f : Frame) (source : Buffer Value) (ty : Ty) (scope : Nat) (writable : Bool)
    (valid : f.state.wellFormed = true)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (supported : CppVectorBindings.supported ty)
    (payload : source.Valid (accepts (.integer ty))) :
    Extends f (copiedFrame f source ty scope writable) := by
  refine ⟨valid,clone_wellFormed f.state source ty scope valid supported payload,lengths,?_,?_,?_,?_,?_⟩
  · simp [copiedFrame,cloned,declareRoot_length,lengths]
  · intro owner old
    exact declareRoot_old f.state.forest ty scope owner old
  · intro owner old
    exact clone_storage_old f.state source ty scope owner old
  · intro owner old
    exact List.getElem?_append_left old
  · intro slot old
    exact List.getElem?_append_left old

theorem copy_vector_extends (f : Frame) (slot : Nat) (ty : Ty) (scope : Nat) (writable : Bool)
    (binding : Binding) (source : Buffer Value)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (supported : CppVectorBindings.supported ty)
    (resolved : f.resolve slot (.integer ty) = some (binding,source)) :
    Extends f (copiedFrame f source ty scope writable) := by
  obtain ⟨tag,object⟩ := resolve_object f slot ty binding source resolved
  obtain ⟨valid,storage,forest,typed⟩ := object_parts f binding.owner ty source tag object
  obtain ⟨actual,found,_,payload⟩ := wellFormed_buffer f.state binding.owner source valid storage
  have same : actual = tag := Option.some.inj (found.symm.trans forest)
  subst actual
  apply copied_frame_extends f source ty scope writable valid lengths supported
  simpa only [typed] using payload.1

theorem copy_vector_keeps_read (f : Frame) (slot : Nat) (ty : Ty) (scope : Nat) (writable : Bool)
    (binding : Binding) (source : Buffer Value) (reference : Reference) (value : Int)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (supported : CppVectorBindings.supported ty)
    (resolved : f.resolve slot (.integer ty) = some (binding,source))
    (read : f.read reference = some value) :
    (copiedFrame f source ty scope writable).read reference = some value :=
  read_kept f _ (copy_vector_extends f slot ty scope writable binding source lengths supported resolved)
    reference value read

theorem copied_resolve (f : Frame) (source : Buffer Value) (ty : Ty) (scope : Nat) (writable : Bool)
    (valid : f.state.wellFormed = true)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (supported : CppVectorBindings.supported ty)
    (payload : source.Valid (accepts (.integer ty))) :
    (copiedFrame f source ty scope writable).resolve f.bindings.length (.integer ty) =
      some (copyBinding f ty scope writable,Proofs.CppVectorCopy.copied source f.state.storage.objects.length) := by
  let next := copiedFrame f source ty scope writable
  have extension := copied_frame_extends f source ty scope writable valid lengths supported payload
  have sf := (wellFormed_parts f.state valid).1
  have tagFound : next.state.forest.lookup f.state.storage.objects.length = some (flatTag ty scope) := by
    have h := declareRoot_new f.state.forest ty scope
    rw [sf] at h
    exact h
  have newObject := object_runs next f.state.storage.objects.length (.integer ty)
    (Proofs.CppVectorCopy.copied source f.state.storage.objects.length) (flatTag ty scope)
    extension.newValid (clone_storage_new f.state source ty scope) tagFound rfl
  have rooted := root_runs next.state.forest f.state.storage.objects.length (flatTag ty scope) tagFound rfl
  have maximum : next.maximum f.state.storage.objects.length = some writable := by
    apply Proofs.CppNestedFacts.maximum_runs next _ _ writable extension.newLengths rooted
    simp [next,copiedFrame,lengths,sf]
  apply Proofs.CppNestedFacts.resolve_root next f.bindings.length (.integer ty)
    (copyBinding f ty scope writable) scope _ (flatTag ty scope) writable
    (by simp [next,copiedFrame]) rfl rfl newObject rfl rfl maximum
  exact fun h => h

theorem copy_root_supported (s : State) (owner : Nat) (ty : Ty) (scope : Nat) (next : State)
    (ran : copyRoot s owner ty scope = some next) : CppVectorBindings.supported ty := by
  unfold copyRoot at ran
  split at ran
  · rename_i good
    exact good.2
  · simp at ran

theorem copy_vector_inv (f out : Frame) (slot index : Nat) (ty : Ty) (scope : Nat) (writable : Bool)
    (ran : copyVector f slot ty scope writable = some (out,index)) :
    ∃ binding source, f.rootWritable.length = f.state.forest.objects.length ∧
      CppVectorBindings.supported ty ∧ f.resolve slot (.integer ty) = some (binding,source) ∧
      out = copiedFrame f source ty scope writable ∧ index = f.bindings.length := by
  unfold copyVector at ran
  split at ran
  · rename_i lengths
    obtain ⟨⟨binding,source⟩,resolved,rest⟩ := bind_some _ _ _ ran
    obtain ⟨state,copied,rest⟩ := bind_some _ _ _ rest
    have result := Prod.mk.inj (Option.some.inj rest)
    exact ⟨binding,source,lengths,copy_root_supported f.state binding.owner ty scope state copied,
      resolved,result.1.symm,result.2.symm⟩
  · simp at ran

theorem copy_vector_success (f out : Frame) (slot index : Nat) (ty : Ty) (scope : Nat) (writable : Bool)
    (ran : copyVector f slot ty scope writable = some (out,index)) : Extends f out := by
  obtain ⟨binding,source,lengths,supported,resolved,rfl,_⟩ := copy_vector_inv f out slot index ty scope writable ran
  exact copy_vector_extends f slot ty scope writable binding source lengths supported resolved

theorem copied_element_ref (f : Frame) (source : Buffer Value) (ty : Ty) (scope index : Nat) (writable : Bool)
    (valid : f.state.wellFormed = true)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (supported : CppVectorBindings.supported ty)
    (payload : source.Valid (accepts (.integer ty))) (inside : index < source.items.length) :
    (copiedFrame f source ty scope writable).elementRef f.bindings.length ty index =
      some ⟨f.bindings.length,ty,writable,⟨f.state.storage.objects.length,0,index⟩⟩ := by
  have resolved := copied_resolve f source ty scope writable valid lengths supported payload
  have captured := Proofs.CppVector.elementRef_runs
    (Proofs.CppVectorCopy.copied source f.state.storage.objects.length) (accepts (.integer ty))
    (index : Int) (Proofs.CppVectorCopy.copied_valid source _ _ payload) (by omega) (by simpa [Proofs.CppVectorCopy.copied] using inside)
  simpa [copyBinding,Proofs.CppVectorCopy.copied] using
    elementRef_runs (copiedFrame f source ty scope writable) f.bindings.length ty (index : Int)
      (copyBinding f ty scope writable) _ _ resolved captured

theorem copied_write_old (f : Frame) (source : Buffer Value) (ty : Ty) (scope index : Nat)
    (out : Frame) (value : Int) (other : Nat) (old : other < f.state.storage.objects.length)
    (actual : (copiedFrame f source ty scope true).write
      ⟨f.bindings.length,ty,true,⟨f.state.storage.objects.length,0,index⟩⟩ value = some out) :
    out.state.storage.lookup other = f.state.storage.lookup other := by
  have same := Proofs.CppFixedWrite.frame_write_other (copiedFrame f source ty scope true) out
    ⟨f.bindings.length,ty,true,⟨f.state.storage.objects.length,0,index⟩⟩ value actual other (by dsimp; omega)
  exact same.trans (clone_storage_old f.state source ty scope other old)

-- A resolved reference and its still-live owner yield the same copy, including
-- failure and the entire frame/cost state. No source write permission is needed.
theorem copy_vector_owner (f : Frame) (slot : Nat) (ty : Ty) (scope : Nat) (writable : Bool)
    (binding : Binding) (source : Buffer Value)
    (resolved : f.resolve slot (.integer ty) = some (binding,source)) :
    copyVector f slot ty scope writable = copyOwner f binding.owner ty scope writable := by
  obtain ⟨tag,object⟩ := resolve_object f slot ty binding source resolved
  simp [copyVector,copyOwner,resolved,object]

-- Temporary bindings can be removed before the owner copy. The new binding
-- follows exactly the retained prefix; the owner and copied storage are unchanged.
theorem copy_owner_rebind (f : Frame) (bindings : List Binding) (owner : Nat)
    (ty : Ty) (scope : Nat) (writable : Bool) :
    copyOwner {f with bindings := bindings} owner ty scope writable =
      (copyOwner f owner ty scope writable).map (fun result =>
        ({result.1 with bindings := bindings ++ [copyBinding f ty scope writable]},bindings.length)) := by
  have object : ({f with bindings := bindings} : Frame).object owner (.integer ty) =
      f.object owner (.integer ty) := rfl
  by_cases lengths : f.rootWritable.length = f.state.forest.objects.length
  · cases found : f.object owner (.integer ty) with
    | none => simp [copyOwner,lengths,object,found]
    | some pair =>
      obtain ⟨source,tag⟩ := pair
      cases copied : copyRoot f.state owner ty scope with
      | none => simp [copyOwner,lengths,object,found,copied]
      | some state => simp [copyOwner,lengths,object,found,copied,copiedFrame,copyBinding]
  · simp [copyOwner,lengths]

theorem copy_owner_runs (f : Frame) (owner : Nat) (ty : Ty) (scope : Nat) (writable : Bool)
    (source : Buffer Value) (tag : Tag)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (supported : CppVectorBindings.supported ty)
    (object : f.object owner (.integer ty) = some (source,tag)) :
    copyOwner f owner ty scope writable = some (copiedFrame f source ty scope writable,f.bindings.length) := by
  obtain ⟨valid,storage,forest,typed⟩ := object_parts f owner ty source tag object
  simp [copyOwner,lengths,object,Proofs.CppNestedCopy.copy_runs f.state source tag owner ty scope
    valid supported forest storage typed]

theorem copy_owner_extends (f : Frame) (owner : Nat) (ty : Ty) (scope : Nat) (writable : Bool)
    (source : Buffer Value) (tag : Tag)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (supported : CppVectorBindings.supported ty)
    (object : f.object owner (.integer ty) = some (source,tag)) :
    Extends f (copiedFrame f source ty scope writable) := by
  obtain ⟨valid,storage,forest,typed⟩ := object_parts f owner ty source tag object
  obtain ⟨actual,found,_,payload⟩ := wellFormed_buffer f.state owner source valid storage
  have same : actual = tag := Option.some.inj (found.symm.trans forest)
  subst actual
  apply copied_frame_extends f source ty scope writable valid lengths supported
  simpa only [typed] using payload.1

end Proofs.CppFrameCopy
