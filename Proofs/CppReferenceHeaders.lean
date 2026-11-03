import Proofs.CppCallFrame

namespace Proofs.CppReferenceHeaders
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppBufferHeaders Proofs.CppCallFrame Proofs.DynamicResultValid

theorem buffer_kept (s t : State) (owner : Nat) (old : Buffer Value)
    (headers : SameHeaders s t) (found : s.storage.lookup owner = some old) :
    ∃ next, t.storage.lookup owner = some next ∧ signature next = signature old := by
  have shape := headers.buffers owner
  rw [found] at shape
  cases lookup : t.storage.lookup owner with
  | none => simp [lookup] at shape
  | some next => exact ⟨next,rfl,Option.some.inj (by simpa [lookup] using shape)⟩

theorem object_facts (f : Frame) (owner : Nat) (ty : Element) (buffer : Buffer Value) (tag : Tag)
    (actual : f.object owner ty = some (buffer,tag)) :
    f.state.storage.lookup owner = some buffer ∧ f.state.forest.lookup owner = some tag ∧ tag.element = ty := by
  unfold Frame.object at actual
  split at actual
  · obtain ⟨old,found,rest⟩ := bind_some _ _ _ actual
    obtain ⟨oldTag,tagFound,rest⟩ := bind_some _ _ _ rest
    split at rest
    · rename_i typed
      obtain ⟨eq1,eq2⟩ := Prod.mk.inj (Option.some.inj rest)
      subst old
      subst oldTag
      exact ⟨found,tagFound,typed⟩
    · simp at rest
  · simp at actual

-- Preserve successful reading, while allowing the stored integer to change.
-- The immutable grant, allocation epoch, type and bounds all remain valid.
theorem read_kept (s t : NState) (reference : Reference) (oldValue : Int)
    (effects : CallEffects s t) (valid : t.frame.state.wellFormed = true)
    (actual : s.frame.read reference = some oldValue) : ∃ value, t.frame.read reference = some value := by
  unfold Frame.read at actual
  obtain ⟨grant,granted,rest⟩ := bind_some _ _ _ actual
  obtain ⟨⟨old,tag⟩,object,rest⟩ := bind_some _ _ _ rest
  obtain ⟨result,read,rest⟩ := bind_some _ _ _ rest
  obtain ⟨found,tagFound,typed⟩ := object_facts s.frame reference.address.owner (.integer reference.element) old tag object
  obtain ⟨next,nextFound,shape⟩ := buffer_kept s.frame.state t.frame.state reference.address.owner old effects.headers found
  have ownerEq := congrArg Signature.owner shape
  have epochEq := congrArg Signature.epoch shape
  have sizeEq := congrArg Signature.size shape
  simp only [signature] at ownerEq epochEq sizeEq
  unfold readRef at read
  split at read
  · rename_i checked
    obtain ⟨oldItem,itemFound,_⟩ := bind_some _ _ _ read
    have inside : reference.address.index < next.items.length := by
      rw [sizeEq]
      exact (List.getElem?_eq_some_iff.mp itemFound).1
    obtain ⟨nextTag,nextTagFound,_,payload⟩ := wellFormed_buffer t.frame.state reference.address.owner next valid nextFound
    have sameTag : nextTag = tag := by
      rw [effects.headers.forest,tagFound] at nextTagFound
      exact Option.some.inj nextTagFound.symm
    subst nextTag
    have nextValid : next.Valid (accepts (.integer reference.element)) := by
      have h := payload.1
      rwa [typed] at h
    cases valueFound : next.items[reference.address.index]? with
    | none =>
      have outside := List.getElem?_eq_none_iff.mp valueFound
      omega
    | some value =>
      have accepted := List.all_eq_true.mp nextValid.2.2 value (List.mem_of_getElem? valueFound)
      cases value with
      | child owner => simp [accepts] at accepted
      | integer value =>
        refine ⟨value,?_⟩
        have newObject := object_runs t.frame reference.address.owner (.integer reference.element) next tag
          valid nextFound (by rw [effects.headers.forest]; exact tagFound) typed
        have newGrant : t.frame.grant reference = some grant := (effects.grant reference).trans granted
        have own : reference.address.owner = next.owner := checked.2.1.trans ownerEq.symm
        have epoch : reference.address.epoch = next.epoch := checked.2.2.trans epochEq.symm
        simp only [Frame.read,newGrant,newObject,Bind.bind,Option.bind]
        simp [readRef,nextValid,own,epoch,valueFound]
  · simp at read

theorem headers_symm (s t : State) (headers : SameHeaders s t) : SameHeaders t s :=
  ⟨headers.forest.symm,headers.count.symm,headers.base.symm,fun owner => (headers.buffers owner).symm⟩

theorem effects_symm (s t : NState) (effects : CallEffects s t) : CallEffects t s :=
  ⟨headers_symm s.frame.state t.frame.state effects.headers,effects.flags.symm,effects.vectorBindings.symm,
    effects.scopedState.symm,effects.slots.symm,effects.scalarBindings.symm,effects.base.symm,
    effects.memoryLength.symm,effects.scalarLive.symm⟩

-- With both heaps well formed, stale/out-of-bounds/unauthorized reads stay
-- rejected as well. Only the returned integer may change.
theorem read_isSome (s t : NState) (reference : Reference) (effects : CallEffects s t)
    (before : s.frame.state.wellFormed = true) (after : t.frame.state.wellFormed = true) :
    (t.frame.read reference).isSome = (s.frame.read reference).isSome := by
  cases old : s.frame.read reference with
  | none =>
    cases new : t.frame.read reference with
    | none => rfl
    | some value =>
      obtain ⟨previous,read⟩ := read_kept t s reference value (effects_symm s t effects) before new
      rw [old] at read
      cases read
  | some value =>
    obtain ⟨next,read⟩ := read_kept s t reference value effects after old
    rw [read]
    rfl

end Proofs.CppReferenceHeaders
