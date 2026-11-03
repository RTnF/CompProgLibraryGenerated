import Proofs.CppReferenceHeaders

namespace Proofs.CppHeaderAliases
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedProgram Proofs.CppBufferHeaders
open Proofs.CppCallFrame Proofs.CppReferenceHeaders

theorem object_kept (s t : NState) (owner : Nat) (element : Element) (old : Buffer Value) (tag : Tag)
    (effects : CallEffects s t) (valid : t.frame.state.wellFormed = true)
    (object : s.frame.object owner element = some (old,tag)) :
    ∃ next, t.frame.object owner element = some (next,tag) ∧ signature next = signature old := by
  obtain ⟨found,tagFound,typed⟩ := object_facts s.frame owner element old tag object
  obtain ⟨next,nextFound,shape⟩ := buffer_kept s.frame.state t.frame.state owner old effects.headers found
  exact ⟨next,object_runs t.frame owner element next tag valid nextFound
    (by rw [effects.headers.forest]; exact tagFound) typed,shape⟩

-- Nested payloads consist of the forest's child IDs. Their values cannot
-- change while the forest, buffer headers and well-formedness are preserved.
theorem nested_lookup_kept (s t : State) (owner : Nat) (element : Element) (old : Buffer Value) (tag : Tag)
    (headers : SameHeaders s t) (before : s.wellFormed = true) (after : t.wellFormed = true)
    (found : s.storage.lookup owner = some old) (tagFound : s.forest.lookup owner = some tag)
    (typed : tag.element = .vector element) : t.storage.lookup owner = some old := by
  obtain ⟨next,nextFound,shape⟩ := buffer_kept s t owner old headers found
  obtain ⟨oldTag,oldTagFound,_,oldPayload⟩ := wellFormed_buffer s owner old before found
  have oldEq : oldTag = tag := Option.some.inj (oldTagFound.symm.trans tagFound)
  subst oldTag
  obtain ⟨newTag,newTagFound,_,newPayload⟩ := wellFormed_buffer t owner next after nextFound
  have newEq : newTag = tag := by rw [headers.forest] at newTagFound; exact Option.some.inj (newTagFound.symm.trans tagFound)
  subst newTag
  have oldItems : old.items = tag.children.map Value.child := by simpa [typed] using oldPayload.2
  have newItems : next.items = tag.children.map Value.child := by simpa [typed] using newPayload.2
  have items : next.items = old.items := newItems.trans oldItems.symm
  have eq : next = old := by
    cases next
    cases old
    simp_all [signature]
  rwa [eq] at nextFound

theorem header_owner (s t : NState) (binding : Binding) (effects : CallEffects s t)
    (before : s.frame.state.wellFormed = true) (after : t.frame.state.wellFormed = true) :
    t.frame.headerOwner binding = s.frame.headerOwner binding := by
  cases header : binding.header with
  | root scope =>
    cases oldObject : s.frame.object binding.owner binding.element with
    | none =>
      cases newObject : t.frame.object binding.owner binding.element with
      | none => simp [Frame.headerOwner,header,oldObject,newObject]
      | some pair =>
        obtain ⟨buffer,tag⟩ := pair
        obtain ⟨previous,previousObject,_⟩ := object_kept t s binding.owner binding.element buffer tag
          (effects_symm s t effects) before newObject
        rw [oldObject] at previousObject
        cases previousObject
    | some pair =>
      obtain ⟨buffer,tag⟩ := pair
      obtain ⟨next,newObject,_⟩ := object_kept s t binding.owner binding.element buffer tag effects after oldObject
      simp [Frame.headerOwner,header,oldObject,newObject]
  | child address =>
    cases oldObject : s.frame.object address.owner (.vector binding.element) with
    | none =>
      cases newObject : t.frame.object address.owner (.vector binding.element) with
      | none => simp [Frame.headerOwner,header,oldObject,newObject]
      | some pair =>
        obtain ⟨buffer,tag⟩ := pair
        obtain ⟨previous,previousObject,_⟩ := object_kept t s address.owner (.vector binding.element) buffer tag
          (effects_symm s t effects) before newObject
        rw [oldObject] at previousObject
        cases previousObject
    | some pair =>
      obtain ⟨buffer,tag⟩ := pair
      obtain ⟨found,tagFound,typed⟩ := object_facts s.frame address.owner (.vector binding.element) buffer tag oldObject
      have nextFound := nested_lookup_kept s.frame.state t.frame.state address.owner binding.element buffer tag
        effects.headers before after found tagFound typed
      have newObject := object_runs t.frame address.owner (.vector binding.element) buffer tag after nextFound
        (by rw [effects.headers.forest]; exact tagFound) typed
      simp only [Frame.headerOwner,header,oldObject,newObject]

theorem resolve_kept (s t : NState) (slot : Nat) (element : Element) (binding : Binding) (old : Buffer Value)
    (effects : CallEffects s t) (before : s.frame.state.wellFormed = true) (after : t.frame.state.wellFormed = true)
    (actual : s.frame.resolve slot element = some (binding,old)) :
    ∃ next, t.frame.resolve slot element = some (binding,next) ∧ signature next = signature old := by
  unfold Frame.resolve at actual
  obtain ⟨b,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  obtain ⟨owner,resolved,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨⟨buffer,tag⟩,object,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨maximum,maxFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  try dsimp only at rest
  split at rest
  · rename_i checked
    obtain ⟨bindingEq,bufferEq⟩ := Prod.mk.inj (Option.some.inj rest)
    subst b
    subst buffer
    obtain ⟨next,newObject,shape⟩ := object_kept s t owner element old tag effects after object
    have newBinding : t.frame.bindings[slot]? = some binding := by rw [effects.vectorBindings]; exact found
    have newHeader : t.frame.headerOwner binding = some owner := (header_owner s t binding effects before after).trans resolved
    have newMaximum : t.frame.maximum owner = some maximum := by
      simpa only [Frame.maximum,effects.flags,effects.headers.forest] using maxFound
    refine ⟨next,?_,shape⟩
    simp only [Frame.resolve,newBinding,newHeader,newObject,newMaximum,Bind.bind,Option.bind,if_pos checked]
  · simp at rest

theorem resolve_signature (s t : NState) (slot : Nat) (element : Element) (effects : CallEffects s t)
    (before : s.frame.state.wellFormed = true) (after : t.frame.state.wellFormed = true) :
    (t.frame.resolve slot element).map (fun pair => (pair.1,signature pair.2)) =
      (s.frame.resolve slot element).map (fun pair => (pair.1,signature pair.2)) := by
  cases old : s.frame.resolve slot element with
  | none =>
    cases new : t.frame.resolve slot element with
    | none => rfl
    | some pair =>
      obtain ⟨binding,buffer⟩ := pair
      obtain ⟨previous,read,_⟩ := resolve_kept t s slot element binding buffer
        (effects_symm s t effects) after before new
      rw [old] at read
      cases read
  | some pair =>
    obtain ⟨binding,buffer⟩ := pair
    obtain ⟨next,new,shape⟩ := resolve_kept s t slot element binding buffer effects before after old
    rw [new]
    simp [shape]

end Proofs.CppHeaderAliases
