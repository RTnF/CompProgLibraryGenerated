import Proofs.CppFrameExtension

namespace Proofs.CppFrameResolveExtension
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.DynamicResultValid Proofs.CppFrameExtension

theorem object_inside {f : Frame} {owner : Nat} {expected : Element}
    {buffer : Proofs.CppVector.Buffer Value} {tag : Tag}
    (valid : f.state.wellFormed = true)
    (found : f.object owner expected = some (buffer,tag)) :
    owner < f.state.storage.objects.length := by
  unfold Frame.object at found
  simp only [valid,ite_true] at found
  obtain ⟨b,lookup,_⟩ := bind_some _ _ _ found
  exact Proofs.CppVectorStore.lookup_bound f.state.storage owner b lookup

-- Success supplies the old owner bounds, including a borrowed child header.
theorem header_owner_kept (f g : Frame) (extension : Extends f g)
    (binding : Binding) (owner : Nat)
    (actual : f.headerOwner binding = some owner) :
    g.headerOwner binding = some owner := by
  cases header : binding.header with
  | root scope =>
    simp only [Frame.headerOwner,header] at actual ⊢
    obtain ⟨⟨buffer,tag⟩,object,_⟩ := bind_some _ _ _ actual
    have inside := object_inside extension.oldValid object
    rw [object_eq f g extension binding.owner binding.element inside]
    exact actual
  | child address =>
    simp only [Frame.headerOwner,header] at actual ⊢
    obtain ⟨⟨parent,tag⟩,object,_⟩ := bind_some _ _ _ actual
    have inside := object_inside extension.oldValid object
    rw [object_eq f g extension address.owner (.vector binding.element) inside]
    exact actual

-- Preserve every successful resolution; no claim is made about forged future owners.
theorem resolve_kept (f g : Frame) (extension : Extends f g)
    (slot : Nat) (expected : Element) (binding : Binding)
    (buffer : Proofs.CppVector.Buffer Value)
    (actual : f.resolve slot expected = some (binding,buffer)) :
    g.resolve slot expected = some (binding,buffer) := by
  have parsed := actual
  unfold Frame.resolve at parsed
  obtain ⟨b,found,rest⟩ := bind_some _ _ _ parsed
  obtain ⟨owner,header,rest⟩ := bind_some _ _ _ rest
  obtain ⟨⟨buf,tag⟩,object,rest⟩ := bind_some _ _ _ rest
  obtain ⟨maximum,maximumFound,rest⟩ := bind_some _ _ _ rest
  split at rest
  · rename_i good
    obtain ⟨sameBinding,sameBuffer⟩ := Prod.mk.inj (Option.some.inj rest)
    subst b
    subst buf
    have inside := object_inside extension.oldValid object
    have lens := (wellFormed_parts f.state extension.oldValid).1
    have nextFound := (extension.bindings slot (List.getElem?_eq_some_iff.mp found).1).trans found
    have nextHeader := header_owner_kept f g extension binding owner header
    have nextObject := object_eq f g extension owner expected inside
    have nextMaximum := maximum_eq f g extension owner (by omega)
    simp only [Frame.resolve,nextFound,Bind.bind,Option.bind,nextHeader,nextObject,object,
      nextMaximum,maximumFound]
    exact ite_eq_left good
  · simp at rest

end Proofs.CppFrameResolveExtension
