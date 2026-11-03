import Proofs.CppConstructionRetire

namespace Proofs.CppFrameExtension
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.DynamicResultValid

-- Parent traversal cannot leave an equal prefix: every step moves backwards.
theorem root_prefix (f g : Forest) (bound : Nat)
    (same : ∀ i, i < bound → g.lookup i = f.lookup i) (owner : Nat) (inside : owner < bound) :
    g.rootOwner owner = f.rootOwner owner := by
  induction owner using Nat.strongRecOn with
  | ind owner ih =>
    have lookup := same owner inside
    cases found : f.lookup owner with
    | none =>
      rw [Forest.rootOwner,Forest.rootOwner]
      simp [lookup,found]
    | some tag =>
      have updated : g.lookup owner = some tag := lookup.trans found
      cases hp : tag.parent with
      | none => rw [root_runs g owner tag updated hp,root_runs f owner tag found hp]
      | some parent =>
        by_cases earlier : parent < owner
        · rw [child_runs g owner parent tag updated hp earlier,child_runs f owner parent tag found hp earlier]
          exact ih parent earlier (by omega)
        · rw [invalid_parent_fails g owner parent tag updated hp (by omega),
            invalid_parent_fails f owner parent tag found hp (by omega)]

theorem root_le (f : Forest) (owner root : Nat) (ran : f.rootOwner owner = some root) : root ≤ owner := by
  induction owner using Nat.strongRecOn with
  | ind owner ih =>
    cases found : f.lookup owner with
    | none => rw [Forest.rootOwner] at ran; simp [found] at ran
    | some tag =>
      cases hp : tag.parent with
      | none => rw [root_runs f owner tag found hp] at ran; cases ran; omega
      | some parent =>
        by_cases earlier : parent < owner
        · rw [child_runs f owner parent tag found hp earlier] at ran
          have bound := ih parent earlier ran
          omega
        · rw [invalid_parent_fails f owner parent tag found hp (by omega)] at ran
          contradiction

structure Extends (f g : Frame) : Prop where
  oldValid : f.state.wellFormed = true
  newValid : g.state.wellFormed = true
  oldLengths : f.rootWritable.length = f.state.forest.objects.length
  newLengths : g.rootWritable.length = g.state.forest.objects.length
  forest : ∀ owner, owner < f.state.forest.objects.length → g.state.forest.lookup owner = f.state.forest.lookup owner
  storage : ∀ owner, owner < f.state.storage.objects.length → g.state.storage.lookup owner = f.state.storage.lookup owner
  flags : ∀ owner, owner < f.rootWritable.length → g.rootWritable[owner]? = f.rootWritable[owner]?
  bindings : ∀ slot, slot < f.bindings.length → g.bindings[slot]? = f.bindings[slot]?

theorem maximum_eq (f g : Frame) (extension : Extends f g) (owner : Nat)
    (inside : owner < f.state.forest.objects.length) : g.maximum owner = f.maximum owner := by
  have roots := root_prefix f.state.forest g.state.forest _ extension.forest owner inside
  simp only [Frame.maximum,extension.oldLengths,extension.newLengths,ite_true,roots]
  cases ran : f.state.forest.rootOwner owner with
  | none => rfl
  | some root =>
    have small := root_le f.state.forest owner root ran
    simpa using extension.flags root (by rw [extension.oldLengths]; omega)

theorem object_eq (f g : Frame) (extension : Extends f g) (owner : Nat) (element : Element)
    (inside : owner < f.state.storage.objects.length) : g.object owner element = f.object owner element := by
  have lens := (wellFormed_parts f.state extension.oldValid).1
  simp [Frame.object,extension.oldValid,extension.newValid,extension.storage owner inside,
    extension.forest owner (by omega)]

theorem grant_eq (f g : Frame) (extension : Extends f g) (reference : Reference) (binding : Binding)
    (found : f.bindings[reference.slot]? = some binding)
    (inside : binding.owner < f.state.storage.objects.length) : g.grant reference = f.grant reference := by
  have slotBound := (List.getElem?_eq_some_iff.mp found).1
  have lens := (wellFormed_parts f.state extension.oldValid).1
  simp [Frame.grant,extension.bindings reference.slot slotBound,found,
    maximum_eq f g extension binding.owner (by omega)]

theorem read_eq (f g : Frame) (extension : Extends f g) (reference : Reference) (binding : Binding)
    (found : f.bindings[reference.slot]? = some binding)
    (inside : binding.owner < f.state.storage.objects.length)
    (address : reference.address.owner < f.state.storage.objects.length) :
    g.read reference = f.read reference := by
  simp only [Frame.read,grant_eq f g extension reference binding found inside,
    object_eq f g extension reference.address.owner (.integer reference.element) address]

-- Successful reads establish the old slot and owner bounds themselves.
theorem read_kept (f g : Frame) (extension : Extends f g) (reference : Reference) (value : Int)
    (read : f.read reference = some value) : g.read reference = some value := by
  unfold Frame.read at read
  obtain ⟨wr,grant,rest⟩ := bind_some _ _ _ read
  obtain ⟨pair,object,_⟩ := bind_some _ _ _ rest
  obtain ⟨buffer,tag⟩ := pair
  have address : reference.address.owner < f.state.storage.objects.length := by
    unfold Frame.object at object
    simp only [extension.oldValid,ite_true] at object
    obtain ⟨b,lookup,_⟩ := bind_some _ _ _ object
    exact Proofs.CppVectorStore.lookup_bound f.state.storage reference.address.owner b lookup
  unfold Frame.grant at grant
  obtain ⟨binding,found,rest⟩ := bind_some _ _ _ grant
  obtain ⟨maximum,_,rest⟩ := bind_some _ _ _ rest
  split at rest
  · rename_i good
    have inside : binding.owner < f.state.storage.objects.length := by rw [good.1]; exact address
    have same := read_eq f g extension reference binding found inside address
    rw [same]
    simpa only [Frame.read] using read
  · simp at rest

end Proofs.CppFrameExtension
