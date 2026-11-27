import Proofs.Cpp.TreeMultiset.GeneratedRelink

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem decode_injective : Function.Injective decode := by
  intro left right same
  by_cases endLeft : left = endIndex
  · rw [endLeft] at same
    exact endLeft.trans ((decode_none right).mp (same.symm.trans ((decode_none endIndex).mpr rfl))).symm
  · have notRight : right ≠ endIndex := by
      intro eq
      simp [decode, endLeft, eq] at same
    exact UInt64.toNat_inj.mp (by simpa [decode, endLeft, notRight] using same)

theorem slotView_injective {K : Type} : Function.Injective (slotView (K := K)) := by
  intro before after same
  cases before
  cases after
  simp only [slotView, StoredNode.mk.injEq] at same
  obtain ⟨key, priority, count, total, left, right⟩ := same
  cases key
  cases priority
  cases UInt64.toNat_inj.mp count
  cases UInt64.toNat_inj.mp total
  cases decode_injective left
  cases decode_injective right
  rfl

structure ArenaFrame {K : Type} (before after : cp.TreeMultiSet K) (modified : List Nat) : Prop where
  root : after.root = before.root
  free : after.free_head = before.free_head
  size : after.slots.size = before.slots.size
  outside : ∀ i, i ∉ modified → (storageView after)[i]? = (storageView before)[i]?

namespace ArenaFrame

theorem rawCell {K : Type} [Inhabited K] {before after : cp.TreeMultiSet K} {modified : List Nat}
    (frame : ArenaFrame before after modified) (code : UInt64)
    (unmodified : (Cpp.toSigned 64 code.toNat).toNat ∉ modified) :
    modelCell after code = modelCell before code := by
  have same := frame.outside _ unmodified
  simp only [storageView, Array.getElem?_map] at same
  have raw : after.slots[(Cpp.toSigned 64 code.toNat).toNat]? =
      before.slots[(Cpp.toSigned 64 code.toNat).toNat]? :=
    Option.map_injective slotView_injective same
  simpa [modelCell, Cpp.get_eq, Array.getElem!_eq_getD] using congrArg (fun v => v.getD default) raw

theorem realizes {K : Type} {before after : cp.TreeMultiSet K} {modified footprint : List Nat}
    {index : Option Nat} {tree : Tree K} (frame : ArenaFrame before after modified)
    (real : Realizes (storageView before) index tree footprint) (apart : List.Disjoint footprint modified) :
    Realizes (storageView after) index tree footprint :=
  real.frame fun i mem => frame.outside i (apart mem)

theorem transOf {K : Type} {first middle last : cp.TreeMultiSet K} {a b c : List Nat}
    (firstFrame : ArenaFrame first middle a) (lastFrame : ArenaFrame middle last b)
    (aIn : a ⊆ c) (bIn : b ⊆ c) : ArenaFrame first last c :=
  ⟨lastFrame.root.trans firstFrame.root, lastFrame.free.trans firstFrame.free, lastFrame.size.trans firstFrame.size,
    fun i outside => (lastFrame.outside i (fun mem => outside (bIn mem))).trans
      (firstFrame.outside i (fun mem => outside (aIn mem)))⟩

end ArenaFrame
end Proofs.Cpp.TreeMultiset
