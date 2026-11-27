import Proofs.Cpp.TreeMultiset.GeneratedWeight
import Proofs.Cpp.TreeMultiset.FreeSlots

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem modelCell_view {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (code : UInt64) (index : Nat) (row : StoredNode K)
    (decoded : decode code = some index) (reads : (storageView arena)[index]? = some row)
    (fits : arena.slots.size ≤ 2 ^ 63) :
    code.toNat = index ∧ index < arena.slots.size ∧ slotView (modelCell arena code) = row := by
  obtain ⟨_, codeNat⟩ := decode_some code index decoded
  have inside : index < arena.slots.size := by
    by_contra bad
    simp [storageView, Array.getElem?_eq_none (show arena.slots.size ≤ index by omega)] at reads
  refine ⟨codeNat, inside, ?_⟩
  have signed := signed_model_index (value := code) (by omega)
  unfold modelCell
  rw [signed, codeNat]
  simpa [storageView, Cpp.get_eq, getElem!_pos, getElem?_pos, inside] using reads

theorem storageView_set {K : Type} (arena : cp.TreeMultiSet K) (index : Nat) (row : cp.TreeMultiSet_Slot K) :
    storageView { arena with slots := Cpp.set arena.slots (index : Int) row } =
      (storageView arena).setIfInBounds index (slotView row) := by
  apply Array.ext_getElem?
  intro i
  by_cases same : i = index
  · subst i
    simp [storageView, Cpp.set, Array.getElem?_setIfInBounds_self]
  · simp [storageView, Cpp.set, Ne.symm same]

theorem storageView_push {K : Type} (arena : cp.TreeMultiSet K) (row : cp.TreeMultiSet_Slot K) :
    storageView { arena with slots := arena.slots.push row } = (storageView arena).push (slotView row) := by
  exact Array.map_push

theorem weight_from_layout {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (code : UInt64) (tree : Tree K) (slots : List Nat)
    (layout : Realizes (storageView arena) (decode code) tree slots) (fits : arena.slots.size ≤ 2 ^ 63) :
    (modelWeight arena code).toNat = tree.weight := by
  obtain ⟨word, run, weight⟩ := generated_weight_spec arena code tree slots layout fits 0
  rw [generated_weight_run] at run
  have wordEq : modelWeight arena code = word := congrArg Prod.fst (Option.some.inj run)
  rwa [wordEq]

theorem generated_release_run {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (code : UInt64)
    (inside : (Cpp.toSigned 64 code.toNat).toNat < arena.slots.size) (start : Nat) :
    let row := { modelCell arena code with key := none, left := arena.free_head }
    (cp.TreeMultiSet.release arena code).run start =
      some (⟨Cpp.set arena.slots (Cpp.toSigned 64 code.toNat) row, arena.root, code⟩, start + 1) := by
  cases arena
  simp [cp.TreeMultiSet.release, Cpp.tick, modelCell,
    read_at_written _ _ _ inside, write_same_cell]

end Proofs.Cpp.TreeMultiset
