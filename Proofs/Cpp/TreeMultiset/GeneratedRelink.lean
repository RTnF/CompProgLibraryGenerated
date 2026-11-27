import Proofs.Cpp.TreeMultiset.GeneratedLayout

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

def putCell {K : Type} (arena : cp.TreeMultiSet K) (code : UInt64) (row : cp.TreeMultiSet_Slot K) : cp.TreeMultiSet K :=
  { arena with slots := Cpp.set arena.slots (Cpp.toSigned 64 code.toNat) row }

theorem putCell_read {K : Type} (arena : cp.TreeMultiSet K) (code : UInt64) (index : Nat)
    (row : cp.TreeMultiSet_Slot K) (position : Cpp.toSigned 64 code.toNat = (index : Int))
    (inside : index < arena.slots.size) :
    (storageView (putCell arena code row))[index]? = some (slotView row) := by
  rw [putCell, position, storageView_set]
  simp [storageView, inside]

theorem putCell_frame {K : Type} (arena : cp.TreeMultiSet K) (code : UInt64) (index : Nat)
    (row : cp.TreeMultiSet_Slot K) (position : Cpp.toSigned 64 code.toNat = (index : Int))
    (other : Nat) (apart : other ≠ index) :
    (storageView (putCell arena code row))[other]? = (storageView arena)[other]? := by
  simp [putCell, position, storageView_set, Ne.symm apart]

theorem putCell_modelCell {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (code : UInt64)
    (row : cp.TreeMultiSet_Slot K) (inside : (Cpp.toSigned 64 code.toNat).toNat < arena.slots.size) :
    modelCell (putCell arena code row) code = row := by
  simp [putCell, modelCell, read_at_written _ _ _ inside]

theorem putCell_size {K : Type} (arena : cp.TreeMultiSet K) (code : UInt64) (row : cp.TreeMultiSet_Slot K) :
    (putCell arena code row).slots.size = arena.slots.size := Cpp.size_set _ _ _

theorem putCell_twice {K : Type} (arena : cp.TreeMultiSet K) (code : UInt64) (before after : cp.TreeMultiSet_Slot K) :
    putCell (putCell arena code before) code after = putCell arena code after := by
  simp [putCell, write_same_cell]

theorem generated_relink_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (code : UInt64) (index : Nat) (row : cp.TreeMultiSet_Slot K) (key : K)
    (left right : Tree K) (leftSlots rightSlots : List Nat)
    (decoded : decode code = some index) (inside : index < arena.slots.size)
    (fits : arena.slots.size ≤ 2 ^ 63) (hasKey : row.key = some key)
    (leftTree : Realizes (storageView arena) (decode row.left) left leftSlots)
    (rightTree : Realizes (storageView arena) (decode row.right) right rightSlots)
    (leftFresh : index ∉ leftSlots) (rightFresh : index ∉ rightSlots)
    (separate : List.Disjoint leftSlots rightSlots)
    (totalFits : row.count.toNat + left.weight + right.weight < 2 ^ 64) (start : Nat) :
    ∃ out, (cp.TreeMultiSet.update (putCell arena code row) code).run start = some (out, start + 5) ∧
      out.root = arena.root ∧ out.free_head = arena.free_head ∧ out.slots.size = arena.slots.size ∧
      Realizes (storageView out) (decode code) (.node key row.priority row.count.toNat left right)
        (index :: (leftSlots ++ rightSlots)) ∧
      ∀ i, i ≠ index → (storageView out)[i]? = (storageView arena)[i]? := by
  obtain ⟨_, codeNat⟩ := decode_some code index decoded
  have position : Cpp.toSigned 64 code.toNat = (index : Int) := by
    rw [signed_model_index (by omega), codeNat]
  have signedInside : (Cpp.toSigned 64 code.toNat).toNat < arena.slots.size := by
    simpa only [position, Int.toNat_natCast]
  let relinked := putCell arena code row
  have oldRead : modelCell relinked code = row := putCell_modelCell _ _ _ signedInside
  have leftRelinked : Realizes (storageView relinked) (decode row.left) left leftSlots :=
    leftTree.frame fun i mem => putCell_frame _ _ _ _ position i (fun same => leftFresh (same ▸ mem))
  have rightRelinked : Realizes (storageView relinked) (decode row.right) right rightSlots :=
    rightTree.frame fun i mem => putCell_frame _ _ _ _ position i (fun same => rightFresh (same ▸ mem))
  have relinkFits : relinked.slots.size ≤ 2 ^ 63 := (putCell_size _ _ _).symm ▸ fits
  have lw := weight_from_layout relinked row.left left leftSlots leftRelinked relinkFits
  have rw := weight_from_layout relinked row.right right rightSlots rightRelinked relinkFits
  let next := { row with total := row.count + modelWeight relinked row.left + modelWeight relinked row.right }
  let out := putCell arena code next
  have exactTotal : next.total.toNat = row.count.toNat + left.weight + right.weight := by
    change (row.count + modelWeight relinked row.left + modelWeight relinked row.right).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_add, lw, rw]
    rw [Nat.mod_eq_of_lt (by omega : row.count.toNat + left.weight < 2 ^ 64), Nat.mod_eq_of_lt totalFits]
  have unchanged := putCell_frame arena code index next position
  refine ⟨out, ?_, rfl, rfl, putCell_size _ _ _, ?_, unchanged⟩
  · rw [generated_update_run, oldRead]
    change some (putCell relinked code next, start + 5) = _
    rw [putCell_twice]
  · rw [decoded]
    refine .node ?_ (leftTree.frame ?_) (rightTree.frame ?_) leftFresh rightFresh separate
    · change (storageView (putCell arena code next))[index]? = _
      rw [putCell_read arena code index next position inside]
      change some (⟨row.key, row.priority, row.count.toNat, next.total.toNat,
        decode row.left, decode row.right⟩ : StoredNode K) = _
      rw [hasKey, exactTotal]
    · intro i mem
      exact unchanged i (fun same => leftFresh (same ▸ mem))
    · intro i mem
      exact unchanged i (fun same => rightFresh (same ▸ mem))

end Proofs.Cpp.TreeMultiset
