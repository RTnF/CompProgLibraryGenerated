import Proofs.Cpp.TreeMultiset.SplitLayout
import Proofs.Cpp.TreeMultiset.MergeLayout

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem Realizes.index_lt {K : Type} {storage : Array (StoredNode K)}
    {root : Option Nat} {tree : Tree K} {slots : List Nat}
    (layout : Realizes storage root tree slots) (i : Nat) (present : i ∈ slots) : i < storage.size := by
  obtain ⟨row, reads, _⟩ := layout.live i present
  by_contra bad
  rw [Array.getElem?_eq_none (Nat.le_of_not_gt bad)] at reads
  contradiction

theorem Realizes.capacity {K : Type} {storage : Array (StoredNode K)}
    {root : Option Nat} {tree : Tree K} {slots : List Nat}
    (layout : Realizes storage root tree slots) : tree.slots ≤ storage.size := by
  rw [← layout.node_count, ← List.length_range (n := storage.size)]
  exact layout.distinct.length_le_of_subset fun {i} mem => List.mem_range.mpr (layout.index_lt i mem)

theorem Realizes.sum_capacity {K : Type} {storage : Array (StoredNode K)}
    {lroot rroot : Option Nat} {left right : Tree K} {ls rs : List Nat}
    (leftLayout : Realizes storage lroot left ls) (rightLayout : Realizes storage rroot right rs)
    (separate : List.Disjoint ls rs) : left.slots + right.slots ≤ storage.size := by
  have nodup : (ls ++ rs).Nodup :=
    List.nodup_append.mpr ⟨leftLayout.distinct, rightLayout.distinct, by
      intro a ha b hb same
      subst b
      exact separate ha hb⟩
  have le := nodup.length_le_of_subset (l₂ := List.range storage.size) (by
    intro i mem
    rcases List.mem_append.mp mem with l | r
    · exact List.mem_range.mpr (leftLayout.index_lt i l)
    · exact List.mem_range.mpr (rightLayout.index_lt i r))
  simpa [List.length_append, leftLayout.node_count, rightLayout.node_count] using le

theorem generated_split_entry {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (tree : Tree K) (pivot : K) (arena : cp.TreeMultiSet K) (code : UInt64) (used : List Nat)
    (layout : Realizes (storageView arena) (decode code) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64) (start : Nat) :
    ∃ low high after stop, (cp.TreeMultiSet.split arena code pivot).run start =
      some (((low, high), after), stop) ∧ stop ≤ start + 4 + 7 * tree.height ∧
      Nonempty (SplitResult arena after used low high (tree.split pivot).1 (tree.split pivot).2) := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨low, high, after, stop, run, ticks, result⟩ :=
    generated_split_spec tree pivot arena code used layout fits weight Cpp.fuel start enough
  have cost := tree.split_height_ticks pivot
  exact ⟨low, high, after, stop, run, by omega, result⟩

theorem generated_merge_entry {K : Type} [Inhabited K] (left right : Tree K)
    (arena : cp.TreeMultiSet K) (lc rc : UInt64) (ls rs : List Nat)
    (leftLayout : Realizes (storageView arena) (decode lc) left ls)
    (rightLayout : Realizes (storageView arena) (decode rc) right rs)
    (separate : List.Disjoint ls rs) (fits : arena.slots.size ≤ 2 ^ 63)
    (weight : left.weight + right.weight < 2 ^ 64) (start : Nat) :
    ∃ code after stop, (cp.TreeMultiSet.merge arena lc rc).run start = some ((code, after), stop) ∧
      stop ≤ start + 3 + 8 * (left.height + right.height) ∧
      Nonempty (MergeResult arena after (ls ++ rs) code (left.merge right)) := by
  have capacity : left.slots + right.slots ≤ arena.slots.size := by
    simpa [storageView] using leftLayout.sum_capacity rightLayout separate
  have leftHeight := left.height_le_slots
  have rightHeight := right.height_le_slots
  have enough : left.height + right.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨code, after, run, result⟩ :=
    generated_merge_spec left right arena lc rc ls rs leftLayout rightLayout separate fits weight Cpp.fuel start enough
  have cost := left.mergeTicks_le right
  exact ⟨code, after, _, run, by omega, result⟩

end Proofs.Cpp.TreeMultiset
