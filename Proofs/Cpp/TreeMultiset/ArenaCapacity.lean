import Proofs.Cpp.TreeMultiset.ArenaEntries
import Proofs.Cpp.TreeMultiset.GeneratedAllocation

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem FreeSlots.distinct {K : Type} {storage : Array (StoredNode K)} {head : Option Nat}
    {slots : List Nat} (layout : FreeSlots storage head slots) : slots.Nodup := by
  induction layout with
  | empty => exact List.nodup_nil
  | cons _ _ _ _ fresh ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩

theorem FreeSlots.index_lt {K : Type} {storage : Array (StoredNode K)} {head : Option Nat}
    {slots : List Nat} (layout : FreeSlots storage head slots) (i : Nat) (present : i ∈ slots) :
    i < storage.size := by
  obtain ⟨row, reads, _⟩ := layout.vacant i present
  by_contra bad
  rw [Array.getElem?_eq_none (Nat.le_of_not_gt bad)] at reads
  contradiction

theorem occupied_capacity {K : Type} {storage : Array (StoredNode K)} {root head : Option Nat}
    {tree : Tree K} {live free : List Nat} (layout : Realizes storage root tree live)
    (available : FreeSlots storage head free)
    (covers : ∀ i, i < storage.size → i ∈ live ++ free) :
    storage.size = tree.slots + free.length := by
  have disjoint := available.disjoint_tree layout
  have nodup : (live ++ free).Nodup :=
    List.nodup_append.mpr ⟨layout.distinct, available.distinct, by
      intro a ha b hb same
      subst b
      exact disjoint hb ha⟩
  have partition : (live ++ free).Perm (List.range storage.size) := by
    apply (List.perm_ext_iff_of_nodup nodup (List.nodup_range (n := storage.size))).mpr
    intro i
    rw [List.mem_append, List.mem_range]
    constructor
    · exact fun p => p.elim (layout.index_lt i) (available.index_lt i)
    · exact fun h => List.mem_append.mp (covers i h)
  simpa [List.length_append, layout.node_count] using partition.length_eq.symm

theorem append_only_when_full {K : Type} {storage : Array (StoredNode K)} {root : Option Nat}
    {tree : Tree K} {live free : List Nat} (layout : Realizes storage root tree live)
    (available : FreeSlots storage none free) (covers : ∀ i, i < storage.size → i ∈ live ++ free) :
    storage.size = tree.slots := by
  cases available
  simpa using occupied_capacity layout FreeSlots.empty covers

end Proofs.Cpp.TreeMultiset
