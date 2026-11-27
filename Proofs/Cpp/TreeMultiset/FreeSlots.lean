import Proofs.Cpp.TreeMultiset.ArenaLayout

namespace Proofs.Cpp.TreeMultiset

inductive FreeSlots (storage : Array (StoredNode K)) : Option Nat → List Nat → Prop
  | empty : FreeSlots storage none []
  | cons {index : Nat} {next : Option Nat} {rest : List Nat} {row : StoredNode K}
      (reads : storage[index]? = some row) (vacant : row.key = none)
      (link : row.left = next) (tail : FreeSlots storage next rest) (fresh : index ∉ rest) :
      FreeSlots storage (some index) (index :: rest)

namespace FreeSlots

theorem frame {K : Type} {before after : Array (StoredNode K)} {head : Option Nat}
    {slots : List Nat} (layout : FreeSlots before head slots)
    (preserved : ∀ index ∈ slots, after[index]? = before[index]?) : FreeSlots after head slots := by
  induction layout with
  | empty => exact .empty
  | @cons index _ _ _ reads vacant link _ fresh ih =>
    refine .cons ((preserved index (List.mem_cons_self ..)).trans reads) vacant link ?_ fresh
    exact ih fun i hi => preserved i (List.mem_cons_of_mem _ hi)

theorem vacant {K : Type} {storage : Array (StoredNode K)} {head : Option Nat}
    {slots : List Nat} (layout : FreeSlots storage head slots) :
    ∀ index ∈ slots, ∃ row, storage[index]? = some row ∧ row.key = none := by
  induction layout with
  | empty => simp
  | cons reads vacant _ _ _ ih =>
    intro index mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨_, reads, vacant⟩
    · exact ih index mem

theorem disjoint_tree {K : Type} {storage : Array (StoredNode K)} {head root : Option Nat}
    {slots treeSlots : List Nat} {tree : Tree K} (layout : FreeSlots storage head slots)
    (treeLayout : Realizes storage root tree treeSlots) : List.Disjoint slots treeSlots := by
  intro i free live
  obtain ⟨freeCell, freeRead, freeKey⟩ := layout.vacant i free
  obtain ⟨liveCell, liveRead, liveKey⟩ := treeLayout.live i live
  have same := Option.some.inj (freeRead.symm.trans liveRead)
  cases same
  simp [freeKey] at liveKey

end FreeSlots
end Proofs.Cpp.TreeMultiset
