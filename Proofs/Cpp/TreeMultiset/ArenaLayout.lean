import Proofs.Math.TreeMultiset.Treap
import Mathlib.Data.List.Nodup

namespace Proofs.Cpp.TreeMultiset

structure StoredNode (K : Type) where
  key : Option K
  priority : UInt64
  count : Nat
  total : Nat
  left : Option Nat
  right : Option Nat

inductive Realizes (storage : Array (StoredNode K)) : Option Nat → Tree K → List Nat → Prop
  | empty : Realizes storage none .empty []
  | node {index : Nat} {key : K} {p : UInt64} {count : Nat} {left right : Tree K}
      {leftIndex rightIndex : Option Nat} {leftSlots rightSlots : List Nat}
      (reads : storage[index]? = some ⟨some key, p, count, count + left.weight + right.weight, leftIndex, rightIndex⟩)
      (leftTree : Realizes storage leftIndex left leftSlots)
      (rightTree : Realizes storage rightIndex right rightSlots)
      (leftFresh : index ∉ leftSlots) (rightFresh : index ∉ rightSlots)
      (separate : List.Disjoint leftSlots rightSlots) :
      Realizes storage (some index) (.node key p count left right) (index :: (leftSlots ++ rightSlots))

namespace Realizes

theorem node_count {K : Type} {storage : Array (StoredNode K)} {root : Option Nat} {tree : Tree K}
    {slots : List Nat} (layout : Realizes storage root tree slots) : slots.length = tree.slots := by
  induction layout with
  | empty => rfl
  | node _ _ _ _ _ _ ihLeft ihRight =>
    simp [Tree.slots, ihLeft, ihRight]
    omega

theorem distinct {K : Type} {storage : Array (StoredNode K)} {root : Option Nat} {tree : Tree K}
    {slots : List Nat} (layout : Realizes storage root tree slots) : slots.Nodup := by
  induction layout with
  | empty => exact List.nodup_nil
  | node _ _ _ leftFresh rightFresh separate ihLeft ihRight =>
    refine List.nodup_cons.mpr ⟨by simp [leftFresh, rightFresh], ?_⟩
    apply List.nodup_append.mpr
    refine ⟨ihLeft, ihRight, ?_⟩
    intro a ha b hb eq
    subst b
    exact separate ha hb

theorem live {K : Type} {storage : Array (StoredNode K)} {root : Option Nat} {tree : Tree K}
    {slots : List Nat} (layout : Realizes storage root tree slots) :
    ∀ index ∈ slots, ∃ row, storage[index]? = some row ∧ row.key.isSome = true := by
  induction layout with
  | empty => simp
  | node reads _ _ _ _ _ ihLeft ihRight =>
    intro index mem
    rcases List.mem_cons.mp mem with rfl | sub
    · exact ⟨_, reads, rfl⟩
    · rcases List.mem_append.mp sub with left | right
      · exact ihLeft index left
      · exact ihRight index right

theorem frame {K : Type} {storage after : Array (StoredNode K)} {root : Option Nat} {tree : Tree K}
    {slots : List Nat} (layout : Realizes storage root tree slots)
    (preserved : ∀ i ∈ slots, after[i]? = storage[i]?) : Realizes after root tree slots := by
  induction layout with
  | empty => exact .empty
  | @node index _ _ _ _ _ _ _ leftSlots rightSlots reads _ _ leftFresh rightFresh separate ihLeft ihRight =>
    have atRoot := preserved index (List.mem_cons_self ..)
    refine .node (atRoot.trans reads) (ihLeft ?_) (ihRight ?_) leftFresh rightFresh separate
    · intro i mem
      exact preserved i (List.mem_cons_of_mem _ (List.mem_append_left _ mem))
    · intro i mem
      exact preserved i (List.mem_cons_of_mem _ (List.mem_append_right _ mem))

theorem write_outside {K : Type} {storage : Array (StoredNode K)} {root : Option Nat} {tree : Tree K}
    {slots : List Nat} (layout : Realizes storage root tree slots) (index : Nat) (row : StoredNode K)
    (external : index ∉ slots) : Realizes (storage.setIfInBounds index row) root tree slots := by
  apply frame layout
  intro i mem
  exact Array.getElem?_setIfInBounds_ne (by
    intro eq
    subst i
    exact external mem)

end Realizes
end Proofs.Cpp.TreeMultiset
