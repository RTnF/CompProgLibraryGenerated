import Proofs.Math.TreeMultiset.Treap

namespace Proofs.Cpp.TreeMultiset.Tree

abbrev inInterval [LE K] [LT K] (first last key : K) : Prop := first ≤ key ∧ key < last

def boundedEntries [LinearOrder K] (first last : K) (parent : Option K) : Tree K → List (K × Nat × Option K)
  | .empty => []
  | .node key _ count left right =>
    (if first < key then boundedEntries first last (some key) left else []) ++
    (if inInterval first last key then [(key, count, parent)] else []) ++
    (if key < last then boundedEntries first last (some key) right else [])

private theorem parent_entry (tree : Tree K) (parent : Option K) {entry : K × Nat × Option K}
    (member : entry ∈ tree.withParents parent) : (entry.1, entry.2.1) ∈ tree.entries := by
  rw [← withParents_projection parent tree]
  exact List.mem_map_of_mem member

theorem bounded_entries_filter {K : Type} [LinearOrder K] (first last : K) (tree : Tree K)
    (ordered : tree.Ordered) (parent : Option K) :
    tree.boundedEntries first last parent = (tree.withParents parent).filter (fun row => decide (inInterval first last row.1)) := by
  induction tree generalizing parent with
  | empty => rfl
  | node key p c left right ihLeft ihRight =>
    obtain ⟨leftOrdered, rightOrdered, less, greater⟩ := ordered_node ordered
    let keep : K × Nat × Option K → Bool := fun row => decide (inInterval first last row.1)
    have leftEq : (if first < key then left.boundedEntries first last (some key) else []) =
        (left.withParents (some key)).filter keep := by
      split
      · exact ihLeft leftOrdered (some key)
      · symm
        apply List.filter_eq_nil_iff.mpr
        intro row mem
        have x : row.1 < key := less _ (parent_entry left (some key) mem)
        have belowFirst : row.1 < first := lt_of_lt_of_le x (le_of_not_gt ‹¬first < key›)
        simp [keep, inInterval, not_le_of_gt belowFirst]
    have rightEq : (if key < last then right.boundedEntries first last (some key) else []) =
        (right.withParents (some key)).filter keep := by
      split
      · exact ihRight rightOrdered (some key)
      · symm
        apply List.filter_eq_nil_iff.mpr
        intro row mem
        have x : key < row.1 := greater _ (parent_entry right (some key) mem)
        have beyond : last ≤ row.1 := le_trans (le_of_not_gt ‹¬key < last›) (le_of_lt x)
        simp [keep, inInterval, not_lt_of_ge beyond]
    change (if first < key then left.boundedEntries first last (some key) else []) ++
        (if inInterval first last key then [(key, c, parent)] else []) ++
        (if key < last then right.boundedEntries first last (some key) else []) =
      (left.withParents (some key) ++ (key, c, parent) :: right.withParents (some key)).filter keep
    rw [leftEq, rightEq, List.filter_append]
    by_cases chosen : inInterval first last key
    · have selected : keep (key, c, parent) = true := decide_eq_true chosen
      rw [ite_eq_left chosen]
      simp only [List.filter_cons, selected, ite_true, List.append_assoc, List.singleton_append]
    · have rejected : keep (key, c, parent) = false := decide_eq_false chosen
      rw [ite_eq_right chosen]
      simp only [List.filter_cons, rejected, Bool.false_eq_true, ite_false, List.append_assoc,
        List.nil_append]

theorem stored_nodes_le_elements {K : Type} (tree : Tree K)
    (positive : ∀ row ∈ tree.entries, 0 < row.2) : tree.slots ≤ tree.weight := by
  induction tree with
  | empty => exact Nat.le_refl _
  | node key p c left right ihLeft ihRight =>
    have here := positive (key, c) (List.mem_append_right _ (List.mem_cons_self ..))
    have lf := ihLeft (fun row mem => positive row (List.mem_append_left _ mem))
    have rt := ihRight (fun row mem => positive row (List.mem_append_right _ (List.mem_cons_of_mem _ mem)))
    simp only [slots, weight]
    omega

end Proofs.Cpp.TreeMultiset.Tree
