import Proofs.Math.TreeMultiset.TreapSelection

namespace Proofs.Cpp.TreeMultiset.Tree

def closedKeys [LinearOrder K] (lo hi : K) : Tree K → List K
  | .empty => []
  | .node key _ count left right =>
    (if lo < key then left.closedKeys lo hi else []) ++
    (if lo ≤ key ∧ key ≤ hi then List.replicate count key else []) ++
    (if key < hi then right.closedKeys lo hi else [])

private theorem member_expanded_key {K : Type} (tree : Tree K) (key : K) (mem : key ∈ tree.expanded) :
    ∃ count, (key, count) ∈ tree.entries := by
  unfold expanded at mem
  obtain ⟨entry, source, found⟩ := List.mem_flatMap.mp mem
  have eq := (List.mem_replicate.mp found).2
  rcases entry with ⟨value, count⟩
  simp only at eq
  cases eq
  exact ⟨count, source⟩

private theorem filter_repeat {K : Type} (keep : K → Bool) (key : K) (count : Nat) :
    (List.replicate count key).filter keep = if keep key then List.replicate count key else [] := by
  induction count with
  | zero => simp
  | succ count ih =>
    cases h : keep key <;> simp [List.replicate_succ, ih, h]

theorem closedKeys_filter {K : Type} [LinearOrder K] (lo hi : K) (tree : Tree K) (ordered : tree.Ordered) :
    tree.closedKeys lo hi = tree.expanded.filter (fun key => decide (lo ≤ key ∧ key ≤ hi)) := by
  induction tree with
  | empty => rfl
  | node key priority count left right ihLeft ihRight =>
    obtain ⟨leftOrdered, rightOrdered, less, greater⟩ := ordered_node ordered
    let keep : K → Bool := fun key => decide (lo ≤ key ∧ key ≤ hi)
    have leftEq : (if lo < key then left.closedKeys lo hi else []) = left.expanded.filter keep := by
      by_cases descend : lo < key
      · rw [ite_eq_left descend]
        exact ihLeft leftOrdered
      · rw [ite_eq_right descend]
        symm
        apply List.filter_eq_nil_iff.mpr
        intro neighbour mem
        obtain ⟨n, row⟩ := member_expanded_key left neighbour mem
        have below := less (neighbour, n) row
        intro accepted
        have bounded : lo ≤ neighbour ∧ neighbour ≤ hi := of_decide_eq_true accepted
        exact descend (lt_of_le_of_lt bounded.1 below)
    have rightEq : (if key < hi then right.closedKeys lo hi else []) = right.expanded.filter keep := by
      by_cases descend : key < hi
      · rw [ite_eq_left descend]
        exact ihRight rightOrdered
      · rw [ite_eq_right descend]
        symm
        apply List.filter_eq_nil_iff.mpr
        intro neighbour mem
        obtain ⟨n, row⟩ := member_expanded_key right neighbour mem
        have above := greater (neighbour, n) row
        intro accepted
        have bounded : lo ≤ neighbour ∧ neighbour ≤ hi := of_decide_eq_true accepted
        exact descend (lt_of_lt_of_le above bounded.2)
    change (if lo < key then left.closedKeys lo hi else []) ++
      (if lo ≤ key ∧ key ≤ hi then List.replicate count key else []) ++
      (if key < hi then right.closedKeys lo hi else []) =
        (Tree.node key priority count left right).expanded.filter keep
    rw [expanded_node, List.filter_append, List.filter_append, leftEq, rightEq, filter_repeat]
    by_cases selected : lo ≤ key ∧ key ≤ hi <;> simp [keep, selected, List.append_assoc]

end Proofs.Cpp.TreeMultiset.Tree
