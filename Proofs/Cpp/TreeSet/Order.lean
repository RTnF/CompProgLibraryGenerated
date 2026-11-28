import Proofs.Cpp.TreeSet.Queries

namespace Proofs.Cpp.TreeSet.Tree

variable {K : Type} [LinearOrder K]

theorem balance_ordered (left : Tree K) (key : K) (right : Tree K)
    (lo : left.Ordered) (hi : right.Ordered)
    (below : ∀ x ∈ left.keys, x < key) (above : ∀ x ∈ right.keys, key < x) :
    (balance left key right).Ordered := by
  unfold Ordered
  rw [balance_keys, List.append_assoc, List.singleton_append]
  apply List.pairwise_append.mpr
  refine ⟨lo, List.pairwise_cons.mpr ⟨above, hi⟩, ?_⟩
  intro x hx y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact below x hx
  · exact lt_trans (below x hx) (above y hy)

theorem insert_ordered (tree : Tree K) (key : K) (ordered : tree.Ordered) :
    (tree.insert key).Ordered ∧ ∀ x, x ∈ (tree.insert key).keys ↔ x = key ∨ x ∈ tree.keys := by
  induction tree with
  | empty => simp [insert, Ordered, keys]
  | node left current right il ir =>
    obtain ⟨ol, or', below, above⟩ := ordered_node ordered
    by_cases toLeft : key < current
    · obtain ⟨newOrder, member⟩ := il ol
      simp only [insert, ite_eq_left toLeft]
      refine ⟨balance_ordered _ _ _ newOrder or' ?_ above, ?_⟩
      · intro x hx
        rcases (member x).mp hx with rfl | hx
        · exact toLeft
        · exact below x hx
      · intro x
        simp only [balance_keys, keys, List.mem_append, List.mem_singleton, member]
        simp [or_assoc, or_left_comm, or_comm]
    · by_cases toRight : current < key
      · obtain ⟨newOrder, member⟩ := ir or'
        simp only [insert, ite_eq_right toLeft, ite_eq_left toRight]
        refine ⟨balance_ordered _ _ _ ol newOrder below ?_, ?_⟩
        · intro x hx
          rcases (member x).mp hx with rfl | hx
          · exact toRight
          · exact above x hx
        · intro x
          simp only [balance_keys, keys, List.mem_append, List.mem_singleton, member]
          simp [or_assoc, or_left_comm, or_comm]
      · have eq : key = current := le_antisymm (le_of_not_gt toRight) (le_of_not_gt toLeft)
        simp only [insert, ite_eq_right toLeft, ite_eq_right toRight]
        refine ⟨ordered, fun x => ⟨Or.inr, ?_⟩⟩
        rintro (rfl | existing)
        · simp [keys, eq]
        · exact existing

theorem erase_ordered (tree : Tree K) (key : K) (ordered : tree.Ordered) (balanced : tree.Balanced) :
    (tree.erase key).keys = tree.keys.filter (fun x => decide (x ≠ key)) ∧ (tree.erase key).Ordered := by
  suffices equality : (tree.erase key).keys = tree.keys.filter (fun x => decide (x ≠ key)) by
    refine ⟨equality, ?_⟩
    unfold Ordered
    rw [equality]
    exact ordered.sublist List.filter_sublist
  induction tree with
  | empty => rfl
  | node left current right il ir =>
    obtain ⟨ol, or', below, above⟩ := ordered_node ordered
    obtain ⟨lb, rb, _, _⟩ := balanced
    by_cases toLeft : key < current
    · have ignoreRight : right.keys.filter (fun x => decide (x ≠ key)) = right.keys := by
        apply List.filter_eq_self.mpr
        intro x hx
        exact decide_eq_true_eq.mpr (ne_of_gt (lt_trans toLeft (above x hx)))
      simp only [erase, ite_eq_left toLeft, balance_keys, il ol lb, keys, List.filter_append, ignoreRight]
      simp [ne_of_gt toLeft]
    · by_cases toRight : current < key
      · have ignoreLeft : left.keys.filter (fun x => decide (x ≠ key)) = left.keys := by
          apply List.filter_eq_self.mpr
          intro x hx
          exact decide_eq_true_eq.mpr (ne_of_lt (lt_trans (below x hx) toRight))
        simp only [erase, ite_eq_right toLeft, ite_eq_left toRight, balance_keys, ir or' rb, keys, List.filter_append, ignoreLeft]
        simp [ne_of_lt toRight]
      · have equal : key = current := le_antisymm (le_of_not_gt toRight) (le_of_not_gt toLeft)
        have noLeft : left.keys.filter (fun x => decide (x ≠ key)) = left.keys := by
          apply List.filter_eq_self.mpr
          intro x hx
          exact decide_eq_true_eq.mpr (ne_of_lt (equal ▸ below x hx))
        have noRight : right.keys.filter (fun x => decide (x ≠ key)) = right.keys := by
          apply List.filter_eq_self.mpr
          intro x hx
          exact decide_eq_true_eq.mpr (ne_of_gt (equal ▸ above x hx))
        have target : (Tree.node left current right).keys.filter (fun x => decide (x ≠ key)) =
            left.keys ++ right.keys := by
          simp only [keys, List.filter_append, noLeft, noRight]
          simp [equal]
        rw [target]
        simp only [erase, ite_eq_right toLeft, ite_eq_right toRight]
        cases left with
        | empty => rfl
        | node ll lk lr =>
          cases right with
          | empty => simp [extractMin, keys]
          | node rl rk rr =>
            obtain ⟨first, replacement, value, _, _, _, listing⟩ :=
              extract_balanced (.node rl rk rr) rb (by simp)
            rw [value, balance_keys, listing, List.append_assoc, List.singleton_append]

end Proofs.Cpp.TreeSet.Tree
