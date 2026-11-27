import Proofs.Math.TreeMultiset.Treap

namespace Proofs.Cpp.TreeMultiset.Tree

def lower [LT K] [DecidableLT K] [DecidableEq K] (query : K) : Tree K → Option K
  | .empty => none
  | .node key _ _ left right =>
    if query = key then some query
    else if query < key then lower query left
    else (lower query right).or (some key)

def upper [LT K] [DecidableLT K] [DecidableEq K] (query : K) : Tree K → Option K
  | .empty => none
  | .node key _ _ left right =>
    if query = key then some query
    else if query < key then (upper query left).or (some key)
    else upper query right

def BestBelow [LT K] [LE K] (entries : List (K × Nat)) (query : K) : Option K → Prop
  | none => ∀ row ∈ entries, query < row.1
  | some answer => (∃ count, (answer, count) ∈ entries) ∧ answer ≤ query ∧
      (∀ row ∈ entries, row.1 ≤ query → row.1 ≤ answer)

def BestAbove [LT K] [LE K] (entries : List (K × Nat)) (query : K) : Option K → Prop
  | none => ∀ row ∈ entries, row.1 < query
  | some answer => (∃ count, (answer, count) ∈ entries) ∧ query ≤ answer ∧
      (∀ row ∈ entries, query ≤ row.1 → answer ≤ row.1)

theorem lower_spec {K : Type} [LinearOrder K] (query : K) (tree : Tree K) (ordered : tree.Ordered) :
    BestBelow tree.entries query (lower query tree) := by
  induction tree with
  | empty => simp [lower, BestBelow, entries]
  | node key p c left right ihLeft ihRight =>
    obtain ⟨lo, hi, below, above⟩ := ordered_node ordered
    have node_mem : (key, c) ∈ (Tree.node key p c left right).entries :=
      List.mem_append_right _ (List.mem_cons_self ..)
    by_cases exact_key : query = key
    · subst query
      simp only [lower, ite_true]
      exact ⟨⟨c, node_mem⟩, le_rfl, fun _ _ h => h⟩
    · by_cases go : query < key
      · rw [lower, ite_eq_right exact_key, ite_eq_left go]
        have h := ihLeft lo
        cases result : lower query left with
        | none =>
          rw [result] at h
          intro row member
          rcases List.mem_append.mp member with fromLeft | rest
          · exact h row fromLeft
          · rcases List.mem_cons.mp rest with rfl | fromRight
            · exact go
            · exact lt_trans go (above row fromRight)
        | some best =>
          rw [result] at h
          obtain ⟨⟨count, found⟩, bound, optimum⟩ := h
          refine ⟨⟨count, List.mem_append_left _ found⟩, bound, ?_⟩
          intro row member possible
          rcases List.mem_append.mp member with fromLeft | rest
          · exact optimum row fromLeft possible
          · exfalso
            rcases List.mem_cons.mp rest with rfl | fromRight
            · exact (not_le_of_gt go) possible
            · exact (not_le_of_gt (lt_trans go (above row fromRight))) possible
      · have order : key < query := lt_of_le_of_ne (le_of_not_gt go) (Ne.symm exact_key)
        rw [lower, ite_eq_right exact_key, ite_eq_right go]
        have h := ihRight hi
        cases result : lower query right with
        | none =>
          rw [result] at h
          refine ⟨⟨c, node_mem⟩, le_of_lt order, ?_⟩
          intro row member possible
          rcases List.mem_append.mp member with fromLeft | rest
          · exact le_of_lt (below row fromLeft)
          · rcases List.mem_cons.mp rest with rfl | fromRight
            · exact le_rfl
            · exact False.elim ((not_le_of_gt (h row fromRight)) possible)
        | some best =>
          rw [result] at h
          obtain ⟨⟨count, found⟩, bound, optimum⟩ := h
          have bigger : key < best := above (best, count) found
          refine ⟨⟨count, List.mem_append_right _ (List.mem_cons_of_mem _ found)⟩, bound, ?_⟩
          intro row member possible
          rcases List.mem_append.mp member with fromLeft | rest
          · exact le_of_lt (lt_trans (below row fromLeft) bigger)
          · rcases List.mem_cons.mp rest with rfl | fromRight
            · exact le_of_lt bigger
            · exact optimum row fromRight possible

theorem upper_spec {K : Type} [LinearOrder K] (query : K) (tree : Tree K) (ordered : tree.Ordered) :
    BestAbove tree.entries query (upper query tree) := by
  induction tree with
  | empty => simp [upper, BestAbove, entries]
  | node key p c left right ihLeft ihRight =>
    obtain ⟨lo, hi, below, above⟩ := ordered_node ordered
    have node_mem : (key, c) ∈ (Tree.node key p c left right).entries :=
      List.mem_append_right _ (List.mem_cons_self ..)
    by_cases exact_key : query = key
    · subst query
      simp only [upper, ite_true]
      exact ⟨⟨c, node_mem⟩, le_rfl, fun _ _ h => h⟩
    · by_cases go : query < key
      · rw [upper, ite_eq_right exact_key, ite_eq_left go]
        have h := ihLeft lo
        cases result : upper query left with
        | none =>
          rw [result] at h
          refine ⟨⟨c, node_mem⟩, le_of_lt go, ?_⟩
          intro row member possible
          rcases List.mem_append.mp member with fromLeft | rest
          · exact False.elim ((not_le_of_gt (h row fromLeft)) possible)
          · rcases List.mem_cons.mp rest with rfl | fromRight
            · exact le_rfl
            · exact le_of_lt (above row fromRight)
        | some best =>
          rw [result] at h
          obtain ⟨⟨count, found⟩, bound, optimum⟩ := h
          have smaller : best < key := below (best, count) found
          refine ⟨⟨count, List.mem_append_left _ found⟩, bound, ?_⟩
          intro row member possible
          rcases List.mem_append.mp member with fromLeft | rest
          · exact optimum row fromLeft possible
          · rcases List.mem_cons.mp rest with rfl | fromRight
            · exact le_of_lt smaller
            · exact le_of_lt (lt_trans smaller (above row fromRight))
      · have order : key < query := lt_of_le_of_ne (le_of_not_gt go) (Ne.symm exact_key)
        rw [upper, ite_eq_right exact_key, ite_eq_right go]
        have h := ihRight hi
        cases result : upper query right with
        | none =>
          rw [result] at h
          intro row member
          rcases List.mem_append.mp member with fromLeft | rest
          · exact lt_trans (below row fromLeft) order
          · rcases List.mem_cons.mp rest with rfl | fromRight
            · exact order
            · exact h row fromRight
        | some best =>
          rw [result] at h
          obtain ⟨⟨count, found⟩, bound, optimum⟩ := h
          refine ⟨⟨count, List.mem_append_right _ (List.mem_cons_of_mem _ found)⟩, bound, ?_⟩
          intro row member possible
          rcases List.mem_append.mp member with fromLeft | rest
          · exact False.elim ((not_le_of_gt (lt_trans (below row fromLeft) order)) possible)
          · rcases List.mem_cons.mp rest with rfl | fromRight
            · exact False.elim ((not_le_of_gt order) possible)
            · exact optimum row fromRight possible

end Proofs.Cpp.TreeMultiset.Tree
