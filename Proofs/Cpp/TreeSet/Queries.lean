import Proofs.Cpp.TreeSet.Updates

namespace Proofs.Cpp.TreeSet.Tree

def select (index : Nat) : Tree K → Option K
  | .empty => none
  | .node left key right =>
    if index < left.size then left.select index
    else if index = left.size then some key
    else right.select (index - left.size - 1)

def rank [LT K] [DecidableLT K] (key : K) : Tree K → Option Nat
  | .empty => none
  | .node left current right =>
    if key < current then left.rank key
    else if current < key then (right.rank key).map (fun i => left.size + 1 + i)
    else some left.size

def selectVisits (index : Nat) : Tree K → Nat
  | .empty => 0
  | .node left _ right =>
    if index < left.size then 1 + left.selectVisits index
    else if index = left.size then 1
    else 1 + right.selectVisits (index - left.size - 1)

def rankVisits [LT K] [DecidableLT K] (key : K) : Tree K → Nat
  | .empty => 0
  | .node left current right =>
    if key < current then 1 + left.rankVisits key
    else if current < key then 1 + right.rankVisits key
    else 1

theorem select_visits_le_height (tree : Tree K) (index : Nat) : tree.selectVisits index ≤ tree.height := by
  induction tree generalizing index with
  | empty => simp [selectVisits, height]
  | node left k right il ir =>
    simp only [selectVisits, height]
    split
    · have := il index
      omega
    split
    · omega
    · have := ir (index - left.size - 1)
      omega

theorem rank_visits_le_height [LT K] [DecidableLT K] (tree : Tree K) (key : K) :
    tree.rankVisits key ≤ tree.height := by
  induction tree with
  | empty => simp [rankVisits, height]
  | node left current right il ir =>
    simp only [rankVisits, height]
    split
    · omega
    split <;> omega

theorem select_correct (tree : Tree K) (index : Nat) :
    tree.select index = tree.keys[index]? := by
  induction tree generalizing index with
  | empty => rfl
  | node left key right il ir =>
    simp only [select, keys, List.append_assoc]
    by_cases earlier : index < left.size
    · rw [ite_eq_left earlier, il, List.getElem?_append_left (by rwa [size_keys])]
    · rw [ite_eq_right earlier, List.getElem?_append_right (by rw [size_keys]; omega), size_keys]
      by_cases same : index = left.size
      · simp [same]
      · have offset : index - left.size = (index - left.size - 1) + 1 := by omega
        rw [ite_eq_right same, ir]
        change right.keys[index - left.size - 1]? = (key :: right.keys)[index - left.size]?
        calc
          _ = (key :: right.keys)[(index - left.size - 1) + 1]? := List.getElem?_cons_succ.symm
          _ = _ := congrArg (fun j => (key :: right.keys)[j]?) offset.symm

def Ordered [LT K] (tree : Tree K) : Prop := tree.keys.Pairwise (· < ·)

theorem ordered_node [LT K] {left right : Tree K} {key : K}
    (ordered : (Tree.node left key right).Ordered) :
    left.Ordered ∧ right.Ordered ∧ (∀ k ∈ left.keys, k < key) ∧ (∀ k ∈ right.keys, key < k) := by
  simp only [Ordered, keys, List.append_assoc, List.singleton_append] at ordered
  obtain ⟨leftOrder, rightOrder, cross⟩ := List.pairwise_append.mp ordered
  obtain ⟨front, tail⟩ := List.pairwise_cons.mp rightOrder
  exact ⟨leftOrder, tail, fun k hk => cross k hk key (by simp), front⟩

section Ordered

variable {K : Type} [LinearOrder K]

theorem rank_absent (key : K) (tree : Tree K) (ordered : tree.Ordered) :
    tree.rank key = none ↔ key ∉ tree.keys := by
  induction tree with
  | empty => simp [rank, keys]
  | node left current right il ir =>
    obtain ⟨ol, or', lo, hi⟩ := ordered_node ordered
    simp only [rank, keys, List.append_assoc, List.mem_append, List.mem_cons]
    by_cases smaller : key < current
    · have absent : key ∉ right.keys := fun inRight => (lt_asymm smaller (hi key inRight))
      simp [smaller, il ol, ne_of_lt smaller, absent]
    · by_cases larger : current < key
      · have absent : key ∉ left.keys := fun inLeft => (lt_asymm larger (lo key inLeft))
        simp [smaller, larger, ne_of_gt larger, absent, ir or']
      · have eq : key = current := le_antisymm (le_of_not_gt larger) (le_of_not_gt smaller)
        simp [eq]

theorem rank_positions (key : K) (tree : Tree K) (ordered : tree.Ordered) {index : Nat}
    (found : tree.rank key = some index) :
    tree.keys[index]? = some key ∧ (tree.keys.filter (fun k => decide (k < key))).length = index := by
  induction tree generalizing index with
  | empty => simp [rank] at found
  | node left current right il ir =>
    obtain ⟨ol, or', lo, hi⟩ := ordered_node ordered
    have noRight (notAbove : ¬ current < key) : right.keys.filter (fun k => decide (k < key)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro k hk
      exact fun h => notAbove (lt_trans (hi k hk) (of_decide_eq_true h))
    have allLeft (above : ¬ key < current) : left.keys.filter (fun k => decide (k < key)) = left.keys := by
      apply List.filter_eq_self.mpr
      intro k hk
      exact decide_eq_true_eq.mpr (lt_of_lt_of_le (lo k hk) (le_of_not_gt above))
    by_cases smaller : key < current
    · simp only [rank, smaller, ite_true] at found
      have part := il ol found
      have inLeft : index < left.size := by
        rw [← size_keys]
        exact List.getElem?_eq_some_iff.mp part.1 |>.1
      constructor
      · simpa only [keys, List.append_assoc, List.getElem?_append_left (by rwa [size_keys])] using part.1
      · simp [keys, part.2, not_lt_of_gt smaller, noRight (not_lt_of_gt smaller)]
    · by_cases larger : current < key
      · simp only [rank, smaller, larger, ite_false, ite_true] at found
        cases hr : right.rank key with
        | none => simp [hr] at found
        | some i =>
          have ref : left.size + 1 + i = index := by simpa [hr] using found
          subst index
          obtain ⟨located, cardinal⟩ := ir or' hr
          constructor
          · rw [keys, List.append_assoc, List.getElem?_append_right (by rw [size_keys]; omega), size_keys]
            have offset : left.size + 1 + i - left.size = i + 1 := by omega
            simpa [offset] using located
          · simp [keys, larger, allLeft smaller, cardinal, size_keys]
            omega
      · have eq : key = current := le_antisymm (le_of_not_gt larger) (le_of_not_gt smaller)
        have ref : left.size = index := by simpa [rank, smaller, larger] using found
        subst index
        constructor
        · rw [keys, List.append_assoc, List.getElem?_append_right (by rw [size_keys]; exact Nat.le_refl _), size_keys]
          simp [eq]
        · simp [keys, larger, size_keys, allLeft smaller, noRight larger]

theorem rank_logarithmic (tree : Tree K) (valid : tree.Balanced) (key : K) :
    tree.rankVisits key ≤ 2 * (tree.size + 1).log2 + 1 :=
  Nat.le_trans (rank_visits_le_height tree key) (height_logarithmic tree valid)

omit [LinearOrder K] in
theorem select_logarithmic (tree : Tree K) (valid : tree.Balanced) (index : Nat) :
    tree.selectVisits index ≤ 2 * (tree.size + 1).log2 + 1 :=
  Nat.le_trans (select_visits_le_height tree index) (height_logarithmic tree valid)

end Ordered
end Proofs.Cpp.TreeSet.Tree
