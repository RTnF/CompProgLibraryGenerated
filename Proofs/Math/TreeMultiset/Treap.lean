import Mathlib.Order.Basic

namespace Proofs.Cpp.TreeMultiset

inductive Tree (K : Type) where
  | empty
  | node (key : K) (priority : UInt64) (count : Nat) (left right : Tree K)
  deriving Inhabited

namespace Tree

def slots : Tree K → Nat
  | .empty => 0
  | .node _ _ _ left right => 1 + slots left + slots right

def weight : Tree K → Nat
  | .empty => 0
  | .node _ _ count left right => count + weight left + weight right

def entries : Tree K → List (K × Nat)
  | .empty => []
  | .node key _ count left right => entries left ++ (key, count) :: entries right

def withParents (parent : Option K) : Tree K → List (K × Nat × Option K)
  | .empty => []
  | .node key _ count left right =>
    withParents (some key) left ++ (key, count, parent) :: withParents (some key) right

def split [LT K] [DecidableLT K] (pivot : K) : Tree K → Tree K × Tree K
  | .empty => (.empty, .empty)
  | .node key p c left right =>
    if pivot < key then
      let (lower, upper) := split pivot left
      (lower, .node key p c upper right)
    else
      let (lower, upper) := split pivot right
      (.node key p c left lower, upper)

def merge (left right : Tree K) : Tree K :=
  match left, right with
  | .empty, r => r
  | l, .empty => l
  | .node kl pl cl ll lr, .node kr pr cr rl rr =>
    if pr < pl then
      .node kl pl cl ll (merge lr (.node kr pr cr rl rr))
    else
      .node kr pr cr (merge (.node kl pl cl ll lr) rl) rr
termination_by left.slots + right.slots
decreasing_by all_goals simp [slots]; omega

def insert [LT K] [DecidableLT K] (key : K) (priority : UInt64) (count : Nat) :
    Tree K → Tree K
  | .empty => .node key priority count .empty .empty
  | .node old p c left right =>
    if p < priority then
      let (lower, upper) := split key (.node old p c left right)
      .node key priority count lower upper
    else if key < old then
      .node old p c (insert key priority count left) right
    else
      .node old p c left (insert key priority count right)

def erase [LT K] [DecidableLT K] [DecidableEq K] (key : K) : Tree K → Tree K
  | .empty => .empty
  | .node old p c left right =>
    if key = old then merge left right
    else if key < old then .node old p c (erase key left) right
    else .node old p c left (erase key right)

def lookup [LT K] [DecidableLT K] [DecidableEq K] (key : K) : Tree K → Option Nat
  | .empty => none
  | .node old _ c left right =>
    if key = old then some c
    else if key < old then lookup key left
    else lookup key right

def changeCount [LT K] [DecidableLT K] [DecidableEq K] (key : K) (f : Nat → Nat) : Tree K → Tree K
  | .empty => .empty
  | .node old p count left right =>
    if key = old then .node old p (f count) left right
    else if key < old then .node old p count (changeCount key f left) right
    else .node old p count left (changeCount key f right)

theorem split_entries [LT K] [DecidableLT K] (pivot : K) (tree : Tree K) :
    (split pivot tree).1.entries ++ (split pivot tree).2.entries = tree.entries := by
  induction tree with
  | empty => rfl
  | node key p count left right ihLeft ihRight =>
    by_cases route : pivot < key
    · simp only [split, ite_eq_left route, entries]
      rw [← List.append_assoc, ihLeft]
    · simp only [split, ite_eq_right route, entries, List.append_assoc, List.cons_append]
      rw [ihRight]

theorem merge_entries (left right : Tree K) : (merge left right).entries = left.entries ++ right.entries := by
  induction left, right using merge.induct with
  | case1 right => rw [merge]; rfl
  | case2 left nonempty =>
    cases left <;> simp [merge, entries]
  | case3 kl pl cl ll lr kr pr cr rl rr h ih =>
    rw [merge]
    simp [h, entries, ih, List.append_assoc]
  | case4 kl pl cl ll lr kr pr cr rl rr h ih =>
    rw [merge]
    simp [h, entries, ih, List.append_assoc]

theorem withParents_projection (parent : Option K) (tree : Tree K) :
    (tree.withParents parent).map (fun item => (item.1, item.2.1)) = tree.entries := by
  induction tree generalizing parent with
  | empty => rfl
  | node key p count left right ihLeft ihRight =>
    simp [entries, withParents, ihLeft, ihRight]

theorem weight_entries (tree : Tree K) :
    tree.weight = (tree.entries.map Prod.snd).sum := by
  induction tree with
  | empty => rfl
  | node key p count left right ihLeft ihRight =>
    simp [weight, entries, ihLeft, ihRight]
    omega

def Ordered (tree : Tree K) [LT K] : Prop :=
  tree.entries.Pairwise (fun a b => a.1 < b.1)

theorem ordered_node {K : Type} [LT K] {key : K} {priority : UInt64} {count : Nat} {left right : Tree K}
    (ordered : (Tree.node key priority count left right).Ordered) :
    left.Ordered ∧ right.Ordered ∧
      (∀ item ∈ left.entries, item.1 < key) ∧ (∀ item ∈ right.entries, key < item.1) := by
  unfold Ordered at *
  simp only [entries] at ordered
  obtain ⟨lo, hi, relation⟩ := List.pairwise_append.mp ordered
  have rest := List.pairwise_cons.mp hi
  exact ⟨lo, rest.2, fun item mem => relation item mem (key, count) (List.mem_cons_self ..), rest.1⟩

theorem split_bounds {K : Type} [LinearOrder K] (pivot : K) (tree : Tree K) (ordered : tree.Ordered) :
    (∀ item ∈ (split pivot tree).1.entries, item.1 ≤ pivot) ∧
    (∀ item ∈ (split pivot tree).2.entries, pivot < item.1) := by
  induction tree with
  | empty => simp [split, entries]
  | node key p count left right ihLeft ihRight =>
    obtain ⟨lo, hi, leftOf, rightOf⟩ := ordered_node ordered
    by_cases h : pivot < key
    · have splitLeft := ihLeft lo
      simp only [split, ite_eq_left h] at *
      refine ⟨splitLeft.1, ?_⟩
      intro item mem
      rcases List.mem_append.mp mem with fromLeft | fromNode
      · exact splitLeft.2 item fromLeft
      · rcases List.mem_cons.mp fromNode with rfl | fromRight
        · exact h
        · exact lt_trans h (rightOf item fromRight)
    · have splitRight := ihRight hi
      simp only [split, ite_eq_right h] at *
      refine ⟨?_, splitRight.2⟩
      intro item mem
      rcases List.mem_append.mp mem with fromLeft | fromNode
      · exact le_trans (le_of_lt (leftOf item fromLeft)) (le_of_not_gt h)
      · rcases List.mem_cons.mp fromNode with rfl | fromRight
        · exact le_of_not_gt h
        · exact splitRight.1 item fromRight

theorem split_ordered {K : Type} [LinearOrder K] (pivot : K) (tree : Tree K) (ordered : tree.Ordered) :
    (split pivot tree).1.Ordered ∧ (split pivot tree).2.Ordered := by
  have sorted : ((split pivot tree).1.entries ++ (split pivot tree).2.entries).Pairwise
      (fun a b => a.1 < b.1) := by
    rw [split_entries]
    exact ordered
  have h := List.pairwise_append.mp sorted
  exact ⟨h.1, h.2.1⟩

theorem merge_ordered {K : Type} [LinearOrder K] (left right : Tree K) (lo : left.Ordered) (hi : right.Ordered)
    (separated : ∀ a ∈ left.entries, ∀ b ∈ right.entries, a.1 < b.1) :
    (merge left right).Ordered := by
  unfold Ordered
  rw [merge_entries]
  exact List.pairwise_append.mpr ⟨lo, hi, separated⟩

theorem insert_entries {K : Type} [LT K] [DecidableLT K] (key : K) (priority : UInt64) (count : Nat)
    (tree : Tree K) : (insert key priority count tree).entries.Perm ((key, count) :: tree.entries) := by
  induction tree with
  | empty => exact List.Perm.refl _
  | node old p c left right ihLeft ihRight =>
    by_cases higher : p < priority
    · simp only [insert, ite_eq_left higher, entries]
      apply (List.perm_cons_append_cons (key, count) _).symm
      exact List.Perm.of_eq (split_entries key (Tree.node old p c left right)).symm
    · by_cases go : key < old
      · simp only [insert, ite_eq_right higher, ite_eq_left go, entries]
        exact ihLeft.append_right _
      · simp only [insert, ite_eq_right higher, ite_eq_right go, entries]
        refine ((ihRight.cons (old, c)).append_left left.entries).trans ?_
        simpa [List.append_assoc] using
          (List.perm_middle (a := (key, count)) (l₁ := left.entries ++ [(old, c)]) (l₂ := right.entries))

private theorem node_ordered {K : Type} [LinearOrder K] {key : K} {p : UInt64} {c : Nat} {left right : Tree K}
    (lo : left.Ordered) (hi : right.Ordered) (less : ∀ item ∈ left.entries, item.1 < key)
    (greater : ∀ item ∈ right.entries, key < item.1) : (Tree.node key p c left right).Ordered := by
  unfold Ordered
  simp only [entries, List.pairwise_append, List.pairwise_cons]
  refine ⟨lo, ⟨greater, hi⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with rfl | rest
  · exact less a ha
  · exact lt_trans (less a ha) (greater b rest)

theorem insert_ordered {K : Type} [LinearOrder K] (key : K) (priority : UInt64) (count : Nat) (tree : Tree K)
    (ordered : tree.Ordered) (absent : ∀ item ∈ tree.entries, key ≠ item.1) :
    (insert key priority count tree).Ordered := by
  induction tree with
  | empty => simp [insert, Ordered, entries]
  | node old p c left right ihLeft ihRight =>
    have orig := ordered
    obtain ⟨lo, hi, below, above⟩ := ordered_node ordered
    have leftIn (item : K × Nat) (h : item ∈ left.entries) : item ∈ (Tree.node old p c left right).entries :=
      List.mem_append_left _ h
    have rightIn (item : K × Nat) (h : item ∈ right.entries) : item ∈ (Tree.node old p c left right).entries :=
      List.mem_append_right _ (List.mem_cons_of_mem _ h)
    by_cases higher : p < priority
    · let oldTree := Tree.node old p c left right
      have slopes := split_bounds key oldTree orig
      have splitSorted := split_ordered key oldTree orig
      have strict (item : K × Nat) (h : item ∈ (split key oldTree).1.entries) : item.1 < key := by
        have joined : item ∈ (split key oldTree).1.entries ++ (split key oldTree).2.entries :=
          List.mem_append_left _ h
        rw [split_entries] at joined
        exact lt_of_le_of_ne (slopes.1 item h) (Ne.symm (absent item joined))
      simp only [insert, ite_eq_left higher]
      exact node_ordered splitSorted.1 splitSorted.2 strict slopes.2
    · by_cases go : key < old
      · simp only [insert, ite_eq_right higher, ite_eq_left go]
        refine node_ordered (ihLeft lo (fun item h => absent item (leftIn item h))) hi ?_ above
        intro item member
        rcases List.mem_cons.mp ((insert_entries key priority count left).mem_iff.mp member) with rfl | rest
        · exact go
        · exact below item rest
      · simp only [insert, ite_eq_right higher, ite_eq_right go]
        refine node_ordered lo (ihRight hi (fun item h => absent item (rightIn item h))) below ?_
        intro item member
        rcases List.mem_cons.mp ((insert_entries key priority count right).mem_iff.mp member) with rfl | rest
        · have distinct : key ≠ old := absent (old, c)
            (List.mem_append_right _ (List.mem_cons_self ..))
          exact lt_of_le_of_ne (le_of_not_gt go) (Ne.symm distinct)
        · exact above item rest

theorem lookup_spec {K : Type} [LinearOrder K] (key : K) (tree : Tree K) (ordered : tree.Ordered) (count : Nat) :
    lookup key tree = some count ↔ (key, count) ∈ tree.entries := by
  induction tree with
  | empty => simp [lookup, entries]
  | node old p c left right ihLeft ihRight =>
    obtain ⟨lo, hi, below, above⟩ := ordered_node ordered
    have leftAbsent (h : old ≤ key) : (key, count) ∉ left.entries :=
      fun mem => (not_lt_of_ge h) (below (key, count) mem)
    have rightAbsent (h : key ≤ old) : (key, count) ∉ right.entries :=
      fun mem => (not_lt_of_ge h) (above (key, count) mem)
    by_cases equal : key = old
    · subst old
      simp [lookup, entries, leftAbsent le_rfl, rightAbsent le_rfl, eq_comm]
    · by_cases go : key < old
      · simp [lookup, entries, equal, go, rightAbsent (le_of_lt go), ihLeft lo]
      · simp [lookup, entries, equal, go, leftAbsent (le_of_not_gt go), ihRight hi]

theorem erase_entries {K : Type} [LinearOrder K] (key : K) (tree : Tree K) (ordered : tree.Ordered) :
    (erase key tree).entries = tree.entries.filter (fun item => !decide (item.1 = key)) := by
  induction tree with
  | empty => rfl
  | node old p c left right ihLeft ihRight =>
    obtain ⟨lo, hi, below, above⟩ := ordered_node ordered
    have filterLeft (h : old ≤ key) :
        left.entries.filter (fun item => !decide (item.1 = key)) = left.entries := by
      apply List.filter_eq_self.mpr
      intro item mem
      simpa using (ne_of_lt (lt_of_lt_of_le (below item mem) h))
    have filterRight (h : key ≤ old) :
        right.entries.filter (fun item => !decide (item.1 = key)) = right.entries := by
      apply List.filter_eq_self.mpr
      intro item mem
      simpa using (ne_of_gt (lt_of_le_of_lt h (above item mem)))
    by_cases equal : key = old
    · subst old
      simp [erase, entries, merge_entries, List.filter_append, filterLeft le_rfl, filterRight le_rfl]
    · have keep : old ≠ key := Ne.symm equal
      by_cases go : key < old
      · simp [erase, entries, equal, keep, go, List.filter_append, filterRight (le_of_lt go), ihLeft lo]
      · simp [erase, entries, equal, keep, go, List.filter_append, filterLeft (le_of_not_gt go), ihRight hi]

theorem erase_ordered {K : Type} [LinearOrder K] (key : K) (tree : Tree K) (ordered : tree.Ordered) :
    (erase key tree).Ordered := by
  unfold Ordered
  rw [erase_entries key tree ordered]
  exact ordered.sublist List.filter_sublist

end Tree
end Proofs.Cpp.TreeMultiset
