import Proofs.Math.TreeMultiset.Treap

namespace Proofs.Cpp.TreeMultiset.Tree

def expanded (tree : Tree K) : List K :=
  tree.entries.flatMap (fun row => List.replicate row.2 row.1)

theorem expanded_node (key : K) (p : UInt64) (c : Nat) (left right : Tree K) :
    (Tree.node key p c left right).expanded = left.expanded ++ List.replicate c key ++ right.expanded := by
  simp [expanded, entries, List.append_assoc]

theorem expanded_length (tree : Tree K) : tree.expanded.length = tree.weight := by
  induction tree with
  | empty => rfl
  | node key p c left right ihLeft ihRight =>
    rw [expanded_node]
    simp [weight, ihLeft, ihRight]
    omega

def select (position : Nat) : Tree K → Option K
  | .empty => none
  | .node key _ c left right =>
    if position < left.weight then select position left
    else if position < left.weight + c then some key
    else select (position - left.weight - c) right

theorem select_expanded (position : Nat) (tree : Tree K) :
    select position tree = tree.expanded[position]? := by
  induction tree generalizing position with
  | empty => rfl
  | node key p c left right ihLeft ihRight =>
    rw [expanded_node, List.append_assoc]
    by_cases inLeft : position < left.weight
    · rw [select, ite_eq_left inLeft, ihLeft, List.getElem?_append_left]
      rwa [expanded_length]
    · have outside : left.expanded.length ≤ position := by rw [expanded_length]; omega
      rw [select, ite_eq_right inLeft, List.getElem?_append_right outside, expanded_length]
      by_cases equal : position < left.weight + c
      · rw [ite_eq_left equal, List.getElem?_append_left]
        · simp only [List.getElem?_replicate, ite_eq_left (show position - left.weight < c by omega)]
        · simp only [List.length_replicate]
          omega
      · have outsideCopies : (List.replicate c key).length ≤ position - left.weight := by simp; omega
        rw [ite_eq_right equal, List.getElem?_append_right outsideCopies, List.length_replicate, ihRight]

def rankBounds [LT K] [DecidableLT K] [DecidableEq K] (key : K) : Tree K → Option (Nat × Nat)
  | .empty => none
  | .node old _ c left right =>
    if key = old then some (left.weight, left.weight + c)
    else if key < old then rankBounds key left
    else (rankBounds key right).map (fun bounds => (left.weight + c + bounds.1, left.weight + c + bounds.2))

theorem rank_exists_iff_lookup {K : Type} [LT K] [DecidableLT K] [DecidableEq K] (key : K) (tree : Tree K) :
    (rankBounds key tree).isSome = (lookup key tree).isSome := by
  induction tree with
  | empty => rfl
  | node old p c left right ihLeft ihRight =>
    by_cases equal : key = old
    · simp [rankBounds, lookup, equal]
    · by_cases go : key < old
      · simp [rankBounds, lookup, equal, go, ihLeft]
      · simp [rankBounds, lookup, equal, go, ihRight]

theorem rank_span {K : Type} [LT K] [DecidableLT K] [DecidableEq K] (key : K) (tree : Tree K) :
    ∀ lo hi, rankBounds key tree = some (lo, hi) → lookup key tree = some (hi - lo) := by
  induction tree with
  | empty => simp [rankBounds]
  | node old p c left right ihLeft ihRight =>
    intro lo hi rank
    by_cases equal : key = old
    · simp only [rankBounds, ite_eq_left equal, Option.some.injEq, Prod.mk.injEq] at rank
      simp [lookup, equal, ← rank.1, ← rank.2]
    · by_cases go : key < old
      · simp only [rankBounds, lookup, ite_eq_right equal, ite_eq_left go] at rank ⊢
        exact ihLeft lo hi rank
      · simp only [rankBounds, lookup, ite_eq_right equal, ite_eq_right go] at rank ⊢
        cases source : rankBounds key right with
        | none => simp [source] at rank
        | some bounds =>
          rcases bounds with ⟨lower, upper⟩
          simp only [source, Option.map_some, Option.some.injEq, Prod.mk.injEq] at rank
          rw [ihRight lower upper source]
          congr 1
          omega

theorem rank_in_bounds {K : Type} [LT K] [DecidableLT K] [DecidableEq K] (key : K) (tree : Tree K) :
    ∀ lo hi, rankBounds key tree = some (lo, hi) → lo ≤ hi ∧ hi ≤ tree.weight := by
  induction tree with
  | empty => simp [rankBounds]
  | node old p c left right ihLeft ihRight =>
    intro lo hi rank
    by_cases equal : key = old
    · simp only [rankBounds, ite_eq_left equal, Option.some.injEq, Prod.mk.injEq] at rank
      simp only [weight]
      omega
    · by_cases go : key < old
      · simp only [rankBounds, ite_eq_right equal, ite_eq_left go] at rank
        obtain ⟨start, finish⟩ := ihLeft lo hi rank
        simp only [weight]
        omega
      · simp only [rankBounds, ite_eq_right equal, ite_eq_right go] at rank
        cases source : rankBounds key right with
        | none => simp [source] at rank
        | some bounds =>
          rcases bounds with ⟨lower, upper⟩
          simp only [source, Option.map_some, Option.some.injEq, Prod.mk.injEq] at rank
          obtain ⟨start, finish⟩ := ihRight lower upper source
          simp only [weight]
          omega

theorem selected_key {tree : Tree K} {position : Nat} {key : K} (found : select position tree = some key) :
    ∃ c, (key, c) ∈ tree.entries := by
  rw [select_expanded] at found
  have mem := List.mem_of_getElem? found
  obtain ⟨⟨item, count⟩, entry, copies⟩ := List.mem_flatMap.mp mem
  have eq := (List.mem_replicate.mp copies).2
  cases eq
  exact ⟨count, entry⟩

theorem rank_positions {K : Type} [LinearOrder K] (key : K) (tree : Tree K) (sorted : tree.Ordered) :
    ∀ lo hi, rankBounds key tree = some (lo, hi) →
      ∀ position, select position tree = some key ↔ lo ≤ position ∧ position < hi := by
  induction tree with
  | empty => simp [rankBounds]
  | node old p c left right ihLeft ihRight =>
    intro lo hi rank position
    obtain ⟨leftOrdered, rightOrdered, leftOf, rightOf⟩ := ordered_node sorted
    have mayLeft (found : select position left = some key) : key < old := by
      obtain ⟨count, entry⟩ := selected_key found
      exact leftOf (key, count) entry
    have mayRight (i : Nat) (found : select i right = some key) : old < key := by
      obtain ⟨count, entry⟩ := selected_key found
      exact rightOf (key, count) entry
    by_cases equal : key = old
    · subst old
      simp only [rankBounds, ite_true, Option.some.injEq, Prod.mk.injEq] at rank
      simp only [select]
      by_cases inLeft : position < left.weight
      · rw [ite_eq_left inLeft]
        have missing : select position left ≠ some key := fun found => (lt_irrefl _) (mayLeft found)
        have outside : ¬(lo ≤ position ∧ position < hi) := by omega
        simp [missing, outside]
      · rw [ite_eq_right inLeft]
        by_cases inKey : position < left.weight + c
        · rw [ite_eq_left inKey]
          have inside : lo ≤ position ∧ position < hi := by omega
          simp [inside]
        · rw [ite_eq_right inKey]
          have missing : select (position - left.weight - c) right ≠ some key :=
            fun found => (lt_irrefl _) (mayRight _ found)
          have outside : ¬(lo ≤ position ∧ position < hi) := by omega
          simp [missing, outside]
    · by_cases go : key < old
      · simp only [rankBounds, ite_eq_right equal, ite_eq_left go] at rank
        have limits := rank_in_bounds key left lo hi rank
        simp only [select]
        by_cases inLeft : position < left.weight
        · rw [ite_eq_left inLeft]
          exact ihLeft leftOrdered lo hi rank position
        · rw [ite_eq_right inLeft]
          by_cases inKey : position < left.weight + c
          · rw [ite_eq_left inKey]
            have other : some old ≠ some key := fun h => equal (Option.some.inj h).symm
            have outside : ¬(lo ≤ position ∧ position < hi) := by omega
            simp only [other, outside]
          · rw [ite_eq_right inKey]
            have other : select (position - left.weight - c) right ≠ some key :=
              fun found => (not_lt_of_ge (le_of_lt go)) (mayRight _ found)
            have outside : ¬(lo ≤ position ∧ position < hi) := by omega
            simp only [other, outside]
      · simp only [rankBounds, ite_eq_right equal, ite_eq_right go] at rank
        cases source : rankBounds key right with
        | none => simp [source] at rank
        | some bounds =>
          rcases bounds with ⟨lower, upper⟩
          simp only [source, Option.map_some, Option.some.injEq, Prod.mk.injEq] at rank
          simp only [select]
          by_cases inLeft : position < left.weight
          · rw [ite_eq_left inLeft]
            have other : select position left ≠ some key := fun found => go (mayLeft found)
            have outside : ¬(lo ≤ position ∧ position < hi) := by omega
            simp only [other, outside]
          · rw [ite_eq_right inLeft]
            by_cases inKey : position < left.weight + c
            · rw [ite_eq_left inKey]
              have other : some old ≠ some key := fun h => equal (Option.some.inj h).symm
              have outside : ¬(lo ≤ position ∧ position < hi) := by omega
              simp only [other, outside]
            · rw [ite_eq_right inKey, ihRight rightOrdered lower upper source]
              omega

end Proofs.Cpp.TreeMultiset.Tree
