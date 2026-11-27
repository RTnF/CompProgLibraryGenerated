import Proofs.Math.TreeMultiset.Treap

namespace Proofs.Cpp.TreeMultiset.Tree

def Bounded (limit : Nat) : Tree K → Prop
  | .empty => True
  | .node _ p _ left right => p.toNat ≤ limit ∧ Bounded limit left ∧ Bounded limit right

def Heap : Tree K → Prop
  | .empty => True
  | .node _ p _ left right => left.Heap ∧ right.Heap ∧ left.Bounded p.toNat ∧ right.Bounded p.toNat

theorem bounded_mono {l u : Nat} (order : l ≤ u) (tree : Tree K) (before : tree.Bounded l) : tree.Bounded u := by
  induction tree with
  | empty => trivial
  | node _ _ _ _ _ ihLeft ihRight =>
    exact ⟨Nat.le_trans before.1 order, ihLeft before.2.1, ihRight before.2.2⟩

theorem split_bounded {K : Type} [LT K] [DecidableLT K] (limit : Nat) (pivot : K) (tree : Tree K)
    (before : tree.Bounded limit) : (split pivot tree).1.Bounded limit ∧ (split pivot tree).2.Bounded limit := by
  induction tree with
  | empty => exact ⟨True.intro, True.intro⟩
  | node key p c left right ihLeft ihRight =>
    by_cases go : pivot < key
    · simp only [split, ite_eq_left go, Bounded]
      obtain ⟨a, b⟩ := ihLeft before.2.1
      exact ⟨a, before.1, b, before.2.2⟩
    · simp only [split, ite_eq_right go, Bounded]
      obtain ⟨a, b⟩ := ihRight before.2.2
      exact ⟨⟨before.1, before.2.1, a⟩, b⟩

theorem split_heap {K : Type} [LT K] [DecidableLT K] (pivot : K) (tree : Tree K) (before : tree.Heap) :
    (split pivot tree).1.Heap ∧ (split pivot tree).2.Heap := by
  induction tree with
  | empty => exact ⟨True.intro, True.intro⟩
  | node key p c left right ihLeft ihRight =>
    obtain ⟨ll, rr, lb, rb⟩ := before
    by_cases go : pivot < key
    · simp only [split, ite_eq_left go, Heap]
      have bounds := split_bounded p.toNat pivot left lb
      obtain ⟨a, b⟩ := ihLeft ll
      exact ⟨a, b, rr, bounds.2, rb⟩
    · simp only [split, ite_eq_right go, Heap]
      have bounds := split_bounded p.toNat pivot right rb
      obtain ⟨a, b⟩ := ihRight rr
      exact ⟨⟨ll, a, lb, bounds.1⟩, b⟩

theorem merge_bounded (limit : Nat) (left right : Tree K) :
    left.Bounded limit → right.Bounded limit → (merge left right).Bounded limit := by
  induction left, right using merge.induct with
  | case1 right => exact fun _ h => by simpa only [merge] using h
  | case2 left nonempty =>
    intro before _
    cases left <;> simpa only [merge] using before
  | case3 kl pl cl ll lr kr pr cr rl rr route ih =>
    intro beforeLeft beforeRight
    simp only [merge, ite_eq_left route, Bounded]
    exact ⟨beforeLeft.1, beforeLeft.2.1, ih beforeLeft.2.2 beforeRight⟩
  | case4 kl pl cl ll lr kr pr cr rl rr route ih =>
    intro beforeLeft beforeRight
    simp only [merge, ite_eq_right route, Bounded]
    exact ⟨beforeRight.1, ih beforeLeft beforeRight.2.1, beforeRight.2.2⟩

theorem root_bounded {K : Type} {key : K} {p : UInt64} {count : Nat} {l r : Tree K}
    (before : (Tree.node key p count l r).Heap) : (Tree.node key p count l r).Bounded p.toNat :=
  ⟨Nat.le_refl _, before.2.2⟩

theorem merge_heap (left right : Tree K) : left.Heap → right.Heap → (merge left right).Heap := by
  induction left, right using merge.induct with
  | case1 right => exact fun _ h => by simpa only [merge] using h
  | case2 left nonempty =>
    intro before _
    cases left <;> simpa only [merge] using before
  | case3 kl pl cl ll lr kr pr cr rl rr route ih =>
    intro hl hr
    have order : pr.toNat ≤ pl.toNat := Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp route)
    have boundedRight := bounded_mono order _ (root_bounded hr)
    simp only [merge, ite_eq_left route, Heap]
    exact ⟨hl.1, ih hl.2.1 hr, hl.2.2.1, merge_bounded pl.toNat _ _ hl.2.2.2 boundedRight⟩
  | case4 kl pl cl ll lr kr pr cr rl rr route ih =>
    intro hl hr
    have order : pl.toNat ≤ pr.toNat := Nat.le_of_not_gt (fun h => route (UInt64.lt_iff_toNat_lt.mpr h))
    have boundedLeft := bounded_mono order _ (root_bounded hl)
    simp only [merge, ite_eq_right route, Heap]
    exact ⟨ih hl hr.1, hr.2.1, merge_bounded pr.toNat _ _ boundedLeft hr.2.2.1, hr.2.2.2⟩

theorem insert_bounded {K : Type} [LT K] [DecidableLT K] (limit : Nat) (key : K)
    (p : UInt64) (n : Nat) (tree : Tree K) (before : tree.Bounded limit) (within : p.toNat ≤ limit) :
    (insert key p n tree).Bounded limit := by
  induction tree with
  | empty => exact ⟨within, True.intro, True.intro⟩
  | node old oldP c left right ihLeft ihRight =>
    by_cases high : oldP < p
    · simp only [insert, ite_eq_left high, Bounded]
      exact ⟨within, split_bounded limit key _ before⟩
    · by_cases go : key < old
      · simp only [insert, ite_eq_right high, ite_eq_left go, Bounded]
        exact ⟨before.1, ihLeft before.2.1, before.2.2⟩
      · simp only [insert, ite_eq_right high, ite_eq_right go, Bounded]
        exact ⟨before.1, before.2.1, ihRight before.2.2⟩

theorem insert_heap {K : Type} [LT K] [DecidableLT K] (key : K)
    (p : UInt64) (n : Nat) (tree : Tree K) (before : tree.Heap) :
    (insert key p n tree).Heap := by
  induction tree with
  | empty => exact ⟨True.intro, True.intro, True.intro, True.intro⟩
  | node old oldP c left right ihLeft ihRight =>
    by_cases high : oldP < p
    · have order : oldP.toNat ≤ p.toNat := Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp high)
      have subs := split_heap key (Tree.node old oldP c left right) before
      have bounds := split_bounded p.toNat key _ (bounded_mono order _ (root_bounded before))
      simp only [insert, ite_eq_left high, Heap]
      exact ⟨subs.1, subs.2, bounds⟩
    · have low : p.toNat ≤ oldP.toNat := Nat.le_of_not_gt (fun h => high (UInt64.lt_iff_toNat_lt.mpr h))
      by_cases go : key < old
      · simp only [insert, ite_eq_right high, ite_eq_left go, Heap]
        exact ⟨ihLeft before.1, before.2.1, insert_bounded oldP.toNat key p n left before.2.2.1 low, before.2.2.2⟩
      · simp only [insert, ite_eq_right high, ite_eq_right go, Heap]
        exact ⟨before.1, ihRight before.2.1, before.2.2.1, insert_bounded oldP.toNat key p n right before.2.2.2 low⟩

theorem erase_bounded {K : Type} [LT K] [DecidableLT K] [DecidableEq K] (limit : Nat) (key : K)
    (tree : Tree K) (before : tree.Bounded limit) : (erase key tree).Bounded limit := by
  induction tree with
  | empty => trivial
  | node old p c left right ihLeft ihRight =>
    by_cases equal : key = old
    · rw [erase, ite_eq_left equal]
      exact merge_bounded limit left right before.2.1 before.2.2
    · by_cases go : key < old
      · simp only [erase, ite_eq_right equal, ite_eq_left go, Bounded]
        exact ⟨before.1, ihLeft before.2.1, before.2.2⟩
      · simp only [erase, ite_eq_right equal, ite_eq_right go, Bounded]
        exact ⟨before.1, before.2.1, ihRight before.2.2⟩

theorem erase_heap {K : Type} [LT K] [DecidableLT K] [DecidableEq K] (key : K)
    (tree : Tree K) (before : tree.Heap) : (erase key tree).Heap := by
  induction tree with
  | empty => trivial
  | node old p c left right ihLeft ihRight =>
    by_cases equal : key = old
    · rw [erase, ite_eq_left equal]
      exact merge_heap left right before.1 before.2.1
    · by_cases go : key < old
      · simp only [erase, ite_eq_right equal, ite_eq_left go, Heap]
        exact ⟨ihLeft before.1, before.2.1, erase_bounded p.toNat key left before.2.2.1, before.2.2.2⟩
      · simp only [erase, ite_eq_right equal, ite_eq_right go, Heap]
        exact ⟨before.1, ihRight before.2.1, before.2.2.1, erase_bounded p.toNat key right before.2.2.2⟩

end Proofs.Cpp.TreeMultiset.Tree
