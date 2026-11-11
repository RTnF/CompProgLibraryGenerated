import Proofs.Cpp.Gen.TreeEdges
import Proofs.Cpp.Lib.Basic

/-! # `tree_edges` (library/tree/tree_edges.hpp)

The arcs of a parent array, in the order the original appends them (`arcs`); `n + 1` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeEdges

/-- Vertex `i` has a parent edge: `parent[i] != i` and `0 <= parent[i] < n`. -/
def HasParent (parent : Array Int) (n : Int) (i : Nat) : Prop := parent[i]! ≠ i ∧ 0 ≤ parent[i]! ∧ parent[i]! < n

instance (parent : Array Int) (n : Int) (i : Nat) : Decidable (HasParent parent n i) := by
  unfold HasParent; infer_instance

/-- The arcs for the vertices `0, ..., k - 1`: `parent[i] → i` and `i → parent[i]` for each `i` with a parent edge. -/
def arcs (parent : Array Int) (n : Int) : Nat → List (Int × Int)
  | 0 => []
  | k + 1 => arcs parent n k ++ if HasParent parent n k then [(parent[k]!, (k : Int)), ((k : Int), parent[k]!)] else []

theorem arcs_length_le (parent : Array Int) (n : Int) (k : Nat) : (arcs parent n k).length ≤ 2 * k := by
  induction k with
  | zero => simp [arcs]
  | succ k ih => simp only [arcs, List.length_append]; split <;> simp <;> omega

/-- `a` holds the list `l` in its first `l.length` slots and `a0` after them. -/
def Holds (a a0 : Array Int) (l : List Int) : Prop :=
  a.size = a0.size ∧ (∀ j (hj : j < l.length), a[j]! = l[j]) ∧ ∀ k, l.length ≤ k → a[k]! = a0[k]!

theorem holds_push (a a0 : Array Int) (l : List Int) (x : Int) (h : Holds a a0 l) (hs : l.length < a0.size) :
    Holds (set a (l.length : Int) x) a0 (l ++ [x]) := by
  obtain ⟨hsz, hd, hr⟩ := h
  refine ⟨by simp [hsz], fun j hj => ?_, fun k hk => ?_⟩
  · rw [getElem!_set _ _ _ _ (by simp; omega), List.getElem_append]
    simp only [List.length_append, List.length_singleton] at hj
    by_cases e : j = l.length
    · subst e; simp
    · simp only [Int.toNat_natCast, e, ite_false, show j < l.length by omega, dite_true]; exact hd j _
  · simp only [List.length_append, List.length_singleton] at hk
    rw [getElem!_set _ _ _ _ (by simp; omega)]
    simp only [Int.toNat_natCast, show k ≠ l.length by omega, ite_false]; exact hr k (by omega)

theorem step_some (parent from_ to_ : Array Int) (n : Int) (b : Array Int × Array Int × Int) (s t0 L : Nat)
    (hf : 2 * n ≤ from_.size) (ht : 2 * n ≤ to_.size) (hv : HasParent parent n L) (hL : (L : Int) < n)
    (h : b.2.2 = (arcs parent n L).length ∧ Holds b.1 from_ ((arcs parent n L).map (·.1)) ∧
      Holds b.2.1 to_ ((arcs parent n L).map (·.2)) ∧ s = t0 + 1 + L) :
    b.2.2 + 1 + 1 = ((arcs parent n (L + 1)).length : Int) ∧
      Holds (set (set b.1 b.2.2 parent[L]!) (b.2.2 + 1) (L : Int)) from_ ((arcs parent n (L + 1)).map (·.1)) ∧
      Holds (set (set b.2.1 b.2.2 (L : Int)) (b.2.2 + 1) parent[L]!) to_ ((arcs parent n (L + 1)).map (·.2)) ∧
      s + 1 = t0 + 1 + (L + 1) := by
  obtain ⟨hm, hf1, ht1, hc⟩ := h
  have ha : arcs parent n (L + 1) = arcs parent n L ++ [(parent[L]!, (L : Int)), ((L : Int), parent[L]!)] := by
    simp [arcs, hv]
  have hle := arcs_length_le parent n L
  have hs1 := hf1.1
  have hs2 := ht1.1
  rw [ha, hm]
  refine ⟨by simp; omega, ?_, ?_, by omega⟩
  · have h1 := holds_push _ _ _ parent[L]! hf1 (by simp; omega)
    have h2 := holds_push _ _ _ (L : Int) h1 (by simp; omega)
    simpa using h2
  · have h1 := holds_push _ _ _ (L : Int) ht1 (by simp; omega)
    have h2 := holds_push _ _ _ parent[L]! h1 (by simp; omega)
    simpa using h2

theorem step_none (parent from_ to_ : Array Int) (n : Int) (b : Array Int × Array Int × Int) (s t0 L : Nat)
    (hv : ¬HasParent parent n L)
    (h : b.2.2 = (arcs parent n L).length ∧ Holds b.1 from_ ((arcs parent n L).map (·.1)) ∧
      Holds b.2.1 to_ ((arcs parent n L).map (·.2)) ∧ s = t0 + 1 + L) :
    b.2.2 = ((arcs parent n (L + 1)).length : Int) ∧ Holds b.1 from_ ((arcs parent n (L + 1)).map (·.1)) ∧
      Holds b.2.1 to_ ((arcs parent n (L + 1)).map (·.2)) ∧ s + 1 = t0 + 1 + (L + 1) := by
  have ha : arcs parent n (L + 1) = arcs parent n L := by simp [arcs, hv]
  rw [ha]; exact ⟨h.1, h.2.1, h.2.2.1, by omega⟩

/-- `tree_edges_from_parent(parent, from, to, n)` writes the arcs `arcs parent n n` to the first slots of
`from`/`to` (the rest is kept) and returns their number; `n + 1` steps. -/
theorem tree_edges_spec (parent from_ to_ : Array Int) (n : Int) (hn : 0 ≤ n)
    (hf : 2 * n ≤ from_.size) (ht : 2 * n ≤ to_.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_edges_from_parent parent from_ to_ n
    ⦃⇓ r c => ⌜r.1 = (arcs parent n n.toNat).length ∧
               Holds r.2.1 from_ ((arcs parent n n.toNat).map (·.1)) ∧
               Holds r.2.2 to_ ((arcs parent n n.toNat).map (·.2)) ∧ c = t0 + 1 + n.toNat⌝⦄ := by
  mvcgen [cp.tree_edges_from_parent]
  case inv1 =>
    exact ⇓⟨xs, r⟩ c => ⌜r.2.2 = (arcs parent n xs.prefix.length).length ∧
      Holds r.1 from_ ((arcs parent n xs.prefix.length).map (·.1)) ∧
      Holds r.2.1 to_ ((arcs parent n xs.prefix.length).map (·.2)) ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  all_goals (try (have e := range_cursor ‹range 0 n = _ ++ _ :: _›; simp at e; subst e))
  all_goals (try simp only [get_natCast] at *)
  · have hl := range_prefix_length ‹range 0 n = _ ++ _ :: _›
    simp only [Int.sub_zero] at hl
    exact step_some _ _ _ _ _ _ _ _ hf ht ⟨‹_›, ‹_›, ‹_›⟩ (by omega) ‹_ ∧ _ ∧ _ ∧ _›
  all_goals (try exact step_none _ _ _ _ _ _ _ _ (by unfold HasParent; omega) ‹_ ∧ _ ∧ _ ∧ _›)
  · refine ⟨by simp [arcs], ⟨rfl, by simp [arcs], fun _ _ => rfl⟩, ⟨rfl, by simp [arcs], fun _ _ => rfl⟩, ‹_›⟩
  · have h := ‹_ = _ ∧ Holds _ _ _ ∧ Holds _ _ _ ∧ _›
    simpa only [range_length, Int.sub_zero] using h

end Proofs.Cpp.TreeEdges
