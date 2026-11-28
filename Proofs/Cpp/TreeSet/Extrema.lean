import Proofs.Cpp.TreeSet.Find
import Proofs.Cpp.TreeSet.Neighbors

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

private theorem node_keys_nonempty {K : Type} (left right : Tree K) (key : K) :
    (Tree.node left key right).keys ≠ [] := by
  intro nil
  have size := (Tree.node left key right).size_keys
  rw [nil] at size
  simp [Tree.size] at size

theorem Layout.first_key {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {i : UInt64} {tree : Tree K} {used : List Nat} (layout : Layout storage i tree used)
    (nonempty : tree ≠ .empty) :
    (cell storage (cell storage i).first).key = tree.keys.head? := by
  induction tree generalizing i used with
  | empty => contradiction
  | node left current right il _ =>
    cases layout with
    | @node i current l r ls rs allocated nonnull value height size first last ll rr fl fr distinct =>
      cases left with
      | empty =>
        rw [first, cachedFirst, ite_eq_left ll.empty_indexes.1]
        simpa [Tree.keys] using value
      | node a x b =>
        rw [first, cachedFirst, ite_eq_right ll.root_key.1, il ll (by simp)]
        have someHead := fun h => node_keys_nonempty a b x (List.head?_eq_none_iff.mp h)
        conv_rhs => rw [Tree.keys, List.head?_append]
        cases found : (Tree.node a x b).keys.head? with
        | none => exact (someHead found).elim
        | some k => simp [found]

theorem Layout.last_key {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {i : UInt64} {tree : Tree K} {used : List Nat} (layout : Layout storage i tree used)
    (nonempty : tree ≠ .empty) :
    (cell storage (cell storage i).last).key = tree.keys.getLast? := by
  induction tree generalizing i used with
  | empty => contradiction
  | node left current right _ ir =>
    cases layout with
    | @node i current l r ls rs allocated nonnull value height size first last ll rr fl fr distinct =>
      cases right with
      | empty =>
        rw [last, cachedLast, ite_eq_left rr.empty_indexes.1]
        simpa [Tree.keys] using value
      | node a x b =>
        rw [last, cachedLast, ite_eq_right rr.root_key.1, ir rr (by simp)]
        have someLast := fun h => node_keys_nonempty a b x (List.getLast?_eq_none_iff.mp h)
        conv_rhs => rw [Tree.keys, List.getLast?_append]
        cases found : (Tree.node a x b).keys.getLast? with
        | none => exact (someLast found).elim
        | some k => simp [found]

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl
private theorem sentinel_run {K : Type} (clock : Nat) :
    (cp.TreeSet.none (T := K)).run clock = some (endIndex, clock + 1) := rfl

theorem generated_extrema_spec {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (tree : Tree K) (used : List Nat) (layout : Layout arena.slots arena.root tree used)
    (nonempty : tree ≠ .empty) (start : Nat) :
    ∃ lo hi, tree.keys.head? = some lo ∧ tree.keys.getLast? = some hi ∧
      (cp.TreeSet.min_ arena).run start = some ((lo, arena), start + 2) ∧
      (cp.TreeSet.max_ arena).run start = some ((hi, arena), start + 2) := by
  cases tree with
  | empty => contradiction
  | node left current right =>
    have first := layout.first_key nonempty
    have last := layout.last_key nonempty
    have nonnull := layout.root_key.1
    cases hf : (Tree.node left current right).keys.head? with
    | none => exact (node_keys_nonempty _ _ _ (List.head?_eq_none_iff.mp hf)).elim
    | some lo =>
      cases hl : (Tree.node left current right).keys.getLast? with
      | none => exact (node_keys_nonempty _ _ _ (List.getLast?_eq_none_iff.mp hl)).elim
      | some hi =>
        rw [hf] at first
        rw [hl] at last
        rcases arena with ⟨slots, root, free⟩
        simp only [cell] at first last
        refine ⟨lo, hi, rfl, rfl, ?_, ?_⟩
        · simp [cp.TreeSet.min_, tick_run, sentinel_run, StateT.run_bind, Cpp.check, Cpp.optionalValue,
            nonnull, first, Nat.add_assoc]
        · simp [cp.TreeSet.max_, tick_run, sentinel_run, StateT.run_bind, Cpp.check, Cpp.optionalValue,
            nonnull, last, Nat.add_assoc]

theorem generated_size_spec {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (tree : Tree K) (used : List Nat) (layout : Layout arena.slots arena.root tree used)
    (fits : tree.size < 2 ^ 31) (start : Nat) :
    (cp.TreeSet.size_ arena).run start = some (((tree.size : Int), arena), start + 3) := by
  have count := layout.model_size
  have decode : Cpp.toSigned 32 tree.size = (tree.size : Int) := by
    unfold Cpp.toSigned
    rw [Nat.mod_eq_of_lt (by omega), ite_eq_left fits]
  rcases arena with ⟨slots, root, free⟩
  simp [cp.TreeSet.size_, StateT.run_bind, tick_run, generated_size_run, Nat.add_assoc, count, decode]

end Proofs.Cpp.TreeSet
