import Proofs.Cpp.TreeSet.Insert

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl
private theorem sentinel_run {K : Type} (clock : Nat) :
    (cp.TreeSet.none (T := K)).run clock = some (endIndex, clock + 1) := rfl
private theorem some_bind {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl
private theorem pure_run {A : Type} (value : A) (clock : Nat) :
    (pure value : Cpp.M A).run clock = some (value, clock) := rfl

private theorem detach_branch_run {K : Type} [Inhabited K] (fuel : Nat)
    (arena : cp.TreeSet K) (i : UInt64) (start : Nat) :
    let row := cell arena.slots i
    (cp.TreeSet.detach_first_rec (fuel + 1) arena i).run start =
      if row.left = endIndex then some (((i, row.right), arena), start + 2)
      else (do
        let child ← (cp.TreeSet.detach_first_rec fuel arena row.left).run (start + 2)
        let refreshed ← (cp.TreeSet.rebalance (linkLeft child.1.2 i child.1.1.2) i).run child.2
        some (((child.1.1.1, refreshed.1.1), refreshed.1.2), refreshed.2)) := by
  rcases arena with ⟨slots, root, free⟩
  by_cases sentinel : (cell slots i).left = endIndex <;>
    simp only [cell, slotOffset, linkLeft, putCell] at sentinel <;>
    simp only [cp.TreeSet.detach_first_rec, StateT.run_bind, tick_run, sentinel_run, some_bind,
      cell, slotOffset, linkLeft, putCell, sentinel, decide_true, decide_false, Bool.false_eq_true,
      ite_true, ite_false, pure_run]

theorem Layout.empty_indexes {K : Type} [Inhabited K] {storage : Array (cp.TreeSet_Slot K)}
    {i : UInt64} {used : List Nat} (layout : Layout storage i Tree.empty used) :
    i = endIndex ∧ used = [] := by
  cases layout
  exact ⟨rfl, rfl⟩

theorem generated_detach_layout {K : Type} [Inhabited K] (tree : Tree K)
    (arena : cp.TreeSet K) (i : UInt64) (used : List Nat) (layout : Layout arena.slots i tree used)
    (nonnull : tree ≠ .empty) (fits : arena.slots.size ≤ 2 ^ 63)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ first replacement next key result remaining stop,
      (cp.TreeSet.detach_first_rec fuel arena i).run start = some (((first, replacement), next), stop) ∧
      stop ≤ start + 57 * tree.height ∧ tree.extractMin = some (key, result) ∧
      first.toNat < next.slots.size ∧ first ≠ endIndex ∧ (cell next.slots first).key = some key ∧
      first.toNat ∉ remaining ∧ Layout next.slots replacement result remaining ∧
      ChangedWithin arena next remaining ∧ (∀ n, n ∈ used ↔ n = first.toNat ∨ n ∈ remaining) := by
  induction tree generalizing arena i used fuel start with
  | empty => exact (nonnull rfl).elim
  | node left current right il _ =>
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      obtain ⟨ls, rs, usedEq, pending⟩ := layout_pending layout
      let row := cell arena.slots i
      cases left with
      | empty =>
        have noLeft : row.left = endIndex ∧ ls = [] := pending.leftLayout.empty_indexes
        refine ⟨i, row.right, arena, current, right, rs, start + 2, ?_, ?_, by simp [Tree.extractMin],
          pending.allocated, pending.nonnull, pending.value, pending.rightApart, pending.rightLayout,
          ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩, ?_⟩
        · rw [detach_branch_run]
          exact ite_eq_left noLeft.1
        · simp only [Tree.height]; omega
        · intro n
          simp [usedEq, noLeft.2]
      | node a x b =>
        have noEnd : row.left ≠ endIndex := pending.leftLayout.root_key.1
        have childFuel : (Tree.node a x b).height < fuel := by
          change max (Tree.node a x b).height right.height + 1 < fuel + 1 at enough
          omega
        obtain ⟨first, child, interim, key, result, remaining, middle, detached, childCost, extracted,
          firstRange, firstNonnull, firstKey, noFirst, childLayout, childFrame, same⟩ :=
          il arena row.left ls pending.leftLayout (by simp) fits fuel (start + 2) childFuel
        have childSubset : remaining ⊆ ls := fun {_} h => (same _).mpr (Or.inr h)
        have firstOld : first.toNat ∈ ls := (same _).mpr (Or.inl rfl)
        have noRoot : i.toNat ∉ remaining := fun h => pending.leftApart (childSubset h)
        have apart : List.Disjoint remaining rs := fun {_} onLeft onRight =>
          pending.disjoint (childSubset onLeft) onRight
        have finite : interim.slots.size ≤ 2 ^ 63 := by rwa [childFrame.size]
        let linked := linkLeft interim i child
        let touched := i.toNat :: (remaining ++ rs)
        have adjusted := pending_relink_left pending childFrame.retained childLayout noRoot apart finite
        obtain ⟨root, next, occupied, stop, balanced, balanceCost, updated, balanceFrame, equivalent⟩ :=
          generated_rebalance_layout linked i result right current remaining rs adjusted
            (by simpa [linked] using finite) middle
        have inside : i.toNat < interim.slots.size := by rw [childFrame.size]; exact pending.allocated
        have linkFrame : ChangedWithin interim linked touched :=
          putCell_changedWithin _ _ _ inside finite (by simp [touched])
        have firstUntouched : first.toNat ∉ touched := by
          have distinct : first.toNat ≠ i.toNat := fun eq => pending.leftApart (eq ▸ firstOld)
          have notRight : first.toNat ∉ rs := fun h => pending.disjoint firstOld h
          simp [touched, distinct, noFirst, notRight]
        have combined := (childFrame.trans linkFrame (by intro n h; simp [touched, h]) (fun _ h => h)).trans
          balanceFrame (fun _ h => h) (fun _ h => h)
        have stillFirst : (cell next.slots first).key = some key := by
          rw [balanceFrame.outside first (by rwa [linkFrame.size]) firstUntouched,
            linkFrame.outside first firstRange firstUntouched]
          exact firstKey
        refine ⟨first, root, next, key, Tree.balance result current right, occupied, stop, ?_,
          ?_, ?_, by rw [balanceFrame.size, linkFrame.size]; exact firstRange, firstNonnull, stillFirst,
          fun h => firstUntouched ((equivalent _).mp h), updated, ?_, ?_⟩
        · rw [detach_branch_run, ite_eq_right noEnd]
          change (do
            let p ← (cp.TreeSet.detach_first_rec fuel arena row.left).run (start + 2)
            let q ← (cp.TreeSet.rebalance (linkLeft p.1.2 i p.1.1.2) i).run p.2
            some (((p.1.1.1, q.1.1), q.1.2), q.2)) = _
          simp only [detached, some_bind]
          change ((cp.TreeSet.rebalance linked i).run middle >>= _) = _
          simp only [balanced, some_bind]
        · change stop ≤ start + 57 * (max (Tree.node a x b).height right.height + 1)
          omega
        · simp [Tree.extractMin, extracted]
        · exact ⟨combined.root, combined.free, combined.size, fun j h apart =>
            combined.outside j h (fun member => apart ((equivalent _).mpr member))⟩
        · intro n
          simp only [usedEq, List.mem_cons, List.mem_append, same n, equivalent n, touched]
          simp only [or_assoc, or_left_comm, or_comm]

end Proofs.Cpp.TreeSet
