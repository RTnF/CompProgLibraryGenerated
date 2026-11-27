import Proofs.Cpp.TreeMultiset.ArenaAdd

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem Tree.split_slots {K : Type} [LT K] [DecidableLT K] (key : K) (tree : Tree K) :
    (tree.split key).1.slots + (tree.split key).2.slots = tree.slots := by
  induction tree with
  | empty => rfl
  | node old p c left right ihLeft ihRight =>
    simp only [Tree.split]
    split <;> simp only [Tree.slots] <;> omega

theorem Tree.insert_slots {K : Type} [LT K] [DecidableLT K]
    (key : K) (priority : UInt64) (count : Nat) (tree : Tree K) :
    (tree.insert key priority count).slots = tree.slots + 1 := by
  induction tree with
  | empty => rfl
  | node old p c left right ihLeft ihRight =>
    simp only [Tree.insert]
    by_cases higher : p < priority
    · rw [ite_eq_left higher]
      have total := Tree.split_slots key (.node old p c left right)
      simp only [Tree.slots] at total ⊢
      omega
    · rw [ite_eq_right higher]
      split <;> simp only [Tree.slots, ihLeft, ihRight] <;> omega

theorem generated_add_growth {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeMultiSet K) (tree : Tree K) (state : ArenaContents arena tree)
    (key : K) (count priority : UInt64) (fits : arena.slots.size < 2 ^ 63)
    (weight : tree.weight + count.toNat < 2 ^ 64) (start : Nat) :
    let next := tree.insert key priority count.toNat
    ∃ out stop, (cp.TreeMultiSet.add_distinct arena key count priority).run start = some (out, stop) ∧
      stop ≤ start + 7 + 7 * (tree.height + 2) ∧
      out.slots.size = max arena.slots.size next.slots ∧
      Nonempty (ArenaContents out next) := by
  obtain ⟨out, stop, run, time, monotone, capacity, grows, ⟨after⟩⟩ :=
    generated_add_distinct_spec arena tree state key count priority fits weight start
  refine ⟨out, stop, run, time, ?_, ⟨after⟩⟩
  by_cases increased : arena.slots.size < out.slots.size
  · have full := grows increased
    have covers : ∀ i, i < (storageView arena).size → i ∈ state.live ++ state.free :=
      fun i h => state.covers i (by simpa [storageView] using h)
    have oldSize : arena.slots.size = tree.slots := by
      simpa [storageView, full] using occupied_capacity state.treeLayout state.freeLayout covers
    rw [Tree.insert_slots, ← oldSize]
    omega
  · have afterCount : (tree.insert key priority count.toNat).slots ≤ out.slots.size := by
      simpa [storageView] using after.treeLayout.capacity
    omega

end Proofs.Cpp.TreeMultiset
