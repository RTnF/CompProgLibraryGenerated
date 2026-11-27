import Proofs.Cpp.TreeMultiset.ArenaEntries

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

private theorem tick_run (start : Nat) : Cpp.tick.run start = some ((), start + 1) := rfl

private theorem none_run {K : Type} (start : Nat) :
    (cp.TreeMultiSet.none (T := K)).run start = some (endIndex, start + 1) := rfl

private theorem pure_run {A : Type} (value : A) (start : Nat) :
    (pure value : Cpp.M A).run start = some (value, start) := rfl

private theorem some_bind {A B : Type} (value : A) (f : A → Option B) :
    (some value >>= f) = f value := rfl

theorem generated_insert_empty {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeMultiSet K) (item : UInt64) (fuel start : Nat) :
    (cp.TreeMultiSet.insert_rec (fuel + 1) arena endIndex item).run start =
      some ((item, arena), start + 2) := by
  cases arena
  simp only [cp.TreeMultiSet.insert_rec, StateT.run_bind, tick_run, none_run,
    some_bind, pure_run, decide_true, ite_true]

theorem generated_insert_split {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena middle after : cp.TreeMultiSet K) (root item lower upper : UInt64) (key : K)
    (fuel start splitStop stop : Nat) (present : root ≠ endIndex)
    (higher : (modelCell arena root).priority < (modelCell arena item).priority)
    (itemKey : (modelCell arena item).key = some key)
    (sub : (cp.TreeMultiSet.split arena root key).run (start + 2) = some (((lower, upper), middle), splitStop))
    (inside : (Cpp.toSigned 64 item.toNat).toNat < middle.slots.size)
    (updated : (cp.TreeMultiSet.update
      (putCell middle item {modelCell middle item with left := lower, right := upper}) item).run splitStop =
        some (after, stop)) :
    (cp.TreeMultiSet.insert_rec (fuel + 1) arena root item).run start = some ((item, after), stop) := by
  cases arena
  cases middle
  cases after
  dsimp only [modelCell, putCell] at higher itemKey updated
  simp only [cp.TreeMultiSet.insert_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    present, decide_false, Bool.false_eq_true, ite_false, higher, decide_true, ite_true, itemKey,
    Cpp.optionalValue, sub, read_at_written _ _ _ inside, write_same_cell, updated]

theorem generated_insert_left {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena middle after : cp.TreeMultiSet K) (root item subroot : UInt64) (key old : K)
    (fuel start subStop stop : Nat) (present : root ≠ endIndex)
    (lowerPriority : ¬ (modelCell arena root).priority < (modelCell arena item).priority)
    (itemKey : (modelCell arena item).key = some key) (rootKey : (modelCell arena root).key = some old)
    (less : key < old)
    (sub : (cp.TreeMultiSet.insert_rec fuel arena (modelCell arena root).left item).run (start + 2) =
      some ((subroot, middle), subStop))
    (updated : (cp.TreeMultiSet.update
      (putCell middle root {modelCell middle root with left := subroot}) root).run subStop =
        some (after, stop)) :
    (cp.TreeMultiSet.insert_rec (fuel + 1) arena root item).run start = some ((root, after), stop) := by
  cases arena
  cases middle
  cases after
  dsimp only [modelCell, putCell] at lowerPriority itemKey rootKey sub updated
  simp only [cp.TreeMultiSet.insert_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    present, lowerPriority, decide_false, Bool.false_eq_true, ite_false,
    itemKey, rootKey, Cpp.optionalValue, less, decide_true, ite_true, sub, updated]

theorem generated_insert_right {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena middle after : cp.TreeMultiSet K) (root item subroot : UInt64) (key old : K)
    (fuel start subStop stop : Nat) (present : root ≠ endIndex)
    (lowerPriority : ¬ (modelCell arena root).priority < (modelCell arena item).priority)
    (itemKey : (modelCell arena item).key = some key) (rootKey : (modelCell arena root).key = some old)
    (less : ¬ key < old)
    (sub : (cp.TreeMultiSet.insert_rec fuel arena (modelCell arena root).right item).run (start + 2) =
      some ((subroot, middle), subStop))
    (updated : (cp.TreeMultiSet.update
      (putCell middle root {modelCell middle root with right := subroot}) root).run subStop =
        some (after, stop)) :
    (cp.TreeMultiSet.insert_rec (fuel + 1) arena root item).run start = some ((root, after), stop) := by
  cases arena
  cases middle
  cases after
  dsimp only [modelCell, putCell] at lowerPriority itemKey rootKey sub updated
  simp only [cp.TreeMultiSet.insert_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    present, lowerPriority, decide_false, Bool.false_eq_true, ite_false,
    itemKey, rootKey, Cpp.optionalValue, less, sub, updated]

end Proofs.Cpp.TreeMultiset
