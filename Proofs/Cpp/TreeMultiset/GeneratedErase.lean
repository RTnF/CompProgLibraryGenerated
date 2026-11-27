import Proofs.Cpp.TreeMultiset.ArenaGrowth

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

private theorem tick_run (start : Nat) : Cpp.tick.run start = some ((), start + 1) := rfl

private theorem pure_run {A : Type} (value : A) (start : Nat) :
    (pure value : Cpp.M A).run start = some (value, start) := rfl

private theorem some_bind {A B : Type} (value : A) (f : A → Option B) :
    (some value >>= f) = f value := rfl

theorem generated_erase_here {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena middle after : cp.TreeMultiSet K) (root joined : UInt64) (key : K)
    (fuel start mergeStop stop : Nat)
    (hasKey : (modelCell arena root).key = some key)
    (merge : (cp.TreeMultiSet.merge arena (modelCell arena root).left (modelCell arena root).right).run (start + 1) =
      some ((joined, middle), mergeStop))
    (release : (cp.TreeMultiSet.release middle root).run mergeStop = some (after, stop)) :
    (cp.TreeMultiSet.erase_rec (fuel + 1) arena root key).run start = some ((joined, after), stop) := by
  cases arena
  cases middle
  cases after
  dsimp only [modelCell] at hasKey merge
  simp only [cp.TreeMultiSet.erase_rec, StateT.run_bind, tick_run, some_bind, pure_run,
    hasKey, Cpp.optionalValue, decide_true, ite_true, merge, release]

theorem generated_erase_left {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena middle after : cp.TreeMultiSet K) (root child : UInt64) (key old : K)
    (fuel start subStop stop : Nat) (different : old ≠ key)
    (hasKey : (modelCell arena root).key = some old) (less : key < old)
    (sub : (cp.TreeMultiSet.erase_rec fuel arena (modelCell arena root).left key).run (start + 1) =
      some ((child, middle), subStop))
    (update : (cp.TreeMultiSet.update (putCell middle root {modelCell middle root with left := child}) root).run subStop =
      some (after, stop)) :
    (cp.TreeMultiSet.erase_rec (fuel + 1) arena root key).run start = some ((root, after), stop) := by
  cases arena
  cases middle
  cases after
  dsimp only [modelCell, putCell] at hasKey sub update
  simp only [cp.TreeMultiSet.erase_rec, StateT.run_bind, tick_run, some_bind, pure_run,
    different, hasKey, Cpp.optionalValue, less, decide_false, Bool.false_eq_true, ite_false, decide_true, ite_true, sub, update]

theorem generated_erase_right {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena middle after : cp.TreeMultiSet K) (root child : UInt64) (key old : K)
    (fuel start subStop stop : Nat) (different : old ≠ key)
    (hasKey : (modelCell arena root).key = some old) (less : ¬ key < old)
    (sub : (cp.TreeMultiSet.erase_rec fuel arena (modelCell arena root).right key).run (start + 1) =
      some ((child, middle), subStop))
    (update : (cp.TreeMultiSet.update (putCell middle root {modelCell middle root with right := child}) root).run subStop =
      some (after, stop)) :
    (cp.TreeMultiSet.erase_rec (fuel + 1) arena root key).run start = some ((root, after), stop) := by
  cases arena
  cases middle
  cases after
  dsimp only [modelCell, putCell] at hasKey sub update
  simp only [cp.TreeMultiSet.erase_rec, StateT.run_bind, tick_run, some_bind, pure_run,
    different, hasKey, Cpp.optionalValue, less, decide_false, Bool.false_eq_true, ite_false, sub, update]

end Proofs.Cpp.TreeMultiset
