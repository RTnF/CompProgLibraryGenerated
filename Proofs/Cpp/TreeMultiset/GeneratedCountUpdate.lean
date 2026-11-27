import Proofs.Cpp.TreeMultiset.LocateLayout

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

private theorem tick_run (start : Nat) : Cpp.tick.run start = some ((), start + 1) := rfl

private theorem pure_run {A : Type} (value : A) (start : Nat) :
    (pure value : Cpp.M A).run start = some (value, start) := rfl

private theorem some_bind {A B : Type} (value : A) (f : A → Option B) :
    (some value >>= f) = f value := rfl

theorem generated_count_here {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena after : cp.TreeMultiSet K) (root count : UInt64) (key : K) (fuel start stop : Nat)
    (hasKey : (modelCell arena root).key = some key)
    (update : (cp.TreeMultiSet.update (putCell arena root {modelCell arena root with count := count}) root).run (start + 1) =
      some (after, stop)) :
    (cp.TreeMultiSet.replace_count_rec (fuel + 1) arena root key count).run start = some (after, stop) := by
  cases arena
  cases after
  dsimp only [modelCell, putCell] at hasKey update
  simp only [hasKey] at update
  simp only [cp.TreeMultiSet.replace_count_rec, StateT.run_bind, tick_run, some_bind, pure_run,
    hasKey, Cpp.optionalValue, decide_true, ite_true, update]

theorem generated_count_left {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena middle after : cp.TreeMultiSet K) (root count : UInt64) (key old : K)
    (fuel start subStop stop : Nat) (different : key ≠ old)
    (hasKey : (modelCell arena root).key = some old) (less : key < old)
    (sub : (cp.TreeMultiSet.replace_count_rec fuel arena (modelCell arena root).left key count).run (start + 1) =
      some (middle, subStop))
    (update : (cp.TreeMultiSet.update middle root).run subStop = some (after, stop)) :
    (cp.TreeMultiSet.replace_count_rec (fuel + 1) arena root key count).run start = some (after, stop) := by
  cases arena
  cases middle
  cases after
  dsimp only [modelCell] at hasKey sub
  simp only [cp.TreeMultiSet.replace_count_rec, StateT.run_bind, tick_run, some_bind, pure_run,
    different, hasKey, Cpp.optionalValue, less, decide_false, Bool.false_eq_true, ite_false, decide_true, ite_true, sub, update]

theorem generated_count_right {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena middle after : cp.TreeMultiSet K) (root count : UInt64) (key old : K)
    (fuel start subStop stop : Nat) (different : key ≠ old)
    (hasKey : (modelCell arena root).key = some old) (less : ¬ key < old)
    (sub : (cp.TreeMultiSet.replace_count_rec fuel arena (modelCell arena root).right key count).run (start + 1) =
      some (middle, subStop))
    (update : (cp.TreeMultiSet.update middle root).run subStop = some (after, stop)) :
    (cp.TreeMultiSet.replace_count_rec (fuel + 1) arena root key count).run start = some (after, stop) := by
  cases arena
  cases middle
  cases after
  dsimp only [modelCell] at hasKey sub
  simp only [cp.TreeMultiSet.replace_count_rec, StateT.run_bind, tick_run, some_bind, pure_run,
    different, hasKey, Cpp.optionalValue, less, decide_false, Bool.false_eq_true, ite_false, sub, update]

end Proofs.Cpp.TreeMultiset
