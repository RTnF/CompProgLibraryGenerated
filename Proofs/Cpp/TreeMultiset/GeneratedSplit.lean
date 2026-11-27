import Proofs.Cpp.TreeMultiset.GeneratedRelink
import Proofs.Math.TreeMultiset.TreapWork

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem Tree.split_weight [LT K] [DecidableLT K] (pivot : K) (tree : Tree K) :
    (tree.split pivot).1.weight + (tree.split pivot).2.weight = tree.weight := by
  induction tree with
  | empty => rfl
  | node key priority count left right ihLeft ihRight =>
    simp only [Tree.split]
    split
    · simp only [Tree.weight]
      omega
    · simp only [Tree.weight]
      omega

private theorem tick_run (start : Nat) : Cpp.tick.run start = some ((), start + 1) := rfl

private theorem none_run {K : Type} (start : Nat) :
    (cp.TreeMultiSet.none (T := K)).run start = some (endIndex, start + 1) := rfl

private theorem pure_run {A : Type} (value : A) (start : Nat) :
    (pure value : Cpp.M A).run start = some (value, start) := rfl

private theorem some_bind {A B : Type} (value : A) (f : A → Option B) :
    (some value >>= f) = f value := rfl

theorem generated_split_empty {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeMultiSet K) (key : K) (fuel start : Nat) :
    (cp.TreeMultiSet.split_rec (fuel + 1) arena endIndex key).run start =
      some (((endIndex, endIndex), arena), start + 4) := by
  cases arena
  simp only [cp.TreeMultiSet.split_rec, StateT.run_bind, tick_run, none_run,
    some_bind, pure_run, decide_true, ite_true]

theorem generated_split_left {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena after out : cp.TreeMultiSet K) (code lower upper : UInt64) (pivot key : K)
    (fuel start middle stop : Nat) (notEnd : code ≠ endIndex)
    (hasKey : (modelCell arena code).key = some key) (less : pivot < key)
    (sub : (cp.TreeMultiSet.split_rec fuel arena (modelCell arena code).left pivot).run (start + 2) =
      some (((lower, upper), after), middle))
    (relink : (cp.TreeMultiSet.update (putCell after code {modelCell after code with left := upper}) code).run middle =
      some (out, stop)) :
    (cp.TreeMultiSet.split_rec (fuel + 1) arena code pivot).run start = some (((lower, code), out), stop) := by
  cases arena
  cases after
  cases out
  dsimp only [modelCell, putCell] at hasKey sub relink
  simp only [cp.TreeMultiSet.split_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    notEnd, decide_false, Bool.false_eq_true, ite_false, hasKey, Cpp.optionalValue,
    less, decide_true, ite_true, sub, relink]

theorem generated_split_right {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena after out : cp.TreeMultiSet K) (code lower upper : UInt64) (pivot key : K)
    (fuel start middle stop : Nat) (notEnd : code ≠ endIndex)
    (hasKey : (modelCell arena code).key = some key) (less : ¬ pivot < key)
    (sub : (cp.TreeMultiSet.split_rec fuel arena (modelCell arena code).right pivot).run (start + 2) =
      some (((lower, upper), after), middle))
    (relink : (cp.TreeMultiSet.update (putCell after code {modelCell after code with right := lower}) code).run middle =
      some (out, stop)) :
    (cp.TreeMultiSet.split_rec (fuel + 1) arena code pivot).run start = some (((code, upper), out), stop) := by
  cases arena
  cases after
  cases out
  dsimp only [modelCell, putCell] at hasKey sub relink
  simp only [cp.TreeMultiSet.split_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    notEnd, decide_false, Bool.false_eq_true, ite_false, hasKey, Cpp.optionalValue,
    less, sub, relink]

end Proofs.Cpp.TreeMultiset
