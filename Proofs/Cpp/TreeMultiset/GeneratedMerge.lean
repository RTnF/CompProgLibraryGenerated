import Proofs.Cpp.TreeMultiset.GeneratedRelink
import Proofs.Math.TreeMultiset.TreapWork

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem Tree.merge_weight (left right : Tree K) :
    (left.merge right).weight = left.weight + right.weight := by
  induction left, right using Tree.mergeSteps.induct with
  | case1 right => rw [Tree.merge]; simp [Tree.weight]
  | case2 left nonempty => rw [Tree.merge.eq_2 left nonempty]; simp [Tree.weight]
  | case3 kl pl cl ll lr kr pr cr rl rr ihLeft ihRight =>
    rw [Tree.merge]
    split
    · simp only [Tree.weight] at ihLeft ⊢
      omega
    · simp only [Tree.weight] at ihRight ⊢
      omega

def Tree.mergeTicks (left right : Tree K) : Nat :=
  match left, right with
  | .empty, _ => 2
  | _, .empty => 3
  | .node kl pl cl ll lr, .node kr pr cr rl rr =>
    8 + if pr < pl then mergeTicks lr (.node kr pr cr rl rr)
                   else mergeTicks (.node kl pl cl ll lr) rl
termination_by left.slots + right.slots
decreasing_by all_goals simp [Tree.slots] <;> omega

theorem Tree.mergeTicks_le (left right : Tree K) :
    mergeTicks left right ≤ 3 + 8 * (left.height + right.height) := by
  induction left, right using Tree.mergeSteps.induct with
  | case1 right => rw [mergeTicks]; omega
  | case2 left nonempty => rw [mergeTicks.eq_2 left nonempty]; omega
  | case3 kl pl cl ll lr kr pr cr rl rr ihLeft ihRight =>
    rw [mergeTicks]
    split
    · simp only [Tree.height] at ihLeft ⊢
      omega
    · simp only [Tree.height] at ihRight ⊢
      omega

private theorem tick_run (start : Nat) : Cpp.tick.run start = some ((), start + 1) := rfl

private theorem none_run {K : Type} (start : Nat) :
    (cp.TreeMultiSet.none (T := K)).run start = some (endIndex, start + 1) := rfl

private theorem pure_run {A : Type} (value : A) (start : Nat) :
    (pure value : Cpp.M A).run start = some (value, start) := rfl

private theorem some_bind {A B : Type} (value : A) (f : A → Option B) :
    (some value >>= f) = f value := rfl

theorem generated_merge_empty_left {K : Type} [Inhabited K]
    (arena : cp.TreeMultiSet K) (right : UInt64) (fuel start : Nat) :
    (cp.TreeMultiSet.merge_rec (fuel + 1) arena endIndex right).run start =
      some ((right, arena), start + 2) := by
  cases arena
  simp only [cp.TreeMultiSet.merge_rec, StateT.run_bind, tick_run, none_run,
    some_bind, pure_run, decide_true, ite_true]

theorem generated_merge_empty_right {K : Type} [Inhabited K]
    (arena : cp.TreeMultiSet K) (left : UInt64) (fuel start : Nat) (present : left ≠ endIndex) :
    (cp.TreeMultiSet.merge_rec (fuel + 1) arena left endIndex).run start =
      some ((left, arena), start + 3) := by
  cases arena
  simp only [cp.TreeMultiSet.merge_rec, StateT.run_bind, tick_run, none_run,
    some_bind, pure_run, present, decide_false, Bool.false_eq_true, ite_false, decide_true, ite_true]

theorem generated_merge_left {K : Type} [Inhabited K]
    (arena after out : cp.TreeMultiSet K) (left right joined : UInt64)
    (fuel start middle stop : Nat) (leftPresent : left ≠ endIndex) (rightPresent : right ≠ endIndex)
    (priority : (modelCell arena right).priority < (modelCell arena left).priority)
    (sub : (cp.TreeMultiSet.merge_rec fuel arena (modelCell arena left).right right).run (start + 3) =
      some ((joined, after), middle))
    (relink : (cp.TreeMultiSet.update (putCell after left {modelCell after left with right := joined}) left).run middle =
      some (out, stop)) :
    (cp.TreeMultiSet.merge_rec (fuel + 1) arena left right).run start = some ((left, out), stop) := by
  cases arena
  cases after
  cases out
  dsimp only [modelCell, putCell] at priority sub relink
  simp only [cp.TreeMultiSet.merge_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    leftPresent, rightPresent, decide_false, Bool.false_eq_true, ite_false, priority,
    decide_true, ite_true, sub, relink]

theorem generated_merge_right {K : Type} [Inhabited K]
    (arena after out : cp.TreeMultiSet K) (left right joined : UInt64)
    (fuel start middle stop : Nat) (leftPresent : left ≠ endIndex) (rightPresent : right ≠ endIndex)
    (priority : ¬ (modelCell arena right).priority < (modelCell arena left).priority)
    (sub : (cp.TreeMultiSet.merge_rec fuel arena left (modelCell arena right).left).run (start + 3) =
      some ((joined, after), middle))
    (relink : (cp.TreeMultiSet.update (putCell after right {modelCell after right with left := joined}) right).run middle =
      some (out, stop)) :
    (cp.TreeMultiSet.merge_rec (fuel + 1) arena left right).run start = some ((right, out), stop) := by
  cases arena
  cases after
  cases out
  dsimp only [modelCell, putCell] at priority sub relink
  simp only [cp.TreeMultiSet.merge_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    leftPresent, rightPresent, priority, decide_false, Bool.false_eq_true, ite_false, sub, relink]

end Proofs.Cpp.TreeMultiset
