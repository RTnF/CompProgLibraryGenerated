import Proofs.Cpp.TreeSet.Erase
import Proofs.Cpp.TreeSet.Rank

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

abbrev FindState (K : Type) := Option (Bool × cp.TreeSet K) × UInt64

def findStep {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) (_ : Unit) (state : FindState K) : Cpp.M (ForInStep (FindState K)) := do
  Cpp.tick
  let i := state.2
  let sentinel ← cp.TreeSet.none (T := K)
  if !(decide (i ≠ sentinel)) then return .done (none, i)
  let current ← Cpp.optionalValue (cell arena.slots i).key
  if decide (key < current) then return .yield (none, (cell arena.slots i).left)
  let current ← Cpp.optionalValue (cell arena.slots i).key
  if decide (current < key) then return .yield (none, (cell arena.slots i).right)
  else return .done (some (true, arena), i)

theorem generated_find_program {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) :
    cp.TreeSet.find arena key = (do
      Cpp.tick
      let result ← forIn Cpp.forever (none, arena.root) (findStep arena key)
      pure (result.1.getD (false, arena))) := by
  rcases arena with ⟨_, _, _⟩
  unfold cp.TreeSet.find findStep cell
  dsimp only
  congr 1
  funext tick
  congr 1
  funext state
  cases state.1 <;> rfl

private theorem some_bind {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl
private theorem sentinel_run {K : Type} (clock : Nat) :
    (cp.TreeSet.none (T := K)).run clock = some (endIndex, clock + 1) := rfl

private theorem find_empty {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) (start : Nat) :
    (findStep arena key () (none, endIndex)).run start = some (.done (none, endIndex), start + 2) := by
  simp [findStep, StateT.run_bind, tick_run, sentinel_run, Nat.add_assoc]

private theorem find_node {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key current : K) (i : UInt64) (start : Nat)
    (nonnull : i ≠ endIndex) (value : (cell arena.slots i).key = some current) :
    (findStep arena key () (none, i)).run start =
      if key < current then some (.yield (none, (cell arena.slots i).left), start + 2)
      else if current < key then some (.yield (none, (cell arena.slots i).right), start + 2)
      else some (.done (some (true, arena), i), start + 2) := by
  by_cases lo : key < current <;> by_cases hi : current < key <;>
    simp [findStep, StateT.run_bind, tick_run, sentinel_run, nonnull, Cpp.optionalValue, value,
      lo, hi, Nat.add_assoc]

private theorem find_loop {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) {tree : Tree K} {i : UInt64} {used : List Nat}
    (layout : Layout arena.slots i tree used) (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ dst stop,
      (Cpp.loopFuel fuel (none, i) (findStep arena key)).run start =
        some (((tree.rank key).map (fun _ => (true, arena)), dst), stop) ∧
      stop ≤ start + 2 + 2 * tree.height := by
  induction tree generalizing i used fuel start with
  | empty =>
    cases layout
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      exact ⟨endIndex, start + 2, by simp [Tree.rank, Cpp.loopFuel, StateT.run_bind, find_empty],
        by simp [Tree.height]⟩
  | node left current right il ir =>
    cases layout with
    | @node i current l r ls rs allocated nonnull value heights sizes _ _ ll rr fl fr distinct =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        have step := find_node arena key current i start nonnull value
        simp only [Tree.height] at enough
        by_cases goLeft : key < current
        · rw [ite_eq_left goLeft] at step
          obtain ⟨dst, stop, run, cost⟩ := il ll fuel (start + 2) (by omega)
          refine ⟨dst, stop, ?_, by simp only [Tree.height]; omega⟩
          simpa [Tree.rank, goLeft, Cpp.loopFuel, StateT.run_bind, step, some_bind] using run
        · by_cases goRight : current < key
          · rw [ite_eq_right goLeft, ite_eq_left goRight] at step
            obtain ⟨dst, stop, run, cost⟩ := ir rr fuel (start + 2) (by omega)
            refine ⟨dst, stop, ?_, by simp only [Tree.height]; omega⟩
            have same : ((right.rank key).map (fun n => left.size + 1 + n)).map (fun _ => (true, arena)) =
                (right.rank key).map (fun _ => (true, arena)) := by cases right.rank key <;> rfl
            simpa only [Tree.rank, ite_eq_right goLeft, ite_eq_left goRight, same, Cpp.loopFuel,
              StateT.run_bind, step, some_bind] using run
          · rw [ite_eq_right goLeft, ite_eq_right goRight] at step
            exact ⟨i, start + 2, by simp [Tree.rank, goLeft, goRight, Cpp.loopFuel, StateT.run_bind, step],
              by simp only [Tree.height]; omega⟩

theorem generated_find_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (key : K) (tree : Tree K) (used : List Nat)
    (layout : Layout arena.slots arena.root tree used) (fits : arena.slots.size ≤ 2 ^ 63)
    (balanced : tree.Balanced) (ordered : tree.Ordered) (start : Nat) :
    ∃ stop, (cp.TreeSet.find arena key).run start = some ((decide (key ∈ tree.keys), arena), stop) ∧
      stop ≤ start + 3 + 2 * (2 * (tree.size + 1).log2 + 1) := by
  have capacity := layout.capacity
  have height := tree.height_le_size
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨dst, stop, run, cost⟩ := find_loop arena key layout Cpp.fuel (start + 1) enough
  have scan : (forIn Cpp.forever (none, arena.root) (findStep arena key)).run (start + 1) =
      some (((tree.rank key).map (fun _ => (true, arena)), dst), stop) := run
  refine ⟨stop, ?_, by have b := tree.height_logarithmic balanced; omega⟩
  rw [generated_find_program]
  cases rankEq : tree.rank key with
  | none => simp [StateT.run_bind, tick_run, scan, rankEq, (tree.rank_absent key ordered).mp rankEq]
  | some i =>
    have present : key ∈ tree.keys := by
      by_contra h
      have absent := (tree.rank_absent key ordered).mpr h
      rw [rankEq] at absent
      contradiction
    simp [StateT.run_bind, tick_run, scan, rankEq, present]

end Proofs.Cpp.TreeSet
