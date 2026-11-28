import Proofs.Cpp.TreeSet.Layout

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

theorem Tree.height_le_size (tree : Tree K) : tree.height ≤ tree.size := by
  induction tree with
  | empty => rfl
  | node left key right il ir => simp only [Tree.height, Tree.size]; omega

abbrev SelectionState (K : Type) := Option K × UInt64 × UInt64

def selectionStep {K : Type} [Inhabited K] (arena : cp.TreeSet K) (_ : Unit)
    (state : SelectionState K) : Cpp.M (ForInStep (SelectionState K)) := do
  Cpp.tick
  let position := state.2.1
  let index := state.2.2
  let row := cell arena.slots index
  let less ← cp.TreeSet.subtree_size arena row.left
  if decide (position < less) then
    return .yield (none, position, row.left)
  else if decide (position = less) then
    let key ← Cpp.optionalValue row.key
    return .done (some key, position, index)
  else
    return .yield (none, position - (less + 1), row.right)

def finishSelection {K : Type} (state : SelectionState K) : Cpp.M K :=
  match state.1 with
  | some key => pure key
  | none => failure

theorem generated_kth_program {K : Type} [Inhabited K] (arena : cp.TreeSet K) (position : UInt64) :
    cp.TreeSet.get_kth arena position = (do
      Cpp.tick
      let weight ← cp.TreeSet.subtree_size arena arena.root
      Cpp.check (decide (position < weight))
      let result ← forIn Cpp.forever (none, position, arena.root) (selectionStep arena)
      finishSelection result) := by
  cases arena
  unfold cp.TreeSet.get_kth selectionStep finishSelection cell
  dsimp only
  congr 1

private theorem selection_step_run {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (position index : UInt64) (key : K)
    (keyEq : (cell arena.slots index).key = some key) (start : Nat) :
    let row := cell arena.slots index
    let less := modelSize arena row.left
    let next := if position < less then ForInStep.yield ((none, position, row.left) : SelectionState K)
      else if position = less then ForInStep.done (some key, position, index)
      else ForInStep.yield (none, position - (less + 1), row.right)
    (selectionStep arena () (none, position, index)).run start = some (next, start + 3) := by
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  by_cases smaller : position < modelSize arena (cell arena.slots index).left <;>
    by_cases same : position = modelSize arena (cell arena.slots index).left <;>
    simp [selectionStep, StateT.run_bind, tickRun, generated_size_run, keyEq, Cpp.optionalValue, smaller, same]

private theorem selection_loop_spec {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (tree : Tree K) (index position : UInt64) (used : List Nat)
    (layout : Layout arena.slots index tree used)
    (weight : tree.size < 2 ^ 64)
    (valid : position.toNat < tree.size) (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ selected finalPos finalIndex stop,
      (Cpp.loopFuel fuel (none, position, index) (selectionStep arena)).run start =
        some ((some selected, finalPos, finalIndex), stop) ∧
      stop ≤ start + 3 * tree.height ∧ tree.select position.toNat = some selected := by
  induction tree generalizing index position used fuel start with
  | empty => simp [Tree.size] at valid
  | node keyLeft key keyRight ihLeft ihRight =>
    cases layout with
    | @node index key left right ls rs allocated notEnd keyEq heights sizes _ _ leftLayout rightLayout fl fr sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        let row := cell arena.slots index
        let less := modelSize arena row.left
        have lessNat : less.toNat = keyLeft.size := leftLayout.model_size
        simp only [Tree.height, Tree.size] at enough valid weight
        have cmp : position < less ↔ position.toNat < keyLeft.size := by
          rw [UInt64.lt_iff_toNat_lt, lessNat]
        have eq : position = less ↔ position.toNat = keyLeft.size := by
          rw [← UInt64.toNat_inj, lessNat]
        have step := selection_step_run arena position index key keyEq start
        change _ = some ((if position < less then ForInStep.yield (none, position, row.left)
          else if position = less then ForInStep.done (some key, position, index)
          else ForInStep.yield (none, position - (less + 1), row.right)), start + 3) at step
        by_cases smaller : position < less
        · have initial : (selectionStep arena () (none, position, index)).run start =
              some (.yield (none, position, row.left), start + 3) := by
            simpa only [ite_eq_left smaller] using step
          obtain ⟨value, finalPos, finalIndex, stop, run, work, result⟩ :=
            ihLeft row.left position ls leftLayout (by omega) (cmp.mp smaller) fuel (start + 3) (by omega)
          refine ⟨value, finalPos, finalIndex, stop, ?_, ?_, ?_⟩
          · simp [Cpp.loopFuel, StateT.run_bind, initial, run]
          · simp only [Tree.height]; omega
          · simpa only [Tree.select, ite_eq_left (cmp.mp smaller)] using result
        · by_cases same : position = less
          · have initial : (selectionStep arena () (none, position, index)).run start =
                some (.done (some key, position, index), start + 3) := by
              simpa only [ite_eq_right smaller, ite_eq_left same] using step
            refine ⟨key, position, index, start + 3, ?_, ?_, ?_⟩
            · simp [Cpp.loopFuel, StateT.run_bind, initial]
            · simp only [Tree.height]; omega
            · simp only [Tree.select, ite_eq_right (fun p => smaller (cmp.mpr p)), ite_eq_left (eq.mp same)]
          · let adjusted := position - (less + 1)
            have limitNat : (less + 1).toNat = keyLeft.size + 1 := by
              rw [UInt64.toNat_add, lessNat]
              change (keyLeft.size + 1) % (2 ^ 64) = keyLeft.size + 1
              exact Nat.mod_eq_of_lt (by omega)
            have atLeast : (less + 1).toNat ≤ position.toNat := by
              rw [limitNat]
              have atOrPast : keyLeft.size ≤ position.toNat := Nat.le_of_not_gt (fun p => smaller (cmp.mpr p))
              have different : position.toNat ≠ keyLeft.size := fun p => same (eq.mpr p)
              omega
            have adjustedNat : adjusted.toNat = position.toNat - keyLeft.size - 1 := by
              dsimp only [adjusted]
              rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr atLeast), limitNat, Nat.sub_sub]
            have initial : (selectionStep arena () (none, position, index)).run start =
                some (.yield (none, adjusted, row.right), start + 3) := by
              simpa only [ite_eq_right smaller, ite_eq_right same] using step
            obtain ⟨value, finalPos, finalIndex, stop, run, work, result⟩ :=
              ihRight row.right adjusted rs rightLayout (by omega) (by omega) fuel (start + 3) (by omega)
            refine ⟨value, finalPos, finalIndex, stop, ?_, ?_, ?_⟩
            · simp [Cpp.loopFuel, StateT.run_bind, initial, run]
            · simp only [Tree.height]; omega
            · have noLeft := fun p => smaller (cmp.mpr p)
              have noHere := fun p => same (eq.mpr p)
              simpa only [Tree.select, ite_eq_right noLeft, ite_eq_right noHere, ← adjustedNat] using result

theorem generated_get_kth_spec {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (tree : Tree K) (used : List Nat) (position : UInt64)
    (layout : Layout arena.slots arena.root tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (valid : position.toNat < tree.size)
    (balanced : tree.Balanced) (start : Nat) :
    ∃ key stop, (cp.TreeSet.get_kth arena position).run start = some (key, stop) ∧
      stop ≤ start + 3 + 3 * (2 * (tree.size + 1).log2 + 1) ∧ tree.keys[position.toNat]? = some key := by
  have capacity := layout.capacity
  have height := tree.height_le_size
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  have inRange : position < modelSize arena arena.root :=
    UInt64.lt_iff_toNat_lt.mpr (layout.model_size.symm ▸ valid)
  obtain ⟨key, finalPos, finalIndex, stop, scan, cost, expected⟩ :=
    selection_loop_spec arena tree arena.root position used layout (by omega) valid Cpp.fuel (start + 3) enough
  have loopRun : (forIn Cpp.forever (none, position, arena.root) (selectionStep arena)).run (start + 3) =
      some ((some key, finalPos, finalIndex), stop) := scan
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  refine ⟨key, stop, ?_, ?_, ?_⟩
  · rw [generated_kth_program]
    simp [StateT.run_bind, tickRun, generated_size_run, Cpp.check, inRange, loopRun, finishSelection]
  · have logBound := tree.height_logarithmic balanced
    omega
  · rwa [← Tree.select_correct]

end Proofs.Cpp.TreeSet
