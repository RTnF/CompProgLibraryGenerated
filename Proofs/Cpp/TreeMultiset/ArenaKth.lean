import Proofs.Cpp.TreeMultiset.ArenaExtrema
import Proofs.Math.TreeMultiset.TreapSelection

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

abbrev SelectionState (K : Type) := Option (K × cp.TreeMultiSet K) × UInt64 × UInt64

def selectionStep {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (_ : Unit)
    (state : SelectionState K) : Cpp.M (ForInStep (SelectionState K)) := do
  Cpp.tick
  let position := state.2.1
  let index := state.2.2
  let row := modelCell arena index
  let less ← cp.TreeMultiSet.weight arena row.left
  if decide (position < less) then
    return .yield (none, position, row.left)
  else if decide (position < less + row.count) then
    let key ← Cpp.optionalValue row.key
    return .done (some (key, arena), position, index)
  else
    return .yield (none, position - (less + row.count), row.right)

def finishSelection {K : Type} (state : SelectionState K) : Cpp.M (K × cp.TreeMultiSet K) :=
  match state.1 with
  | some result => pure result
  | none => failure

theorem generated_kth_program {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (position : UInt64) :
    cp.TreeMultiSet.get_kth arena position = (do
      Cpp.tick
      let weight ← cp.TreeMultiSet.weight arena arena.root
      Cpp.check (decide (position < weight))
      let result ← forIn Cpp.forever (none, position, arena.root) (selectionStep arena)
      finishSelection result) := by
  cases arena
  unfold cp.TreeMultiSet.get_kth selectionStep finishSelection modelCell
  dsimp only
  congr 1
  funext tickResult
  congr 1
  funext weight
  congr 1
  funext checkResult
  congr 1
  funext state
  cases state.1 <;> rfl

private theorem selection_step_run {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (position index : UInt64) (key : K)
    (keyEq : (modelCell arena index).key = some key) (start : Nat) :
    let row := modelCell arena index
    let less := modelWeight arena row.left
    let next := if position < less then ForInStep.yield ((none, position, row.left) : SelectionState K)
      else if position < less + row.count then ForInStep.done (some (key, arena), position, index)
      else ForInStep.yield (none, position - (less + row.count), row.right)
    (selectionStep arena () (none, position, index)).run start = some (next, start + 3) := by
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  have weightRun :
      (cp.TreeMultiSet.weight arena (modelCell arena index).left).run (start + 1) =
        some (modelWeight arena (modelCell arena index).left, start + 3) :=
    generated_weight_run arena (modelCell arena index).left (start + 1)
  by_cases smaller : position < modelWeight arena (modelCell arena index).left <;>
    by_cases within : position < modelWeight arena (modelCell arena index).left + (modelCell arena index).count <;>
    simp [selectionStep, StateT.run_bind, tickRun, weightRun, keyEq, Cpp.optionalValue, smaller, within]

private theorem selection_loop_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (tree : Tree K) (index position : UInt64) (used : List Nat)
    (layout : Realizes (storageView arena) (decode index) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64)
    (valid : position.toNat < tree.weight) (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ selected finalPos finalIndex stop,
      (Cpp.loopFuel fuel (none, position, index) (selectionStep arena)).run start =
        some ((some (selected, arena), finalPos, finalIndex), stop) ∧
      stop ≤ start + 3 * tree.height ∧ tree.select position.toNat = some selected := by
  induction tree generalizing index position used fuel start with
  | empty => simp [Tree.weight] at valid
  | node key priority count left right ihLeft ihRight =>
    generalize decoded : decode index = code at layout
    cases layout with
    | @node slot _ _ _ _ _ lc rc ls rs reads ll rr lf rf sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        obtain ⟨_, _, view⟩ := modelCell_view arena index slot _ decoded reads fits
        let row := modelCell arena index
        have keyEq : row.key = some key := congrArg StoredNode.key view
        have countEq : row.count.toNat = count := congrArg StoredNode.count view
        have leftEq : decode row.left = lc := congrArg StoredNode.left view
        have rightEq : decode row.right = rc := congrArg StoredNode.right view
        have leftLayout : Realizes (storageView arena) (decode row.left) left ls := leftEq.symm ▸ ll
        have rightLayout : Realizes (storageView arena) (decode row.right) right rs := rightEq.symm ▸ rr
        let less := modelWeight arena row.left
        let limit := less + row.count
        have lessNat : less.toNat = left.weight := weight_from_layout arena row.left left ls leftLayout fits
        simp only [Tree.height, Tree.weight] at enough valid weight
        have limitNat : limit.toNat = left.weight + count := by
          dsimp only [limit]
          rw [UInt64.toNat_add, lessNat, countEq, Nat.mod_eq_of_lt (by omega)]
        have lessCompare : position < less ↔ position.toNat < left.weight := by
          rw [UInt64.lt_iff_toNat_lt, lessNat]
        have limitCompare : position < limit ↔ position.toNat < left.weight + count := by
          rw [UInt64.lt_iff_toNat_lt, limitNat]
        have step : (selectionStep arena () (none, position, index)).run start =
            some ((if position < less then ForInStep.yield (none, position, row.left)
              else if position < limit then ForInStep.done (some (key, arena), position, index)
              else ForInStep.yield (none, position - limit, row.right)), start + 3) :=
          selection_step_run arena position index key keyEq start
        by_cases smaller : position < less
        · have initial : (selectionStep arena () (none, position, index)).run start =
              some (.yield (none, position, row.left), start + 3) := by
            simpa only [ite_eq_left smaller] using step
          obtain ⟨value, finalPos, finalIndex, stop, run, work, result⟩ :=
            ihLeft row.left position ls leftLayout (by omega) (lessCompare.mp smaller) fuel (start + 3) (by omega)
          refine ⟨value, finalPos, finalIndex, stop, ?_, ?_, ?_⟩
          · simp [Cpp.loopFuel, StateT.run_bind, initial, run]
          · simp only [Tree.height]; omega
          · simpa only [Tree.select, ite_eq_left (lessCompare.mp smaller)] using result
        · by_cases within : position < limit
          · have initial : (selectionStep arena () (none, position, index)).run start =
                some (.done (some (key, arena), position, index), start + 3) := by
              simpa only [ite_eq_right smaller, ite_eq_left within] using step
            refine ⟨key, position, index, start + 3, ?_, ?_, ?_⟩
            · simp [Cpp.loopFuel, StateT.run_bind, initial]
            · simp only [Tree.height]; omega
            · simp only [Tree.select, ite_eq_right (fun p => smaller (lessCompare.mpr p)), ite_eq_left (limitCompare.mp within)]
          · let adjusted := position - limit
            have atLeast : limit.toNat ≤ position.toNat := Nat.le_of_not_gt (fun h => within (limitCompare.mpr (by rwa [limitNat] at h)))
            have adjustedNat : adjusted.toNat = position.toNat - (left.weight + count) := by
              dsimp only [adjusted]
              rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr atLeast), limitNat]
            have initial : (selectionStep arena () (none, position, index)).run start =
                some (.yield (none, adjusted, row.right), start + 3) := by
              simpa only [ite_eq_right smaller, ite_eq_right within] using step
            obtain ⟨value, finalPos, finalIndex, stop, run, work, result⟩ :=
              ihRight row.right adjusted rs rightLayout (by omega) (by omega) fuel (start + 3) (by omega)
            refine ⟨value, finalPos, finalIndex, stop, ?_, ?_, ?_⟩
            · simp [Cpp.loopFuel, StateT.run_bind, initial, run]
            · simp only [Tree.height]; omega
            · have noLeft := fun p => smaller (lessCompare.mpr p)
              have noHere := fun p => within (limitCompare.mpr p)
              simpa only [Tree.select, ite_eq_right noLeft, ite_eq_right noHere, Nat.sub_sub, ← adjustedNat] using result

theorem generated_get_kth_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (tree : Tree K) (used : List Nat) (position : UInt64)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64) (valid : position.toNat < tree.weight)
    (start : Nat) :
    ∃ key stop, (cp.TreeMultiSet.get_kth arena position).run start = some ((key, arena), stop) ∧
      stop ≤ start + 3 + 3 * tree.height ∧ tree.expanded[position.toNat]? = some key := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨word, rootWeight, wordNat⟩ := generated_weight_spec arena arena.root tree used layout fits (start + 1)
  have inRange : position < word := UInt64.lt_iff_toNat_lt.mpr (wordNat.symm ▸ valid)
  obtain ⟨key, finalPos, finalIndex, stop, scan, cost, expected⟩ :=
    selection_loop_spec arena tree arena.root position used layout fits weight valid Cpp.fuel (start + 3) enough
  have loopRun : (forIn Cpp.forever (none, position, arena.root) (selectionStep arena)).run (start + 3) =
      some ((some (key, arena), finalPos, finalIndex), stop) := scan
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  refine ⟨key, stop, ?_, cost, ?_⟩
  · rw [generated_kth_program]
    simp [StateT.run_bind, tickRun, rootWeight, Cpp.check, inRange, loopRun, finishSelection]
  · rwa [← Tree.select_expanded]


end Proofs.Cpp.TreeMultiset
