import Proofs.Cpp.TreeMultiset.EraseLayout

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

abbrev LocateState (K : Type) := Option (UInt64 × cp.TreeMultiSet K) × UInt64

def locateStep {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key : K) (_ : Unit) (state : LocateState K) : Cpp.M (ForInStep (LocateState K)) := do
  tick
  let sentinel ← cp.TreeMultiSet.none (T := K)
  let index := state.2
  if !(decide (index ≠ sentinel)) then
    return .done (none, index)
  let current ← Cpp.optionalValue (modelCell arena index).key
  if decide (key = current) then return .done (some (index, arena), index)
  let current ← Cpp.optionalValue (modelCell arena index).key
  let child := if decide (key < current) then (modelCell arena index).left else (modelCell arena index).right
  return .yield (none, child)

def finishLocate {K : Type} (arena : cp.TreeMultiSet K) (state : LocateState K) : Cpp.M (UInt64 × cp.TreeMultiSet K) := do
  match state.1 with
  | some result => pure result
  | none =>
    let sentinel ← cp.TreeMultiSet.none (T := K)
    return (sentinel, arena)

theorem generated_locate_program {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key : K) :
    cp.TreeMultiSet.locate arena key = (do
      tick
      let result ← forIn Cpp.forever (none, arena.root) (locateStep arena key)
      finishLocate arena result) := by
  cases arena
  unfold cp.TreeMultiSet.locate locateStep finishLocate modelCell
  dsimp only
  congr 1
  funext tickResult
  congr 1
  funext state
  cases state.1 <;> rfl

private theorem tick_run (start : Nat) : Cpp.tick.run start = some ((), start + 1) := rfl

private theorem none_run {K : Type} (start : Nat) :
    (cp.TreeMultiSet.none (T := K)).run start = some (endIndex, start + 1) := rfl

private theorem some_bind {A B : Type} (value : A) (f : A → Option B) :
    (some value >>= f) = f value := rfl

theorem locate_step_end {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key : K) (start : Nat) :
    (locateStep arena key () (none, endIndex)).run start = some (.done (none, endIndex), start + 2) := by
  simp [locateStep, StateT.run_bind, tick_run, none_run, some_bind]

theorem locate_step_here {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key : K) (code : UInt64)
    (present : code ≠ endIndex) (keyEq : (modelCell arena code).key = some key) (start : Nat) :
    (locateStep arena key () (none, code)).run start = some (.done (some (code, arena), code), start + 2) := by
  simp [locateStep, StateT.run_bind, tick_run, none_run, some_bind,
    present, keyEq, Cpp.optionalValue]

theorem locate_step_child {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key current : K) (code : UInt64)
    (present : code ≠ endIndex) (keyEq : (modelCell arena code).key = some current) (different : key ≠ current)
    (start : Nat) :
    let row := modelCell arena code
    let child := if key < current then row.left else row.right
    (locateStep arena key () (none, code)).run start = some (.yield (none, child), start + 2) := by
  by_cases less : key < current <;>
    simp [locateStep, StateT.run_bind, tick_run, none_run, some_bind,
      present, keyEq, different, Cpp.optionalValue, less]

end Proofs.Cpp.TreeMultiset
