import Proofs.Cpp.TreeMultiset.ArenaRank
import Proofs.Cpp.TreeMultiset.ArenaEnumerate
import Proofs.Math.TreeMultiset.TreapNeighbors

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

abbrev NeighborState (K : Type) := Option (Option K × cp.TreeMultiSet K) × UInt64 × UInt64

def neighborStep {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (upper : Bool) (arena : cp.TreeMultiSet K) (query : K) (_ : Unit) (state : NeighborState K) :
    Cpp.M (ForInStep (NeighborState K)) := do
  tick
  let index := state.2.1
  let saved := state.2.2
  let sentinel ← cp.TreeMultiSet.none (T := K)
  if !(decide (index ≠ sentinel)) then return .done (none, index, saved)
  let row := modelCell arena index
  let current ← Cpp.optionalValue row.key
  if decide (query = current) then return .done (some (some query, arena), index, saved)
  let current ← Cpp.optionalValue row.key
  if decide (query < current) then
    return .yield (none, row.left, if upper then index else saved)
  else
    return .yield (none, row.right, if upper then saved else index)

def finishNeighbor {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (state : NeighborState K) :
    Cpp.M (Option K × cp.TreeMultiSet K) := do
  match state.1 with
  | some result => pure result
  | none =>
    let sentinel ← cp.TreeMultiSet.none (T := K)
    if decide (state.2.2 = sentinel) then return (none, arena)
    let value ← Cpp.optionalValue (modelCell arena state.2.2).key
    return (some value, arena)

def neighborProgram {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (upper : Bool) (arena : cp.TreeMultiSet K) (query : K) : Cpp.M (Option K × cp.TreeMultiSet K) := do
  tick
  let sentinel ← cp.TreeMultiSet.none (T := K)
  let result ← forIn Cpp.forever (none, arena.root, sentinel) (neighborStep upper arena query)
  finishNeighbor arena result

theorem generated_find_lower_program {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key : K) :
    cp.TreeMultiSet.find_lower arena key = neighborProgram false arena key := by
  cases arena
  unfold cp.TreeMultiSet.find_lower neighborProgram neighborStep finishNeighbor modelCell
  dsimp only
  congr 1
  funext tickResult
  congr 1
  funext sentinel
  congr 1
  funext state
  cases state.1 <;> rfl

theorem generated_find_upper_program {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key : K) :
    cp.TreeMultiSet.find_upper arena key = neighborProgram true arena key := by
  cases arena
  unfold cp.TreeMultiSet.find_upper neighborProgram neighborStep finishNeighbor modelCell
  dsimp only
  congr 1
  funext tickResult
  congr 1
  funext sentinel
  congr 1
  funext state
  cases state.1 <;> rfl

def neighbor {K : Type} [LT K] [DecidableLT K] [DecidableEq K] (upper : Bool) (query : K) (tree : Tree K) :
    Option K := if upper then tree.upper query else tree.lower query

private theorem neighbor_step_end {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (upper : Bool) (arena : cp.TreeMultiSet K) (key : K) (saved : UInt64) (start : Nat) :
    (neighborStep upper arena key () (none, endIndex, saved)).run start =
      some (.done (none, endIndex, saved), start + 2) := by
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  have noneRun : (cp.TreeMultiSet.none (T := K)).run (start + 1) = some (endIndex, start + 2) := rfl
  simp [neighborStep, StateT.run_bind, tickRun, noneRun]

private theorem neighbor_step_node {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (upper : Bool) (arena : cp.TreeMultiSet K) (key current : K) (index saved : UInt64)
    (present : index ≠ endIndex) (keyEq : (modelCell arena index).key = some current) (start : Nat) :
    let row := modelCell arena index
    let next : ForInStep (NeighborState K) :=
      if key = current then .done (some (some key, arena), index, saved)
      else if key < current then .yield (none, row.left, if upper then index else saved)
      else .yield (none, row.right, if upper then saved else index)
    (neighborStep upper arena key () (none, index, saved)).run start = some (next, start + 2) := by
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  have noneRun : (cp.TreeMultiSet.none (T := K)).run (start + 1) = some (endIndex, start + 2) := rfl
  by_cases equal : key = current <;> by_cases less : key < current <;>
    simp [neighborStep, StateT.run_bind, tickRun, noneRun, present, keyEq, equal, less, Cpp.optionalValue]

private theorem neighbor_loop_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (upper : Bool) (arena : cp.TreeMultiSet K) (tree : Tree K) (query : K) (index saved : UInt64)
    (fallback : Option K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode index) tree used)
    (savedAt : ParentAt arena saved fallback)
    (fits : arena.slots.size ≤ 2 ^ 63) (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ (hit : Option K) (finalIndex finalSaved : UInt64) (finalFallback : Option K) (stop : Nat),
      (Cpp.loopFuel fuel (none, index, saved) (neighborStep upper arena query)).run start =
        some ((hit.map (fun value => (some value, arena)), finalIndex, finalSaved), stop) ∧
      stop ≤ start + 2 * (tree.height + 1) ∧ ParentAt arena finalSaved finalFallback ∧
      hit.or finalFallback = (neighbor upper query tree).or fallback := by
  induction tree generalizing index saved fallback used fuel start with
  | empty =>
    generalize decoded : decode index = root at layout
    cases layout with
    | empty =>
      have sentinel := (decode_none _).mp decoded
      subst index
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        refine ⟨none, endIndex, saved, fallback, start + 2, ?_, by simp [Tree.height], savedAt, ?_⟩
        · simp [Cpp.loopFuel, neighbor_step_end]
        · cases upper <;> rfl
  | node current priority count left right ihLeft ihRight =>
    generalize decoded : decode index = root at layout
    cases layout with
    | @node slot _ _ _ _ _ lc rc ls rs reads ll rr lf rf sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        obtain ⟨present, _⟩ := decode_some index slot decoded
        obtain ⟨_, _, view⟩ := modelCell_view arena index slot _ decoded reads fits
        let row := modelCell arena index
        have keyEq : row.key = some current := congrArg StoredNode.key view
        have leftEq : decode row.left = lc := congrArg StoredNode.left view
        have rightEq : decode row.right = rc := congrArg StoredNode.right view
        have here : ParentAt arena index (some current) := ⟨present, keyEq⟩
        have step : (neighborStep upper arena query () (none, index, saved)).run start =
            some ((if query = current then ForInStep.done (some (some query, arena), index, saved)
              else if query < current then .yield (none, row.left, if upper then index else saved)
              else .yield (none, row.right, if upper then saved else index)), start + 2) :=
          neighbor_step_node upper arena query current index saved present keyEq start
        simp only [Tree.height] at enough
        by_cases same : query = current
        · have done : (neighborStep upper arena query () (none, index, saved)).run start =
              some (.done (some (some query, arena), index, saved), start + 2) := by
            simpa only [ite_eq_left same] using step
          refine ⟨some query, index, saved, fallback, start + 2, ?_, ?_, savedAt, ?_⟩
          · simp [Cpp.loopFuel, StateT.run_bind, done]
          · simp only [Tree.height]; omega
          · cases upper <;> simp [neighbor, Tree.lower, Tree.upper, same]
        · by_cases less : query < current
          · let next := if upper then index else saved
            let option := if upper then some current else fallback
            have stored : ParentAt arena next option := by
              cases upper
              · exact savedAt
              · exact here
            have leading : (neighborStep upper arena query () (none, index, saved)).run start =
                some (.yield (none, row.left, next), start + 2) := by
              simpa only [ite_eq_right same, ite_eq_left less] using step
            obtain ⟨hit, final, finalSaved, finalOption, stop, run, cost, finalAt, result⟩ :=
              ihLeft row.left next option ls (leftEq.symm ▸ ll) stored fuel (start + 2) (by omega)
            refine ⟨hit, final, finalSaved, finalOption, stop, ?_, ?_, finalAt, ?_⟩
            · simp [Cpp.loopFuel, StateT.run_bind, leading, run]
            · simp only [Tree.height]; omega
            · rw [result]
              cases upper <;>
                simp only [neighbor, Tree.lower, Tree.upper, ite_eq_right same, ite_eq_left less, option,
                  Bool.false_eq_true, ite_false, ite_true, Option.or_assoc, Option.some_or]
          · let next := if upper then saved else index
            let option := if upper then fallback else some current
            have stored : ParentAt arena next option := by
              cases upper
              · exact here
              · exact savedAt
            have leading : (neighborStep upper arena query () (none, index, saved)).run start =
                some (.yield (none, row.right, next), start + 2) := by
              simpa only [ite_eq_right same, ite_eq_right less] using step
            obtain ⟨hit, final, finalSaved, finalOption, stop, run, cost, finalAt, result⟩ :=
              ihRight row.right next option rs (rightEq.symm ▸ rr) stored fuel (start + 2) (by omega)
            refine ⟨hit, final, finalSaved, finalOption, stop, ?_, ?_, finalAt, ?_⟩
            · simp [Cpp.loopFuel, StateT.run_bind, leading, run]
            · simp only [Tree.height]; omega
            · rw [result]
              cases upper <;>
                simp only [neighbor, Tree.lower, Tree.upper, ite_eq_right same, ite_eq_right less, option,
                  Bool.false_eq_true, ite_false, ite_true, Option.or_assoc, Option.some_or]

private theorem finish_neighbor_run {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (hit : Option K) (final saved : UInt64) (option : Option K) (savedAt : ParentAt arena saved option)
    (start : Nat) :
    (finishNeighbor arena (hit.map (fun value => (some value, arena)), final, saved)).run start =
      some ((hit.or option, arena), start + if hit.isSome then 0 else 1) := by
  cases hit with
  | some value => rfl
  | none =>
    have noneRun : (cp.TreeMultiSet.none (T := K)).run start = some (endIndex, start + 1) := rfl
    cases option with
    | none =>
      have endCode : saved = endIndex := savedAt
      simp [finishNeighbor, StateT.run_bind, noneRun, endCode]
    | some value =>
      obtain ⟨present, keyEq⟩ := savedAt
      simp [finishNeighbor, StateT.run_bind, noneRun, present, keyEq, Cpp.optionalValue]

theorem generated_neighbor_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (upper : Bool) (arena : cp.TreeMultiSet K) (tree : Tree K) (query : K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ stop, (neighborProgram upper arena query).run start = some ((neighbor upper query tree, arena), stop) ∧
      stop ≤ start + 2 * tree.height + 5 := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨hit, final, finalSaved, option, middle, scan, cost, saved, result⟩ :=
    neighbor_loop_spec upper arena tree query arena.root endIndex none used layout rfl fits Cpp.fuel (start + 2) enough
  have loopRun : (forIn Cpp.forever (none, arena.root, endIndex) (neighborStep upper arena query)).run (start + 2) =
      some ((hit.map (fun value => (some value, arena)), final, finalSaved), middle) := scan
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  have noneRun : (cp.TreeMultiSet.none (T := K)).run (start + 1) = some (endIndex, start + 2) := rfl
  have finish := finish_neighbor_run arena hit final finalSaved option saved middle
  rw [result, Option.or_none] at finish
  refine ⟨middle + (if hit.isSome then 0 else 1), ?_, ?_⟩
  · simp [neighborProgram, StateT.run_bind, tickRun, noneRun, loopRun, finish]
  · cases hit <;> simp at * <;> omega

theorem generated_find_lower_spec {K : Type} [Inhabited K] [LinearOrder K] (arena : cp.TreeMultiSet K) (tree : Tree K)
    (query : K) (used : List Nat) (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (ordered : tree.Ordered) (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ value stop, (cp.TreeMultiSet.find_lower arena query).run start = some ((value, arena), stop) ∧
      stop ≤ start + 2 * tree.height + 5 ∧ Tree.BestBelow tree.entries query value := by
  rw [generated_find_lower_program]
  obtain ⟨stop, run, cost⟩ := generated_neighbor_spec false arena tree query used layout fits start
  exact ⟨tree.lower query, stop, run, cost, Tree.lower_spec query tree ordered⟩

theorem generated_find_upper_spec {K : Type} [Inhabited K] [LinearOrder K] (arena : cp.TreeMultiSet K) (tree : Tree K)
    (query : K) (used : List Nat) (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (ordered : tree.Ordered) (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ value stop, (cp.TreeMultiSet.find_upper arena query).run start = some ((value, arena), stop) ∧
      stop ≤ start + 2 * tree.height + 5 ∧ Tree.BestAbove tree.entries query value := by
  rw [generated_find_upper_program]
  obtain ⟨stop, run, cost⟩ := generated_neighbor_spec true arena tree query used layout fits start
  exact ⟨tree.upper query, stop, run, cost, Tree.upper_spec query tree ordered⟩

end Proofs.Cpp.TreeMultiset
