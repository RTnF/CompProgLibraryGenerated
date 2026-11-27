import Proofs.Cpp.TreeMultiset.ArenaKth

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

abbrev RankValue := Int × Int
abbrev RankState (K : Type) := Option (RankValue × cp.TreeMultiSet K) × UInt64 × UInt64

def rankStep {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key : K) (_ : Unit) (state : RankState K) : Cpp.M (ForInStep (RankState K)) := do
  tick
  let index := state.2.1
  let offset := state.2.2
  let sentinel ← cp.TreeMultiSet.none (T := K)
  if !(decide (index ≠ sentinel)) then return .done (none, index, offset)
  let row := modelCell arena index
  let current ← Cpp.optionalValue row.key
  if decide (key = current) then
    let less ← cp.TreeMultiSet.weight arena row.left
    let first := offset + less
    let bounds := (Cpp.toSigned 32 first.toNat, Cpp.toSigned 32 (first + row.count).toNat)
    return .done (some (bounds, arena), index, offset)
  let current ← Cpp.optionalValue row.key
  if decide (key < current) then
    return .yield (none, row.left, offset)
  else
    let less ← cp.TreeMultiSet.weight arena row.left
    return .yield (none, row.right, offset + (less + row.count))

def finishRank {K : Type} (arena : cp.TreeMultiSet K) (state : RankState K) : Cpp.M (RankValue × cp.TreeMultiSet K) :=
  match state.1 with
  | some result => pure result
  | none => pure ((-1, -1), arena)

theorem generated_rank_program {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key : K) :
    cp.TreeMultiSet.rank arena key = (do
      tick
      let result ← forIn Cpp.forever (none, arena.root, 0) (rankStep arena key)
      finishRank arena result) := by
  cases arena
  unfold cp.TreeMultiSet.rank rankStep finishRank modelCell
  dsimp only
  congr 1
  funext tickResult
  congr 1
  funext result
  cases result.1 <;> rfl

private theorem rank_step_end {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key : K) (offset : UInt64) (start : Nat) :
    (rankStep arena key () (none, endIndex, offset)).run start =
      some (.done (none, endIndex, offset), start + 2) := by
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  have noneRun : (cp.TreeMultiSet.none (T := K)).run (start + 1) = some (endIndex, start + 2) := rfl
  simp [rankStep, StateT.run_bind, tickRun, noneRun]

private theorem rank_step_node {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (key current : K) (index offset : UInt64)
    (present : index ≠ endIndex) (keyEq : (modelCell arena index).key = some current) (start : Nat) :
    let row := modelCell arena index
    let less := modelWeight arena row.left
    let first := offset + less
    let interval := (Cpp.toSigned 32 first.toNat, Cpp.toSigned 32 (first + row.count).toNat)
    let next : ForInStep (RankState K) :=
      if key = current then .done (some (interval, arena), index, offset)
      else if key < current then .yield (none, row.left, offset)
      else .yield (none, row.right, offset + (less + row.count))
    let cost := if key ≠ current ∧ key < current then 2 else 4
    (rankStep arena key () (none, index, offset)).run start = some (next, start + cost) := by
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  have noneRun : (cp.TreeMultiSet.none (T := K)).run (start + 1) = some (endIndex, start + 2) := rfl
  have leftRun :
      (cp.TreeMultiSet.weight arena (modelCell arena index).left).run (start + 2) =
        some (modelWeight arena (modelCell arena index).left, start + 4) :=
    generated_weight_run arena (modelCell arena index).left (start + 2)
  by_cases equal : key = current <;> by_cases less : key < current <;>
    simp [rankStep, StateT.run_bind, tickRun, noneRun, leftRun, present, keyEq, equal, less, Cpp.optionalValue]

def encodedRank (offset : Nat) (bounds : Nat × Nat) : RankValue :=
  (Cpp.toSigned 32 (offset + bounds.1), Cpp.toSigned 32 (offset + bounds.2))

private theorem rank_loop_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (tree : Tree K) (key : K) (index offset : UInt64) (used : List Nat)
    (layout : Realizes (storageView arena) (decode index) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : offset.toNat + tree.weight < 2 ^ 64)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ finalIndex finalOffset stop,
      (Cpp.loopFuel fuel (none, index, offset) (rankStep arena key)).run start =
        some ((((tree.rankBounds key).map (fun result => (encodedRank offset.toNat result, arena))), finalIndex, finalOffset), stop) ∧
      stop ≤ start + 4 * tree.height + 2 := by
  induction tree generalizing index offset used fuel start with
  | empty =>
    generalize decoded : decode index = root at layout
    cases layout with
    | empty =>
      have sentinel := (decode_none _).mp decoded
      subst index
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        refine ⟨endIndex, offset, start + 2, ?_, by simp [Tree.height]⟩
        simp [Cpp.loopFuel, rank_step_end, Tree.rankBounds]
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
        have countEq : row.count.toNat = count := congrArg StoredNode.count view
        have leftEq : decode row.left = lc := congrArg StoredNode.left view
        have rightEq : decode row.right = rc := congrArg StoredNode.right view
        have leftLayout : Realizes (storageView arena) (decode row.left) left ls := leftEq.symm ▸ ll
        have rightLayout : Realizes (storageView arena) (decode row.right) right rs := rightEq.symm ▸ rr
        let less := modelWeight arena row.left
        have lessNat : less.toNat = left.weight := weight_from_layout arena row.left left ls leftLayout fits
        simp only [Tree.weight, Tree.height] at weight enough
        let first := offset + less
        have firstNat : first.toNat = offset.toNat + left.weight := by
          dsimp only [first]
          rw [UInt64.toNat_add, lessNat, Nat.mod_eq_of_lt (by omega)]
        have lastNat : (first + row.count).toNat = offset.toNat + left.weight + count := by
          rw [UInt64.toNat_add, firstNat, countEq, Nat.mod_eq_of_lt (by omega)]
        have nextNat : (offset + (less + row.count)).toNat = offset.toNat + (left.weight + count) := by
          rw [UInt64.toNat_add, UInt64.toNat_add, lessNat, countEq,
            Nat.mod_eq_of_lt (by omega : left.weight + count < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
        have step : (rankStep arena key () (none, index, offset)).run start =
            some ((if key = current then ForInStep.done
                (some ((Cpp.toSigned 32 first.toNat, Cpp.toSigned 32 (first + row.count).toNat), arena), index, offset)
              else if key < current then .yield (none, row.left, offset)
              else .yield (none, row.right, offset + (less + row.count))),
              start + (if key ≠ current ∧ key < current then 2 else 4)) :=
          rank_step_node arena key current index offset present keyEq start
        by_cases equal : key = current
        · have done : (rankStep arena key () (none, index, offset)).run start =
              some (.done (some ((Cpp.toSigned 32 first.toNat, Cpp.toSigned 32 (first + row.count).toNat), arena),
                index, offset), start + 4) := by
            simpa [equal] using step
          refine ⟨index, offset, start + 4, ?_, ?_⟩
          · simp only [Cpp.loopFuel, StateT.run_bind, done]
            simp [Tree.rankBounds, equal, encodedRank, firstNat, lastNat, Nat.add_assoc]
          · simp only [Tree.height]; omega
        · by_cases goLeft : key < current
          · have initial : (rankStep arena key () (none, index, offset)).run start =
                some (.yield (none, row.left, offset), start + 2) := by
              simpa [equal, goLeft] using step
            obtain ⟨final, finalOffset, stop, loop, cost⟩ :=
              ihLeft row.left offset ls leftLayout (by omega) fuel (start + 2) (by omega)
            refine ⟨final, finalOffset, stop, ?_, ?_⟩
            · simp [Cpp.loopFuel, StateT.run_bind, initial, loop, Tree.rankBounds, equal, goLeft]
            · simp only [Tree.height]; omega
          · let next := offset + (less + row.count)
            have initial : (rankStep arena key () (none, index, offset)).run start =
                some (.yield (none, row.right, next), start + 4) := by
              simpa [equal, goLeft] using step
            obtain ⟨final, finalOffset, stop, loop, cost⟩ :=
              ihRight row.right next rs rightLayout (by rw [nextNat]; omega)
                fuel (start + 4) (by omega)
            refine ⟨final, finalOffset, stop, ?_, ?_⟩
            · simp [Cpp.loopFuel, StateT.run_bind, initial, loop, Tree.rankBounds, equal, goLeft,
                encodedRank, Option.map_map, Function.comp_def, next, nextNat, Nat.add_assoc]
            · simp only [Tree.height]; omega

theorem generated_rank_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (tree : Tree K) (key : K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64) (start : Nat) :
    ∃ interval stop, (cp.TreeMultiSet.rank arena key).run start = some ((interval, arena), stop) ∧
      interval = ((tree.rankBounds key).map (encodedRank 0)).getD (-1, -1) ∧
      stop ≤ start + 4 * tree.height + 3 := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨last, offset, stop, loop, work⟩ :=
    rank_loop_spec arena tree key arena.root 0 used layout fits (by simpa) Cpp.fuel (start + 1) enough
  let found := tree.rankBounds key
  have run : (forIn Cpp.forever (none, arena.root, 0) (rankStep arena key)).run (start + 1) =
      some ((found.map (fun result => (encodedRank 0 result, arena)), last, offset), stop) := loop
  refine ⟨(found.map (encodedRank 0)).getD (-1, -1), stop, ?_, rfl, by omega⟩
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  rw [generated_rank_program]
  simp only [StateT.run_bind, tickRun]
  simp [run, finishRank]
  cases found <;> rfl

theorem encodedRank_fits (first last : Nat) (ordered : first ≤ last) (fits : last < 2 ^ 31) :
    encodedRank 0 (first, last) = ((first : Int), (last : Int)) := by
  have low : Cpp.toSigned 32 first = (first : Int) := by simp [Cpp.toSigned]; omega
  have high : Cpp.toSigned 32 last = (last : Int) := by simp [Cpp.toSigned]; omega
  simpa [encodedRank] using And.intro low high

end Proofs.Cpp.TreeMultiset
