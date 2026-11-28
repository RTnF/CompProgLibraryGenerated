import Proofs.Cpp.TreeSet.Kth

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

abbrev RankBounds := Int × Int
abbrev RankState := Option RankBounds × UInt64 × UInt64

def rankStep {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) (_ : Unit) (state : RankState) : Cpp.M (ForInStep RankState) := do
  Cpp.tick
  let index := state.2.1
  let before := state.2.2
  let sentinel ← cp.TreeSet.none (T := K)
  if !(decide (index ≠ sentinel)) then return .done (none, index, before)
  let row := cell arena.slots index
  let current ← Cpp.optionalValue row.key
  if decide (key < current) then return .yield (none, row.left, before)
  let current ← Cpp.optionalValue row.key
  if decide (current < key) then
    let size ← cp.TreeSet.subtree_size arena row.left
    return .yield (none, row.right, before + (1 + size))
  else
    let size ← cp.TreeSet.subtree_size arena row.left
    let first := before + size
    return .done (some (Cpp.toSigned 32 first.toNat, Cpp.toSigned 32 (first + 1).toNat), index, before)

def rankBounds (i : Nat) : RankBounds := (Int.ofNat i, Int.ofNat (i + 1))

def finishRank (state : RankState) : Cpp.M RankBounds :=
  pure (state.1.getD (-1, -1))

theorem generated_rank_program {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) :
    cp.TreeSet.rank arena key = (do
      Cpp.tick
      let result ← forIn Cpp.forever (none, arena.root, 0) (rankStep arena key)
      finishRank result) := by
  cases arena
  unfold cp.TreeSet.rank rankStep finishRank cell
  dsimp only
  congr 1
  funext tickResult
  congr 1
  funext state
  cases state.1 <;> rfl

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl

private theorem sentinel_run {K : Type} (clock : Nat) :
    (cp.TreeSet.none (T := K)).run (clock + 1) = some (endIndex, clock + 2) := rfl

private theorem empty_rank_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) (offset : UInt64) (clock : Nat) :
    (rankStep arena key () (none, endIndex, offset)).run clock =
      some (ForInStep.done (none, endIndex, offset), clock + 2) := by
  simp [rankStep, StateT.run_bind, tick_run, sentinel_run]

private theorem rank_branch_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key current : K) (i offset : UInt64)
    (nonnull : i ≠ endIndex) (hasKey : (cell arena.slots i).key = some current) (start : Nat) :
    let row := cell arena.slots i
    let size := modelSize arena row.left
    let first := offset + size
    (rankStep arena key () (none, i, offset)).run start =
      if key < current then some (ForInStep.yield (none, row.left, offset), start + 2)
      else if current < key then some (ForInStep.yield (none, row.right, offset + (1 + size)), start + 4)
      else some (ForInStep.done (some (Cpp.toSigned 32 first.toNat, Cpp.toSigned 32 (first + 1).toNat), i, offset), start + 4) := by
  by_cases left : key < current <;> by_cases right : current < key <;>
    simp [rankStep, StateT.run_bind, tick_run, sentinel_run, nonnull, hasKey,
      Cpp.optionalValue, generated_size_run, left, right, Nat.add_assoc]

private theorem signed_rank (word : UInt64) (fit : word.toNat < 2 ^ 31) :
    Cpp.toSigned 32 word.toNat = (word.toNat : Int) := by
  unfold Cpp.toSigned
  simp only [Nat.mod_eq_of_lt (by omega : word.toNat < 2 ^ 32), fit, ite_true]

private theorem rank_loop {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) (tree : Tree K) (index offset : UInt64) (occupied : List Nat)
    (layout : Layout arena.slots index tree occupied)
    (fits : offset.toNat + tree.size < 2 ^ 31) (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ answer finalIndex finalOffset stop,
      (Cpp.loopFuel fuel (none, index, offset) (rankStep arena key)).run start =
        some ((answer, finalIndex, finalOffset), stop) ∧
      stop ≤ start + 2 + 4 * tree.height ∧
      answer = (tree.rank key).map (fun n => rankBounds (offset.toNat + n)) := by
  induction tree generalizing index offset occupied fuel start with
  | empty =>
    cases layout
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      exact ⟨none, endIndex, offset, start + 2, by simp [Cpp.loopFuel, StateT.run_bind, empty_rank_run],
        by simp [Tree.height], rfl⟩
  | node left current right il ir =>
    cases layout with
    | @node index current l r ls rs allocated hasIndex keyEq heights sizes _ _ leftLayout rightLayout fl fr sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        let row := cell arena.slots index
        let size := modelSize arena row.left
        let first := offset + size
        have leftSize : size.toNat = left.size := leftLayout.model_size
        have pos := rank_branch_run arena key current index offset hasIndex keyEq start
        change _ = (if key < current then some (ForInStep.yield (none, row.left, offset), start + 2)
          else if current < key then some (ForInStep.yield (none, row.right, offset + (1 + size)), start + 4)
          else some (ForInStep.done (some (Cpp.toSigned 32 first.toNat, Cpp.toSigned 32 (first + 1).toNat), index, offset), start + 4)) at pos
        simp only [Tree.size] at fits
        simp only [Tree.height] at enough
        by_cases lower : key < current
        · have step : (rankStep arena key () (none, index, offset)).run start =
              some (ForInStep.yield (none, row.left, offset), start + 2) := by rwa [ite_eq_left lower] at pos
          obtain ⟨answer, dst, before, stop, run, work, value⟩ :=
            il row.left offset ls leftLayout (by omega) fuel (start + 2) (by omega)
          refine ⟨answer, dst, before, stop, by simp [Cpp.loopFuel, StateT.run_bind, step, run], ?_, ?_⟩
          · simp only [Tree.height]; omega
          · simpa only [Tree.rank, ite_eq_left lower] using value
        · by_cases upper : current < key
          · let advanced := offset + (1 + size)
            have rightAdvance : (1 + size).toNat = left.size + 1 := by
              rw [UInt64.toNat_add, leftSize]
              change (1 + left.size) % (2 ^ 64) = left.size + 1
              rw [Nat.mod_eq_of_lt (by omega)]; omega
            have number : advanced.toNat = offset.toNat + left.size + 1 := by
              dsimp only [advanced]
              rw [UInt64.toNat_add, rightAdvance, Nat.mod_eq_of_lt (by omega)]
              omega
            have step : (rankStep arena key () (none, index, offset)).run start =
                some (ForInStep.yield (none, row.right, advanced), start + 4) := by
              rwa [ite_eq_right lower, ite_eq_left upper] at pos
            obtain ⟨answer, dst, before, stop, run, work, value⟩ :=
              ir row.right advanced rs rightLayout (by rw [number]; omega) fuel (start + 4) (by omega)
            refine ⟨answer, dst, before, stop, by simp [Cpp.loopFuel, StateT.run_bind, step, run], ?_, ?_⟩
            · simp only [Tree.height]; omega
            · simp only [Tree.rank, ite_eq_right lower, ite_eq_left upper, value]
              rw [number]
              cases right.rank key <;> simp [Nat.add_assoc]
          · have before : first.toNat = offset.toNat + left.size := by
              dsimp only [first]
              rw [UInt64.toNat_add, leftSize, Nat.mod_eq_of_lt (by omega)]
            have next : (first + 1).toNat = offset.toNat + left.size + 1 := by
              rw [UInt64.toNat_add, before]
              change (offset.toNat + left.size + 1) % (2 ^ 64) = _
              rw [Nat.mod_eq_of_lt (by omega)]
            have step : (rankStep arena key () (none, index, offset)).run start =
                some (ForInStep.done (some (rankBounds (offset.toNat + left.size)), index, offset), start + 4) := by
              rw [ite_eq_right lower, ite_eq_right upper,
                signed_rank first (by rw [before]; omega),
                signed_rank (first + 1) (by rw [next]; omega), before, next] at pos
              exact pos
            refine ⟨some (rankBounds (offset.toNat + left.size)), index, offset, start + 4,
              by simp [Cpp.loopFuel, StateT.run_bind, step], ?_, ?_⟩
            · simp only [Tree.height]; omega
            · simp [Tree.rank, lower, upper]

theorem generated_rank_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (key : K) (tree : Tree K) (occupied : List Nat)
    (layout : Layout arena.slots arena.root tree occupied)
    (fits : tree.size < 2 ^ 31) (balanced : tree.Balanced) (ordered : tree.Ordered) (start : Nat) :
    ∃ result stop, (cp.TreeSet.rank arena key).run start = some (result, stop) ∧
      stop ≤ start + 3 + 4 * (2 * (tree.size + 1).log2 + 1) ∧
      result = if key ∈ tree.keys then rankBounds ((tree.keys.filter (fun k => decide (k < key))).length)
        else (-1, -1) := by
  have height := tree.height_le_size
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨answer, dst, before, stop, ran, work, value⟩ :=
    rank_loop arena key tree arena.root 0 occupied layout (by simpa using fits) Cpp.fuel (start + 1) enough
  have scan : (forIn Cpp.forever (none, arena.root, 0) (rankStep arena key)).run (start + 1) =
      some ((answer, dst, before), stop) := ran
  refine ⟨answer.getD (-1, -1), stop, ?_, ?_, ?_⟩
  · rw [generated_rank_program]
    simp [StateT.run_bind, tick_run, scan, finishRank]
  · have logarithmic := tree.height_logarithmic balanced
    omega
  · rw [value]
    cases found : tree.rank key with
    | none =>
      simp [((tree.rank_absent key ordered).mp found)]
    | some i =>
      have notMissing : key ∈ tree.keys := by
        by_contra absent
        have impossible := (tree.rank_absent key ordered).mpr absent
        rw [found] at impossible
        contradiction
      simp [notMissing, (tree.rank_positions key ordered found).2]

end Proofs.Cpp.TreeSet
