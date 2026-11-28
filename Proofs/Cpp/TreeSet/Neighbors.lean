import Proofs.Cpp.TreeSet.Frame
import Proofs.Cpp.TreeSet.Kth

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

def Tree.neighbor {K : Type} [LT K] [DecidableLT K]
    (upper : Bool) (key : K) (candidate : Option K) : Tree K → Option K
  | .empty => candidate
  | .node left current right =>
    if upper then
      if current < key then right.neighbor upper key candidate
      else left.neighbor upper key (some current)
    else
      if key < current then left.neighbor upper key candidate
      else right.neighbor upper key (some current)

abbrev NeighborState := UInt64 × UInt64

def neighborStep {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (upper : Bool) (key : K) (_ : Unit) (state : NeighborState) :
    Cpp.M (ForInStep NeighborState) := do
  Cpp.tick
  let index := state.1
  let candidate := state.2
  let sentinel ← cp.TreeSet.none (T := K)
  if !(decide (index ≠ sentinel)) then return .done (index, candidate)
  let row := cell arena.slots index
  let current ← Cpp.optionalValue row.key
  if upper then
    if decide (current < key) then return .yield (row.right, candidate)
    else return .yield (row.left, index)
  else
    if decide (key < current) then return .yield (row.left, candidate)
    else return .yield (row.right, index)

def finishNeighbor {K : Type} [Inhabited K] (arena : cp.TreeSet K) (candidate : UInt64) :
    Cpp.M (Option K) := do
  let sentinel ← cp.TreeSet.none (T := K)
  if decide (candidate = sentinel) then return none
  let key ← Cpp.optionalValue (cell arena.slots candidate).key
  return some key

def candidateKey {K : Type} [Inhabited K] (arena : cp.TreeSet K) (candidate : UInt64) : Option K :=
  if candidate = endIndex then none else (cell arena.slots candidate).key

def candidateValid {K : Type} [Inhabited K] (arena : cp.TreeSet K) (candidate : UInt64) : Prop :=
  candidate = endIndex ∨ ∃ key, (cell arena.slots candidate).key = some key

def neighborProgram {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (upper : Bool) (key : K) : Cpp.M (Option K) := do
  Cpp.tick
  let sentinel ← cp.TreeSet.none (T := K)
  let result ← forIn Cpp.forever (arena.root, sentinel) (neighborStep arena upper key)
  finishNeighbor arena result.2

theorem generated_neighbor_program {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (upper : Bool) (key : K) :
    (if upper then cp.TreeSet.find_upper arena key else cp.TreeSet.find_lower arena key) =
      neighborProgram arena upper key := by
  cases arena
  cases upper <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    simp only [cp.TreeSet.find_upper, cp.TreeSet.find_lower, neighborProgram, finishNeighbor, cell] <;>
    rfl

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl

private theorem sentinel_run {K : Type} (clock : Nat) :
    (cp.TreeSet.none (T := K)).run clock = some (endIndex, clock + 1) := rfl

private theorem neighbor_empty_step {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (upper : Bool) (key : K) (candidate : UInt64) (start : Nat) :
    (neighborStep arena upper key () (endIndex, candidate)).run start =
      some (.done (endIndex, candidate), start + 2) := by
  simp [neighborStep, StateT.run_bind, tick_run, sentinel_run, Nat.add_assoc]

private theorem neighbor_node_step {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (upper : Bool) (key current : K) (i candidate : UInt64)
    (nonnull : i ≠ endIndex) (value : (cell arena.slots i).key = some current) (start : Nat) :
    let row := cell arena.slots i
    let next :=
      if upper then
        if current < key then (row.right, candidate) else (row.left, i)
      else
        if key < current then (row.left, candidate) else (row.right, i)
    (neighborStep arena upper key () (i, candidate)).run start =
      some (.yield next, start + 2) := by
  cases upper <;> by_cases lo : key < current <;> by_cases hi : current < key <;>
    simp [neighborStep, StateT.run_bind, tick_run, sentinel_run, Nat.add_assoc, nonnull,
      Cpp.optionalValue, value, lo, hi]

private theorem finish_neighbor_run {K : Type} [Inhabited K]
    (arena : cp.TreeSet K) (i : UInt64) (valid : candidateValid arena i) (start : Nat) :
    (finishNeighbor arena i).run start = some (candidateKey arena i, start + 1) := by
  by_cases sentinel : i = endIndex
  · simp [finishNeighbor, candidateKey, StateT.run_bind, sentinel_run, sentinel]
  · obtain ⟨key, value⟩ := valid.resolve_left sentinel
    simp [finishNeighbor, candidateKey, StateT.run_bind, sentinel_run, sentinel, Cpp.optionalValue, value]

private theorem neighbor_loop {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (upper : Bool) (key : K) {tree : Tree K} {i : UInt64} {slots : List Nat}
    (layout : Layout arena.slots i tree slots) (candidate : UInt64) (valid : candidateValid arena candidate)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ dst selected stop,
      (Cpp.loopFuel fuel (i, candidate) (neighborStep arena upper key)).run start =
        some ((dst, selected), stop) ∧
      stop ≤ start + 2 + 2 * tree.height ∧ candidateValid arena selected ∧
      candidateKey arena selected = tree.neighbor upper key (candidateKey arena candidate) := by
  induction tree generalizing i slots candidate fuel start with
  | empty =>
    cases layout
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      exact ⟨endIndex, candidate, start + 2,
        by simp [Cpp.loopFuel, StateT.run_bind, neighbor_empty_step],
        by simp [Tree.height], valid, rfl⟩
  | node left current right il ir =>
    cases layout with
    | @node i current l r ls rs allocated nonnull value heights sizes _ _ ll rr fl fr distinct =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        have currentValid : candidateValid arena i := Or.inr ⟨current, value⟩
        have currentKey : candidateKey arena i = some current := ite_eq_right nonnull |>.trans value
        have step := neighbor_node_step arena upper key current i candidate nonnull value start
        simp only [Tree.height] at enough
        cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at step
        · by_cases goLeft : key < current
          · rw [ite_eq_left goLeft] at step
            obtain ⟨dst, selected, stop, run, cost, kept, answer⟩ :=
              il ll candidate valid fuel (start + 2) (by omega)
            exact ⟨dst, selected, stop, by simp [Cpp.loopFuel, StateT.run_bind, step, run],
              by simp only [Tree.height]; omega, kept, by simpa [Tree.neighbor, goLeft] using answer⟩
          · rw [ite_eq_right goLeft] at step
            obtain ⟨dst, selected, stop, run, cost, kept, answer⟩ :=
              ir rr i currentValid fuel (start + 2) (by omega)
            exact ⟨dst, selected, stop, by simp [Cpp.loopFuel, StateT.run_bind, step, run],
              by simp only [Tree.height]; omega, kept, by simpa [Tree.neighbor, goLeft, currentKey] using answer⟩
        · by_cases goRight : current < key
          · rw [ite_eq_left goRight] at step
            obtain ⟨dst, selected, stop, run, cost, kept, answer⟩ :=
              ir rr candidate valid fuel (start + 2) (by omega)
            exact ⟨dst, selected, stop, by simp [Cpp.loopFuel, StateT.run_bind, step, run],
              by simp only [Tree.height]; omega, kept, by simpa [Tree.neighbor, goRight] using answer⟩
          · rw [ite_eq_right goRight] at step
            obtain ⟨dst, selected, stop, run, cost, kept, answer⟩ :=
              il ll i currentValid fuel (start + 2) (by omega)
            exact ⟨dst, selected, stop, by simp [Cpp.loopFuel, StateT.run_bind, step, run],
              by simp only [Tree.height]; omega, kept, by simpa [Tree.neighbor, goRight, currentKey] using answer⟩

theorem generated_neighbor_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (upper : Bool) (key : K) (tree : Tree K) (occupied : List Nat)
    (layout : Layout arena.slots arena.root tree occupied)
    (enough : tree.height < Cpp.fuel) (balanced : tree.Balanced) (start : Nat) :
    ∃ stop,
      ((if upper then cp.TreeSet.find_upper arena key else cp.TreeSet.find_lower arena key).run start) =
        some (tree.neighbor upper key none, stop) ∧
      stop ≤ start + 5 + 2 * (2 * (tree.size + 1).log2 + 1) := by
  obtain ⟨dst, selected, endClock, run, cost, valid, result⟩ :=
    neighbor_loop arena upper key layout endIndex (Or.inl rfl) Cpp.fuel (start + 2) enough
  have scan : (forIn Cpp.forever (arena.root, endIndex) (neighborStep arena upper key)).run (start + 2) =
      some ((dst, selected), endClock) := run
  refine ⟨endClock + 1, ?_, ?_⟩
  · rw [generated_neighbor_program]
    simpa [neighborProgram, StateT.run_bind, tick_run, sentinel_run, Nat.add_assoc, scan,
      finish_neighbor_run arena selected valid, result, candidateKey]
  · have logarithmic := tree.height_logarithmic balanced
    omega


theorem Tree.neighbor_upper {K : Type} [LinearOrder K] (tree : Tree K) (key : K)
    (ordered : tree.Ordered) (candidate : Option K) :
    tree.neighbor true key candidate =
      ((tree.keys.filter (fun k => decide (key ≤ k))).head?).or candidate := by
  induction tree generalizing candidate with
  | empty => simp [Tree.neighbor, Tree.keys]
  | node left current right il ir =>
    obtain ⟨ol, or', lo, _⟩ := Tree.ordered_node ordered
    by_cases goRight : current < key
    · have noLeft : left.keys.filter (fun k => decide (key ≤ k)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro k present
        exact fun qualifies => (not_le_of_gt (lt_trans (lo k present) goRight)) (of_decide_eq_true qualifies)
      simp [Tree.neighbor, Tree.keys, goRight, not_le_of_gt goRight, noLeft, ir or']
    · have qualifies : key ≤ current := le_of_not_gt goRight
      cases tail : (left.keys.filter (fun k => decide (key ≤ k))).head? <;>
        simp [Tree.neighbor, Tree.keys, goRight, qualifies, il ol, tail]

theorem Tree.neighbor_lower {K : Type} [LinearOrder K] (tree : Tree K) (key : K)
    (ordered : tree.Ordered) (candidate : Option K) :
    tree.neighbor false key candidate =
      ((tree.keys.filter (fun k => decide (k ≤ key))).getLast?).or candidate := by
  induction tree generalizing candidate with
  | empty => simp [Tree.neighbor, Tree.keys]
  | node left current right il ir =>
    obtain ⟨ol, or', _, hi⟩ := Tree.ordered_node ordered
    by_cases goLeft : key < current
    · have noRight : right.keys.filter (fun k => decide (k ≤ key)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro k present
        exact fun qualifies => (not_le_of_gt (lt_trans goLeft (hi k present))) (of_decide_eq_true qualifies)
      simp [Tree.neighbor, Tree.keys, goLeft, not_le_of_gt goLeft, noRight, il ol]
    · have qualifies : current ≤ key := le_of_not_gt goLeft
      cases tail : (right.keys.filter (fun k => decide (k ≤ key))).getLast? <;>
        simp [Tree.neighbor, Tree.keys, List.append_assoc, goLeft, qualifies, ir or', tail, List.getLast?_cons]


theorem generated_neighbors_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (key : K) (tree : Tree K) (occupied : List Nat)
    (layout : Layout arena.slots arena.root tree occupied) (fits : tree.size < 2 ^ 31)
    (balanced : tree.Balanced) (ordered : tree.Ordered) (start : Nat) :
    let work := 5 + 2 * (2 * (tree.size + 1).log2 + 1)
    (∃ lowerStop, (cp.TreeSet.find_lower arena key).run start =
      some ((tree.keys.filter (fun k => decide (k ≤ key))).getLast?, lowerStop) ∧
      lowerStop ≤ start + work) ∧
    (∃ upperStop, (cp.TreeSet.find_upper arena key).run start =
      some ((tree.keys.filter (fun k => decide (key ≤ k))).head?, upperStop) ∧
      upperStop ≤ start + work) := by
  have enough : tree.height < Cpp.fuel := by have := tree.height_le_size; unfold Cpp.fuel; omega
  have lower := generated_neighbor_run arena false key tree occupied layout enough balanced start
  have upper := generated_neighbor_run arena true key tree occupied layout enough balanced start
  constructor
  · simpa [tree.neighbor_lower key ordered, Nat.add_assoc] using lower
  · simpa [tree.neighbor_upper key ordered, Nat.add_assoc] using upper

end Proofs.Cpp.TreeSet
