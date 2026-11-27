import Proofs.Cpp.TreeMultiset.GeneratedLocate

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

def FoundAt {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (key : K) (used : List Nat)
    (code : UInt64) (count : Nat) : Prop :=
  ∃ index, decode code = some index ∧ index ∈ used ∧
    (modelCell arena code).key = some key ∧ (modelCell arena code).count.toNat = count

theorem FoundAt.weaken {K : Type} [Inhabited K] {arena : cp.TreeMultiSet K} {key : K}
    {before after : List Nat} {code : UInt64} {count : Nat}
    (found : FoundAt arena key before code count) (subset : before ⊆ after) :
    FoundAt arena key after code count := by
  obtain ⟨i, decoded, mem, keyEq, countEq⟩ := found
  exact ⟨i, decoded, subset mem, keyEq, countEq⟩

def LookupWitness {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (key : K) (used : List Nat)
    (found : Option UInt64) (specified : Option Nat) : Prop :=
  match found, specified with
  | none, none => True
  | some code, some count => FoundAt arena key used code count
  | _, _ => False

theorem LookupWitness.weaken {K : Type} [Inhabited K] {arena : cp.TreeMultiSet K} {key : K}
    {before after : List Nat} {code : Option UInt64} {count : Option Nat}
    (witness : LookupWitness arena key before code count) (subset : before ⊆ after) :
    LookupWitness arena key after code count := by
  cases code <;> cases count <;> simp_all only [LookupWitness]
  exact witness.weaken subset

private theorem step_done {S : Type} (step : Unit → S → Cpp.M (ForInStep S))
    (fuel start stop : Nat) (input output : S) (run : (step () input).run start = some (.done output, stop)) :
    (Cpp.loopFuel (fuel + 1) input step).run start = some (output, stop) := by
  simp [Cpp.loopFuel, StateT.run_bind, run]

private theorem step_yield {S : Type} (step : Unit → S → Cpp.M (ForInStep S))
    (fuel start middle stop : Nat) (input next output : S)
    (run : (step () input).run start = some (.yield next, middle))
    (rest : (Cpp.loopFuel fuel next step).run middle = some (output, stop)) :
    (Cpp.loopFuel (fuel + 1) input step).run start = some (output, stop) := by
  simp [Cpp.loopFuel, StateT.run_bind, run, rest]

theorem locate_loop_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (tree : Tree K) (arena : cp.TreeMultiSet K) (key : K) (code : UInt64) (used : List Nat)
    (layout : Realizes (storageView arena) (decode code) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ found final stop, (Cpp.loopFuel fuel (none, code) (locateStep arena key)).run start =
      some ((found.map (fun x => (x, arena)), final), stop) ∧
      stop ≤ start + 2 * (tree.height + 1) ∧ LookupWitness arena key used found (tree.lookup key) := by
  induction tree generalizing code used fuel start with
  | empty =>
    generalize decoded : decode code = root at layout
    cases layout with
    | empty =>
      have emptyCode := (decode_none _).mp decoded
      subst code
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        exact ⟨none, endIndex, start + 2, step_done _ _ _ _ _ _ (locate_step_end arena key start),
          by simp [Tree.height], trivial⟩
  | node current priority count left right ihLeft ihRight =>
    generalize decoded : decode code = root at layout
    cases layout with
    | @node index _ _ _ _ _ lc rc ls rs reads ll rr lf rf sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        obtain ⟨present, _⟩ := decode_some code index decoded
        obtain ⟨_, _, view⟩ := modelCell_view arena code index _ decoded reads fits
        let row := modelCell arena code
        have currentKey : row.key = some current := congrArg StoredNode.key view
        have countExact : row.count.toNat = count := congrArg StoredNode.count view
        have leftCode : decode row.left = lc := congrArg StoredNode.left view
        have rightCode : decode row.right = rc := congrArg StoredNode.right view
        simp only [Tree.height] at enough
        by_cases same : key = current
        · have step := locate_step_here arena key code present (same.symm ▸ currentKey) start
          refine ⟨some code, code, start + 2, step_done _ _ _ _ _ _ step, ?_, ?_⟩
          · simp only [Tree.height]
            omega
          · simp only [Tree.lookup, ite_eq_left same, LookupWitness]
            exact ⟨index, decoded, List.mem_cons_self .., same.symm ▸ currentKey, countExact⟩
        · have step := locate_step_child arena key current code present currentKey same start
          by_cases less : key < current
          · obtain ⟨found, final, stop, run, time, witness⟩ :=
              ihLeft row.left ls (leftCode.symm ▸ ll) fuel (start + 2) (by omega)
            refine ⟨found, final, stop, step_yield _ _ _ _ _ _ _ _ (by simpa only [ite_eq_left less] using step) run,
              ?_, ?_⟩
            · simp only [Tree.height]
              omega
            · simp only [Tree.lookup, ite_eq_right same, ite_eq_left less]
              exact witness.weaken fun {_} mem => List.mem_cons_of_mem _ (List.mem_append_left _ mem)
          · obtain ⟨found, final, stop, run, time, witness⟩ :=
              ihRight row.right rs (rightCode.symm ▸ rr) fuel (start + 2) (by omega)
            refine ⟨found, final, stop, step_yield _ _ _ _ _ _ _ _ (by simpa only [ite_eq_right less] using step) run,
              ?_, ?_⟩
            · simp only [Tree.height]
              omega
            · simp only [Tree.lookup, ite_eq_right same, ite_eq_right less]
              exact witness.weaken fun {_} mem => List.mem_cons_of_mem _ (List.mem_append_right _ mem)

private theorem finish_locate_run {K : Type} (arena : cp.TreeMultiSet K) (found : Option UInt64)
    (final : UInt64) (start : Nat) :
    (finishLocate arena (found.map (fun code => (code, arena)), final)).run start =
      some ((found.getD endIndex, arena), start + if found.isSome then 0 else 1) := by
  cases found <;> rfl

theorem generated_locate_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (tree : Tree K) (key : K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ code stop, (cp.TreeMultiSet.locate arena key).run start = some ((code, arena), stop) ∧
      stop ≤ start + 2 * tree.height + 4 ∧
      match tree.lookup key with
      | none => code = endIndex
      | some count => FoundAt arena key used code count := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨found, final, middle, loop, work, witness⟩ :=
    locate_loop_spec tree arena key arena.root used layout fits Cpp.fuel (start + 1) enough
  have loopRun : (forIn Cpp.forever (none, arena.root) (locateStep arena key)).run (start + 1) =
      some ((found.map (fun x => (x, arena)), final), middle) := loop
  refine ⟨found.getD endIndex, middle + (if found.isSome then 0 else 1), ?_, ?_, ?_⟩
  · rw [generated_locate_program]
    have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
    simp [StateT.run_bind, tickRun, loopRun, finish_locate_run]
  · cases found <;> simp at * <;> omega
  · cases found <;> cases result : tree.lookup key <;> simp_all [LookupWitness]


end Proofs.Cpp.TreeMultiset
