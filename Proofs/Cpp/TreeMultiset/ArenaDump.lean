import Proofs.Cpp.TreeMultiset.ArenaVerify
import Proofs.Cpp.TreeMultiset.StreamPlan

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

section Output

variable {K : Type} [Inhabited K] [LinearOrder K] [Cpp.Streams]
  [Cpp.StreamWrite K] [Cpp.StreamWrite Cpp.StreamChar]

omit [Inhabited K] [LinearOrder K] [Cpp.Streams] [Cpp.StreamWrite K] [Cpp.StreamWrite Cpp.StreamChar] in
private theorem end_program :
    cp.TreeMultiSet.none (T := K) = (do Cpp.tick; pure endIndex) := rfl

omit [Inhabited K] [LinearOrder K] in
private theorem selected_loop (arena : cp.TreeMultiSet K) (code : UInt64) (key : K)
    (keyEq : (modelCell arena code).key = some key) (output : Cpp.OStream) :
    (forIn Cpp.forever (output, (0 : UInt64)) (fun (_ : Unit) state => do
      tick
      if !(decide (state.2 < (modelCell arena code).count)) then return .done state
      let value ← Cpp.optionalValue (modelCell arena code).key
      let stream ← Cpp.StreamWrite.write state.1 value
      let stream ← Cpp.StreamWrite.write stream (⟨10⟩ : Cpp.StreamChar)
      return .yield (stream, state.2 + 1))) = (do
        let out ← repeatPrint key (modelCell arena code).count.toNat output
        pure (out, (modelCell arena code).count)) := by
  rw [← print_loop_from_zero key (modelCell arena code).count output]
  congr 1
  funext ignored state
  simp [keyEq, Cpp.optionalValue, printStep, printLine]

omit [Inhabited K] [LinearOrder K] in
private theorem selected_loop_order (arena : cp.TreeMultiSet K) (code : UInt64) (key : K)
    (hasKey : (modelCell arena code).key = some key) (output : Cpp.OStream) :
    (forIn Cpp.forever (output, (0 : UInt64)) (fun (_ : Unit) state => do
      tick
      if (modelCell arena code).count ≤ state.2 then pure (.done state)
      else do
        let stream ← Cpp.StreamWrite.write state.1 key
        let stream ← Cpp.StreamWrite.write stream (⟨10⟩ : Cpp.StreamChar)
        pure (.yield (stream, state.2 + 1)))) = (do
      let out ← repeatPrint key (modelCell arena code).count.toNat output
      pure (out, (modelCell arena code).count)) := by
  rw [← selected_loop arena code key hasKey output]
  congr 1
  funext ignored state
  simp [Cpp.optionalValue, hasKey]

private theorem generated_dump_plan {arena : cp.TreeMultiSet K} (tree : Tree K) (code : UInt64)
    (used : List Nat) (layout : Realizes (storageView arena) (decode code) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (lo hi : K) (fuel : Nat) (enough : tree.height < fuel)
    (output : Cpp.OStream) :
    cp.TreeMultiSet.dump_in_rec fuel arena code lo hi output = (do
      let out ← runPrintPlan (printPlan lo hi tree) output
      pure (out, arena)) := by
  induction tree generalizing code used fuel output with
  | empty =>
    have endCode := (decode_none _).mp (layout.empty_iff.mpr rfl)
    subst code
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      cases arena
      simp [cp.TreeMultiSet.dump_in_rec, printPlan, runPrintPlan, end_program]
  | node key priority count left right ihLeft ihRight =>
    generalize decoded : decode code = index at layout
    cases layout with
    | @node slot _ _ _ _ _ lc rc ls rs reads ll rr lf rf sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        obtain ⟨present, _⟩ := decode_some code slot decoded
        obtain ⟨_, _, view⟩ := modelCell_view arena code slot _ decoded reads fits
        let row := modelCell arena code
        have keyEq : row.key = some key := congrArg StoredNode.key view
        have countEq : row.count.toNat = count := congrArg StoredNode.count view
        have leftEq : decode row.left = lc := congrArg StoredNode.left view
        have rightEq : decode row.right = rc := congrArg StoredNode.right view
        simp only [Tree.height] at enough
        have leftProgram (stream : Cpp.OStream) :=
          ihLeft row.left ls (leftEq.symm ▸ ll) fuel (by omega) stream
        have rightProgram (stream : Cpp.OStream) :=
          ihRight row.right rs (rightEq.symm ▸ rr) fuel (by omega) stream
        have emit (stream : Cpp.OStream) := selected_loop_order arena code key keyEq stream
        cases arena
        dsimp only [row, modelCell] at leftProgram rightProgram emit keyEq countEq
        simp only [bind_pure_comp, countEq] at emit
        by_cases lookLeft : lo < key <;> by_cases lookRight : key < hi <;>
          by_cases overLow : lo ≤ key <;> by_cases underHigh : key ≤ hi <;>
          simp [cp.TreeMultiSet.dump_in_rec, printPlan, end_program, present, keyEq, Cpp.optionalValue,
            lookLeft, lookRight, overLow, underHigh, leftProgram, rightProgram, run_plan_append,
            run_plan_repeat, run_plan_advance]
        all_goals simp [emit]

def publicPrintPlan (lo hi : K) : Tree K → List (Option K)
  | .empty => []
  | .node key priority count left right => printPlan lo hi (.node key priority count left right)

omit [Inhabited K] [Cpp.Streams] [Cpp.StreamWrite K] [Cpp.StreamWrite Cpp.StreamChar] in
theorem public_plan_empty (lo hi : K) (tree : Tree K) (empty : tree = .empty) :
    publicPrintPlan lo hi tree = [] := by subst tree; rfl

omit [Inhabited K] [Cpp.Streams] [Cpp.StreamWrite K] [Cpp.StreamWrite Cpp.StreamChar] in
theorem public_plan_present (lo hi : K) (tree : Tree K) (nonempty : tree ≠ .empty) :
    publicPrintPlan lo hi tree = printPlan lo hi tree := by
  cases tree with
  | empty => exact (nonempty rfl).elim
  | node => rfl

theorem generated_aoj_dump_plan (arena : cp.TreeMultiSet K) (tree : Tree K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (lo hi : K) (output : Cpp.OStream) :
    cp.TreeMultiSet.aoj_dump arena lo hi output = (do
      tick
      tick
      let out ← runPrintPlan (publicPrintPlan lo hi tree) output
      pure (out, arena)) := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  have call : cp.TreeMultiSet.dump_in arena arena.root lo hi output = (do
      let out ← runPrintPlan (printPlan lo hi tree) output
      pure (out, arena)) := by
    rw [cp.TreeMultiSet.dump_in]
    exact generated_dump_plan tree arena.root used layout fits lo hi Cpp.fuel enough output
  by_cases missing : tree = .empty
  · have marker : arena.root = endIndex := (decode_none _).mp (layout.empty_iff.mpr missing)
    cases arena
    dsimp only at marker
    simp [cp.TreeMultiSet.aoj_dump, end_program, marker, public_plan_empty lo hi tree missing, runPrintPlan]
  · have present : arena.root ≠ endIndex := fun marker => missing (layout.empty_iff.mp ((decode_none _).mpr marker))
    cases arena
    dsimp only at present
    simp [cp.TreeMultiSet.aoj_dump, end_program, present, public_plan_present lo hi tree missing, call]

omit [Inhabited K] [Cpp.Streams] [Cpp.StreamWrite K] [Cpp.StreamWrite Cpp.StreamChar] in
theorem public_print_keys (tree : Tree K) (ordered : tree.Ordered) (lo hi : K) :
    (publicPrintPlan lo hi tree).filterMap id =
      tree.expanded.filter (fun key => decide (lo ≤ key ∧ key ≤ hi)) := by
  cases tree with
  | empty => rfl
  | node key p count left right =>
    change (printPlan lo hi (.node key p count left right)).filterMap id = _
    rw [printPlan_keys, Tree.closedKeys_filter lo hi _ ordered]

theorem generated_aoj_dump_work (arena : cp.TreeMultiSet K) (tree : Tree K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (lo hi : K) (output : Cpp.OStream)
    (lineCost start : Nat)
    (bounded : ∀ stream (key : K) clock, ∃ out stop, (printLine stream key).run clock = some (out, stop) ∧
      stop ≤ clock + lineCost) :
    ∃ after stop, (cp.TreeMultiSet.aoj_dump arena lo hi output).run start = some ((after, arena), stop) ∧
      stop ≤ start + 4 + 5 * tree.slots + (lineCost + 1) * (tree.closedKeys lo hi).length := by
  have lengthEq : (publicPrintPlan lo hi tree).filterMap id = tree.closedKeys lo hi := by
    cases tree with
    | empty => rfl
    | node => exact printPlan_keys lo hi _
  have lengthBound : (publicPrintPlan lo hi tree).length ≤ 2 + 5 * tree.slots + (tree.closedKeys lo hi).length := by
    cases tree with
    | empty => simp [publicPrintPlan, Tree.closedKeys, Tree.slots]
    | node => exact printPlan_length lo hi _
  obtain ⟨after, stop, run, cost⟩ := run_plan_work (publicPrintPlan lo hi tree) lineCost bounded output (start + 2)
  have first : Cpp.tick.run start = some ((), start + 1) := rfl
  have second : Cpp.tick.run (start + 1) = some ((), start + 2) := rfl
  refine ⟨after, stop, ?_, ?_⟩
  · rw [generated_aoj_dump_plan arena tree used layout fits lo hi output]
    simp [StateT.run_bind, first, second, run]
  · rw [lengthEq] at cost
    rw [Nat.add_mul]
    omega

end Output
end Proofs.Cpp.TreeMultiset
