import Proofs.Cpp.TreeMultiset.ArenaPublicCounts
import Proofs.Math.TreeMultiset.TreapRange

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

variable {K : Type} [Inhabited K] [Cpp.ConditionalResult K Int]
  [Cpp.Conv (Cpp.ConditionalResult.Value (Left := K) (Right := Int)) K]

abbrev ParentValue (K : Type) [Cpp.ConditionalResult K Int] := Cpp.ConditionalResult.Value (Left := K) (Right := Int)

def parentValue (parent : Option K) : ParentValue K :=
  match parent with
  | none => Cpp.ConditionalResult.right (Left := K) (-1)
  | some key => Cpp.ConditionalResult.left (Right := Int) key

def outputRow (row : K × UInt64 × K) : K × Nat × K := (row.1, row.2.1.toNat, row.2.2)

def formatRow (row : K × Nat × Option K) : K × Nat × K :=
  (row.1, row.2.1, Cpp.Conv.conv (parentValue row.2.2))

def ParentAt (arena : cp.TreeMultiSet K) (index : UInt64) (parent : Option K) : Prop :=
  match parent with
  | none => index = endIndex
  | some key => index ≠ endIndex ∧ (modelCell arena index).key = some key

def readParent (arena : cp.TreeMultiSet K) (index : UInt64) : Cpp.M (ParentValue K) :=
  if decide (index ≠ endIndex) then
    do
      let key ← Cpp.optionalValue (modelCell arena index).key
      return Cpp.ConditionalResult.left (Right := Int) key
  else pure (Cpp.ConditionalResult.right (Left := K) (-1))

private theorem tick_run (start : Nat) : Cpp.tick.run start = some ((), start + 1) := rfl

private theorem none_run (K : Type) (start : Nat) :
    (cp.TreeMultiSet.none (T := K)).run start = some (endIndex, start + 1) := rfl

private theorem pure_run {A : Type} (value : A) (start : Nat) :
    (pure value : Cpp.M A).run start = some (value, start) := rfl

private theorem some_bind {A B : Type} (value : A) (f : A → Option B) :
    (some value >>= f) = f value := rfl

omit [Inhabited K] [Cpp.Conv (Cpp.ConditionalResult.Value (Left := K) (Right := Int)) K] in
theorem readParent_spec (arena : cp.TreeMultiSet K) (code : UInt64) (parent : Option K)
    (layout : ParentAt arena code parent) (start : Nat) :
    (readParent arena code).run start = some (parentValue parent, start) := by
  cases parent with
  | none =>
    change code = endIndex at layout
    simp [readParent, layout, parentValue]
  | some key =>
    obtain ⟨present, keyEq⟩ := layout
    simp [readParent, present, keyEq, Cpp.optionalValue, parentValue]

private theorem enum_all_empty (arena : cp.TreeMultiSet K) (rows : Array (K × UInt64 × K))
    (parent : UInt64) (fuel start : Nat) :
    (cp.TreeMultiSet.enumerate_all_in_rec (fuel + 1) arena rows endIndex parent).run start =
      some ((rows, arena), start + 2) := by
  cases arena
  simp only [cp.TreeMultiSet.enumerate_all_in_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    decide_true, ite_true]

private theorem fold_choice {A B : Type} (cond : Prop) [Decidable cond] (yes no : Cpp.M A)
    (rest : A → Cpp.M B) :
    (if cond then yes >>= rest else no >>= rest) = ((if cond then yes else no) >>= rest) := by
  split <;> rfl

private theorem enum_all_node (arena : cp.TreeMultiSet K) (before middle after : Array (K × UInt64 × K))
    (code parent : UInt64) (key : K) (parentArg : ParentValue K)
    (fuel start walked stop : Nat)
    (present : code ≠ endIndex) (keyEq : (modelCell arena code).key = some key)
    (leftRun : (cp.TreeMultiSet.enumerate_all_in_rec fuel arena before (modelCell arena code).left code).run (start + 2) =
      some ((middle, arena), walked))
    (parentRead : (readParent arena parent).run (walked + 1) = some (parentArg, walked + 1))
    (rightRun : (cp.TreeMultiSet.enumerate_all_in_rec fuel arena
      (middle.push (key, (modelCell arena code).count, Cpp.Conv.conv parentArg))
        (modelCell arena code).right code).run (walked + 2) = some ((after, arena), stop)) :
    (cp.TreeMultiSet.enumerate_all_in_rec (fuel + 1) arena before code parent).run start =
      some ((after, arena), stop) := by
  cases arena
  dsimp only [readParent, modelCell] at leftRun keyEq parentRead rightRun
  simp only [Cpp.optionalValue] at parentRead
  simp only [cp.TreeMultiSet.enumerate_all_in_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    present, decide_false, Bool.false_eq_true, ite_false, leftRun, fold_choice, parentRead, keyEq, Cpp.optionalValue, rightRun]

private theorem generated_enumerate_all_loop (arena : cp.TreeMultiSet K) (code parent : UInt64) (tree : Tree K)
    (parentKey : Option K) (used : List Nat) (rows : Array (K × UInt64 × K))
    (layout : Realizes (storageView arena) (decode code) tree used)
    (parentLayout : ParentAt arena parent parentKey) (fits : arena.slots.size ≤ 2 ^ 63)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ after, (cp.TreeMultiSet.enumerate_all_in_rec fuel arena rows code parent).run start =
      some ((after, arena), start + 2 + 6 * tree.slots) ∧
      after.toList.map outputRow = rows.toList.map outputRow ++ (tree.withParents parentKey).map formatRow := by
  induction tree generalizing code parent parentKey used rows fuel start with
  | empty =>
    generalize decoded : decode code = index at layout
    cases layout with
    | empty =>
      have sentinel := (decode_none _).mp decoded
      subst code
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        exact ⟨rows, enum_all_empty arena rows parent fuel start, by simp [Tree.withParents]⟩
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
        have parentAt : ParentAt arena code (some key) := ⟨present, keyEq⟩
        simp only [Tree.height] at enough
        let walked := start + 2 + 2 + 6 * left.slots
        obtain ⟨lhs, leftRun, leftRows⟩ :=
          ihLeft row.left code (some key) ls rows (leftEq.symm ▸ ll) parentAt fuel (start + 2) (by omega)
        let nextRow : K × UInt64 × K := (key, row.count, Cpp.Conv.conv (parentValue parentKey))
        obtain ⟨out, rightRun, rightRows⟩ :=
          ihRight row.right code (some key) rs (lhs.push nextRow) (rightEq.symm ▸ rr) parentAt fuel (walked + 2) (by omega)
        have run := enum_all_node arena rows lhs out code parent key (parentValue parentKey)
          fuel start walked (walked + 2 + 2 + 6 * right.slots) present keyEq leftRun
          (readParent_spec arena parent parentKey parentLayout (walked + 1)) rightRun
        have clock : walked + 2 + 2 + 6 * right.slots = start + 2 + 6 * (Tree.node key priority count left right).slots := by
          simp only [walked, Tree.slots]
          omega
        refine ⟨out, ?_, ?_⟩
        · simpa only [clock] using run
        · rw [rightRows]
          simp only [Array.toList_push, List.map_append, List.map_nil, leftRows, Tree.withParents,
            List.map_cons, List.append_assoc, List.singleton_append, outputRow, formatRow, nextRow, countEq]

omit [Inhabited K] [Cpp.ConditionalResult K Int] [Cpp.Conv (Cpp.ConditionalResult.Value (Left := K) (Right := Int)) K] in
theorem Tree.withParents_length (tree : Tree K) (parent : Option K) :
    (tree.withParents parent).length = tree.slots := by
  induction tree generalizing parent with
  | empty => rfl
  | node key p c left right ihLeft ihRight =>
    simp only [Tree.withParents, Tree.slots, List.length_append, List.length_cons, ihLeft, ihRight]
    omega

private theorem enum_all_entry_run (arena : cp.TreeMultiSet K) (rows : Array (K × UInt64 × K)) (start stop : Nat)
    (loop : (cp.TreeMultiSet.enumerate_all_in arena ([] : List (K × UInt64 × K)).toArray arena.root endIndex).run
      (start + 1 + 1) = some ((rows, arena), stop)) :
    (cp.TreeMultiSet.enumerate_all arena).run start = some ((rows, arena), stop) := by
  rw [cp.TreeMultiSet.enumerate_all]
  simp only [StateT.run_bind, tick_run, none_run, some_bind, pure_run]
  rw [loop]
  rfl

theorem generated_enumerate_all_spec (arena : cp.TreeMultiSet K) (tree : Tree K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ rows, (cp.TreeMultiSet.enumerate_all arena).run start = some ((rows, arena), start + 4 + 6 * tree.slots) ∧
      rows.toList.map outputRow = (tree.withParents none).map formatRow ∧ rows.size = tree.slots := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨rows, loop, result⟩ := generated_enumerate_all_loop arena arena.root endIndex tree none used (List.toArray [])
    layout rfl fits Cpp.fuel (start + 2) enough
  have size : rows.size = tree.slots := by
    simpa [Tree.withParents_length] using congrArg List.length result
  refine ⟨rows, ?_, by simpa using result, size⟩
  apply enum_all_entry_run
  rw [cp.TreeMultiSet.enumerate_all_in]
  exact loop

section Range

variable [LinearOrder K]

private theorem enum_range_empty (arena : cp.TreeMultiSet K) (rows : Array (K × UInt64 × K))
    (parent : UInt64) (lo hi : K) (fuel start : Nat) :
    (cp.TreeMultiSet.enumerate_in_rec (fuel + 1) arena rows endIndex lo hi parent).run start =
      some ((rows, arena), start + 2) := by
  cases arena
  simp only [cp.TreeMultiSet.enumerate_in_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
    decide_true, ite_true]

private theorem enum_range_node (arena : cp.TreeMultiSet K) (before middle after : Array (K × UInt64 × K))
    (code parent : UInt64) (key lo hi : K) (parentArg : ParentValue K)
    (fuel start walked stop : Nat)
    (present : code ≠ endIndex) (keyEq : (modelCell arena code).key = some key)
    (leftRun : (if lo < key then
        (cp.TreeMultiSet.enumerate_in_rec fuel arena before (modelCell arena code).left lo hi code).run (start + 2)
      else some ((before, arena), start + 2)) = some ((middle, arena), walked))
    (parentRead : (readParent arena parent).run (walked + 1) = some (parentArg, walked + 1))
    (rightRun : (if key < hi then
      (cp.TreeMultiSet.enumerate_in_rec fuel arena
        (if lo ≤ key then middle.push (key, (modelCell arena code).count, Cpp.Conv.conv parentArg) else middle)
        (modelCell arena code).right lo hi code).run (walked + if lo ≤ key then 2 else 0)
      else some ((middle, arena), walked)) = some ((after, arena), stop)) :
    (cp.TreeMultiSet.enumerate_in_rec (fuel + 1) arena before code lo hi parent).run start =
      some ((after, arena), stop) := by
  cases arena
  dsimp only [modelCell, readParent] at keyEq leftRun parentRead rightRun
  simp only [Cpp.optionalValue] at parentRead
  have selected : (!decide (key < lo)) = decide (lo ≤ key) := by
    by_cases above : lo ≤ key
    · simp [above, not_lt_of_ge above]
    · simp [above, lt_of_not_ge above]
  by_cases scanLeft : lo < key <;> by_cases keep : lo ≤ key <;> by_cases scanRight : key < hi <;>
    simp only [ite_true, ite_false, scanLeft, keep, scanRight, Nat.add_zero,
      Option.some.injEq, Prod.mk.injEq, and_true] at leftRun rightRun
  all_goals
    try (obtain ⟨rfl, rfl⟩ := leftRun)
    try (obtain ⟨rfl, rfl⟩ := rightRun)
    simp only [cp.TreeMultiSet.enumerate_in_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
      decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false, Cpp.optionalValue, fold_choice, *]

private theorem generated_enumerate_range_loop (arena : cp.TreeMultiSet K) (code parent : UInt64) (tree : Tree K)
    (parentKey : Option K) (lo hi : K) (used : List Nat) (rows : Array (K × UInt64 × K))
    (layout : Realizes (storageView arena) (decode code) tree used)
    (parentLayout : ParentAt arena parent parentKey) (fits : arena.slots.size ≤ 2 ^ 63)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ after stop, (cp.TreeMultiSet.enumerate_in_rec fuel arena rows code lo hi parent).run start =
      some ((after, arena), stop) ∧ stop ≤ start + 2 + 6 * tree.slots ∧
      after.toList.map outputRow = rows.toList.map outputRow ++ (tree.boundedEntries lo hi parentKey).map formatRow := by
  induction tree generalizing code parent parentKey used rows fuel start with
  | empty =>
    generalize decoded : decode code = index at layout
    cases layout with
    | empty =>
      have sentinel := (decode_none _).mp decoded
      subst code
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        exact ⟨rows, start + 2, enum_range_empty arena rows parent lo hi fuel start,
          by simp [Tree.slots], by simp [Tree.boundedEntries]⟩
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
        have currentParent : ParentAt arena code (some key) := ⟨present, keyEq⟩
        simp only [Tree.height] at enough
        have leftStage : ∃ middle walked,
            (if lo < key then (cp.TreeMultiSet.enumerate_in_rec fuel arena rows row.left lo hi code).run (start + 2)
              else some ((rows, arena), start + 2)) = some ((middle, arena), walked) ∧
            walked ≤ start + 4 + 6 * left.slots ∧
            middle.toList.map outputRow = rows.toList.map outputRow ++
              (if lo < key then left.boundedEntries lo hi (some key) else []).map formatRow := by
          by_cases scan : lo < key
          · obtain ⟨middle, walked, run, cost, output⟩ :=
              ihLeft row.left code (some key) ls rows (leftEq.symm ▸ ll) currentParent fuel (start + 2) (by omega)
            exact ⟨middle, walked, by simpa only [ite_eq_left scan], by omega, by simpa only [ite_eq_left scan]⟩
          · exact ⟨rows, start + 2, by simp [scan], by omega, by simp [scan]⟩
        obtain ⟨middle, walked, leftRun, leftCost, leftRows⟩ := leftStage
        let parentArg := parentValue parentKey
        let joined : K × UInt64 × K := (key, row.count, Cpp.Conv.conv parentArg)
        let keep : Prop := lo ≤ key ∧ key < hi
        let push := if keep then middle.push joined else middle
        let scanned := walked + if keep then 2 else 0
        have pushRows : push.toList.map outputRow = middle.toList.map outputRow ++
             (if Tree.inInterval lo hi key then [(key, count, parentKey)] else []).map formatRow := by
          by_cases selected : Tree.inInterval lo hi key
          · have keepIt : keep := selected
            dsimp only [push]
            rw [ite_eq_left keepIt, ite_eq_left selected]
            simp [joined, outputRow, formatRow, countEq, parentArg]
          · have omitIt : ¬keep := selected
            dsimp only [push]
            rw [ite_eq_right omitIt, ite_eq_right selected]
            simp
        have rightStage : ∃ after stop,
            (if key < hi then (cp.TreeMultiSet.enumerate_in_rec fuel arena push row.right lo hi code).run scanned
              else some ((middle, arena), walked)) = some ((after, arena), stop) ∧
            stop ≤ walked + 4 + 6 * right.slots ∧
            after.toList.map outputRow = push.toList.map outputRow ++
              (if key < hi then right.boundedEntries lo hi (some key) else []).map formatRow := by
          by_cases scan : key < hi
          · obtain ⟨out, stop, run, cost, output⟩ :=
              ihRight row.right code (some key) rs push (rightEq.symm ▸ rr) currentParent fuel scanned (by omega)
            have afterAppend : scanned ≤ walked + 2 := by dsimp [scanned]; split <;> omega
            exact ⟨out, stop, by simpa only [ite_eq_left scan], by omega, by simpa only [ite_eq_left scan]⟩
          · exact ⟨middle, walked, by simp [scan], by omega, by simp [push, keep, scan]⟩
        obtain ⟨out, stop, rightRun, rightCost, rightRows⟩ := rightStage
        refine ⟨out, stop, ?_, ?_, ?_⟩
        · apply enum_range_node arena rows middle out code parent key lo hi parentArg fuel start walked stop present keyEq leftRun
            (readParent_spec arena parent parentKey parentLayout (walked + 1))
          by_cases scan : key < hi <;> simpa [scan, push, scanned, keep, joined] using rightRun
        · simp only [Tree.slots]
          omega
        · rw [rightRows, pushRows, leftRows]
          simp only [Tree.boundedEntries, List.map_append, List.append_assoc]

private theorem enum_range_entry_run (arena : cp.TreeMultiSet K) (rows : Array (K × UInt64 × K))
    (lo hi : K) (start stop : Nat)
    (loop : (cp.TreeMultiSet.enumerate_in arena ([] : List (K × UInt64 × K)).toArray arena.root lo hi endIndex).run
      (start + 1 + 1) = some ((rows, arena), stop)) :
    (cp.TreeMultiSet.enumerate arena lo hi).run start = some ((rows, arena), stop) := by
  rw [cp.TreeMultiSet.enumerate]
  simp only [StateT.run_bind, tick_run, none_run, some_bind, pure_run]
  rw [loop]
  rfl

theorem generated_enumerate_spec (arena : cp.TreeMultiSet K) (tree : Tree K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (ordered : tree.Ordered) (fits : arena.slots.size ≤ 2 ^ 63) (lo hi : K) (start : Nat) :
    ∃ rows stop, (cp.TreeMultiSet.enumerate arena lo hi).run start = some ((rows, arena), stop) ∧
      stop ≤ start + 4 + 6 * tree.slots ∧
      rows.toList.map outputRow =
        ((tree.withParents none).filter (fun item => decide (Tree.inInterval lo hi item.1))).map formatRow ∧
      rows.size ≤ tree.slots := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨rows, stop, loop, cost, output⟩ := generated_enumerate_range_loop arena arena.root endIndex tree none lo hi used (List.toArray [])
    layout rfl fits Cpp.fuel (start + 2) enough
  have result : rows.toList.map outputRow =
      ((tree.withParents none).filter (fun item => decide (Tree.inInterval lo hi item.1))).map formatRow := by
    simpa [Tree.bounded_entries_filter lo hi tree ordered] using output
  refine ⟨rows, stop, ?_, by omega, result, ?_⟩
  · apply enum_range_entry_run
    rw [cp.TreeMultiSet.enumerate_in]
    exact loop
  · have exactSize : rows.size =
        ((tree.withParents none).filter (fun item => decide (Tree.inInterval lo hi item.1))).length := by
      simpa using congrArg List.length result
    rw [exactSize, ← Tree.withParents_length tree none]
    exact List.length_filter_le _ _

end Range

end Proofs.Cpp.TreeMultiset
