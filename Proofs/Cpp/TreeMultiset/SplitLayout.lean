import Proofs.Cpp.TreeMultiset.GeneratedSplit
import Proofs.Cpp.TreeMultiset.GeneratedFrame

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem Tree.split_height_ticks [LT K] [DecidableLT K] (pivot : K) (tree : Tree K) :
    7 * tree.splitSteps pivot - 3 ≤ 4 + 7 * tree.height := by
  have steps := tree.split_steps_le pivot
  omega

structure SplitResult {K : Type} (before after : cp.TreeMultiSet K) (modified : List Nat)
    (low high : UInt64) (lower upper : Tree K) where
  lowSlots : List Nat
  highSlots : List Nat
  lowTree : Realizes (storageView after) (decode low) lower lowSlots
  highTree : Realizes (storageView after) (decode high) upper highSlots
  separate : List.Disjoint lowSlots highSlots
  covers : ∀ i, i ∈ lowSlots ++ highSlots ↔ i ∈ modified
  frame : ArenaFrame before after modified

namespace SplitResult

theorem low_subset {K : Type} {before after : cp.TreeMultiSet K} {modified : List Nat} {low high : UInt64}
    {lower upper : Tree K} (joined : SplitResult before after modified low high lower upper) :
    joined.lowSlots ⊆ modified := fun {_} h => (joined.covers _).mp (List.mem_append_left _ h)

theorem high_subset {K : Type} {before after : cp.TreeMultiSet K} {modified : List Nat} {low high : UInt64}
    {lower upper : Tree K} (joined : SplitResult before after modified low high lower upper) :
    joined.highSlots ⊆ modified := fun {_} h => (joined.covers _).mp (List.mem_append_right _ h)

end SplitResult

theorem generated_split_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (tree : Tree K) (pivot : K) (arena : cp.TreeMultiSet K) (code : UInt64) (used : List Nat)
    (layout : Realizes (storageView arena) (decode code) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ low high after stop,
      (cp.TreeMultiSet.split_rec fuel arena code pivot).run start = some (((low, high), after), stop) ∧
      stop = start + (7 * tree.splitSteps pivot - 3) ∧
      Nonempty (SplitResult arena after used low high (tree.split pivot).1 (tree.split pivot).2) := by
  induction tree generalizing arena code used fuel start with
  | empty =>
    generalize rootEq : decode code = root at layout
    cases layout with
    | empty =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        have sentinel := (decode_none _).mp rootEq
        subst code
        have emptyDecode : decode endIndex = none := (decode_none _).mpr rfl
        have emptyTree : Realizes (storageView arena) (decode endIndex) (.empty : Tree K) [] :=
          emptyDecode.symm ▸ .empty
        refine ⟨endIndex, endIndex, arena, start + 4, generated_split_empty arena pivot fuel start, rfl,
          ⟨⟨[], [], emptyTree, emptyTree, by simp, by simp, ⟨rfl, rfl, rfl, fun _ _ => rfl⟩⟩⟩⟩
  | node key priority count left right ihLeft ihRight =>
    generalize rootEq : decode code = root at layout
    cases layout with
    | @node index _ _ _ _ _ leftCode rightCode leftUsed rightUsed reads leftLayout
        rightLayout leftFresh rightFresh separate =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        obtain ⟨notEnd, _⟩ := decode_some code index rootEq
        obtain ⟨codeNat, inside, view⟩ := modelCell_view arena code index _ rootEq reads fits
        have signedNat : (Cpp.toSigned 64 code.toNat).toNat = index := by
          rw [signed_model_index (by omega), codeNat, Int.toNat_natCast]
        let row := modelCell arena code
        have keyEq : row.key = some key := congrArg StoredNode.key view
        have priorityEq : row.priority = priority := congrArg StoredNode.priority view
        have countEq : row.count.toNat = count := congrArg StoredNode.count view
        have leftEq : decode row.left = leftCode := congrArg StoredNode.left view
        have rightEq : decode row.right = rightCode := congrArg StoredNode.right view
        simp only [Tree.height, Tree.weight] at enough weight
        by_cases less : pivot < key
        · obtain ⟨lo, hi, middle, tick, subRun, subTicks, ⟨sub⟩⟩ :=
            ihLeft arena row.left leftUsed (leftEq.symm ▸ leftLayout) fits (by omega) fuel (start + 2) (by omega)
          have rootStable : modelCell middle code = row :=
            sub.frame.rawCell code (signedNat.symm ▸ leftFresh)
          have stableRight := sub.frame.realizes rightLayout (List.disjoint_comm.mp separate)
          have freshHigh : index ∉ sub.highSlots := fun mem => leftFresh (sub.high_subset mem)
          have freshLow : index ∉ sub.lowSlots := fun mem => leftFresh (sub.low_subset mem)
          have highApart : List.Disjoint sub.highSlots rightUsed := fun {_} h => separate (sub.high_subset h)
          let relinked : cp.TreeMultiSet_Slot K := {modelCell middle code with left := hi}
          have bound : relinked.count.toNat + (left.split pivot).2.weight + right.weight < 2 ^ 64 := by
            have conserved := Tree.split_weight pivot left
            simp only [relinked, rootStable, countEq]
            omega
          obtain ⟨after, updated, rootPreserved, freePreserved, sizePreserved, built, outside⟩ :=
            generated_relink_spec middle code index relinked key (left.split pivot).2 right sub.highSlots rightUsed
              rootEq (sub.frame.size.symm ▸ inside) (sub.frame.size.symm ▸ fits)
              (by simpa [relinked, rootStable]) sub.highTree (by simpa [relinked, rootStable, rightEq] using stableRight)
              freshHigh rightFresh highApart bound tick
          have relinkFrame : ArenaFrame middle after [index] := ⟨rootPreserved, freePreserved, sizePreserved,
            fun i other => outside i (by simpa using other)⟩
          have frame := sub.frame.transOf relinkFrame (fun {_} h => List.mem_cons_of_mem _ (List.mem_append_left _ h))
            (fun {i} h => by simp at h; simp [h] :
              [index] ⊆ index :: (leftUsed ++ rightUsed))
          have stableLow : Realizes (storageView after) (decode lo) (left.split pivot).1 sub.lowSlots :=
            sub.lowTree.frame fun i mem => outside i fun e => freshLow (e ▸ mem)
          have built' : Realizes (storageView after) (decode code)
              (.node key priority count (left.split pivot).2 right) (index :: (sub.highSlots ++ rightUsed)) := by
            simpa [relinked, rootStable, priorityEq, countEq] using built
          have positive : 0 < left.splitSteps pivot := by cases left <;> simp [Tree.splitSteps]
          refine ⟨lo, code, after, tick + 5,
            generated_split_left arena middle after code lo hi pivot key fuel start tick (tick + 5)
              notEnd keyEq less subRun updated, ?_, ?_⟩
          · simp only [Tree.splitSteps, ite_eq_left less]
            omega
          · simp only [Tree.split, ite_eq_left less]
            refine ⟨⟨sub.lowSlots, index :: (sub.highSlots ++ rightUsed), stableLow, built',
              ?_, ?_, frame⟩⟩
            · intro i lowMem highMem
              rcases List.mem_cons.mp highMem with rfl | either
              · exact freshLow lowMem
              rcases List.mem_append.mp either with h | h
              · exact sub.separate lowMem h
              · exact separate (sub.low_subset lowMem) h
            · intro i
              have covers := sub.covers i
              simp only [List.mem_append, List.mem_cons] at covers ⊢
              rw [← covers]
              simp only [or_left_comm, or_comm]
        · obtain ⟨lo, hi, middle, tick, subRun, subTicks, ⟨sub⟩⟩ :=
            ihRight arena row.right rightUsed (rightEq.symm ▸ rightLayout) fits (by omega) fuel (start + 2) (by omega)
          have rootStable : modelCell middle code = row :=
            sub.frame.rawCell code (signedNat.symm ▸ rightFresh)
          have stableLeft := sub.frame.realizes leftLayout separate
          have freshHigh : index ∉ sub.highSlots := fun mem => rightFresh (sub.high_subset mem)
          have freshLow : index ∉ sub.lowSlots := fun mem => rightFresh (sub.low_subset mem)
          have lowApart : List.Disjoint leftUsed sub.lowSlots :=
            fun {_} l r => separate l (sub.low_subset r)
          let relinked : cp.TreeMultiSet_Slot K := {modelCell middle code with right := lo}
          have bound : relinked.count.toNat + left.weight + (right.split pivot).1.weight < 2 ^ 64 := by
            have conserved := Tree.split_weight pivot right
            simp only [relinked, rootStable, countEq]
            omega
          obtain ⟨after, updated, rootPreserved, freePreserved, sizePreserved, built, outside⟩ :=
            generated_relink_spec middle code index relinked key left (right.split pivot).1 leftUsed sub.lowSlots
              rootEq (sub.frame.size.symm ▸ inside) (sub.frame.size.symm ▸ fits)
              (by simpa [relinked, rootStable]) (by simpa [relinked, rootStable, leftEq] using stableLeft)
              sub.lowTree leftFresh freshLow lowApart bound tick
          have relinkFrame : ArenaFrame middle after [index] := ⟨rootPreserved, freePreserved, sizePreserved,
            fun i other => outside i (by simpa using other)⟩
          have frame := sub.frame.transOf relinkFrame
            (fun {_} h => List.mem_cons_of_mem _ (List.mem_append_right _ h))
            (fun {i} h => by simp at h; simp [h] :
              [index] ⊆ index :: (leftUsed ++ rightUsed))
          have stableHigh : Realizes (storageView after) (decode hi) (right.split pivot).2 sub.highSlots :=
            sub.highTree.frame fun i mem => outside i fun e => freshHigh (e ▸ mem)
          have built' : Realizes (storageView after) (decode code)
              (.node key priority count left (right.split pivot).1) (index :: (leftUsed ++ sub.lowSlots)) := by
            simpa [relinked, rootStable, priorityEq, countEq] using built
          have positive : 0 < right.splitSteps pivot := by cases right <;> simp [Tree.splitSteps]
          refine ⟨code, hi, after, tick + 5,
            generated_split_right arena middle after code lo hi pivot key fuel start tick (tick + 5)
              notEnd keyEq less subRun updated, ?_, ?_⟩
          · simp only [Tree.splitSteps, ite_eq_right less]
            omega
          · simp only [Tree.split, ite_eq_right less]
            refine ⟨⟨index :: (leftUsed ++ sub.lowSlots), sub.highSlots, built', stableHigh,
              ?_, ?_, frame⟩⟩
            · intro i lowMem highMem
              rcases List.mem_cons.mp lowMem with rfl | either
              · exact freshHigh highMem
              rcases List.mem_append.mp either with h | h
              · exact separate h (sub.high_subset highMem)
              · exact sub.separate h highMem
            · intro i
              have covers := sub.covers i
              simp only [List.mem_append, List.mem_cons] at covers ⊢
              rw [← covers]
              simp only [or_assoc]

end Proofs.Cpp.TreeMultiset
