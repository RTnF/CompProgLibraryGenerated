import Proofs.Cpp.TreeMultiset.GeneratedCountUpdate

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem Tree.change_count_weight {K : Type} [LT K] [DecidableLT K] [DecidableEq K]
    (tree : Tree K) (key : K) (before after : Nat) (found : tree.lookup key = some before) :
    (tree.changeCount key (fun _ => after)).weight + before = tree.weight + after := by
  induction tree with
  | empty => simp [Tree.lookup] at found
  | node old p n left right ihLeft ihRight =>
    simp only [Tree.lookup, Tree.changeCount] at found ⊢
    by_cases equal : key = old
    · rw [ite_eq_left equal] at found ⊢
      cases found
      simp only [Tree.weight]
      omega
    · rw [ite_eq_right equal] at found ⊢
      by_cases less : key < old
      · rw [ite_eq_left less] at found ⊢
        have weight := ihLeft found
        simp only [Tree.weight]
        omega
      · rw [ite_eq_right less] at found ⊢
        have weight := ihRight found
        simp only [Tree.weight]
        omega

private theorem putCell_same {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (code : UInt64)
    (inside : (Cpp.toSigned 64 code.toNat).toNat < arena.slots.size) :
    putCell arena code (modelCell arena code) = arena := by
  cases arena
  dsimp only at inside
  simp [putCell, modelCell, Cpp.get_eq, Cpp.set, Array.setIfInBounds, getElem!_pos, inside]

theorem generated_replace_count_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (tree : Tree K) (key : K) (count : Nat) (next : UInt64) (found : tree.lookup key = some count)
    (arena : cp.TreeMultiSet K) (code : UInt64) (used : List Nat)
    (layout : Realizes (storageView arena) (decode code) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : (tree.changeCount key (fun _ => next.toNat)).weight < 2 ^ 64)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ after stop, (cp.TreeMultiSet.replace_count_rec fuel arena code key next).run start = some (after, stop) ∧
      stop ≤ start + 6 * tree.height ∧
      Realizes (storageView after) (decode code) (tree.changeCount key (fun _ => next.toNat)) used ∧
      ArenaFrame arena after used := by
  induction tree generalizing arena code used fuel start with
  | empty => simp [Tree.lookup] at found
  | node old priority n left right ihLeft ihRight =>
    generalize decoded : decode code = index at layout
    cases layout with
    | @node slot _ _ _ _ _ leftCode rightCode ls rs reads ll rr lf rf sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        obtain ⟨codeNat, inside, view⟩ := modelCell_view arena code slot _ decoded reads fits
        have signedNat : (Cpp.toSigned 64 code.toNat).toNat = slot := by
          rw [signed_model_index (by omega), codeNat, Int.toNat_natCast]
        let row := modelCell arena code
        have rootKey : row.key = some old := congrArg StoredNode.key view
        have rootPriority : row.priority = priority := congrArg StoredNode.priority view
        have rootCount : row.count.toNat = n := congrArg StoredNode.count view
        have leftEq : decode row.left = leftCode := congrArg StoredNode.left view
        have rightEq : decode row.right = rightCode := congrArg StoredNode.right view
        simp only [Tree.height] at enough
        by_cases equal : key = old
        · simp only [Tree.changeCount, ite_eq_left equal, Tree.weight] at weight
          let relinked : cp.TreeMultiSet_Slot K := {modelCell arena code with count := next}
          obtain ⟨after, update, outRoot, outFree, outSize, built, outside⟩ :=
            generated_relink_spec arena code slot relinked old left right ls rs decoded inside fits
              rootKey (leftEq.symm ▸ ll) (rightEq.symm ▸ rr) lf rf sep weight (start + 1)
          have run := generated_count_here arena after code next key fuel start (start + 1 + 5)
            (equal.symm ▸ rootKey) update
          refine ⟨after, _, run, ?_, ?_, ⟨outRoot, outFree, outSize, ?_⟩⟩
          · simp only [Tree.height]; omega
          · have priorityEq : relinked.priority = priority := rootPriority
            simpa only [Tree.changeCount, ite_eq_left equal, decoded, priorityEq] using built
          · intro i other
            exact outside i fun e => other (e.symm ▸ List.mem_cons_self ..)
        · simp only [Tree.lookup, ite_eq_right equal] at found
          simp only [Tree.changeCount, ite_eq_right equal] at weight
          by_cases less : key < old
          · simp only [ite_eq_left less] at found
            simp only [ite_eq_left less, Tree.weight] at weight
            let changed := left.changeCount key (fun _ => next.toNat)
            obtain ⟨middle, subStop, subRun, subTime, changedLayout, frame⟩ :=
              ihLeft found arena row.left ls (leftEq.symm ▸ ll) fits (by omega) fuel (start + 1) (by omega)
            have rootStable : modelCell middle code = row := frame.rawCell code (signedNat.symm ▸ lf)
            have stableOther : Realizes (storageView middle) rightCode right rs :=
              frame.realizes rr (List.disjoint_comm.mp sep)
            have bounded : row.count.toNat + changed.weight + right.weight < 2 ^ 64 := by
              rw [rootCount]
              exact weight
            obtain ⟨after, update, outRoot, outFree, outSize, built, outside⟩ :=
              generated_relink_spec middle code slot row old changed right ls rs decoded
                (frame.size.symm ▸ inside) (frame.size.symm ▸ fits) rootKey
                changedLayout (rightEq.symm ▸ stableOther) lf rf sep bounded subStop
            have sameCell : putCell middle code row = middle := by
              rw [← rootStable]
              apply putCell_same
              rwa [signedNat, frame.size]
            rw [sameCell] at update
            have run := generated_count_left arena middle after code next key old fuel start subStop (subStop + 5)
              equal rootKey less subRun update
            refine ⟨after, _, run, ?_, ?_, ?_⟩
            · simp only [Tree.height]; omega
            · simpa only [Tree.changeCount, ite_eq_right equal, ite_eq_left less, decoded, rootPriority, rootCount] using built
            · have relink : ArenaFrame middle after [slot] :=
                ⟨outRoot, outFree, outSize, fun i h => outside i (by simpa using h)⟩
              exact frame.transOf relink (fun {_} h => List.mem_cons_of_mem _ (List.mem_append_left _ h))
                (fun {_} h => by simp at h; simp [h])
          · simp only [ite_eq_right less] at found
            simp only [ite_eq_right less, Tree.weight] at weight
            let changed := right.changeCount key (fun _ => next.toNat)
            obtain ⟨middle, subStop, subRun, subTime, changedLayout, frame⟩ :=
              ihRight found arena row.right rs (rightEq.symm ▸ rr) fits (by omega) fuel (start + 1) (by omega)
            have rootStable : modelCell middle code = row := frame.rawCell code (signedNat.symm ▸ rf)
            have stableOther : Realizes (storageView middle) leftCode left ls :=
              frame.realizes ll (sep)
            have bounded : row.count.toNat + left.weight + changed.weight < 2 ^ 64 := by
              rw [rootCount]
              exact weight
            obtain ⟨after, update, outRoot, outFree, outSize, built, outside⟩ :=
              generated_relink_spec middle code slot row old left changed ls rs decoded
                (frame.size.symm ▸ inside) (frame.size.symm ▸ fits) rootKey
                (leftEq.symm ▸ stableOther) changedLayout lf rf sep bounded subStop
            have sameCell : putCell middle code row = middle := by
              rw [← rootStable]
              apply putCell_same
              rwa [signedNat, frame.size]
            rw [sameCell] at update
            have run := generated_count_right arena middle after code next key old fuel start subStop (subStop + 5)
              equal rootKey less subRun update
            refine ⟨after, _, run, ?_, ?_, ?_⟩
            · simp only [Tree.height]; omega
            · simpa only [Tree.changeCount, ite_eq_right equal, ite_eq_right less, decoded, rootPriority, rootCount] using built
            · have relink : ArenaFrame middle after [slot] :=
                ⟨outRoot, outFree, outSize, fun i h => outside i (by simpa using h)⟩
              exact frame.transOf relink (fun {_} h => List.mem_cons_of_mem _ (List.mem_append_right _ h))
                (fun {_} h => by simp at h; simp [h])


theorem generated_count_entry {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (tree : Tree K) (key : K) (count : Nat) (next : UInt64)
    (found : tree.lookup key = some count) (arena : cp.TreeMultiSet K) (code : UInt64) (used : List Nat)
    (layout : Realizes (storageView arena) (decode code) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : (tree.changeCount key (fun _ => next.toNat)).weight < 2 ^ 64)
    (start : Nat) :
    ∃ after stop, (cp.TreeMultiSet.replace_count arena code key next).run start = some (after, stop) ∧
      stop ≤ start + 6 * tree.height ∧
      Realizes (storageView after) (decode code) (tree.changeCount key (fun _ => next.toNat)) used ∧
      ArenaFrame arena after used := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  exact generated_replace_count_spec tree key count next found arena code used layout fits weight Cpp.fuel start enough

end Proofs.Cpp.TreeMultiset
