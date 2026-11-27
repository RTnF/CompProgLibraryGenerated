import Proofs.Cpp.TreeMultiset.GeneratedErase

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem Tree.erase_weight {K : Type} [LT K] [DecidableLT K] [DecidableEq K]
    (tree : Tree K) (key : K) (count : Nat) (found : tree.lookup key = some count) :
    (tree.erase key).weight + count = tree.weight := by
  induction tree with
  | empty => simp [Tree.lookup] at found
  | node old p n left right ihLeft ihRight =>
    simp only [Tree.lookup, Tree.erase] at found ⊢
    by_cases equal : key = old
    · rw [ite_eq_left equal] at found ⊢
      cases found
      rw [Tree.merge_weight, Tree.weight]
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

structure EraseResult {K : Type} (before after : cp.TreeMultiSet K) (modified free : List Nat)
    (root : UInt64) (tree : Tree K) where
  removed : Nat
  slots : List Nat
  treeLayout : Realizes (storageView after) (decode root) tree slots
  freeLayout : FreeSlots (storageView after) (decode after.free_head) (removed :: free)
  covers : ∀ i, i = removed ∨ i ∈ slots ↔ i ∈ modified
  rootPreserved : after.root = before.root
  sizePreserved : after.slots.size = before.slots.size
  outside : ∀ i, i ∉ modified → (storageView after)[i]? = (storageView before)[i]?

theorem generated_erase_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (tree : Tree K) (key : K) (count : Nat) (found : tree.lookup key = some count)
    (arena : cp.TreeMultiSet K) (code : UInt64) (used free : List Nat)
    (layout : Realizes (storageView arena) (decode code) tree used)
    (freeList : FreeSlots (storageView arena) (decode arena.free_head) free)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ root after stop, (cp.TreeMultiSet.erase_rec fuel arena code key).run start = some ((root, after), stop) ∧
      stop ≤ start + 16 * tree.height + 5 ∧ Nonempty (EraseResult arena after used free root (tree.erase key)) := by
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
        simp only [Tree.weight, Tree.height] at weight enough
        by_cases equal : key = old
        · obtain ⟨joined, middle, merged, mergeRun, mergeTime, ⟨merge⟩⟩ :=
            generated_merge_entry left right arena row.left row.right ls rs
              (leftEq.symm ▸ ll) (rightEq.symm ▸ rr) sep fits (by omega) (start + 1)
          have fresh : slot ∉ ls ++ rs := by simp [lf, rf]
          have rootLive : (storageView middle)[slot]? = some (slotView row) := by
            rw [merge.frame.outside _ fresh, reads, view]
          have freeStable : FreeSlots (storageView middle) (decode middle.free_head) free := by
            rw [merge.frame.free]
            apply freeList.frame
            intro i vacant
            exact merge.frame.outside i fun changed => (List.mem_append.mp changed).elim
              (freeList.disjoint_tree ll vacant) (freeList.disjoint_tree rr vacant)
          obtain ⟨after, releaseRun, rootSame, _, sizeSame, freeAfter, releaseFrame⟩ :=
            generated_release_spec middle code slot (slotView row) free decoded rootLive
              (by change row.key.isSome = true; simp [rootKey]) freeStable (merge.frame.size.symm ▸ fits) merged
          have built : Realizes (storageView after) (decode joined) (left.merge right) merge.slots :=
            merge.treeLayout.frame fun i mem => releaseFrame i fun same => fresh ((merge.covers _).mp (same ▸ mem))
          have run := generated_erase_here arena middle after code joined key fuel start merged (merged + 1)
            (by rw [equal]; exact rootKey) mergeRun releaseRun
          refine ⟨joined, after, merged + 1, run, ?_, ?_⟩
          · simp only [Tree.height]
            omega
          · simp only [Tree.erase, ite_eq_left equal]
            refine ⟨⟨slot, merge.slots, built, freeAfter, ?_, rootSame.trans merge.frame.root,
              sizeSame.trans merge.frame.size, ?_⟩⟩
            · intro i
              rw [merge.covers, List.mem_cons]
            · intro i other
              have diff : i ≠ slot := fun e => other (e.symm ▸ List.mem_cons_self ..)
              exact (releaseFrame i diff).trans (merge.frame.outside i fun mem => other (List.mem_cons_of_mem _ mem))
        · simp only [Tree.lookup, ite_eq_right equal] at found
          by_cases less : key < old
          · simp only [ite_eq_left less] at found
            obtain ⟨child, middle, subStop, subRun, subTime, ⟨sub⟩⟩ :=
              ihLeft found arena row.left ls (leftEq.symm ▸ ll) freeList fits (by omega) fuel (start + 1) (by omega)
            have rootStableReads := sub.outside slot lf
            have rootStable : modelCell middle code = row := by
              have sameView := (modelCell_view middle code slot _ decoded (rootStableReads.trans reads)
                (sub.sizePreserved.symm ▸ fits)).2.2
              exact slotView_injective (sameView.trans view.symm)
            have stableOther : Realizes (storageView middle) rightCode right rs :=
              rr.frame fun i mem => sub.outside i (fun changed => sep changed mem)
            have fresh : slot ∉ sub.slots := fun mem => lf ((sub.covers _).mp (Or.inr mem))
            have separate : List.Disjoint sub.slots rs :=
              fun {_} h q => sep ((sub.covers _).mp (Or.inr h)) q
            let relinked : cp.TreeMultiSet_Slot K := {modelCell middle code with left := child}
            let shape := left.erase key
            have bound : relinked.count.toNat + shape.weight + right.weight < 2 ^ 64 := by
              have subWeight := Tree.erase_weight left key count found
              simp only [relinked, rootStable, rootCount, shape]
              omega
            obtain ⟨after, update, outRoot, outFree, outSize, built, preserved⟩ :=
              generated_relink_spec middle code slot relinked old shape right sub.slots rs decoded
                (sub.sizePreserved.symm ▸ inside) (sub.sizePreserved.symm ▸ fits)
                (by simp only [relinked, rootStable, rootKey]) sub.treeLayout
                (by simpa only [relinked, rootStable, rightEq] using stableOther) fresh rf separate bound subStop
            have freeAfter : FreeSlots (storageView after) (decode after.free_head) (sub.removed :: free) := by
              rw [outFree]
              apply sub.freeLayout.frame
              intro i vacant
              apply preserved i
              intro same
              subst i
              obtain ⟨empty, checked, noKey⟩ := sub.freeLayout.vacant slot vacant
              have eq := Option.some.inj (checked.symm.trans (rootStableReads.trans reads))
              cases eq
              contradiction
            have built' : Realizes (storageView after) (decode code)
                (.node old priority n shape right) (slot :: (sub.slots ++ rs)) := by
              simpa only [relinked, rootStable, rootPriority, rootCount] using built
            have run := generated_erase_left arena middle after code child key old fuel start subStop (subStop + 5)
              (Ne.symm equal) rootKey less subRun update
            refine ⟨code, after, subStop + 5, run, ?_, ?_⟩
            · simp only [Tree.height]
              omega
            · simp only [Tree.erase, ite_eq_right equal, ite_eq_left less]
              refine ⟨⟨sub.removed, slot :: (sub.slots ++ rs), built', freeAfter, ?_,
                outRoot.trans sub.rootPreserved, outSize.trans sub.sizePreserved, ?_⟩⟩
              · intro i
                have covers := sub.covers i
                simp only [List.mem_cons, List.mem_append] at covers ⊢
                rw [← covers]
                simp only [or_left_comm, or_comm]
              · intro i outside
                have diff : i ≠ slot := fun e => outside (e.symm ▸ List.mem_cons_self ..)
                exact (preserved i diff).trans (sub.outside i fun mem =>
                  outside (List.mem_cons_of_mem _ (List.mem_append_left _ mem)))
          · simp only [ite_eq_right less] at found
            obtain ⟨child, middle, subStop, subRun, subTime, ⟨sub⟩⟩ :=
              ihRight found arena row.right rs (rightEq.symm ▸ rr) freeList fits (by omega) fuel (start + 1) (by omega)
            have rootStableReads := sub.outside slot rf
            have rootStable : modelCell middle code = row := by
              have sameView := (modelCell_view middle code slot _ decoded (rootStableReads.trans reads)
                (sub.sizePreserved.symm ▸ fits)).2.2
              exact slotView_injective (sameView.trans view.symm)
            have stableOther : Realizes (storageView middle) leftCode left ls :=
              ll.frame fun i mem => sub.outside i (fun changed => sep mem changed)
            have fresh : slot ∉ sub.slots := fun mem => rf ((sub.covers _).mp (Or.inr mem))
            have separate : List.Disjoint ls sub.slots :=
              fun {_} h q => sep h ((sub.covers _).mp (Or.inr q))
            let relinked : cp.TreeMultiSet_Slot K := {modelCell middle code with right := child}
            let shape := right.erase key
            have bound : relinked.count.toNat + left.weight + shape.weight < 2 ^ 64 := by
              have subWeight := Tree.erase_weight right key count found
              simp only [relinked, rootStable, rootCount, shape]
              omega
            obtain ⟨after, update, outRoot, outFree, outSize, built, preserved⟩ :=
              generated_relink_spec middle code slot relinked old left shape ls sub.slots decoded
                (sub.sizePreserved.symm ▸ inside) (sub.sizePreserved.symm ▸ fits)
                (by simp only [relinked, rootStable, rootKey]) (by simpa only [relinked, rootStable, leftEq] using stableOther)
                sub.treeLayout lf fresh separate bound subStop
            have freeAfter : FreeSlots (storageView after) (decode after.free_head) (sub.removed :: free) := by
              rw [outFree]
              apply sub.freeLayout.frame
              intro i vacant
              apply preserved i
              intro same
              subst i
              obtain ⟨empty, checked, noKey⟩ := sub.freeLayout.vacant slot vacant
              have eq := Option.some.inj (checked.symm.trans (rootStableReads.trans reads))
              cases eq
              contradiction
            have built' : Realizes (storageView after) (decode code)
                (.node old priority n left shape) (slot :: (ls ++ sub.slots)) := by
              simpa only [relinked, rootStable, rootPriority, rootCount] using built
            have run := generated_erase_right arena middle after code child key old fuel start subStop (subStop + 5)
              (Ne.symm equal) rootKey less subRun update
            refine ⟨code, after, subStop + 5, run, ?_, ?_⟩
            · simp only [Tree.height]
              omega
            · simp only [Tree.erase, ite_eq_right equal, ite_eq_right less]
              refine ⟨⟨sub.removed, slot :: (ls ++ sub.slots), built', freeAfter, ?_,
                outRoot.trans sub.rootPreserved, outSize.trans sub.sizePreserved, ?_⟩⟩
              · intro i
                have covers := sub.covers i
                simp only [List.mem_cons, List.mem_append] at covers ⊢
                rw [← covers]
                simp only [or_left_comm]
              · intro i outside
                have diff : i ≠ slot := fun e => outside (e.symm ▸ List.mem_cons_self ..)
                exact (preserved i diff).trans (sub.outside i fun mem =>
                  outside (List.mem_cons_of_mem _ (List.mem_append_right _ mem)))


theorem generated_erase_entry {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (tree : Tree K) (key : K) (count : Nat) (found : tree.lookup key = some count)
    (arena : cp.TreeMultiSet K) (code : UInt64) (used free : List Nat)
    (layout : Realizes (storageView arena) (decode code) tree used)
    (freeList : FreeSlots (storageView arena) (decode arena.free_head) free)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64) (start : Nat) :
    ∃ root after stop, (cp.TreeMultiSet.erase arena code key).run start = some ((root, after), stop) ∧
      stop ≤ start + 16 * tree.height + 5 ∧ Nonempty (EraseResult arena after used free root (tree.erase key)) := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  exact generated_erase_spec tree key count found arena code used free layout freeList fits weight
    Cpp.fuel start enough

end Proofs.Cpp.TreeMultiset
