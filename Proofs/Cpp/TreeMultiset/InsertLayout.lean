import Proofs.Cpp.TreeMultiset.GeneratedInsert
import Proofs.Cpp.TreeMultiset.ArenaCapacity

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem Tree.insert_weight {K : Type} [LT K] [DecidableLT K]
    (key : K) (priority : UInt64) (count : Nat) (tree : Tree K) :
    (tree.insert key priority count).weight = tree.weight + count := by
  induction tree with
  | empty => simp [Tree.insert, Tree.weight]
  | node old p c left right ihLeft ihRight =>
    simp only [Tree.insert]
    by_cases higher : p < priority
    · rw [ite_eq_left higher]
      simp only [Tree.weight]
      have total := Tree.split_weight key (.node old p c left right)
      simp only [Tree.weight] at total
      omega
    · rw [ite_eq_right higher]
      split <;> simp only [Tree.weight, ihLeft, ihRight] <;> omega

private theorem item_view {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K)
    (code : UInt64) (index : Nat) (key : K) (priority : UInt64) (count : Nat)
    (layout : Realizes (storageView arena) (decode code) (.node key priority count .empty .empty) [index])
    (fits : arena.slots.size ≤ 2 ^ 63) :
    decode code = some index ∧ index < arena.slots.size ∧
      (modelCell arena code).key = some key ∧
      (modelCell arena code).priority = priority ∧ (modelCell arena code).count.toNat = count := by
  generalize decoded : decode code = root at layout
  generalize usedEq : [index] = physicalSlots at layout
  cases layout with
  | @node stored _ _ _ _ _ _ _ _ _ reads _ _ _ _ _ =>
    have same : index = stored := (List.cons.inj usedEq).1
    subst stored
    obtain ⟨_, inBounds, view⟩ := modelCell_view arena code index _ decoded reads fits
    exact ⟨rfl, inBounds, congrArg StoredNode.key view,
      congrArg StoredNode.priority view, congrArg StoredNode.count view⟩

structure InsertResult {K : Type} (before after : cp.TreeMultiSet K) (modified : List Nat)
    (root : UInt64) (tree : Tree K) where
  slots : List Nat
  treeLayout : Realizes (storageView after) (decode root) tree slots
  covers : ∀ i, i ∈ slots ↔ i ∈ modified
  frame : ArenaFrame before after modified

theorem generated_insert_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (tree : Tree K) (key : K) (priority : UInt64) (count : Nat)
    (arena : cp.TreeMultiSet K) (root item : UInt64) (used : List Nat) (index : Nat)
    (layout : Realizes (storageView arena) (decode root) tree used)
    (leaf : Realizes (storageView arena) (decode item) (.node key priority count .empty .empty) [index])
    (apart : index ∉ used) (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight + count < 2 ^ 64)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ code after stop, (cp.TreeMultiSet.insert_rec fuel arena root item).run start = some ((code, after), stop) ∧
      stop ≤ start + 7 * tree.insertSteps key priority ∧
      Nonempty (InsertResult arena after (index :: used) code (tree.insert key priority count)) := by
  induction tree generalizing arena root used fuel start with
  | empty =>
    generalize rootEq : decode root = rootIndex at layout
    cases layout with
    | empty =>
      have nil := (decode_none root).mp rootEq
      subst root
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        exact ⟨item, arena, start + 2, generated_insert_empty arena item fuel start,
          by simp [Tree.insertSteps], ⟨⟨[index], leaf, fun _ => Iff.rfl, ⟨rfl, rfl, rfl, fun _ _ => rfl⟩⟩⟩⟩
  | node old p c left right ihLeft ihRight =>
    generalize rootEq : decode root = rootIndex at layout
    cases layout with
    | @node rootSlot _ _ _ _ _ leftCode rightCode ls rs reads ll rr lf rf sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        obtain ⟨present, rootNat⟩ := decode_some root rootSlot rootEq
        obtain ⟨_, inside, view⟩ := modelCell_view arena root rootSlot _ rootEq reads fits
        obtain ⟨itemCode, itemInside, itemKey, itemPriority, itemCount⟩ :=
          item_view arena item index key priority count leaf fits
        have rootPosition : (Cpp.toSigned 64 root.toNat).toNat = rootSlot := by
          rw [signed_model_index (by omega), rootNat, Int.toNat_natCast]
        obtain ⟨_, itemNat⟩ := decode_some item index itemCode
        have itemPosition : (Cpp.toSigned 64 item.toNat).toNat = index := by
          rw [signed_model_index (by omega), itemNat, Int.toNat_natCast]
        let row := modelCell arena root
        let itemRow := modelCell arena item
        have rootKey : row.key = some old := congrArg StoredNode.key view
        have rootPriority : row.priority = p := congrArg StoredNode.priority view
        have rootCount : row.count.toNat = c := congrArg StoredNode.count view
        have leftEq : decode row.left = leftCode := congrArg StoredNode.left view
        have rightEq : decode row.right = rightCode := congrArg StoredNode.right view
        let tree := Tree.node old p c left right
        have original : Realizes (storageView arena) (decode root) tree (rootSlot :: (ls ++ rs)) :=
          rootEq.symm ▸ .node reads ll rr lf rf sep
        have totalWeight : tree.weight + count < 2 ^ 64 := weight
        by_cases higher : p < priority
        · have cap : tree.slots ≤ arena.slots.size := by simpa [storageView] using original.capacity
          have deep := Tree.height_le_slots tree
          have splitFuel : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
          obtain ⟨lower, upper, middle, subStop, subRun, subTime, ⟨sub⟩⟩ :=
            generated_split_spec tree key arena root (rootSlot :: (ls ++ rs)) original fits
              (by omega) Cpp.fuel (start + 2) splitFuel
          have stableItem : modelCell middle item = itemRow :=
            sub.frame.rawCell item (itemPosition.symm ▸ apart)
          have freshLow : index ∉ sub.lowSlots := fun mem => apart (sub.low_subset mem)
          have freshHigh : index ∉ sub.highSlots := fun mem => apart (sub.high_subset mem)
          let relinked : cp.TreeMultiSet_Slot K := {modelCell middle item with left := lower, right := upper}
          have bound : relinked.count.toNat + (tree.split key).1.weight + (tree.split key).2.weight < 2 ^ 64 := by
            have conserved := Tree.split_weight key tree
            change (modelCell middle item).count.toNat + _ + _ < 2 ^ 64
            rw [stableItem]
            change (modelCell arena item).count.toNat + _ + _ < 2 ^ 64
            rw [itemCount]
            omega
          obtain ⟨after, update, outRoot, outFree, outSize, built, unchanged⟩ :=
            generated_relink_spec middle item index relinked key (tree.split key).1 (tree.split key).2
              sub.lowSlots sub.highSlots itemCode (sub.frame.size.symm ▸ itemInside) (sub.frame.size.symm ▸ fits)
              (by change (modelCell middle item).key = some key; rw [stableItem]; exact itemKey)
              sub.lowTree sub.highTree freshLow freshHigh sub.separate bound subStop
          have frameRelink : ArenaFrame middle after [index] :=
            ⟨outRoot, outFree, outSize, fun i h => unchanged i (by simpa using h)⟩
          have frame := sub.frame.transOf frameRelink (fun {_} h => List.mem_cons_of_mem _ h)
            (fun {_} h => by simp at h; simp [h] : [index] ⊆ index :: rootSlot :: (ls ++ rs))
          have built' : Realizes (storageView after) (decode item)
              (.node key priority count (tree.split key).1 (tree.split key).2)
              (index :: (sub.lowSlots ++ sub.highSlots)) := by
            have pEq : relinked.priority = priority := by
              change (modelCell middle item).priority = priority
              rw [stableItem]
              exact itemPriority
            have cEq : relinked.count.toNat = count := by
              change (modelCell middle item).count.toNat = count
              rw [stableItem]
              exact itemCount
            simpa only [pEq, cEq] using built
          have run := generated_insert_split arena middle after root item lower upper key fuel start subStop (subStop + 5)
            present (by change row.priority < (modelCell arena item).priority; rwa [rootPriority, itemPriority])
            itemKey subRun (by rw [itemPosition, sub.frame.size]; exact itemInside) update
          refine ⟨item, after, subStop + 5, run, ?_, ?_⟩
          · rw [Tree.insertSteps, ite_eq_left higher]
            change _ ≤ start + 7 * (1 + tree.splitSteps key)
            omega
          · simp only [Tree.insert, ite_eq_left higher]
            refine ⟨⟨index :: (sub.lowSlots ++ sub.highSlots), built', ?_, frame⟩⟩
            intro i
            rw [List.mem_cons, List.mem_cons, sub.covers]
        · have lowerPriority : ¬ (modelCell arena root).priority < (modelCell arena item).priority := by
            change ¬ row.priority < (modelCell arena item).priority
            rwa [rootPriority, itemPriority]
          have notRoot : index ≠ rootSlot := fun e => apart (e.symm ▸ List.mem_cons_self ..)
          have notLeft : index ∉ ls := fun h => apart (List.mem_cons_of_mem _ (List.mem_append_left _ h))
          have notRight : index ∉ rs := fun h => apart (List.mem_cons_of_mem _ (List.mem_append_right _ h))
          simp only [Tree.weight, Tree.height] at weight enough
          by_cases less : key < old
          · obtain ⟨child, middle, subStop, subRun, subTime, ⟨sub⟩⟩ :=
              ihLeft arena row.left ls (leftEq.symm ▸ ll) leaf notLeft fits (by omega) fuel (start + 2) (by omega)
            have rootStable : modelCell middle root = row :=
              sub.frame.rawCell root (by simpa only [rootPosition, List.mem_cons, notRoot.symm, false_or])
            have stableRight : Realizes (storageView middle) rightCode right rs :=
              sub.frame.realizes rr (fun {_} mem changed => (List.mem_cons.mp changed).elim
                (fun eq => notRight (eq ▸ mem)) (fun h => sep h mem))
            have fresh : rootSlot ∉ sub.slots := by
              intro mem
              exact (List.mem_cons.mp ((sub.covers _).mp mem)).elim notRoot.symm lf
            have separate : List.Disjoint sub.slots rs :=
              fun {_} modified mem => (List.mem_cons.mp ((sub.covers _).mp modified)).elim
                (fun same => notRight (same ▸ mem)) (fun h => sep h mem)
            let relinked : cp.TreeMultiSet_Slot K := {modelCell middle root with left := child}
            let shape := left.insert key priority count
            have bound : relinked.count.toNat + shape.weight + right.weight < 2 ^ 64 := by
              simp only [relinked, rootStable, rootCount, shape, Tree.insert_weight]
              omega
            obtain ⟨after, update, outRoot, outFree, outSize, built, preserved⟩ :=
              generated_relink_spec middle root rootSlot relinked old shape right sub.slots rs rootEq
                (sub.frame.size.symm ▸ inside) (sub.frame.size.symm ▸ fits)
                (by simp only [relinked, rootStable, rootKey]) sub.treeLayout
                (by simpa only [relinked, rootStable, rightEq] using stableRight) fresh rf separate bound subStop
            have frameRelink : ArenaFrame middle after [rootSlot] :=
              ⟨outRoot, outFree, outSize, fun i h => preserved i (by simpa using h)⟩
            have frame : ArenaFrame arena after (index :: rootSlot :: (ls ++ rs)) :=
              sub.frame.transOf frameRelink
                (fun {_} h => (List.mem_cons.mp h).elim
                  (fun eq => eq.symm ▸ List.mem_cons_self ..)
                  (fun mem => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ mem))))
                (fun {_} h => by simp at h; simp [h])
            have built' : Realizes (storageView after) (decode root)
                (.node old p c shape right) (rootSlot :: (sub.slots ++ rs)) := by
              simpa only [relinked, rootStable, rootPriority, rootCount] using built
            have run := generated_insert_left arena middle after root item child key old fuel start subStop (subStop + 5)
              present lowerPriority itemKey rootKey less subRun update
            refine ⟨root, after, subStop + 5, run, ?_, ?_⟩
            · simp only [Tree.insertSteps, ite_eq_right higher, ite_eq_left less]
              omega
            · simp only [Tree.insert, ite_eq_right higher, ite_eq_left less]
              refine ⟨⟨rootSlot :: (sub.slots ++ rs), built', ?_, frame⟩⟩
              intro i
              rw [List.mem_cons, List.mem_append, sub.covers]
              simp only [List.mem_cons, List.mem_append, or_assoc, or_left_comm]
          · obtain ⟨child, middle, subStop, subRun, subTime, ⟨sub⟩⟩ :=
              ihRight arena row.right rs (rightEq.symm ▸ rr) leaf notRight fits (by omega) fuel (start + 2) (by omega)
            have rootStable : modelCell middle root = row :=
              sub.frame.rawCell root (by simpa only [rootPosition, List.mem_cons, notRoot.symm, false_or])
            have stableLeft : Realizes (storageView middle) leftCode left ls :=
              sub.frame.realizes ll (fun {_} mem changed => (List.mem_cons.mp changed).elim
                (fun eq => notLeft (eq ▸ mem)) (fun h => sep mem h))
            have fresh : rootSlot ∉ sub.slots := by
              intro mem
              exact (List.mem_cons.mp ((sub.covers _).mp mem)).elim notRoot.symm rf
            have separate : List.Disjoint ls sub.slots :=
              fun {_} mem modified => (List.mem_cons.mp ((sub.covers _).mp modified)).elim
                (fun same => notLeft (same ▸ mem)) (fun h => sep mem h)
            let relinked : cp.TreeMultiSet_Slot K := {modelCell middle root with right := child}
            let shape := right.insert key priority count
            have bound : relinked.count.toNat + left.weight + shape.weight < 2 ^ 64 := by
              simp only [relinked, rootStable, rootCount, shape, Tree.insert_weight]
              omega
            obtain ⟨after, update, outRoot, outFree, outSize, built, preserved⟩ :=
              generated_relink_spec middle root rootSlot relinked old left shape ls sub.slots rootEq
                (sub.frame.size.symm ▸ inside) (sub.frame.size.symm ▸ fits)
                (by simp only [relinked, rootStable, rootKey])
                (by simpa only [relinked, rootStable, leftEq] using stableLeft) sub.treeLayout lf fresh separate bound subStop
            have frameRelink : ArenaFrame middle after [rootSlot] :=
              ⟨outRoot, outFree, outSize, fun i h => preserved i (by simpa using h)⟩
            have frame : ArenaFrame arena after (index :: rootSlot :: (ls ++ rs)) :=
              sub.frame.transOf frameRelink
                (fun {_} h => (List.mem_cons.mp h).elim
                  (fun eq => eq.symm ▸ List.mem_cons_self ..)
                  (fun mem => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ mem))))
                (fun {_} h => by simp at h; simp [h])
            have built' : Realizes (storageView after) (decode root)
                (.node old p c left shape) (rootSlot :: (ls ++ sub.slots)) := by
              simpa only [relinked, rootStable, rootPriority, rootCount] using built
            have run := generated_insert_right arena middle after root item child key old fuel start subStop (subStop + 5)
              present lowerPriority itemKey rootKey less subRun update
            refine ⟨root, after, subStop + 5, run, ?_, ?_⟩
            · simp only [Tree.insertSteps, ite_eq_right higher, ite_eq_right less]
              omega
            · simp only [Tree.insert, ite_eq_right higher, ite_eq_right less]
              refine ⟨⟨rootSlot :: (ls ++ sub.slots), built', ?_, frame⟩⟩
              intro i
              rw [List.mem_cons, List.mem_append, sub.covers]
              simp only [List.mem_cons, List.mem_append, or_left_comm]

theorem generated_insert_entry {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (tree : Tree K) (key : K) (priority : UInt64) (count : Nat)
    (arena : cp.TreeMultiSet K) (root item : UInt64) (used : List Nat) (index : Nat)
    (layout : Realizes (storageView arena) (decode root) tree used)
    (leaf : Realizes (storageView arena) (decode item) (.node key priority count .empty .empty) [index])
    (apart : index ∉ used) (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight + count < 2 ^ 64)
    (start : Nat) :
    ∃ code after stop, (cp.TreeMultiSet.insert arena root item).run start = some ((code, after), stop) ∧
      stop ≤ start + 7 * (tree.height + 2) ∧
      Nonempty (InsertResult arena after (index :: used) code (tree.insert key priority count)) := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨code, after, stop, run, ticks, result⟩ :=
    generated_insert_spec tree key priority count arena root item used index layout leaf apart
      fits weight Cpp.fuel start enough
  have cost := tree.insert_steps_le key priority
  exact ⟨code, after, stop, run, by omega, result⟩

end Proofs.Cpp.TreeMultiset
