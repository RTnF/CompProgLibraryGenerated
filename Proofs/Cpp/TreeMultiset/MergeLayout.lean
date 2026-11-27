import Proofs.Cpp.TreeMultiset.GeneratedMerge
import Proofs.Cpp.TreeMultiset.GeneratedFrame

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

structure MergeResult {K : Type} (before after : cp.TreeMultiSet K) (modified : List Nat)
    (root : UInt64) (tree : Tree K) where
  slots : List Nat
  treeLayout : Realizes (storageView after) (decode root) tree slots
  covers : ∀ i, i ∈ slots ↔ i ∈ modified
  frame : ArenaFrame before after modified

namespace MergeResult

theorem unchanged {K : Type} (arena : cp.TreeMultiSet K) (root : UInt64) (tree : Tree K)
    (slots : List Nat) (layout : Realizes (storageView arena) (decode root) tree slots) :
    Nonempty (MergeResult arena arena slots root tree) :=
  ⟨⟨slots, layout, fun _ => Iff.rfl, ⟨rfl, rfl, rfl, fun _ _ => rfl⟩⟩⟩

end MergeResult

private theorem left_pair_disjoint {a b c : List Nat} (ab : List.Disjoint a b) (ac : List.Disjoint a c) :
    List.Disjoint a (b ++ c) :=
  fun {_} inA inBC => (List.mem_append.mp inBC).elim (ab inA) (ac inA)

private theorem right_pair_disjoint {a b c : List Nat} (ac : List.Disjoint a c) (bc : List.Disjoint b c) :
    List.Disjoint (a ++ b) c :=
  fun {_} inAB inC => (List.mem_append.mp inAB).elim (fun h => ac h inC) (fun h => bc h inC)

theorem generated_merge_spec {K : Type} [Inhabited K] (left right : Tree K)
    (arena : cp.TreeMultiSet K) (lc rc : UInt64) (ls rs : List Nat)
    (leftLayout : Realizes (storageView arena) (decode lc) left ls)
    (rightLayout : Realizes (storageView arena) (decode rc) right rs)
    (apart : List.Disjoint ls rs) (fits : arena.slots.size ≤ 2 ^ 63)
    (weight : left.weight + right.weight < 2 ^ 64)
    (fuel start : Nat) (enough : left.height + right.height < fuel) :
    ∃ root after,
      (cp.TreeMultiSet.merge_rec fuel arena lc rc).run start = some ((root, after), start + left.mergeTicks right) ∧
      Nonempty (MergeResult arena after (ls ++ rs) root (left.merge right)) := by
  induction left, right using Tree.mergeSteps.induct generalizing arena lc rc ls rs fuel start with
  | case1 right =>
    generalize leftEq : decode lc = lp at leftLayout
    cases leftLayout with
    | empty =>
      have endLeft := (decode_none lc).mp leftEq
      subst lc
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [Tree.mergeTicks, Tree.merge, List.nil_append]
        exact ⟨rc, arena, generated_merge_empty_left arena rc fuel start,
          MergeResult.unchanged arena rc right rs rightLayout⟩
  | case2 left nonempty =>
    generalize leftEq : decode lc = lp at leftLayout
    generalize rightEq : decode rc = rp at rightLayout
    cases rightLayout with
    | empty =>
      have endRight := (decode_none rc).mp rightEq
      subst rc
      cases leftLayout with
      | empty => exact (nonempty rfl).elim
      | node reads ll lr lf rf sep =>
        have present := (decode_some lc _ leftEq).1
        cases fuel with
        | zero => omega
        | succ fuel =>
          rw [Tree.mergeTicks.eq_2 _ (by intro h; cases h), Tree.merge.eq_2 _ (by intro h; cases h), List.append_nil]
          exact ⟨lc, arena, generated_merge_empty_right arena lc fuel start present,
            MergeResult.unchanged arena lc _ _ (leftEq.symm ▸ .node reads ll lr lf rf sep)⟩
  | case3 kl pl cl ll lr kr pr cr rl rr ihLeft ihRight =>
    generalize leftEq : decode lc = lp at leftLayout
    generalize rightEq : decode rc = rp at rightLayout
    cases leftLayout with
    | @node li _ _ _ _ _ lli lri lls lrs lRead llTree lrTree llFresh lrFresh lSep =>
      cases rightLayout with
      | @node ri _ _ _ _ _ rli rri rls rrs rRead rlTree rrTree rlFresh rrFresh rSep =>
        cases fuel with
        | zero => omega
        | succ fuel =>
          obtain ⟨leftPresent, _⟩ := decode_some lc li leftEq
          obtain ⟨rightPresent, _⟩ := decode_some rc ri rightEq
          obtain ⟨lNat, lInside, lView⟩ := modelCell_view arena lc li _ leftEq lRead fits
          obtain ⟨rNat, rInside, rView⟩ := modelCell_view arena rc ri _ rightEq rRead fits
          have lPosition : (Cpp.toSigned 64 lc.toNat).toNat = li := by
            rw [signed_model_index (by omega), lNat, Int.toNat_natCast]
          have rPosition : (Cpp.toSigned 64 rc.toNat).toNat = ri := by
            rw [signed_model_index (by omega), rNat, Int.toNat_natCast]
          let lrow := modelCell arena lc
          let rrow := modelCell arena rc
          have lPriority : lrow.priority = pl := congrArg StoredNode.priority lView
          have rPriority : rrow.priority = pr := congrArg StoredNode.priority rView
          have lKey : lrow.key = some kl := congrArg StoredNode.key lView
          have rKey : rrow.key = some kr := congrArg StoredNode.key rView
          have lCount : lrow.count.toNat = cl := congrArg StoredNode.count lView
          have rCount : rrow.count.toNat = cr := congrArg StoredNode.count rView
          have llEq : decode lrow.left = lli := congrArg StoredNode.left lView
          have lrEq : decode lrow.right = lri := congrArg StoredNode.right lView
          have rlEq : decode rrow.left = rli := congrArg StoredNode.left rView
          have rrEq : decode rrow.right = rri := congrArg StoredNode.right rView
          let leftTree := Tree.node kl pl cl ll lr
          let rightTree := Tree.node kr pr cr rl rr
          have leftReal : Realizes (storageView arena) (decode lc) leftTree (li :: (lls ++ lrs)) :=
            leftEq.symm ▸ .node lRead llTree lrTree llFresh lrFresh lSep
          have rightReal : Realizes (storageView arena) (decode rc) rightTree (ri :: (rls ++ rrs)) :=
            rightEq.symm ▸ .node rRead rlTree rrTree rlFresh rrFresh rSep
          simp only [Tree.height, Tree.weight] at enough weight
          by_cases higher : pr < pl
          · have subApart : List.Disjoint lrs (ri :: (rls ++ rrs)) :=
              fun {_} mem => apart (List.mem_cons_of_mem _ (List.mem_append_right _ mem))
            have llApart : List.Disjoint lls (ri :: (rls ++ rrs)) :=
              fun {_} mem => apart (List.mem_cons_of_mem _ (List.mem_append_left _ mem))
            have noWriteLeft : List.Disjoint lls (lrs ++ ri :: (rls ++ rrs)) :=
              left_pair_disjoint lSep llApart
            have fresh : li ∉ lrs ++ ri :: (rls ++ rrs) :=
              fun mem => (List.mem_append.mp mem).elim lrFresh (apart (List.mem_cons_self ..))
            obtain ⟨joined, middle, subRun, ⟨sub⟩⟩ :=
              ihLeft arena lrow.right rc lrs (ri :: (rls ++ rrs))
                (lrEq.symm ▸ lrTree) rightReal subApart fits (by simp [Tree.weight]; omega)
                fuel (start + 3) (by simp [Tree.height]; omega)
            have rootStable : modelCell middle lc = lrow :=
              sub.frame.rawCell lc (lPosition.symm ▸ fresh)
            have stableLeft := sub.frame.realizes llTree noWriteLeft
            let updatedRow : cp.TreeMultiSet_Slot K := {modelCell middle lc with right := joined}
            have jointFresh : li ∉ sub.slots := fun mem => fresh ((sub.covers _).mp mem)
            have jointApart : List.Disjoint lls sub.slots :=
              fun {_} leftMem jointMem => noWriteLeft leftMem ((sub.covers _).mp jointMem)
            have bound : updatedRow.count.toNat + ll.weight + (lr.merge rightTree).weight < 2 ^ 64 := by
              simp only [updatedRow, rootStable, lCount, Tree.merge_weight, rightTree, Tree.weight]
              omega
            obtain ⟨after, runUpdate, rootPreserved, freePreserved, sizePreserved, result, untouched⟩ :=
              generated_relink_spec middle lc li updatedRow kl ll (lr.merge rightTree) lls sub.slots
                leftEq (sub.frame.size.symm ▸ lInside) (sub.frame.size.symm ▸ fits)
                (by simp only [updatedRow, rootStable, lKey])
                (by simpa only [updatedRow, rootStable, llEq] using stableLeft)
                sub.treeLayout llFresh jointFresh jointApart bound (start + 3 + lr.mergeTicks rightTree)
            have rebuilt : Realizes (storageView after) (decode lc)
                (.node kl pl cl ll (lr.merge rightTree)) (li :: (lls ++ sub.slots)) := by
              simpa only [updatedRow, rootStable, lPriority, lCount] using result
            have finalFrame : ArenaFrame middle after [li] :=
              ⟨rootPreserved, freePreserved, sizePreserved, fun i other => untouched i (by simpa using other)⟩
            have frame : ArenaFrame arena after ((li :: (lls ++ lrs)) ++ ri :: (rls ++ rrs)) :=
              sub.frame.transOf finalFrame
                (fun {_} mem => (List.mem_append.mp mem).elim
                  (fun h => List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
                  (List.mem_append_right _))
                (by intro i mem; simp at mem; simp [mem])
            rw [Tree.merge, Tree.mergeTicks, ite_eq_left higher, ite_eq_left higher]
            have run := generated_merge_left arena middle after lc rc joined fuel start
              (start + 3 + lr.mergeTicks rightTree) (start + 3 + lr.mergeTicks rightTree + 5)
              leftPresent rightPresent (by change rrow.priority < lrow.priority; rwa [rPriority, lPriority]) subRun runUpdate
            have ticks : start + 3 + lr.mergeTicks rightTree + 5 = start + (8 + lr.mergeTicks rightTree) := by omega
            rw [ticks] at run
            refine ⟨lc, after, run, ⟨⟨_, rebuilt, ?_, frame⟩⟩⟩
            intro i
            have covers := sub.covers i
            simp only [List.mem_append, List.mem_cons] at covers ⊢
            rw [covers]
            simp only [or_assoc]
          · have subApart : List.Disjoint (li :: (lls ++ lrs)) rls :=
              fun {_} l r => apart l (List.mem_cons_of_mem _ (List.mem_append_left _ r))
            have rrApart : List.Disjoint (li :: (lls ++ lrs)) rrs :=
              fun {_} l r => apart l (List.mem_cons_of_mem _ (List.mem_append_right _ r))
            have noWriteRight : List.Disjoint ((li :: (lls ++ lrs)) ++ rls) rrs :=
              right_pair_disjoint rrApart rSep
            have fresh : ri ∉ (li :: (lls ++ lrs)) ++ rls :=
              fun mem => (List.mem_append.mp mem).elim (fun l => apart l (List.mem_cons_self ..)) rlFresh
            obtain ⟨joined, middle, subRun, ⟨sub⟩⟩ :=
              ihRight arena lc rrow.left (li :: (lls ++ lrs)) rls
                leftReal (rlEq.symm ▸ rlTree) subApart fits (by simp [Tree.weight]; omega)
                fuel (start + 3) (by simp [Tree.height]; omega)
            have rootStable : modelCell middle rc = rrow :=
              sub.frame.rawCell rc (rPosition.symm ▸ fresh)
            have stableRight := sub.frame.realizes rrTree (List.disjoint_comm.mp noWriteRight)
            let updatedRow : cp.TreeMultiSet_Slot K := {modelCell middle rc with left := joined}
            have jointFresh : ri ∉ sub.slots := fun mem => fresh ((sub.covers _).mp mem)
            have jointApart : List.Disjoint sub.slots rrs :=
              fun {_} jointMem rightMem => noWriteRight ((sub.covers _).mp jointMem) rightMem
            have bound : updatedRow.count.toNat + (leftTree.merge rl).weight + rr.weight < 2 ^ 64 := by
              simp only [updatedRow, rootStable, rCount, Tree.merge_weight, leftTree, Tree.weight]
              omega
            obtain ⟨after, runUpdate, rootPreserved, freePreserved, sizePreserved, result, untouched⟩ :=
              generated_relink_spec middle rc ri updatedRow kr (leftTree.merge rl) rr sub.slots rrs
                rightEq (sub.frame.size.symm ▸ rInside) (sub.frame.size.symm ▸ fits)
                (by simp only [updatedRow, rootStable, rKey])
                sub.treeLayout (by simpa only [updatedRow, rootStable, rrEq] using stableRight)
                jointFresh rrFresh jointApart bound (start + 3 + leftTree.mergeTicks rl)
            have rebuilt : Realizes (storageView after) (decode rc)
                (.node kr pr cr (leftTree.merge rl) rr) (ri :: (sub.slots ++ rrs)) := by
              simpa only [updatedRow, rootStable, rPriority, rCount] using result
            have finalFrame : ArenaFrame middle after [ri] :=
              ⟨rootPreserved, freePreserved, sizePreserved, fun i other => untouched i (by simpa using other)⟩
            have frame : ArenaFrame arena after ((li :: (lls ++ lrs)) ++ ri :: (rls ++ rrs)) :=
              sub.frame.transOf finalFrame
                (fun {_} mem => (List.mem_append.mp mem).elim (List.mem_append_left _)
                  (fun h => List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ h))))
                (by intro i mem; simp at mem; simp [mem])
            rw [Tree.merge, Tree.mergeTicks, ite_eq_right higher, ite_eq_right higher]
            have run := generated_merge_right arena middle after lc rc joined fuel start
              (start + 3 + leftTree.mergeTicks rl) (start + 3 + leftTree.mergeTicks rl + 5)
              leftPresent rightPresent (by change ¬ rrow.priority < lrow.priority; rwa [rPriority, lPriority]) subRun runUpdate
            have ticks : start + 3 + leftTree.mergeTicks rl + 5 = start + (8 + leftTree.mergeTicks rl) := by omega
            rw [ticks] at run
            refine ⟨rc, after, run, ⟨⟨_, rebuilt, ?_, frame⟩⟩⟩
            intro i
            rw [List.mem_cons, List.mem_append, sub.covers i]
            simp only [List.mem_append, List.mem_cons]
            simp only [or_assoc, or_left_comm]

end Proofs.Cpp.TreeMultiset
