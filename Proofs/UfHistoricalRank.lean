import Proofs.UfRankDoubling

namespace Proofs.UfHistoricalRank
open Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression

-- Separate from the existing descending termination rank. A historical rank
-- grows toward parents and stays attached to a node after it ceases to be root.
def ParentRanks (ps : List Int) (rank : Nat → Nat) : Prop :=
  ∀ (i p : Nat), ps[i]? = some (p : Int) → rank i < rank p

theorem reach_mono {ps : List Int} {rank : Nat → Nat}
    (ranks : ParentRanks ps rank) {a r : Nat} (reach : Reach ps a r) :
    rank a ≤ rank r := by
  induction reach with
  | refl a => exact Nat.le_refl _
  | step a p r edge rest ih => exact Nat.le_trans (Nat.le_of_lt (ranks a p edge)) ih

theorem reach_strict {ps : List Int} {rank : Nat → Nat}
    (ranks : ParentRanks ps rank) {a r : Nat} (reach : Reach ps a r)
    (different : a ≠ r) : rank a < rank r := by
  cases reach with
  | refl a => exact False.elim (different rfl)
  | step a p r edge rest => exact Nat.lt_of_lt_of_le (ranks a p edge) (reach_mono ranks rest)

theorem compression_preserves {ps vec : List Int} {rank : Nat → Nat} {a r : Nat}
    (ranks : ParentRanks ps rank) (compressed : Compressed ps vec a r) :
    ParentRanks vec rank := by
  intro i p edge
  by_cases path : PathSet ps a r i
  · have same : p = r := by
      rw [(compressed.entries i).1 path] at edge
      have eq := Option.some.inj edge
      omega
    subst p
    exact reach_strict ranks (path_reaches_root compressed path) path.2
  · rw [(compressed.entries i).2 path] at edge
    exact ranks i p edge

-- Merging roots changes only the winning root's historical rank. The bound
-- on level will later come from the actual merged component size.
def promote (rank : Nat → Nat) (winner level : Nat) : Nat → Nat :=
  fun i => if i = winner then level else rank i

theorem linking_preserves (ps : List Int) (rank : Nat → Nat)
    (ranks : ParentRanks ps rank) (winner loser : Nat) (size : Int)
    (winnerInside : winner < ps.length) (loserInside : loser < ps.length)
    (different : winner ≠ loser) (negative : size < 0)
    (level : Nat) (winnerGrowth : rank winner ≤ level) (loserGrowth : rank loser < level) :
    ParentRanks (Proofs.UfMergeInvariant.linked ps winner loser size) (promote rank winner level) := by
  intro i p edge
  unfold Proofs.UfMergeInvariant.linked at edge
  by_cases isLoser : i = loser
  · subst i
    rw [List.getElem?_set_self (by simpa using loserInside)] at edge
    have same : p = winner := by
      have eq := Option.some.inj edge
      omega
    subst p
    simpa [promote,Ne.symm different] using loserGrowth
  · rw [List.getElem?_set_ne (Ne.symm isLoser)] at edge
    by_cases isWinner : i = winner
    · subst i
      rw [List.getElem?_set_self winnerInside] at edge
      have eq := Option.some.inj edge
      omega
    · rw [List.getElem?_set_ne (Ne.symm isWinner)] at edge
      have old := ranks i p edge
      by_cases parentWinner : p = winner
      · subst p
        simpa [promote,isWinner] using Nat.lt_of_lt_of_le old winnerGrowth
      · simpa [promote,isWinner,parentWinner] using old

-- Union by size strictly raises the winner above the loser's old level.
theorem merge_levels (a b : Nat) (positive : 0 < b) (smaller : b ≤ a) :
    Nat.log2 a ≤ Nat.log2 (a+b) ∧ Nat.log2 b < Nat.log2 (a+b) := by
  have totalPositive : a+b ≠ 0 := by omega
  have powerA := (Nat.le_log2 (by omega : a ≠ 0)).mp (Nat.le_refl (Nat.log2 a))
  have powerB := (Nat.le_log2 (by omega : b ≠ 0)).mp (Nat.le_refl (Nat.log2 b))
  have first : Nat.log2 a ≤ Nat.log2 (a+b) :=
    (Nat.le_log2 totalPositive).mpr (by omega)
  have second : Nat.log2 b+1 ≤ Nat.log2 (a+b) := by
    apply (Nat.le_log2 totalPositive).mpr
    rw [pow_succ]
    omega
  exact ⟨first,by omega⟩

def RootRanks (ps : List Int) (rank : Nat → Nat) : Prop :=
  ∀ (r : Nat) (w : Int), ps[r]? = some w → w < 0 →
    rank r = Nat.log2 (-w).toNat

theorem size_gives_growth (ps : List Int) (rank : Nat → Nat)
    (roots : RootRanks ps rank) (winner loser : Nat) (vx vy : Int)
    (fx : ps[winner]? = some vx) (fy : ps[loser]? = some vy)
    (nx : vx < 0) (ny : vy < 0) (smaller : -vy ≤ -vx) :
    rank winner ≤ Nat.log2 (-(vx+vy)).toNat ∧
      rank loser < Nat.log2 (-(vx+vy)).toNat := by
  have xRank := roots winner vx fx nx
  have yRank := roots loser vy fy ny
  have total : (-(vx+vy)).toNat = (-vx).toNat+(-vy).toNat := by omega
  rw [xRank,yRank,total]
  exact merge_levels _ _ (by omega) (by omega)

theorem root_ranks_compressed {ps vec : List Int} {rank : Nat → Nat} {a r : Nat}
    (roots : RootRanks ps rank) (compressed : Compressed ps vec a r) :
    RootRanks vec rank := by
  intro z w found negative
  exact roots z w ((negative_entry compressed w negative).mp found) negative

theorem root_ranks_linked (ps : List Int) (rank : Nat → Nat)
    (roots : RootRanks ps rank) (winner loser : Nat) (size : Int)
    (winnerInside : winner < ps.length) (loserInside : loser < ps.length) :
    RootRanks (Proofs.UfMergeInvariant.linked ps winner loser size)
      (promote rank winner (Nat.log2 (-size).toNat)) := by
  intro z w found negative
  unfold Proofs.UfMergeInvariant.linked at found
  by_cases isLoser : z = loser
  · subst z
    rw [List.getElem?_set_self (by simpa using loserInside)] at found
    have eq := Option.some.inj found
    omega
  · rw [List.getElem?_set_ne (Ne.symm isLoser)] at found
    by_cases isWinner : z = winner
    · subst z
      rw [List.getElem?_set_self winnerInside] at found
      have eq := Option.some.inj found
      subst w
      simp [promote]
    · rw [List.getElem?_set_ne (Ne.symm isWinner)] at found
      simpa [promote,isWinner] using roots z w found negative

theorem merge_preserves (ps : List Int) (rank : Nat → Nat)
    (parents : ParentRanks ps rank) (roots : RootRanks ps rank)
    (winner loser : Nat) (vx vy : Int)
    (fx : ps[winner]? = some vx) (fy : ps[loser]? = some vy)
    (nx : vx < 0) (ny : vy < 0) (different : winner ≠ loser)
    (smaller : -vy ≤ -vx) :
    ParentRanks (Proofs.UfMergeInvariant.linked ps winner loser (vx+vy))
      (promote rank winner (Nat.log2 (-(vx+vy)).toNat)) ∧
    RootRanks (Proofs.UfMergeInvariant.linked ps winner loser (vx+vy))
      (promote rank winner (Nat.log2 (-(vx+vy)).toNat)) := by
  have winnerInside := (List.getElem?_eq_some_iff.mp fx).1
  have loserInside := (List.getElem?_eq_some_iff.mp fy).1
  have growth := size_gives_growth ps rank roots winner loser vx vy fx fy nx ny smaller
  exact ⟨linking_preserves ps rank parents winner loser (vx+vy)
      winnerInside loserInside different (by omega) _ growth.1 growth.2,
    root_ranks_linked ps rank roots winner loser (vx+vy) winnerInside loserInside⟩

open Proofs.UfUniteCall Proofs.UfClassInvariant

def History (ps : List Int) (rank : Nat → Nat) : Prop :=
  ParentRanks ps rank ∧ RootRanks ps rank

theorem history_compressed {ps vec : List Int} {rank : Nat → Nat} {a r : Nat}
    (history : History ps rank) (compressed : Compressed ps vec a r) :
    History vec rank :=
  ⟨compression_preserves history.1 compressed,root_ranks_compressed history.2 compressed⟩

theorem unite_history {ps : List Int} {rank : Nat → Nat}
    (history : History ps rank) (r1 r2 : Nat)
    (root1 : ∃ w, ps[r1]? = some w ∧ w < 0)
    (root2 : ∃ w, ps[r2]? = some w ∧ w < 0) :
    ∃ nextRank, History (uniteVec ps r1 r2) nextRank := by
  by_cases same : r1 = r2
  · exact ⟨rank,by simpa [uniteVec,same] using history⟩
  · obtain ⟨v1,f1,n1⟩ := root1
    obtain ⟨v2,f2,n2⟩ := root2
    by_cases swap : 0-ps.getD r1 0 < 0-ps.getD r2 0
    · have smaller : -v1 ≤ -v2 := by
        have compare : -v1 < -v2 := by
          simpa only [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2,zero_sub] using swap
        omega
      have both := merge_preserves ps rank history.1 history.2 r2 r1 v2 v1 f2 f1 n2 n1 (Ne.symm same) smaller
      refine ⟨promote rank r2 (Nat.log2 (-(v2+v1)).toNat),?_⟩
      simp only [uniteVec,if_neg same,uniteX,uniteY,if_pos swap]
      rw [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2]
      simpa only [History,Proofs.UfMergeInvariant.linked,Int.add_comm] using both
    · have smaller : -v2 ≤ -v1 := by
        have compare : ¬ (-v1 < -v2) := by
          simpa only [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2,zero_sub] using swap
        omega
      have both := merge_preserves ps rank history.1 history.2 r1 r2 v1 v2 f1 f2 n1 n2 same smaller
      refine ⟨promote rank r1 (Nat.log2 (-(v1+v2)).toNat),?_⟩
      simp only [uniteVec,if_neg same,uniteX,uniteY,if_neg swap]
      rw [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2]
      exact both

theorem initial_history (n : Nat) : History (initial n) (fun _ => 0) := by
  constructor
  · intro i p found
    have eq : (p : Int) = -1 := (List.mem_replicate.mp (List.mem_of_getElem? found)).2
    omega
  · intro r w found negative
    have eq : w = -1 := (List.mem_replicate.mp (List.mem_of_getElem? found)).2
    subst w
    rfl

theorem historical_rank_bound {ps : List Int} {groups : Int} {rank rho : Nat → Nat}
    (valid : Valid ps groups rank) (history : History ps rho)
    (i : Nat) (inside : i < ps.length) : rho i ≤ Nat.log2 ps.length := by
  classical
  obtain ⟨out,r,run,ret,reach,rootInside,root,rest⟩ :=
    Proofs.UfFindCall.body_exec_find [] ps rank valid.forest valid.length i inside (rank i+2) (by omega)
  obtain ⟨w,found,negative⟩ := root
  have monotone := reach_mono history.1 reach
  rw [history.2 r w found negative] at monotone
  have size := valid.sizes r w found negative
  have membersBound : (members ps r).length ≤ ps.length := by
    simpa only [members,List.length_range] using
      List.length_filter_le (fun j => decide (Reach ps j r)) (List.range ps.length)
  have positive : (-w).toNat ≠ 0 := by omega
  have power := (Nat.le_log2 positive).mp monotone
  exact (Nat.le_log2 (by omega : ps.length ≠ 0)).mpr (by omega)

end Proofs.UfHistoricalRank
