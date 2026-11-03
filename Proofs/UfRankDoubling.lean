import Proofs.UfMergeInvariant

namespace Proofs.UfRankDoubling
open Proofs.DoublingNested Proofs.UfUniteCall
open Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression Proofs.UfClassInvariant Proofs.UfMergeInvariant

structure Balanced (ps : List Int) (rank : Nat → Nat) : Prop where
  rootZero : ∀ r w, ps[r]? = some w → w < 0 → rank r = 0
  doubling : ∀ i r, i < ps.length → Reach ps i r →
    (∃ w, ps[r]? = some w ∧ w < 0) → 2 ^ rank i ≤ (members ps r).length

theorem initial_balanced (n : Nat) : Balanced (initial n) (fun _ => 0) := by
  classical
  refine ⟨fun _ _ _ _ => rfl,?_⟩
  intro i r inside reach root
  have member : i ∈ members (initial n) r := by simp [members,inside,reach]
  have positive := List.length_pos_of_mem member
  simp only [pow_zero]
  omega

theorem Balanced.compressed {ps vec : List Int} {rank : Nat → Nat} {a r : Nat}
    (balanced : Balanced ps rank) (compressed : Compressed ps vec a r) : Balanced vec rank := by
  refine ⟨?_,?_⟩
  · intro z w found negative
    exact balanced.rootZero z w ((negative_entry compressed w negative).mp found) negative
  · intro i z inside reach root
    obtain ⟨w,found,negative⟩ := root
    have oldRoot : ∃ w, ps[z]? = some w ∧ w < 0 := ⟨w,(negative_entry compressed w negative).mp found,negative⟩
    rw [members_compressed compressed oldRoot]
    exact balanced.doubling i z (by rw [compressed.length] at inside; exact inside)
      (reach_backward compressed reach) oldRoot

noncomputable def shift (ps : List Int) (rank : Nat → Nat) (X Y : Nat) : Nat → Nat :=
  by
    classical
    exact fun i => if Reach ps i Y then rank i + rank X + 1 else rank i

theorem Balanced.linked {ps : List Int} {rank : Nat → Nat} (balanced : Balanced ps rank)
    (X Y : Nat) (vx vy : Int) (fx : ps[X]? = some vx) (fy : ps[Y]? = some vy)
    (nx : vx < 0) (ny : vy < 0) (different : X ≠ Y) (negative : vx+vy < 0)
    (smaller : (members ps Y).length ≤ (members ps X).length) :
    Balanced (linked ps X Y (vx+vy)) (shift ps rank X Y) := by
  classical
  have rx : ∃ w, ps[X]? = some w ∧ w < 0 := ⟨vx,fx,nx⟩
  have ry : ∃ w, ps[Y]? = some w ∧ w < 0 := ⟨vy,fy,ny⟩
  have zero : rank X = 0 := balanced.rootZero X vx fx nx
  refine ⟨?_,?_⟩
  · intro z w found neg
    obtain ⟨oldRoot,notY⟩ := (negative_root_iff ps X Y (vx+vy) rx ry different negative z).mp ⟨w,found,neg⟩
    have noReach : ¬ Reach ps z Y := by
      intro reach
      exact notY (root_reach ps z oldRoot Y reach).symm
    obtain ⟨old,foundOld,negativeOld⟩ := oldRoot
    simpa [shift,noReach] using balanced.rootZero z old foundOld negativeOld
  · intro i z inside reach newRoot
    have oldInside : i < ps.length := by simpa only [Proofs.UfMergeInvariant.linked,List.length_set] using inside
    obtain ⟨oldRoot,notY⟩ := (negative_root_iff ps X Y (vx+vy) rx ry different negative z).mp newRoot
    have reaches := (reach_iff ps X Y (vx+vy) rx ry different negative i z).mp reach
    by_cases smallTree : Reach ps i Y
    · have same : z = X := by
        rcases reaches with old | ⟨same,_⟩
        · exact False.elim (notY (root_unique old smallTree oldRoot ry))
        · exact same
      subst z
      have bound := balanced.doubling i Y oldInside smallTree ry
      rw [members_linked_x_length ps X Y (vx+vy) rx ry different negative]
      simp only [shift,if_pos smallTree,zero,Nat.add_zero,pow_succ]
      omega
    · have oldReach : Reach ps i z := by
        rcases reaches with old | ⟨_,impossible⟩
        · exact old
        · exact False.elim (smallTree impossible)
      have bound := balanced.doubling i z oldInside oldReach oldRoot
      simp only [shift,if_neg smallTree]
      by_cases isX : z = X
      · subst z
        rw [members_linked_x_length ps X Y (vx+vy) rx ry different negative]
        omega
      · rw [members_linked_other ps X Y z (vx+vy) rx ry different negative isX]
        exact bound

theorem forest_shift (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank) (X Y : Nat) (sz : Int)
    (hXl : X < ps.length) (hYl : Y < ps.length) (hX : ∃ v, ps[X]? = some v ∧ v < 0)
    (hY : ∃ v, ps[Y]? = some v ∧ v < 0) (hne : X ≠ Y) (hsz : sz < 0) (hszv : i32.valid sz = true)
    (hn : ps.length < 2147483648) :
    Forest ((ps.set X sz).set Y (X : Int)) (shift ps rank X Y) := by
  classical
  unfold shift
  have hXv : i32.valid (X : Int) = true := Proofs.VectorSumCall.i32_valid X (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with h | h
    · rcases List.mem_or_eq_of_mem_set h with h' | h'
      · exact hF.valid x h'
      · rw [h']; exact hszv
    · rw [h]; exact hXv
  · intro i p hi h0
    by_cases hiY : i = Y
    · subst hiY
      rw [List.getElem?_set_self (by simp; omega)] at hi
      have := Option.some.inj hi; subst this
      simp; omega
    · rw [List.getElem?_set_ne (Ne.symm hiY)] at hi
      by_cases hiX : i = X
      · subst hiX
        rw [List.getElem?_set_self hXl] at hi
        have := Option.some.inj hi; subst this
        omega
      · rw [List.getElem?_set_ne (Ne.symm hiX)] at hi
        have := hF.inside i p hi h0
        simpa using this
  · intro i p hi h0
    by_cases hiY : i = Y
    · subst hiY
      rw [List.getElem?_set_self (by simp; omega)] at hi
      have := Option.some.inj hi; subst this
      have hXY : ¬ Reach ps X i := by
        intro h
        obtain ⟨w, hw, hneg⟩ := hX
        exact hne (root_reach ps X ⟨w, hw, hneg⟩ i h).symm
      simp only [Int.toNat_natCast, if_pos (Reach.refl i), if_neg hXY]
      omega
    · rw [List.getElem?_set_ne (Ne.symm hiY)] at hi
      by_cases hiX : i = X
      · subst hiX
        rw [List.getElem?_set_self hXl] at hi
        have := Option.some.inj hi; subst this
        omega
      · rw [List.getElem?_set_ne (Ne.symm hiX)] at hi
        have hd := hF.decrease i p hi h0
        have hpar : ps[i]? = some ((p.toNat : Nat) : Int) := by rw [Int.toNat_of_nonneg h0]; exact hi
        by_cases hr : Reach ps i Y
        · have hp : Reach ps p.toNat Y := by
            cases hr with
            | refl => exact absurd rfl hiY
            | step _ b' _ hp' hr' =>
              have e : ps[i]? = some (b' : Int) := hp'
              rw [hpar] at e
              have := Option.some.inj e
              have : p.toNat = b' := by omega
              rw [this]; exact hr'
          rw [if_pos hr, if_pos hp]; omega
        · have hp : ¬ Reach ps p.toNat Y := by
            intro h
            exact hr (Reach.step i p.toNat Y hpar h)
          rw [if_neg hr, if_neg hp]; exact hd


theorem valid_linked {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (balanced : Balanced ps rank)
    (X Y : Nat) (vx vy : Int) (fx : ps[X]? = some vx) (fy : ps[Y]? = some vy)
    (nx : vx < 0) (ny : vy < 0) (different : X ≠ Y)
    (smaller : (members ps Y).length ≤ (members ps X).length) :
    Valid (linked ps X Y (vx+vy)) (groups-1) (shift ps rank X Y) ∧
      Balanced (linked ps X Y (vx+vy)) (shift ps rank X Y) := by
  have safe := valid.sum_valid X Y vx vy fx fy nx ny different
  have forest := forest_shift ps rank valid.forest X Y (vx+vy)
    (List.getElem?_eq_some_iff.mp fx).1 (List.getElem?_eq_some_iff.mp fy).1
    ⟨vx,fx,nx⟩ ⟨vy,fy,ny⟩ different safe.2.1 safe.2.2 valid.length
  obtain ⟨otherRank,math⟩ := valid.linked X Y vx vy fx fy nx ny different
  exact ⟨⟨forest,math.length,math.sizes,math.count⟩,
    balanced.linked X Y vx vy fx fy nx ny different safe.2.1 smaller⟩

theorem unite_balanced {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (balanced : Balanced ps rank) (r1 r2 : Nat)
    (root1 : ∃ w, ps[r1]? = some w ∧ w < 0) (root2 : ∃ w, ps[r2]? = some w ∧ w < 0) :
    ∃ nextRank, Valid (uniteVec ps r1 r2) (if r1=r2 then groups else groups-1) nextRank ∧
      Balanced (uniteVec ps r1 r2) nextRank := by
  by_cases same : r1=r2
  · exact ⟨rank,by simpa [uniteVec,same] using valid,by simpa [uniteVec,same] using balanced⟩
  · obtain ⟨v1,f1,n1⟩ := root1
    obtain ⟨v2,f2,n2⟩ := root2
    have size1 := valid.sizes r1 v1 f1 n1
    have size2 := valid.sizes r2 v2 f2 n2
    by_cases swap : 0-ps.getD r1 0 < 0-ps.getD r2 0
    · have smaller : (members ps r1).length ≤ (members ps r2).length := by
        have compare : -v1 < -v2 := by simpa only [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2,zero_sub] using swap
        omega
      have both := valid_linked valid balanced r2 r1 v2 v1 f2 f1 n2 n1 (Ne.symm same) smaller
      refine ⟨shift ps rank r2 r1,?_⟩
      simp only [uniteVec,if_neg same,uniteX,uniteY,if_pos swap]
      rw [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2]
      simpa only [Proofs.UfMergeInvariant.linked,Int.add_comm] using both
    · have smaller : (members ps r2).length ≤ (members ps r1).length := by
        have compare : ¬ (-v1 < -v2) := by simpa only [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2,zero_sub] using swap
        omega
      have both := valid_linked valid balanced r1 r2 v1 v2 f1 f2 n1 n2 same smaller
      refine ⟨shift ps rank r1 r2,?_⟩
      simp only [uniteVec,if_neg same,uniteX,uniteY,if_neg swap]
      rw [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2]
      exact both

theorem rank_bound {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (balanced : Balanced ps rank) (i : Nat) (inside : i < ps.length) :
    rank i ≤ Nat.log2 ps.length := by
  classical
  obtain ⟨out,r,run,ret,reach,rootInside,root,rest⟩ :=
    Proofs.UfFindCall.body_exec_find [] ps rank valid.forest valid.length i inside (rank i+2) (by omega)
  have power := balanced.doubling i r inside reach root
  have membersBound : (members ps r).length ≤ ps.length := by
    simpa only [members,List.length_range] using List.length_filter_le (fun j => decide (Reach ps j r)) (List.range ps.length)
  exact (Nat.le_log2 (by omega : ps.length ≠ 0)).mpr (by omega)

end Proofs.UfRankDoubling
