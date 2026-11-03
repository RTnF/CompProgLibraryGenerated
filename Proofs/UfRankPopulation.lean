import Proofs.UfHistoricalRank

namespace Proofs.UfRankPopulation
open Proofs.UfHistoricalRank Proofs.UfClassInvariant Proofs.UfCompression
open Proofs.UfMergeInvariant Proofs.UfRootCall Proofs.UfFindCall

def Budget (size count threshold : Nat) : Prop :=
  (size < threshold → count = 0) ∧
  (threshold ≤ size → count * threshold + threshold ≤ 2 * size)

def mergedCount (a b ca cb threshold : Nat) : Nat :=
  ca+cb+(if a < threshold ∧ threshold ≤ a+b then 1 else 0)

theorem merge_budget (a b ca cb threshold : Nat) (smaller : b ≤ a)
    (left : Budget a ca threshold) (right : Budget b cb threshold) :
    Budget (a+b) (mergedCount a b ca cb threshold) threshold := by
  unfold mergedCount
  split_ifs with crossing
  · have caZero := left.1 crossing.1
    have cbZero := right.1 (show b < threshold by omega)
    simp only [caZero,cbZero,Nat.zero_add]
    constructor
    · intro small
      omega
    · intro large
      simp only [Nat.one_mul]
      omega
  · simp only [Nat.add_zero]
    constructor
    · intro small
      have caZero := left.1 (show a < threshold by omega)
      have cbZero := right.1 (show b < threshold by omega)
      omega
    · intro large
      have aLarge : threshold ≤ a := by omega
      have first := left.2 aLarge
      by_cases bSmall : b < threshold
      · have zero := right.1 bSmall
        simp only [zero,Nat.add_zero]
        omega
      · have second := right.2 (show threshold ≤ b by omega)
        rw [Nat.add_mul]
        omega

noncomputable def count (ps : List Int) (predicate : Nat → Bool) (root : Nat) : Nat :=
  ((members ps root).filter predicate).length

theorem count_linked_fixed (ps : List Int) (X Y : Nat) (size : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) (negative : size < 0) (predicate : Nat → Bool) :
    count (linked ps X Y size) predicate X = count ps predicate X + count ps predicate Y := by
  classical
  have length : (linked ps X Y size).length = ps.length := by simp [linked]
  have union : members (linked ps X Y size) X =
      (List.range ps.length).filter (fun i => decide (Reach ps i X) || decide (Reach ps i Y)) := by
    simp only [members,length]
    apply List.filter_congr
    intro i _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Bool.or_eq_true]
    simpa only [true_and] using reach_iff ps X Y size rx ry different negative i X
  have disjoint : ∀ i, (predicate i && decide (Reach ps i X)) = true →
      (predicate i && decide (Reach ps i Y)) = true → False := by
    intro i hx hy
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hx hy
    exact members_disjoint ps X Y rx ry different i hx.2 hy.2
  have both := filter_union_length (List.range ps.length)
    (fun i => predicate i && decide (Reach ps i X))
    (fun i => predicate i && decide (Reach ps i Y)) disjoint
  have distribute : (fun i => predicate i && (decide (Reach ps i X) || decide (Reach ps i Y))) =
      (fun i => (predicate i && decide (Reach ps i X)) || (predicate i && decide (Reach ps i Y))) := by
    funext i
    cases predicate i <;> simp
  unfold count
  rw [union]
  simp only [members,List.filter_filter]
  rw [distribute]
  exact both

theorem filter_add_one (l : List Nat) (nodup : l.Nodup) (X : Nat) (member : X ∈ l)
    (predicate : Nat → Bool) (absent : predicate X = false) :
    (l.filter (fun i => decide (i = X) || predicate i)).length = (l.filter predicate).length+1 := by
  induction l with
  | nil => simp at member
  | cons a l ih =>
    obtain ⟨notMember,tailDup⟩ := List.nodup_cons.mp nodup
    by_cases same : a = X
    · subst a
      have tail : l.filter (fun i => decide (i = X) || predicate i) = l.filter predicate := by
        apply List.filter_congr
        intro i inside
        have different : i ≠ X := by intro eq; subst i; exact notMember inside
        simp [different]
      simp [absent,tail]
    · have inside : X ∈ l := by simpa [Ne.symm same] using member
      have tail := ih tailDup inside
      cases selected : predicate a <;> simp [same,selected,tail]

theorem filter_promote (l : List Nat) (nodup : l.Nodup) (X : Nat) (member : X ∈ l)
    (rank : Nat → Nat) (level : Nat) (growth : rank X ≤ level) (k : Nat) :
    (l.filter (fun i => decide (k ≤ promote rank X level i))).length =
      (l.filter (fun i => decide (k ≤ rank i))).length + (if rank X < k ∧ k ≤ level then 1 else 0) := by
  by_cases crossing : rank X < k ∧ k ≤ level
  · have predicates : (fun i => decide (k ≤ promote rank X level i)) =
        (fun i => decide (i = X) || decide (k ≤ rank i)) := by
      funext i
      by_cases same : i = X
      · subst i; simp [promote,crossing.2]
      · simp [promote,same]
    rw [predicates,if_pos crossing]
    exact filter_add_one l nodup X member _ (by simp [show ¬ k ≤ rank X by omega])
  · have rootSame : (k ≤ level) ↔ k ≤ rank X := by omega
    simp only [if_neg crossing,Nat.add_zero]
    apply congrArg List.length
    apply List.filter_congr
    intro i _
    by_cases same : i = X
    · subst i; simp [promote,rootSame]
    · simp [promote,same]

noncomputable def highCount (ps : List Int) (rank : Nat → Nat) (k root : Nat) : Nat :=
  count ps (fun i => decide (k ≤ rank i)) root

def Population (ps : List Int) (rank : Nat → Nat) : Prop :=
  ∀ (r : Nat) (w : Int), ps[r]? = some w → w < 0 → ∀ k,
    Budget (members ps r).length (highCount ps rank k r) (2^k)

theorem population_initial (n : Nat) : Population (initial n) (fun _ => 0) := by
  intro r w found _negative k
  have inside : r < n := by simpa [initial] using (List.getElem?_eq_some_iff.mp found).1
  simp only [highCount,count,initial_members n r inside]
  cases k with
  | zero => simp [Budget]
  | succ k => simp [Budget]

theorem population_compressed {ps vec : List Int} {rank : Nat → Nat} {a r : Nat}
    (population : Population ps rank) (compressed : Compressed ps vec a r) : Population vec rank := by
  intro z w found negative k
  have old := (negative_entry compressed w negative).mp found
  have result := population z w old negative k
  simpa only [highCount,count,members_compressed compressed ⟨w,old,negative⟩] using result

theorem highCount_linked (ps : List Int) (rank : Nat → Nat) (X Y : Nat) (size : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) (negative : size < 0) (level : Nat) (growth : rank X ≤ level) (k : Nat) :
    highCount (linked ps X Y size) (promote rank X level) k X =
      highCount ps rank k X+highCount ps rank k Y+(if rank X < k ∧ k ≤ level then 1 else 0) := by
  classical
  have inside : X < ps.length := by
    obtain ⟨w,found,_⟩ := rx
    exact (List.getElem?_eq_some_iff.mp found).1
  have nodup : (members (linked ps X Y size) X).Nodup := by
    unfold members
    exact List.Pairwise.filter _ List.nodup_range
  have member : X ∈ members (linked ps X Y size) X := by
    simp [members,linked,inside,Reach.refl]
  have changed := filter_promote (members (linked ps X Y size) X) nodup X member rank level growth k
  change highCount (linked ps X Y size) (promote rank X level) k X =
    count (linked ps X Y size) (fun i => decide (k ≤ rank i)) X+_ at changed
  rw [count_linked_fixed ps X Y size rx ry different negative] at changed
  exact changed

theorem highCount_linked_other (ps : List Int) (rank : Nat → Nat) (X Y z : Nat) (size : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) (negative : size < 0) (other : z ≠ X) (level k : Nat) :
    highCount (linked ps X Y size) (promote rank X level) k z = highCount ps rank k z := by
  classical
  unfold highCount count
  rw [members_linked_other ps X Y z size rx ry different negative other]
  apply congrArg List.length
  apply List.filter_congr
  intro i member
  have reach : Reach ps i z := (List.mem_filter.mp member).2 |> of_decide_eq_true
  have notWinner : i ≠ X := by
    intro same
    subst i
    have eq := root_reach ps X rx z reach
    exact other (by omega)
  simp [promote,notWinner]

theorem population_linked (ps : List Int) (rank rho : Nat → Nat) (groups : Int)
    (valid : Valid ps groups rank) (history : History ps rho) (population : Population ps rho)
    (X Y : Nat) (vx vy : Int) (fx : ps[X]? = some vx) (fy : ps[Y]? = some vy)
    (nx : vx < 0) (ny : vy < 0) (different : X ≠ Y) (smaller : -vy ≤ -vx) :
    Population (linked ps X Y (vx+vy)) (promote rho X (Nat.log2 (-(vx+vy)).toNat)) := by
  classical
  have rx : ∃ w, ps[X]? = some w ∧ w < 0 := ⟨vx,fx,nx⟩
  have ry : ∃ w, ps[Y]? = some w ∧ w < 0 := ⟨vy,fy,ny⟩
  have negative : vx+vy < 0 := by omega
  have sizeX := valid.sizes X vx fx nx
  have sizeY := valid.sizes Y vy fy ny
  let a := (members ps X).length
  let b := (members ps Y).length
  have aPositive : 0 < a := by dsimp [a]; omega
  have bPositive : 0 < b := by dsimp [b]; omega
  have smallerNat : b ≤ a := by dsimp [a,b]; omega
  have total : (-(vx+vy)).toNat = a+b := by dsimp [a,b]; omega
  have oldRank : rho X = Nat.log2 a := by
    rw [history.2 X vx fx nx]
    congr 1
    dsimp [a]
    omega
  have growth := size_gives_growth ps rho history.2 X Y vx vy fx fy nx ny smaller
  intro z w found negativeZ k
  by_cases same : z = X
  · subst z
    have crossing : (rho X < k ∧ k ≤ Nat.log2 (-(vx+vy)).toNat) ↔
        (a < 2^k ∧ 2^k ≤ a+b) := by
      rw [oldRank,total,Nat.log2_lt (by omega : a ≠ 0),Nat.le_log2 (by omega : a+b ≠ 0)]
    have budget := merge_budget a b (highCount ps rho k X) (highCount ps rho k Y) (2^k)
      smallerNat (population X vx fx nx k) (population Y vy fy ny k)
    unfold mergedCount at budget
    rw [members_linked_x_length ps X Y (vx+vy) rx ry different negative,
      highCount_linked ps rho X Y (vx+vy) rx ry different negative _ growth.1 k]
    simpa only [crossing] using budget
  · obtain ⟨oldRoot,_notY⟩ := (negative_root_iff ps X Y (vx+vy) rx ry different negative z).mp
      ⟨w,found,negativeZ⟩
    obtain ⟨old,oldFound,oldNegative⟩ := oldRoot
    rw [members_linked_other ps X Y z (vx+vy) rx ry different negative same,
      highCount_linked_other ps rho X Y z (vx+vy) rx ry different negative same]
    exact population z old oldFound oldNegative k

open Proofs.UfUniteCall

theorem unite_population {ps : List Int} {rank rho : Nat → Nat} {groups : Int}
    (valid : Valid ps groups rank) (history : History ps rho) (population : Population ps rho)
    (r1 r2 : Nat) (root1 : ∃ w, ps[r1]? = some w ∧ w < 0)
    (root2 : ∃ w, ps[r2]? = some w ∧ w < 0) :
    ∃ nextRho, History (uniteVec ps r1 r2) nextRho ∧ Population (uniteVec ps r1 r2) nextRho := by
  by_cases same : r1 = r2
  · exact ⟨rho,by simpa [uniteVec,same] using history,by simpa [uniteVec,same] using population⟩
  · obtain ⟨v1,f1,n1⟩ := root1
    obtain ⟨v2,f2,n2⟩ := root2
    by_cases swap : 0-ps.getD r1 0 < 0-ps.getD r2 0
    · have smaller : -v1 ≤ -v2 := by
        have compare : -v1 < -v2 := by
          simpa only [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2,zero_sub] using swap
        omega
      have hist := merge_preserves ps rho history.1 history.2 r2 r1 v2 v1 f2 f1 n2 n1 (Ne.symm same) smaller
      have pop := population_linked ps rank rho groups valid history population r2 r1 v2 v1 f2 f1 n2 n1 (Ne.symm same) smaller
      refine ⟨promote rho r2 (Nat.log2 (-(v2+v1)).toNat),?_⟩
      simp only [uniteVec,if_neg same,uniteX,uniteY,if_pos swap]
      rw [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2]
      simpa only [History,linked,Int.add_comm] using And.intro hist pop
    · have smaller : -v2 ≤ -v1 := by
        have compare : ¬ (-v1 < -v2) := by
          simpa only [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2,zero_sub] using swap
        omega
      have hist := merge_preserves ps rho history.1 history.2 r1 r2 v1 v2 f1 f2 n1 n2 same smaller
      have pop := population_linked ps rank rho groups valid history population r1 r2 v1 v2 f1 f2 n1 n2 same smaller
      refine ⟨promote rho r1 (Nat.log2 (-(v1+v2)).toNat),?_⟩
      simp only [uniteVec,if_neg same,uniteX,uniteY,if_neg swap]
      rw [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2]
      exact ⟨hist,pop⟩

def HistoryWithPopulation (ps : List Int) (rank : Nat → Nat) : Prop :=
  History ps rank ∧ Population ps rank

theorem initial_population_history (n : Nat) : HistoryWithPopulation (initial n) (fun _ => 0) :=
  ⟨initial_history n,population_initial n⟩

theorem population_history_compressed {ps vec : List Int} {rank : Nat → Nat} {a r : Nat}
    (history : HistoryWithPopulation ps rank) (compressed : Compressed ps vec a r) :
    HistoryWithPopulation vec rank :=
  ⟨history_compressed history.1 compressed,population_compressed history.2 compressed⟩

theorem unite_population_history {ps : List Int} {rank rho : Nat → Nat} {groups : Int}
    (valid : Valid ps groups rank) (history : HistoryWithPopulation ps rho)
    (r1 r2 : Nat) (root1 : ∃ w, ps[r1]? = some w ∧ w < 0)
    (root2 : ∃ w, ps[r2]? = some w ∧ w < 0) :
    ∃ nextRho, HistoryWithPopulation (Proofs.UfUniteCall.uniteVec ps r1 r2) nextRho :=
  unite_population valid history.1 history.2 r1 r2 root1 root2

end Proofs.UfRankPopulation
