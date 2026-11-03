import Proofs.UfClassInvariant
import Proofs.UfUniteCall

namespace Proofs.UfMergeInvariant
open Proofs.DoublingNested Proofs.CppScalar Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression
open Proofs.UfClassInvariant

theorem filter_union_length (l : List Nat) (p q : Nat → Bool)
    (disjoint : ∀ i, p i = true → q i = true → False) :
    (l.filter (fun i => p i || q i)).length = (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a <;> cases hq : q a
    all_goals first
      | exact False.elim (disjoint a hp hq)
      | simp [hp,hq,ih,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem filter_disjoint_le (l : List Nat) (p q : Nat → Bool)
    (disjoint : ∀ i, p i = true → q i = true → False) :
    (l.filter p).length + (l.filter q).length ≤ l.length := by
  rw [← filter_union_length l p q disjoint]
  exact List.length_filter_le _ _

theorem members_disjoint (ps : List Int) (X Y : Nat)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0) (different : X ≠ Y) :
    ∀ i, Reach ps i X → Reach ps i Y → False := by
  intro i ix iy
  exact different (root_unique ix iy rx ry)

theorem members_sum_le (ps : List Int) (X Y : Nat)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0) (different : X ≠ Y) :
    (members ps X).length + (members ps Y).length ≤ ps.length := by
  classical
  have disjoint : ∀ i, decide (Reach ps i X) = true → decide (Reach ps i Y) = true → False := by
    simpa only [decide_eq_true_eq] using members_disjoint ps X Y rx ry different
  simpa [members] using filter_disjoint_le (List.range ps.length) _ _ disjoint

theorem _root_.Proofs.UfClassInvariant.Valid.sum_valid {ps : List Int} {groups : Int} {rank : Nat → Nat} (valid : Valid ps groups rank)
    (X Y : Nat) (vx vy : Int) (fx : ps[X]? = some vx) (fy : ps[Y]? = some vy)
    (nx : vx < 0) (ny : vy < 0) (different : X ≠ Y) :
    -(ps.length : Int) ≤ vx+vy ∧ vx+vy < 0 ∧ i32.valid (vx+vy) = true := by
  have bound := members_sum_le ps X Y ⟨vx,fx,nx⟩ ⟨vy,fy,ny⟩ different
  have sx := valid.sizes X vx fx nx
  have sy := valid.sizes Y vy fy ny
  have length := valid.length
  refine ⟨by omega,by omega,?_⟩
  exact Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)

theorem _root_.Proofs.UfClassInvariant.Valid.count_ge_two {ps : List Int} {groups : Int} {rank : Nat → Nat} (valid : Valid ps groups rank)
    (X Y : Nat) (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) : 2 ≤ groups := by
  classical
  have mx : X ∈ roots ps := by
    obtain ⟨w,found,negative⟩ := rx
    simp only [roots,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨(List.getElem?_eq_some_iff.mp found).1,w,found,negative⟩
  have my : Y ∈ roots ps := by
    obtain ⟨w,found,negative⟩ := ry
    simp only [roots,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨(List.getElem?_eq_some_iff.mp found).1,w,found,negative⟩
  have count := valid.count
  cases he : roots ps with
  | nil => rw [he] at mx; simp at mx
  | cons a rest =>
    rw [he] at mx my count
    cases rest with
    | nil => simp only [List.mem_singleton] at mx my; exact False.elim (different (mx.trans my.symm))
    | cons b rest => simp only [List.length_cons] at count; omega

theorem _root_.Proofs.UfClassInvariant.Valid.decrement_valid {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (X Y : Nat)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0) (different : X ≠ Y) :
    1 ≤ groups-1 ∧ i32.valid (groups-1) = true := by
  have lower := valid.count_ge_two X Y rx ry different
  have bounds := valid.count_range
  have length := valid.length
  exact ⟨by omega,Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)⟩

-- The two element writes of the original candidate, with no sentinel cell.
def linked (ps : List Int) (X Y : Nat) (sz : Int) : List Int := (ps.set X sz).set Y (X : Int)

theorem linked_x (ps : List Int) (X Y : Nat) (sz : Int) (inside : X < ps.length) (different : X ≠ Y) :
    (linked ps X Y sz)[X]? = some sz := by
  simp [linked,List.getElem?_set_ne (Ne.symm different),List.getElem?_set_self inside]

theorem linked_y (ps : List Int) (X Y : Nat) (sz : Int) (inside : Y < ps.length) :
    (linked ps X Y sz)[Y]? = some (X : Int) := by simp [linked,inside]

theorem linked_other (ps : List Int) (X Y i : Nat) (sz : Int) (hx : i ≠ X) (hy : i ≠ Y) :
    (linked ps X Y sz)[i]? = ps[i]? := by
  simp only [linked,List.getElem?_set_ne (Ne.symm hy),List.getElem?_set_ne (Ne.symm hx)]

theorem reach_forward (ps : List Int) (X Y : Nat) (sz : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    {i z : Nat} (reach : Reach ps i z) : Reach (linked ps X Y sz) i z := by
  induction reach with
  | refl => exact Reach.refl _
  | step i p z parent rest ih =>
    have hx : i ≠ X := by
      intro same; subst i
      obtain ⟨w,found,negative⟩ := rx
      have edge : ps[X]? = some (p : Int) := parent
      rw [found] at edge; have := Option.some.inj edge; omega
    have hy : i ≠ Y := by
      intro same; subst i
      obtain ⟨w,found,negative⟩ := ry
      have edge : ps[Y]? = some (p : Int) := parent
      rw [found] at edge; have := Option.some.inj edge; omega
    exact Reach.step i p z (by change (linked ps X Y sz)[i]? = some (p : Int); rw [linked_other ps X Y i sz hx hy]; exact parent) ih

theorem reach_iff (ps : List Int) (X Y : Nat) (sz : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) (negative : sz < 0) (i z : Nat) :
    Reach (linked ps X Y sz) i z ↔ Reach ps i z ∨ (z=X ∧ Reach ps i Y) := by
  obtain ⟨vx,fx,nx⟩ := rx
  obtain ⟨vy,fy,ny⟩ := ry
  have ix := (List.getElem?_eq_some_iff.mp fx).1
  have iy := (List.getElem?_eq_some_iff.mp fy).1
  have newX := linked_x ps X Y sz ix different
  have newY := linked_y ps X Y sz iy
  constructor
  · intro reach
    induction reach with
    | refl => exact Or.inl (Reach.refl _)
    | step i p z parent rest ih =>
      by_cases hy : i=Y
      · subst i
        have edge : (linked ps X Y sz)[Y]? = some (p : Int) := parent
        rw [newY] at edge
        have same : p=X := by have := Option.some.inj edge; omega
        subst p
        have target : z=X := root_reach (linked ps X Y sz) X ⟨sz,newX,negative⟩ z rest
        exact Or.inr ⟨target,Reach.refl Y⟩
      · by_cases hx : i=X
        · subst i
          have edge : (linked ps X Y sz)[X]? = some (p : Int) := parent
          rw [newX] at edge
          have := Option.some.inj edge
          omega
        · have edge : ps[i]? = some (p : Int) := by
            have edge : (linked ps X Y sz)[i]? = some (p : Int) := parent
            rw [linked_other ps X Y i sz hx hy] at edge
            exact edge
          rcases ih with old | ⟨same,old⟩
          · exact Or.inl (Reach.step i p z edge old)
          · exact Or.inr ⟨same,Reach.step i p Y edge old⟩
  · rintro (old | ⟨same,old⟩)
    · exact reach_forward ps X Y sz ⟨vx,fx,nx⟩ ⟨vy,fy,ny⟩ old
    · subst z
      exact reach_trans _ i Y X (reach_forward ps X Y sz ⟨vx,fx,nx⟩ ⟨vy,fy,ny⟩ old)
        (Reach.step Y X X newY (Reach.refl X))

theorem negative_root_iff (ps : List Int) (X Y : Nat) (sz : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) (negative : sz < 0) (i : Nat) :
    (∃ w, (linked ps X Y sz)[i]? = some w ∧ w < 0) ↔
      (∃ w, ps[i]? = some w ∧ w < 0) ∧ i ≠ Y := by
  obtain ⟨vx,fx,nx⟩ := rx
  obtain ⟨vy,fy,ny⟩ := ry
  have ix := (List.getElem?_eq_some_iff.mp fx).1
  have iy := (List.getElem?_eq_some_iff.mp fy).1
  by_cases hy : i=Y
  · subst i
    constructor
    · rintro ⟨w,found,neg⟩
      rw [linked_y ps X Y sz iy] at found
      have := Option.some.inj found
      omega
    · rintro ⟨_,no⟩
      exact False.elim (no rfl)
  · by_cases hx : i=X
    · subst i
      exact ⟨fun _ => ⟨⟨vx,fx,nx⟩,different⟩,fun _ => ⟨sz,linked_x ps X Y sz ix different,negative⟩⟩
    · rw [linked_other ps X Y i sz hx hy]
      exact ⟨fun h => ⟨h,hy⟩,And.left⟩

theorem roots_linked (ps : List Int) (X Y : Nat) (sz : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) (negative : sz < 0) :
    roots (linked ps X Y sz) = (roots ps).filter (· != Y) := by
  classical
  have length : (linked ps X Y sz).length = ps.length := by simp [linked]
  simp only [roots,length,List.filter_filter]
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,Bool.and_eq_true,bne_iff_ne]
  simpa only [and_comm] using negative_root_iff ps X Y sz rx ry different negative i

theorem filter_partition_length (l : List Nat) (p : Nat → Bool) :
    (l.filter p).length + (l.filter (fun i => Bool.not (p i))).length = l.length := by
  have disjoint : ∀ i, p i = true → Bool.not (p i) = true → False := by
    intro i yes no
    simp [yes] at no
  have union := filter_union_length l p (fun i => Bool.not (p i)) disjoint
  have all : l.filter (fun i => p i || Bool.not (p i)) = l := by
    apply List.filter_eq_self.mpr
    intro i _
    cases p i <;> rfl
  rw [all] at union
  exact union.symm

theorem roots_linked_length (ps : List Int) (X Y : Nat) (sz : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) (negative : sz < 0) :
    (roots (linked ps X Y sz)).length+1 = (roots ps).length := by
  classical
  have my : Y ∈ roots ps := by
    obtain ⟨w,found,neg⟩ := ry
    simp only [roots,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨(List.getElem?_eq_some_iff.mp found).1,w,found,neg⟩
  have partition := filter_partition_length (roots ps) (· == Y)
  rw [List.filter_beq,(roots_nodup ps).count_of_mem my] at partition
  rw [roots_linked ps X Y sz rx ry different negative]
  simpa [List.length_replicate,Nat.add_comm,bne] using partition

theorem members_linked_other (ps : List Int) (X Y z : Nat) (sz : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) (negative : sz < 0) (other : z ≠ X) :
    members (linked ps X Y sz) z = members ps z := by
  classical
  have length : (linked ps X Y sz).length = ps.length := by simp [linked]
  simp only [members,length]
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  simpa [other] using reach_iff ps X Y sz rx ry different negative i z

theorem members_linked_x_length (ps : List Int) (X Y : Nat) (sz : Int)
    (rx : ∃ w, ps[X]? = some w ∧ w < 0) (ry : ∃ w, ps[Y]? = some w ∧ w < 0)
    (different : X ≠ Y) (negative : sz < 0) :
    (members (linked ps X Y sz) X).length = (members ps X).length+(members ps Y).length := by
  classical
  have length : (linked ps X Y sz).length = ps.length := by simp [linked]
  have union : members (linked ps X Y sz) X =
      (List.range ps.length).filter (fun i => decide (Reach ps i X) || decide (Reach ps i Y)) := by
    simp only [members,length]
    apply List.filter_congr
    intro i _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Bool.or_eq_true]
    simpa only [true_and] using reach_iff ps X Y sz rx ry different negative i X
  rw [union]
  have disjoint : ∀ i, decide (Reach ps i X) = true → decide (Reach ps i Y) = true → False := by
    simpa only [decide_eq_true_eq] using members_disjoint ps X Y rx ry different
  simpa only [members] using filter_union_length (List.range ps.length) _ _ disjoint

theorem _root_.Proofs.UfClassInvariant.Valid.linked {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (X Y : Nat) (vx vy : Int)
    (fx : ps[X]? = some vx) (fy : ps[Y]? = some vy) (nx : vx < 0) (ny : vy < 0) (different : X ≠ Y) :
    ∃ rank', Valid (linked ps X Y (vx+vy)) (groups-1) rank' := by
  have rx : ∃ w, ps[X]? = some w ∧ w < 0 := ⟨vx,fx,nx⟩
  have ry : ∃ w, ps[Y]? = some w ∧ w < 0 := ⟨vy,fy,ny⟩
  have ix := (List.getElem?_eq_some_iff.mp fx).1
  have iy := (List.getElem?_eq_some_iff.mp fy).1
  have safe := valid.sum_valid X Y vx vy fx fy nx ny different
  obtain ⟨rank',forest⟩ := Proofs.UfUniteCall.link_forest ps rank valid.forest X Y (vx+vy) ix iy rx ry
    different safe.2.1 safe.2.2 valid.length
  refine ⟨rank',forest,by change ((ps.set X (vx+vy)).set Y (X : Int)).length < 2147483648; simpa using valid.length,?_,?_⟩
  · intro z w found negative
    by_cases same : z=X
    · subst z
      rw [linked_x ps X Y (vx+vy) ix different] at found
      have value := Option.some.inj found
      rw [← value,members_linked_x_length ps X Y (vx+vy) rx ry different safe.2.1]
      have sx := valid.sizes X vx fx nx
      have sy := valid.sizes Y vy fy ny
      omega
    · have root := (negative_root_iff ps X Y (vx+vy) rx ry different safe.2.1 z).mp ⟨w,found,negative⟩
      have old : ps[z]? = some w := by rw [linked_other ps X Y z (vx+vy) same root.2] at found; exact found
      rw [members_linked_other ps X Y z (vx+vy) rx ry different safe.2.1 same]
      exact valid.sizes z w old negative
  · have lengths := roots_linked_length ps X Y (vx+vy) rx ry different safe.2.1
    have count := valid.count
    omega

-- Reuse the existing two-write, no-sentinel union-by-size effect.
-- uniteVecC, which writes a counter sentinel, is deliberately not used here.
theorem _root_.Proofs.UfClassInvariant.Valid.unite_vec {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (r1 r2 : Nat)
    (root1 : ∃ w, ps[r1]? = some w ∧ w < 0) (root2 : ∃ w, ps[r2]? = some w ∧ w < 0) :
    ∃ rank', Valid (Proofs.UfUniteCall.uniteVec ps r1 r2) (if r1=r2 then groups else groups-1) rank' := by
  by_cases same : r1=r2
  · exact ⟨rank,by simpa [Proofs.UfUniteCall.uniteVec,same] using valid⟩
  · obtain ⟨vx,fx,nx⟩ := root1
    obtain ⟨vy,fy,ny⟩ := root2
    have dx := Proofs.UfUniteCall.getD_of ps r1 vx fx
    have dy := Proofs.UfUniteCall.getD_of ps r2 vy fy
    unfold Proofs.UfUniteCall.uniteVec Proofs.UfUniteCall.uniteX Proofs.UfUniteCall.uniteY
    rw [if_neg same,if_neg same,dx,dy]
    by_cases swap : 0-vx < 0-vy
    · rw [if_pos swap,if_pos swap]
      simpa [UfMergeInvariant.linked,Int.add_comm] using valid.linked r2 r1 vy vx fy fx ny nx (Ne.symm same)
    · rw [if_neg swap,if_neg swap]
      exact valid.linked r1 r2 vx vy fx fy nx ny same

theorem _root_.Proofs.UfClassInvariant.Valid.unite_compressed {ps one two : List Int} {groups : Int}
    {rank : Nat → Nat} (valid : Valid ps groups rank) (a b r1 r2 : Nat)
    (first : Compressed ps one a r1) (second : Compressed one two b r2) :
    ∃ rank', Valid (Proofs.UfUniteCall.uniteVec two r1 r2) (if r1=r2 then groups else groups-1) rank' := by
  obtain ⟨vx,fx,nx⟩ := first.root
  obtain ⟨vy,fy,ny⟩ := second.root
  have xmid := (negative_entry first vx nx).mpr fx
  have xfinal := (negative_entry second vx nx).mpr xmid
  have yfinal := (negative_entry second vy ny).mpr fy
  exact ((valid.compressed first).compressed second).unite_vec r1 r2 ⟨vx,xfinal,nx⟩ ⟨vy,yfinal,ny⟩

end Proofs.UfMergeInvariant
