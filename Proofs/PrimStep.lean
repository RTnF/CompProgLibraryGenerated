import Proofs.DijkstraOldExec
import Proofs.PrimRelax
import Proofs.PrimMath

namespace Proofs.PrimStep
open Proofs.BellmanFordMath (Edge)
open Proofs.DijkstraOldExec (doneOf doneOf_length doneOf_getD doneOf_push getD_oob)
open Proofs.DijkstraMath (Eall mem_Eall mem_Eall_inv)
open Proofs.PrimRelax (relaxL relaxL_length relaxL_getD foldl_length foldl_le foldl_done foldl_cases foldl_cover getD_set_same getD_set_ne)

/-- The picks of the first `j` visits are `D.take j`; visit `j` brought in `v` at cost `c`. -/
def StepOK (Ed : List Edge) (D : List Nat) (j v : Nat) (c : Int) : Prop :=
  (c = 0 ∧ ∀ e ∈ Ed, e.1 ∈ D.take j → e.2.1 ∈ D.take j) ∨
  (∃ y ∈ D.take j, (y, v, c) ∈ Ed ∧ ∀ e ∈ Ed, e.1 ∈ D.take j → e.2.1 ∉ D.take j → c ≤ e.2.2)

/-- The invariant of Prim's loop after `D.length` picks. -/
structure PInv (n : Nat) (inf : Int) (Ed : List Edge) (Dd : List Int) (Dn : List Nat) (D : List Nat) (cs : List Int) : Prop where
  len : cs.length = D.length
  nodup : D.Nodup
  lt : ∀ v ∈ D, v < n
  done : Dn = doneOf n D
  ddl : Dd.length = n
  bnd : ∀ j, j < n → 0 ≤ Dd.getD j 0 ∧ Dd.getD j 0 ≤ inf
  cl1 : ∀ e ∈ Ed, e.1 ∈ D → e.2.1 ∉ D → Dd.getD e.2.1 0 ≤ e.2.2
  cl2 : ∀ z, z < n → z ∉ D → Dd.getD z 0 = inf ∨ ∃ e ∈ Ed, e.1 ∈ D ∧ e.2.1 = z ∧ e.2.2 = Dd.getD z 0
  cl3 : ∀ j (h : j < D.length), Dd.getD D[j] 0 = cs.getD j 0
  steps : ∀ j (h : j < D.length), StepOK Ed D j D[j] (cs.getD j 0)

theorem PInv_init (n : Nat) (inf : Int) (Ed : List Edge) (Dd : List Int) (hl : Dd.length = n) (hall : ∀ j, j < n → Dd.getD j 0 = inf)
    (hinf : 0 ≤ inf) : PInv n inf Ed Dd (doneOf n []) [] [] := by
  refine ⟨rfl, List.nodup_nil, fun v hv => by simp at hv, rfl, hl, fun j hj => ?_, fun e _ h => by simp at h,
    fun z hz _ => Or.inl (hall z hz), fun j h => by simp at h, fun j h => by simp at h⟩
  rw [hall j hj]
  exact ⟨hinf, Int.le_refl _⟩

theorem doneOf_ne (n : Nat) (D : List Nat) (x : Nat) (hx : x < n) (h : x ∈ D) : (doneOf n D).getD x 0 ≠ 0 := by
  rw [doneOf_getD n D x hx, if_pos h]; omega

theorem doneOf_eq (n : Nat) (D : List Nat) (x : Nat) (hx : x < n) (h : x ∉ D) : (doneOf n D).getD x 0 = 0 := by
  rw [doneOf_getD n D x hx, if_neg h]

theorem PInv_step {n : Nat} {inf : Int} {Ed : List Edge} {Dd : List Int} {Dn : List Nat} {D : List Nat} {cs : List Int}
    (I : PInv n inf Ed Dd Dn D cs) (L : List Edge) (b : Nat) (bd' : Int)
    (hEd : ∀ e ∈ Ed, e.1 < n ∧ e.2.1 < n ∧ 0 ≤ e.2.2 ∧ e.2.2 < inf)
    (hL : ∀ e ∈ L, e ∈ Ed ∧ e.1 = b) (hLcov : ∀ e ∈ Ed, e.1 = b → e ∈ L)
    (hbn : b < n) (hb0 : b ∉ D) (hbd0 : 0 ≤ bd') (hbdI : bd' ≤ inf) (hinf0 : 0 ≤ inf)
    (hcase : (bd' < inf ∧ Dd.getD b 0 = bd' ∧ ∀ x, x < n → x ∉ D → bd' ≤ Dd.getD x 0) ∨
      (bd' = 0 ∧ ∀ x, x < n → x ∉ D → inf ≤ Dd.getD x 0)) :
    PInv n inf Ed (L.foldl (relaxL (doneOf n (D ++ [b]))) (Dd.set b bd')) (doneOf n (D ++ [b])) (D ++ [b]) (cs ++ [bd']) := by
  obtain ⟨hlen, hnd, hlt, hdone, hddl, hbnd, hcl1, hcl2, hcl3, hsteps⟩ := I
  have hD'nd : (D ++ [b]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
    intro x hx y hy
    simp at hy
    subst hy
    intro hxy; subst hxy; exact hb0 hx
  have hmemD' : ∀ x, x ∈ D ++ [b] ↔ x ∈ D ∨ x = b := by intro x; simp
  have hdn' : ∀ x, x < n → x ∈ D ++ [b] → (doneOf n (D ++ [b])).getD x 0 ≠ 0 := fun x hx h => doneOf_ne n _ x hx h
  have hdn0 : ∀ x, x < n → x ∉ D ++ [b] → (doneOf n (D ++ [b])).getD x 0 = 0 := fun x hx h => doneOf_eq n _ x hx h
  set D1 := Dd.set b bd' with hD1
  have hD1l : D1.length = n := by simp [hD1, hddl]
  have hD1get : ∀ x, x ≠ b → D1.getD x 0 = Dd.getD x 0 := fun x hx => getD_set_ne _ _ _ _ hx
  have hD1b : D1.getD b 0 = bd' := getD_set_same _ _ _ (by omega)
  have hD1bnd : ∀ j, j < n → 0 ≤ D1.getD j 0 ∧ D1.getD j 0 ≤ inf := by
    intro j hj
    by_cases hjb : j = b
    · subst hjb; rw [hD1b]; exact ⟨hbd0, hbdI⟩
    · rw [hD1get j hjb]; exact hbnd j hj
  set R := L.foldl (relaxL (doneOf n (D ++ [b]))) D1 with hR
  have hRl : R.length = n := by rw [hR, foldl_length, hD1l]
  have hRle : ∀ x, R.getD x 0 ≤ D1.getD x 0 := fun x => foldl_le _ L x D1
  have hRcases : ∀ x, x < n → R.getD x 0 = D1.getD x 0 ∨ ∃ e ∈ L, e.2.1 = x ∧ (doneOf n (D ++ [b])).getD x 0 = 0 ∧ R.getD x 0 = e.2.2 :=
    fun x hx => foldl_cases _ L x D1 (by omega)
  have hRdone : ∀ x, x < n → x ∈ D ++ [b] → R.getD x 0 = D1.getD x 0 := fun x hx h => foldl_done _ L x (hdn' x hx h) D1
  have hnewbnd : ∀ e ∈ L, 0 ≤ e.2.2 ∧ e.2.2 < inf := fun e he => by
    have := hEd e (hL e he).1
    exact ⟨this.2.2.1, this.2.2.2⟩
  refine ⟨?_, hD'nd, ?_, rfl, hRl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlen]
  · intro v hv
    rcases (hmemD' v).mp hv with h | h
    · exact hlt v h
    · subst h; exact hbn
  · -- bounds
    intro j hj
    refine ⟨?_, by have := hRle j; have := (hD1bnd j hj).2; omega⟩
    rcases hRcases j hj with h | ⟨e, he, _, _, h⟩
    · rw [h]; exact (hD1bnd j hj).1
    · rw [h]; exact (hnewbnd e he).1
  · -- clause 1
    intro e he h1 h2
    have hz := (hEd e he).2.1
    have hzb : e.2.1 ≠ b := fun h => h2 (by rw [h]; simp)
    have hzD : e.2.1 ∉ D := fun h => h2 (by simp [h])
    rcases (hmemD' e.1).mp h1 with hx | hx
    · have := hcl1 e he hx hzD
      have h3 := hRle e.2.1
      rw [hD1get _ hzb] at h3
      omega
    · have hmem : e ∈ L := hLcov e he hx
      exact foldl_cover _ L D1 e hmem (by omega) (hdn0 _ hz h2)
  · -- clause 2
    intro z hz hzn
    have hzD : z ∉ D := fun h => hzn (by simp [h])
    have hzb : z ≠ b := fun h => hzn (by simp [h])
    rcases hRcases z hz with h | ⟨e, he, h1, _, h3⟩
    · rw [h, hD1get z hzb]
      rcases hcl2 z hz hzD with h4 | ⟨e, he, h5, h6, h7⟩
      · exact Or.inl h4
      · exact Or.inr ⟨e, he, by simp [h5], h6, h7⟩
    · right
      refine ⟨e, (hL e he).1, by simp [(hL e he).2], h1, h3.symm⟩
  · -- clause 3
    intro j hj
    have hl1 : (D ++ [b]).length = D.length + 1 := by simp
    by_cases hjk : j < D.length
    · have hg1 : (D ++ [b])[j] = D[j] := List.getElem_append_left hjk
      have hg2 : (cs ++ [bd']).getD j 0 = cs.getD j 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < cs.length)]
      rw [hg1, hg2]
      have hmem : D[j] ∈ D := List.getElem_mem _
      have hne : D[j] ≠ b := fun h => hb0 (h ▸ hmem)
      rw [hRdone _ (hlt _ hmem) (List.mem_append_left _ hmem), hD1get _ hne]
      exact hcl3 j hjk
    · have hj0 : j = D.length := by omega
      have hg1 : (D ++ [b])[j] = b := by
        subst hj0; simp
      have hg2 : (cs ++ [bd']).getD j 0 = bd' := by
        subst hj0
        simp [List.getD_eq_getElem?_getD, hlen]
      rw [hg1, hg2, hRdone b hbn (by simp), hD1b]
  · -- steps
    intro j hj
    have hl1 : (D ++ [b]).length = D.length + 1 := by simp
    by_cases hjk : j < D.length
    · have hg1 : (D ++ [b])[j] = D[j] := List.getElem_append_left hjk
      have hg2 : (cs ++ [bd']).getD j 0 = cs.getD j 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < cs.length)]
      have htk : (D ++ [b]).take j = D.take j := List.take_append_of_le_length (by omega)
      rw [hg1, hg2]
      have h := hsteps j hjk
      unfold StepOK at h ⊢
      rw [htk]
      exact h
    · have hj0 : j = D.length := by omega
      subst hj0
      have hg1 : (D ++ [b])[D.length] = b := by simp
      have hg2 : (cs ++ [bd']).getD D.length 0 = bd' := by simp [List.getD_eq_getElem?_getD, hlen]
      have htk : (D ++ [b]).take D.length = D := List.take_left' rfl
      rw [hg1, hg2]
      unfold StepOK
      rw [htk]
      rcases hcase with ⟨hlt', hDb, hmin⟩ | ⟨h0, hall⟩
      · right
        rcases hcl2 b hbn hb0 with h | ⟨e, he, h1, h2, h3⟩
        · exfalso; rw [hDb] at h; omega
        · refine ⟨e.1, h1, ?_, ?_⟩
          · have : (e.1, b, bd') = e := by
              refine Prod.ext rfl (Prod.ext h2.symm ?_)
              show bd' = e.2.2
              rw [h3, hDb]
            rw [this]; exact he
          · intro e' he' h1' h2'
            have hz := (hEd e' he').2.1
            have := hmin e'.2.1 hz h2'
            have h4 := hcl1 e' he' h1' h2'
            omega
      · left
        refine ⟨h0, fun e he h1 => ?_⟩
        by_contra hnot
        have hz := (hEd e he).2.1
        have h4 := hcl1 e he h1 hnot
        have h5 := hall e.2.1 hz hnot
        have h6 := (hEd e he).2.2.2
        omega

/-! ### The potential: the number of arcs leaving the unvisited vertices -/

open Proofs.PrimMath (ssum ssum_add ssum_congr ssum_zero)

def degSum (n : Nat) (H : List Nat) (D : List Nat) : Nat :=
  ssum n (fun v => if v ∈ D then 0 else H.getD (v + 1) 0 - H.getD v 0)

theorem ssum_single (c b : Nat) : ∀ n, b < n → ssum n (fun v => if v = b then c else 0) = c := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    simp only [ssum]
    by_cases hb : b < n
    · rw [ih hb]
      have : n ≠ b := by omega
      simp [this]
    · have hbn : b = n := by omega
      subst hbn
      have : ssum b (fun v => if v = b then c else 0) = 0 := by
        have := ssum_congr b (fun v => if v = b then c else 0) (fun _ => 0) (by
          intro k hk
          have : k ≠ b := by omega
          simp [this])
        rw [this, ssum_zero]
      rw [this]
      simp

theorem degSum_push (n : Nat) (H D : List Nat) (b : Nat) (hb : b < n) (hbD : b ∉ D) :
    degSum n H (D ++ [b]) + (H.getD (b + 1) 0 - H.getD b 0) = degSum n H D := by
  unfold degSum
  have e : ∀ v, (if v ∈ D then 0 else H.getD (v + 1) 0 - H.getD v 0) =
      (if v ∈ D ++ [b] then 0 else H.getD (v + 1) 0 - H.getD v 0) +
      (if v = b then H.getD (b + 1) 0 - H.getD b 0 else 0) := by
    intro v
    by_cases hv : v = b
    · subst hv
      simp [hbD]
    · simp [hv]
  rw [ssum_congr n _ (fun v => (if v ∈ D ++ [b] then 0 else H.getD (v + 1) 0 - H.getD v 0) +
      (if v = b then H.getD (b + 1) 0 - H.getD b 0 else 0)) (fun k _ => e k), ssum_add, ssum_single _ _ n hb]

theorem ssum_telescope (H : List Nat) (n : Nat) (hmono : ∀ i, i < n → H.getD i 0 ≤ H.getD (i + 1) 0) :
    ∀ k, k ≤ n → H.getD 0 0 ≤ H.getD k 0 ∧ ssum k (fun v => H.getD (v + 1) 0 - H.getD v 0) = H.getD k 0 - H.getD 0 0 := by
  intro k
  induction k with
  | zero => intro _; simp [ssum]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have h3 := hmono k (by omega)
    simp only [ssum]
    rw [h2]
    omega

theorem degSum_init_le (n : Nat) (H T : List Nat) (HK : Proofs.TopoSortMath.HeadOK H T n) : degSum n H [] ≤ T.length := by
  unfold degSum
  have e : ssum n (fun v => if v ∈ ([] : List Nat) then 0 else H.getD (v + 1) 0 - H.getD v 0) =
      ssum n (fun v => H.getD (v + 1) 0 - H.getD v 0) := by
    apply ssum_congr
    intro k _
    simp
  rw [e, (ssum_telescope H n HK.mono n (Nat.le_refl _)).2, HK.zero, HK.last]
  omega

/-! ### Bounds on the picks and the sum -/

theorem perm_sum_int {l1 l2 : List Int} (h : l1.Perm l2) : l1.sum = l2.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem sum_le_len_mul (l : List Int) (Cm : Int) (h : ∀ x ∈ l, 0 ≤ x ∧ x ≤ Cm) : 0 ≤ l.sum ∧ l.sum ≤ (l.length : Int) * Cm := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.sum_cons, List.length_cons]
    refine ⟨by omega, ?_⟩
    have : ((l.length + 1 : Nat) : Int) * Cm = (l.length : Int) * Cm + Cm := by push_cast; ring
    rw [this]; omega

theorem pk_bounds {n : Nat} {inf : Int} {Ed : List Edge} {Dd : List Int} {Dn : List Nat} {D : List Nat} {pk : List Int}
    (I : PInv n inf Ed Dd Dn D pk) (Cm : Int) (hCm : 0 ≤ Cm) (hE : ∀ e ∈ Ed, 0 ≤ e.2.2 ∧ e.2.2 ≤ Cm) :
    ∀ x ∈ pk, 0 ≤ x ∧ x ≤ Cm := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hjD : j < D.length := by rw [← I.len]; exact hj
  have hget : pk.getD j 0 = pk[j] := by simp [List.getD_eq_getElem?_getD, hj]
  have hst := I.steps j hjD
  rw [hget] at hst
  rcases hst with ⟨h0, _⟩ | ⟨y, _, hmem, _⟩
  · rw [h0]; exact ⟨Int.le_refl _, hCm⟩
  · exact hE _ hmem

theorem D_perm_range {n : Nat} {D : List Nat} (hnd : D.Nodup) (hlt : ∀ v ∈ D, v < n) (hlen : D.length = n) :
    D.Perm (List.range n) := by
  rw [List.perm_ext_iff_of_nodup hnd List.nodup_range]
  intro a
  constructor
  · intro ha; exact List.mem_range.mpr (hlt a ha)
  · intro ha
    refine Classical.byContradiction fun hna => ?_
    have hnd' : (a :: D).Nodup := List.nodup_cons.mpr ⟨hna, hnd⟩
    have hsub : (a :: D) ⊆ List.range n := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact List.mem_range.mpr (hlt x hx)
    have := List.Nodup.length_le_of_subset hnd' hsub
    simp at this
    omega

end Proofs.PrimStep
