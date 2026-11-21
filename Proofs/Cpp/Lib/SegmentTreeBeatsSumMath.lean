import Proofs.Cpp.Lib.SegmentTreeBeatsMath

namespace Proofs.Cpp.SegmentTreeBeatsMath

/-! ## Sums of the leaf values (segment_tree_beats_sum) -/

theorem sum_map_count (L : List Int) (f : Int → Int) (m d : Int) (hf : ∀ v ∈ L, f v = v + (if v = m then d else 0)) :
    (L.map f).sum = L.sum + (L.count m : Int) * d := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons]
    rw [hf a List.mem_cons_self, ih (fun v hv => hf v (List.mem_cons_of_mem _ hv))]
    by_cases ha : a = m
    · subst ha; simp; ring
    · simp [ha, beq_iff_eq]; ring

theorem le_smax_of_ne (L : List Int) (v : Int) (hv : v ∈ L) (hne : v ≠ lmax L) : v ≤ smax L := by
  have := lmax_ge L v hv
  exact lmax_ge _ v (List.mem_filter.mpr ⟨hv, by simp; omega⟩)

theorem ge_smin_of_ne (L : List Int) (v : Int) (hv : v ∈ L) (hne : v ≠ lmin L) : smin L ≤ v := by
  have := lmin_le L v hv
  exact lmin_le _ v (List.mem_filter.mpr ⟨hv, by simp; omega⟩)

/-- `update_node_max(c, x)` on the sum: the values equal to the maximum become `x`. -/
theorem sum_chmin (L : List Int) (mx sx cx mn sn cn x : Int) (hS : Summ L mx sx cx mn sn cn) (h1 : sx < x)
    (h2 : x < mx) : (L.map (min · x)).sum = L.sum + (x - mx) * cx := by
  rw [hS.mxc, sum_map_count L _ mx (x - mx) (fun v hv => ?_)]
  · simp [cmax, hS.mx]; ring
  · by_cases he : v = mx
    · subst he; simp; omega
    · have := le_smax_of_ne L v hv (by rw [← hS.mx]; exact he); rw [← hS.smx] at this
      simp [he]; omega

theorem sum_chmax (L : List Int) (mx sx cx mn sn cn x : Int) (hS : Summ L mx sx cx mn sn cn) (h1 : mn < x)
    (h2 : x < sn) : (L.map (max · x)).sum = L.sum + (x - mn) * cn := by
  rw [hS.mnc, sum_map_count L _ mn (x - mn) (fun v hv => ?_)]
  · simp [cmin, hS.mn]; ring
  · by_cases he : v = mn
    · subst he; simp; omega
    · have := ge_smin_of_ne L v hv (by rw [← hS.mn]; exact he); rw [← hS.smn] at this
      simp [he]; omega

theorem sum_add (L : List Int) (x : Int) : (L.map (· + x)).sum = L.sum + (L.length : Int) * x := by
  induction L with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; push_cast; ring

theorem sum_replicate (m : Nat) (x : Int) : (List.replicate m x).sum = x * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.sum_cons, ih]; push_cast; ring

/-- Every node `j` below `k` holds the sum of its leaf values in `sm j`. -/
def SInv (s : BS) (sm : Nat → Int) (n : Nat) : Nat → Nat → Nat → Prop
  | 0, k, lo => sm k = (T s n 0 k lo).sum
  | h + 1, k, lo => SInv s sm n h (2 * k + 1) lo ∧ SInv s sm n h (2 * k + 2) (lo + 2 ^ h) ∧
      sm k = (T s n (h + 1) k lo).sum

theorem sinv_top (s : BS) (sm : Nat → Int) (n : Nat) : ∀ h k lo, SInv s sm n h k lo → sm k = (T s n h k lo).sum := by
  intro h k lo hS; cases h with
  | zero => exact hS
  | succ h => exact hS.2.2

theorem sinv_frame (s t : BS) (sm sm' : Nat → Int) (n : Nat) : ∀ h k lo,
    (∀ j, Sub h k j → AgreeAt s t j ∧ sm' j = sm j) → SInv s sm n h k lo → SInv t sm' n h k lo := by
  intro h
  induction h with
  | zero =>
    intro k lo hA hS
    show sm' k = _
    rw [(hA k rfl).2, ← T_frame s t n 0 k lo (fun j hj => (hA j hj).1)]; exact hS
  | succ h ih =>
    intro k lo hA hS
    refine ⟨ih _ _ (fun j hj => hA j (sub_child1 h k j hj)) hS.1, ih _ _ (fun j hj => hA j (sub_child2 h k j hj)) hS.2.1,
      ?_⟩
    rw [(hA k (Or.inl rfl)).2, ← T_frame s t n (h + 1) k lo (fun j hj => (hA j hj).1)]; exact hS.2.2

/-- Only the top of the subtree changed. -/
theorem sinv_change_top (s t : BS) (sm sm' : Nat → Int) (n h c lo : Nat) (hS : SInv s sm n h c lo)
    (hA : ∀ j, j ≠ c → AgreeAt s t j ∧ sm' j = sm j) (htop : sm' c = (T t n h c lo).sum) : SInv t sm' n h c lo := by
  cases h with
  | zero => exact htop
  | succ h =>
    have hb : ∀ j, (SegmentTreeBeatsMath.Sub h (2 * c + 1) j ∨ SegmentTreeBeatsMath.Sub h (2 * c + 2) j) → j ≠ c :=
      fun j hj => notsub_k h c j hj
    exact ⟨sinv_frame s t sm sm' n h _ _ (fun j hj => hA j (hb j (Or.inl hj))) hS.1,
      sinv_frame s t sm sm' n h _ _ (fun j hj => hA j (hb j (Or.inr hj))) hS.2.1, htop⟩

/-! ## The sum array under the node operations (the C++ updates of `sum[k]`) -/

def unmS (s : BS) (sm : Nat → Int) (c : Nat) (x : Int) : Nat → Int := upF sm c (sm c + (x - s.mx c) * s.cx c)
def unminS (s : BS) (sm : Nat → Int) (c : Nat) (x : Int) : Nat → Int := upF sm c (sm c + (x - s.mn c) * s.cn c)
def addS (s : BS) (sm : Nat → Int) (c : Nat) (x : Int) : Nat → Int := upF sm c (sm c + s.len c * x)
def updS (s : BS) (sm : Nat → Int) (c : Nat) (x : Int) : Nat → Int := upF sm c (x * s.len c)
def updSum (sm : Nat → Int) (k : Nat) : Nat → Int := upF sm k (sm (2 * k + 1) + sm (2 * k + 2))

theorem upF_ne (f : Nat → Int) (k j : Nat) (v : Int) (h : j ≠ k) : upF f k v j = f j := by simp [upF, h]
theorem upF_eq (f : Nat → Int) (k : Nat) (v : Int) : upF f k v k = v := by simp [upF]

theorem unm_sinv (s : BS) (sm : Nat → Int) (n : Nat) (B : Int) (hB : B < INF) (h c lo : Nat) (O : List Int)
    (h0 : 0 ∈ O) (hI : Inv s n h c lo) (hS : Safe s n B h c lo O) (hSI : SInv s sm n h c lo) (x : Int)
    (h1 : s.sx c < x) (h2 : x < s.mx c) : SInv (unm s c x) (unmS s sm c x) n h c lo := by
  obtain ⟨-, t⟩ := unm_node s n B hB h c lo O h0 hI hS x h1 h2
  refine sinv_change_top s _ sm _ n h c lo hSI (fun j hj => ⟨unm_agree s c x j hj, upF_ne _ _ _ _ hj⟩) ?_
  have hsum := inv_summ s n h c lo hI
  rw [t, sum_chmin _ _ _ _ _ _ _ x hsum h1 h2, ← sinv_top s sm n h c lo hSI]
  simp [unmS, upF]

theorem unmin_sinv (s : BS) (sm : Nat → Int) (n : Nat) (B : Int) (hB : B < INF) (h c lo : Nat) (O : List Int)
    (h0 : 0 ∈ O) (hI : Inv s n h c lo) (hS : Safe s n B h c lo O) (hSI : SInv s sm n h c lo) (x : Int)
    (h1 : s.mn c < x) (h2 : x < s.sn c) : SInv (unmin s c x) (unminS s sm c x) n h c lo := by
  obtain ⟨-, t⟩ := unmin_node s n B hB h c lo O h0 hI hS x h1 h2
  refine sinv_change_top s _ sm _ n h c lo hSI (fun j hj => ⟨unmin_agree s c x j hj, upF_ne _ _ _ _ hj⟩) ?_
  have hsum := inv_summ s n h c lo hI
  rw [t, sum_chmax _ _ _ _ _ _ _ x hsum h1 h2, ← sinv_top s sm n h c lo hSI]
  simp [unminS, upF]

theorem addAll_sinv (s : BS) (sm : Nat → Int) (n : Nat) (B : Int) (hB : B < INF) (h c lo : Nat) (O : List Int)
    (h0 : 0 ∈ O) (hI : Inv s n h c lo) (hS : Safe s n B h c lo O) (hSI : SInv s sm n h c lo)
    (hreal : lo + 2 ^ h ≤ n) (x : Int) (hx : x ∈ O) : SInv (addAll s c x) (addS s sm c x) n h c lo := by
  obtain ⟨-, t⟩ := addAll_node s n B hB h c lo O h0 hI hS hreal x hx
  refine sinv_change_top s _ sm _ n h c lo hSI (fun j hj => ⟨addAll_agree s c x j hj, upF_ne _ _ _ _ hj⟩) ?_
  rw [t, sum_add, ← sinv_top s sm n h c lo hSI, inv_real_length s n h c lo hreal]
  simp [addS, upF, inv_len s n h c lo hI]

theorem updAll_sinv (s : BS) (sm : Nat → Int) (n : Nat) (h c lo : Nat) (hI : Inv s n h c lo)
    (hSI : SInv s sm n h c lo) (hreal : lo + 2 ^ h ≤ n) (x : Int) (hx : -INF < x ∧ x < INF) :
    SInv (updAll s c x) (updS s sm c x) n h c lo := by
  obtain ⟨-, t⟩ := updAll_spec s n h c lo x hI hreal hx
  refine sinv_change_top s _ sm _ n h c lo hSI (fun j hj => ⟨updAll_agree s c x j hj, upF_ne _ _ _ _ hj⟩) ?_
  rw [t, sum_replicate]
  simp [updS, upF, inv_len s n h c lo hI]

theorem upd_sinv (s : BS) (sm : Nat → Int) (n h k lo : Nat)
    (h1 : SInv s sm n h (2 * k + 1) lo) (h2 : SInv s sm n h (2 * k + 2) (lo + 2 ^ h))
    (hT : T (upd s k) n (h + 1) k lo = T s n h (2 * k + 1) lo ++ T s n h (2 * k + 2) (lo + 2 ^ h)) :
    SInv (upd s k) (updSum sm k) n (h + 1) k lo := by
  have nk1 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → j ≠ k := fun j hj => notsub_k h k j (Or.inl hj)
  have nk2 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 2) j → j ≠ k := fun j hj => notsub_k h k j (Or.inr hj)
  refine ⟨sinv_frame s _ sm _ n h _ _ (fun j hj => ⟨upd_agree s k j (nk1 j hj), upF_ne _ _ _ _ (nk1 j hj)⟩) h1,
    sinv_frame s _ sm _ n h _ _ (fun j hj => ⟨upd_agree s k j (nk2 j hj), upF_ne _ _ _ _ (nk2 j hj)⟩) h2, ?_⟩
  rw [hT, List.sum_append, ← sinv_top s sm n h _ _ h1, ← sinv_top s sm n h _ _ h2]
  simp [updSum, upF]

/-- `push`'s cap of child `c` on the sum array (`update_node_max` then `update_node_min`, as in C++). -/
def capsS (s : BS) (sm : Nat → Int) (k c : Nat) : Nat → Int :=
  let sm1 := if s.mx k < s.mx c then unmS s sm c (s.mx k) else sm
  let s1 := if s.mx k < s.mx c then unm s c (s.mx k) else s
  if s1.mn c < s1.mn k then unminS s1 sm1 c (s1.mn k) else sm1

theorem caps_sinv (s : BS) (sm : Nat → Int) (n : Nat) (B : Int) (hB : B < INF) (h c lo : Nat) (O : List Int) (h0 : 0 ∈ O)
    (k : Nat) (hck : k ≠ c) (hI : Inv s n h c lo) (hS : Safe s n B h c lo O)
    (hk0 : -INF ≤ s.mx k ∧ s.mn k ≤ INF) (hmn' : T s n h c lo ≠ [] → s.mn k ≤ s.mx k)
    (hbx' : T s n h c lo ≠ [] → ∀ o ∈ O, |s.mx k + o| ≤ B ∧ |s.mn k + o| ≤ B)
    (ok : (s.mx k < lmax (T s n h c lo) → smax (T s n h c lo) < s.mx k) ∧
      (lmin (T s n h c lo) < s.mn k → s.mn k < smin (T s n h c lo)) ∧
      (s.mx k = s.mn k → lmax (T s n h c lo) = lmin (T s n h c lo) ∨ T s n h c lo = []))
    (hSI : SInv s sm n h c lo) : SInv (caps s k c) (capsS s sm k c) n h c lo := by
  set L := T s n h c lo with hL
  have hSum := inv_summ s n h c lo hI
  have hR := inR_zero _ (safe_inR s n B hB h c lo O hS 0 h0)
  by_cases hLe : L = []
  · have hLe' : T s n h c lo = [] := hLe
    have hmxc : s.mx c = -INF := by rw [hSum.mx, hLe']; rfl
    have hmnc : s.mn c = INF := by rw [hSum.mn, hLe']; rfl
    have hc : caps s k c = s := by
      simp only [caps, if_neg (show ¬ s.mx k < s.mx c by omega), if_neg (show ¬ s.mn c < s.mn k by omega)]
    have hcs : capsS s sm k c = sm := by
      simp only [capsS, if_neg (show ¬ s.mx k < s.mx c by omega), if_neg (show ¬ s.mn c < s.mn k by omega)]
    rw [hc, hcs]; exact hSI
  have hmn := hmn' hLe
  have hbx := hbx' hLe
  obtain ⟨bx0, bn0⟩ := hbx 0 h0
  simp only [add_zero] at bx0 bn0
  rw [abs_le] at bx0 bn0
  -- the cap from above
  obtain ⟨I1, S1, T1, A1, SI1⟩ : Inv (if s.mx k < s.mx c then unm s c (s.mx k) else s) n h c lo ∧
      Safe (if s.mx k < s.mx c then unm s c (s.mx k) else s) n B h c lo O ∧
      T (if s.mx k < s.mx c then unm s c (s.mx k) else s) n h c lo = L.map (min · (s.mx k)) ∧
      (∀ j, j ≠ c → AgreeAt s (if s.mx k < s.mx c then unm s c (s.mx k) else s) j) ∧
      SInv (if s.mx k < s.mx c then unm s c (s.mx k) else s)
        (if s.mx k < s.mx c then unmS s sm c (s.mx k) else sm) n h c lo := by
    split_ifs with hc
    · have hsx : s.sx c < s.mx k := by rw [hSum.smx]; exact ok.1 (by rw [← hSum.mx]; exact hc)
      obtain ⟨i, t⟩ := unm_node s n B hB h c lo O h0 hI hS (s.mx k) hsx hc
      obtain ⟨-, -, -, -, -, -, -, f8, f9⟩ := unm_fields s c (s.mx k)
      refine ⟨i, safe_change_top s _ n B h c lo O (unm_agree s c _) f8 (by
          rw [f9]; split_ifs with hh
          · constructor <;> intro <;> unfold INF at * <;> omega
          · exact Iff.rfl) hS (fun o ho v hv => by
          rw [t] at hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
          exact abs_min_le _ _ _ _ (safe_top s n B h c lo O hS o ho w hw) (hbx o ho).1), t, unm_agree s c _,
        unm_sinv s sm n B hB h c lo O h0 hI hS hSI _ hsx hc⟩
    · refine ⟨hI, hS, (lmax_map_min_id L _ (by rw [← hSum.mx]; omega)).symm, fun j _ => ?_, hSI⟩
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  set s1 := (if s.mx k < s.mx c then unm s c (s.mx k) else s) with hs1
  have hk1 : AgreeAt s s1 k := A1 k hck
  have hSum1 := inv_summ s1 n h c lo I1
  rw [T1] at hSum1
  set sm1 := (if s.mx k < s.mx c then unmS s sm c (s.mx k) else sm) with hsm1
  have hcaps : caps s k c = if s1.mn c < s1.mn k then unmin s1 c (s1.mn k) else s1 := rfl
  have hcapsS : capsS s sm k c = if s1.mn c < s1.mn k then unminS s1 sm1 c (s1.mn k) else sm1 := rfl
  rw [hcaps, hcapsS, ← hk1.2.2.2.1]
  split_ifs with hc
  · have hlt : lmin (L.map (min · (s.mx k))) < s.mn k := by rw [← hSum1.mn]; exact hc
    have hLne : L ≠ [] := by intro he; rw [he] at hlt; simp [lmin_nil] at hlt; omega
    have hlt0 : lmin L < s.mn k := by
      have := lmin_map_min_ge L (s.mx k) (by omega); omega
    have hsn : s.mn k < s1.sn c := by
      rw [hSum1.smn]
      have hs2 := ok.2.1 hlt0
      by_cases he : s.mx k = s.mn k
      · rcases ok.2.2 he with hsing | hemp
        · have hmx' : lmax L < s.mx k := by have := lmin_le_lmax L hR hLne; omega
          rw [lmax_map_min_id L _ (by omega), smin_single L hsing]; omega
        · exact absurd hemp hLne
      · exact lt_smin_map_min L _ _ hR hLne (by omega) hs2 (by omega) (by omega)
    exact unmin_sinv s1 sm1 n B hB h c lo O h0 I1 S1 SI1 (s.mn k) hc hsn
  · exact SI1

theorem capsS_ne (s : BS) (sm : Nat → Int) (k c j : Nat) (h : j ≠ c) : capsS s sm k c j = sm j := by
  unfold capsS; split_ifs <;> simp [unmS, unminS, upF, h]

/-- `push(k)` on the sum array, in the order of the C++ code. -/
def pushSS (s : BS) (sm : Nat → Int) (k : Nat) : Nat → Int :=
  if s.lv k ≠ INF then updS (updAll s (2 * k + 1) (s.lv k)) (updS s sm (2 * k + 1) (s.lv k)) (2 * k + 2) (s.lv k)
  else
    let s1 := if s.la k ≠ 0 then setLa (addAll (addAll s (2 * k + 1) (s.la k)) (2 * k + 2) (s.la k)) k 0 else s
    let sm1 := if s.la k ≠ 0 then addS (addAll s (2 * k + 1) (s.la k)) (addS s sm (2 * k + 1) (s.la k)) (2 * k + 2)
      (s.la k) else sm
    capsS (caps s1 k (2 * k + 1)) (capsS s1 sm1 k (2 * k + 1)) k (2 * k + 2)

theorem stage1_sinv (s : BS) (sm : Nat → Int) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int)
    (h0 : 0 ∈ O) (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O) (hlv : s.lv k = INF)
    (hSI : SInv s sm n (h + 1) k lo) :
    SInv (if s.la k ≠ 0 then setLa (addAll (addAll s (2 * k + 1) (s.la k)) (2 * k + 2) (s.la k)) k 0 else s)
      (if s.la k ≠ 0 then addS (addAll s (2 * k + 1) (s.la k)) (addS s sm (2 * k + 1) (s.la k)) (2 * k + 2)
        (s.la k) else sm) n h (2 * k + 1) lo ∧
    SInv (if s.la k ≠ 0 then setLa (addAll (addAll s (2 * k + 1) (s.la k)) (2 * k + 2) (s.la k)) k 0 else s)
      (if s.la k ≠ 0 then addS (addAll s (2 * k + 1) (s.la k)) (addS s sm (2 * k + 1) (s.la k)) (2 * k + 2)
        (s.la k) else sm) n h (2 * k + 2) (lo + 2 ^ h) := by
  obtain ⟨i1, i2, -, -, i5, -, -⟩ := hI
  obtain ⟨-, hS2⟩ := hS
  obtain ⟨sa, sb⟩ := hS2 hlv
  obtain ⟨si1, si2, -⟩ := hSI
  split_ifs with hla
  swap
  · exact ⟨si1, si2⟩
  have hreal : lo + 2 ^ (h + 1) ≤ n := by by_contra hc; exact hla (i5 (by omega)).1
  have hreal2 : lo + 2 ^ h + 2 ^ h ≤ n := by rw [pow_succ] at hreal; omega
  have hreal1 : lo + 2 ^ h ≤ n := Nat.le_trans (Nat.le_add_right _ _) hreal2
  have hx : s.la k ∈ 0 :: O.map (· + s.la k) := List.mem_cons_of_mem _ (List.mem_map.mpr ⟨0, h0, by simp⟩)
  have A := addAll_sinv s sm n B hB h _ lo _ List.mem_cons_self i1 sa si1 hreal1 _ hx
  set s' := addAll s (2 * k + 1) (s.la k)
  set sm' := addS s sm (2 * k + 1) (s.la k)
  have fb : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 2) j → AgreeAt s s' j ∧ sm' j = sm j :=
    fun j hj => ⟨addAll_agree s _ _ j (sub_disjoint h k j hj), upF_ne _ _ _ _ (sub_disjoint h k j hj)⟩
  have i2' := inv_frame s s' n h _ _ (fun j hj => (fb j hj).1) i2
  have sb' := safe_frame s s' n B h _ _ _ (fun j hj => (fb j hj).1) sb
  have si2' := sinv_frame s s' sm sm' n h _ _ fb si2
  have Bb := addAll_sinv s' sm' n B hB h _ (lo + 2 ^ h) _ List.mem_cons_self i2' sb' si2' hreal2 _ hx
  set s'' := addAll s' (2 * k + 2) (s.la k)
  set sm'' := addS s' sm' (2 * k + 2) (s.la k)
  have fa : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → AgreeAt s' s'' j ∧ sm'' j = sm' j :=
    fun j hj => ⟨addAll_agree s' _ _ j (sub_disjoint' h k j hj), upF_ne _ _ _ _ (sub_disjoint' h k j hj)⟩
  have gl : ∀ c, (SegmentTreeBeatsMath.Sub h (2 * k + 1) c ∨ SegmentTreeBeatsMath.Sub h (2 * k + 2) c) →
      AgreeAt s'' (setLa s'' k 0) c ∧ sm'' c = sm'' c := fun c hc => ⟨setLa_agree s'' k 0 c (notsub_k h k c hc), rfl⟩
  exact ⟨sinv_frame _ _ _ _ n h _ _ (fun j hj => gl j (Or.inl hj)) (sinv_frame s' s'' sm' sm'' n h _ _ fa A),
    sinv_frame _ _ _ _ n h _ _ (fun j hj => gl j (Or.inr hj)) Bb⟩

theorem push_sinv_add (s : BS) (sm : Nat → Int) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int)
    (h0 : 0 ∈ O) (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O) (hlv : s.lv k = INF)
    (hSI : SInv s sm n (h + 1) k lo) : SInv (push s k) (pushSS s sm k) n (h + 1) k lo := by
  have hI0 := hI
  obtain ⟨-, -, i3, i4, i5, -, i7⟩ := hI
  obtain ⟨c1, c2⟩ := i7 hlv
  set s1 := (if s.la k ≠ 0 then setLa (addAll (addAll s (2 * k + 1) (s.la k)) (2 * k + 2) (s.la k)) k 0 else s)
    with hs1
  obtain ⟨I1, I2, S1, S2, T1, T2, l1, l2, m1, m2, m3, m4, m5, m6, m7, A1⟩ := push_stage1 s n B hB h k lo O h0 hI0 hS hlv
  set sm1 := (if s.la k ≠ 0 then addS (addAll s (2 * k + 1) (s.la k)) (addS s sm (2 * k + 1) (s.la k)) (2 * k + 2)
    (s.la k) else sm) with hsm1
  obtain ⟨SI1, SI2⟩ := stage1_sinv s sm n B hB h k lo O h0 hI0 hS hlv hSI
  have hpush : push s k = caps (caps s1 k (2 * k + 1)) k (2 * k + 2) := by
    unfold push; rw [if_neg (by simpa using hlv)]
  have hRk := inR_zero _ (safe_inR s n B hB (h + 1) k lo O hS 0 h0)
  have hk0 : -INF ≤ s1.mx k ∧ s1.mn k ≤ INF := by
    rw [m1, m4, i3.mx, i3.mn]; exact ⟨lmax_ge_ninf _, lmin_le_inf _⟩
  have hmnF : T s n (h + 1) k lo ≠ [] → s1.mn k ≤ s1.mx k := by
    intro hne; rw [m1, m4, i3.mx, i3.mn]; exact lmin_le_lmax _ hRk hne
  have hbxF : T s n (h + 1) k lo ≠ [] → ∀ o ∈ 0 :: O, |s1.mx k + o| ≤ B ∧ |s1.mn k + o| ≤ B := by
    intro hne o ho
    have ho' : o ∈ O := by rcases List.mem_cons.mp ho with rfl | ho; exacts [h0, ho]
    rw [m1, m4, i3.mx, i3.mn]
    exact ⟨safe_top s n B _ _ _ _ hS o ho' _ (lmax_mem _ hne hRk),
      safe_top s n B _ _ _ _ hS o ho' _ (lmin_mem _ hne hRk)⟩
  have ok1 : (s1.mx k < lmax (T s1 n h (2 * k + 1) lo) → smax (T s1 n h (2 * k + 1) lo) < s1.mx k) ∧
      (lmin (T s1 n h (2 * k + 1) lo) < s1.mn k → s1.mn k < smin (T s1 n h (2 * k + 1) lo)) ∧
      (s1.mx k = s1.mn k → lmax (T s1 n h (2 * k + 1) lo) = lmin (T s1 n h (2 * k + 1) lo) ∨
        T s1 n h (2 * k + 1) lo = []) := by rw [T1, m1, m4]; exact c1
  have ok2 : (s1.mx k < lmax (T s1 n h (2 * k + 2) (lo + 2 ^ h)) → smax (T s1 n h (2 * k + 2) (lo + 2 ^ h)) < s1.mx k) ∧
      (lmin (T s1 n h (2 * k + 2) (lo + 2 ^ h)) < s1.mn k → s1.mn k < smin (T s1 n h (2 * k + 2) (lo + 2 ^ h))) ∧
      (s1.mx k = s1.mn k → lmax (T s1 n h (2 * k + 2) (lo + 2 ^ h)) = lmin (T s1 n h (2 * k + 2) (lo + 2 ^ h)) ∨
        T s1 n h (2 * k + 2) (lo + 2 ^ h) = []) := by rw [T2, m1, m4]; exact c2
  have ne1 : T s1 n h (2 * k + 1) lo ≠ [] → T s n (h + 1) k lo ≠ [] := fun hn =>
    T_child_nonempty s n h k lo _ _ (Or.inl ⟨rfl, rfl⟩) (by rw [← T1]; exact hn)
  have ne2 : T s1 n h (2 * k + 2) (lo + 2 ^ h) ≠ [] → T s n (h + 1) k lo ≠ [] := fun hn =>
    T_child_nonempty s n h k lo _ _ (Or.inr ⟨rfl, rfl⟩) (by rw [← T2]; exact hn)
  have K1 := caps_sinv s1 sm1 n B hB h (2 * k + 1) lo (0 :: O) List.mem_cons_self k (by omega) I1 S1 hk0
    (fun hn => hmnF (ne1 hn)) (fun hn => hbxF (ne1 hn)) ok1 SI1
  obtain ⟨J1, R1, U1, B1⟩ := caps_spec s1 n B hB h (2 * k + 1) lo (0 :: O) List.mem_cons_self k (by omega) I1 S1 hk0
    (fun hn => hmnF (ne1 hn)) (fun hn => hbxF (ne1 hn)) ok1
  set t1 := caps s1 k (2 * k + 1)
  have f2 : ∀ j, Sub h (2 * k + 2) j → AgreeAt s1 t1 j := fun j hj => B1 j (sub_disjoint h k j hj)
  have I2' := inv_frame s1 t1 n h _ _ f2 I2
  have S2' := safe_frame s1 t1 n B h _ _ _ f2 S2
  have T2' := T_frame s1 t1 n h _ (lo + 2 ^ h) f2
  have ak1 := B1 k (by omega)
  have hk0' : -INF ≤ t1.mx k ∧ t1.mn k ≤ INF := by rw [← ak1.1, ← ak1.2.2.2.1]; exact hk0
  have ok2' := ok2
  rw [T2', ak1.1, ak1.2.2.2.1] at ok2'
  set sm2 := capsS s1 sm1 k (2 * k + 1)
  have SI2' : SInv t1 sm2 n h (2 * k + 2) (lo + 2 ^ h) :=
    sinv_frame s1 t1 sm1 sm2 n h _ _ (fun j hj => ⟨f2 j hj, capsS_ne _ _ _ _ _ (sub_disjoint h k j hj)⟩) SI2
  have K2 := caps_sinv t1 sm2 n B hB h (2 * k + 2) (lo + 2 ^ h) (0 :: O) List.mem_cons_self k (by omega)
    I2' S2' hk0' (fun hn => by rw [← ak1.1, ← ak1.2.2.2.1]; exact hmnF (ne2 (by rw [T2']; exact hn)))
    (fun hn => by rw [← ak1.1, ← ak1.2.2.2.1]; exact hbxF (ne2 (by rw [T2']; exact hn))) ok2' SI2'
  obtain ⟨J2, R2, U2, B2⟩ := caps_spec t1 n B hB h (2 * k + 2) (lo + 2 ^ h) (0 :: O) List.mem_cons_self k (by omega)
    I2' S2' hk0' (fun hn => by rw [← ak1.1, ← ak1.2.2.2.1]; exact hmnF (ne2 (by rw [T2']; exact hn)))
    (fun hn => by rw [← ak1.1, ← ak1.2.2.2.1]; exact hbxF (ne2 (by rw [T2']; exact hn))) ok2'
  set t2 := caps t1 k (2 * k + 2)
  have f1 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → AgreeAt t1 t2 j := fun j hj => B2 j (sub_disjoint' h k j hj)
  have hp' : push s k = t2 := hpush
  have hps : pushSS s sm k = capsS t1 sm2 k (2 * k + 2) := by
    unfold pushSS; rw [if_neg (by simpa using hlv)]
  rw [hp', hps]
  obtain ⟨-, -, hT, -⟩ := push_add s n B hB h k lo O h0 hI0 hS hlv
  rw [hp'] at hT
  refine ⟨sinv_frame t1 t2 sm2 _ n h _ _ (fun j hj => ⟨f1 j hj, capsS_ne _ _ _ _ _ (sub_disjoint' h k j hj)⟩) K1, K2, ?_⟩
  rw [hT, ← sinv_top s sm n (h + 1) k lo hSI]
  rw [capsS_ne _ _ _ _ _ (by omega)]
  show capsS s1 sm1 k (2 * k + 1) k = sm k
  rw [capsS_ne _ _ _ _ _ (by omega)]
  by_cases hla : s.la k = 0
  · rw [hsm1, if_neg (by simpa using hla)]
  · rw [hsm1, if_pos hla]; simp [addS, upF]; omega

theorem push_sinv_set (s : BS) (sm : Nat → Int) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int)
    (h0 : 0 ∈ O) (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O) (hlv : s.lv k ≠ INF)
    (hSI : SInv s sm n (h + 1) k lo) : SInv (push s k) (pushSS s sm k) n (h + 1) k lo := by
  have hI0 := hI
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := hI
  obtain ⟨e1, e2, e3, e4⟩ := i6 hlv
  obtain ⟨si1, si2, si3⟩ := hSI
  have hreal : lo + 2 ^ (h + 1) ≤ n := by by_contra hc; exact hlv (i5 (by omega)).2
  have hreal2 : lo + 2 ^ h + 2 ^ h ≤ n := by rw [pow_succ] at hreal; omega
  have hreal1 : lo + 2 ^ h ≤ n := Nat.le_trans (Nat.le_add_right _ _) hreal2
  have hRk := inR_zero _ (safe_inR s n B hB (h + 1) k lo O hS 0 h0)
  have hne : T s n (h + 1) k lo ≠ [] := by
    intro he; have hl := inv_real_length s n (h + 1) k lo hreal; rw [he] at hl
    have := Nat.two_pow_pos (h + 1); simp at hl; omega
  have hmem : s.lv k ∈ T s n (h + 1) k lo := by rw [← e1, i3.mx]; exact lmax_mem _ hne hRk
  have hx : -INF < s.lv k ∧ s.lv k < INF := hRk _ hmem
  have A := updAll_sinv s sm n h _ lo i1 si1 hreal1 _ hx
  set s' := updAll s (2 * k + 1) (s.lv k)
  set sm' := updS s sm (2 * k + 1) (s.lv k)
  have fb : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 2) j → AgreeAt s s' j ∧ sm' j = sm j :=
    fun j hj => ⟨updAll_agree s _ _ j (sub_disjoint h k j hj), upF_ne _ _ _ _ (sub_disjoint h k j hj)⟩
  have i2' := inv_frame s s' n h _ _ (fun j hj => (fb j hj).1) i2
  have si2' := sinv_frame s s' sm sm' n h _ _ fb si2
  have Bb := updAll_sinv s' sm' n h _ (lo + 2 ^ h) i2' si2' hreal2 _ hx
  set s'' := updAll s' (2 * k + 2) (s.lv k)
  set sm'' := updS s' sm' (2 * k + 2) (s.lv k)
  have fa : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → AgreeAt s' s'' j ∧ sm'' j = sm' j :=
    fun j hj => ⟨updAll_agree s' _ _ j (sub_disjoint' h k j hj), upF_ne _ _ _ _ (sub_disjoint' h k j hj)⟩
  have hpush : push s k = setLv s'' k INF := by unfold push; rw [if_pos hlv]
  have hps : pushSS s sm k = sm'' := by unfold pushSS; rw [if_pos hlv]
  have gl : ∀ c, (SegmentTreeBeatsMath.Sub h (2 * k + 1) c ∨ SegmentTreeBeatsMath.Sub h (2 * k + 2) c) →
      AgreeAt s'' (setLv s'' k INF) c ∧ sm'' c = sm'' c := fun c hc => ⟨setLv_agree s'' k INF c (notsub_k h k c hc), rfl⟩
  obtain ⟨-, -, hT, -⟩ := push_set s n B hB h k lo O h0 hI0 hS hlv
  rw [hpush] at hT
  rw [hpush, hps]
  refine ⟨sinv_frame _ _ _ _ n h _ _ (fun j hj => gl j (Or.inl hj)) (sinv_frame s' s'' sm' sm'' n h _ _ fa A),
    sinv_frame _ _ _ _ n h _ _ (fun j hj => gl j (Or.inr hj)) Bb, ?_⟩
  rw [hT, ← si3]
  show updS s' sm' (2 * k + 2) (s.lv k) k = sm k
  rw [show updS s' sm' (2 * k + 2) (s.lv k) k = sm' k from upF_ne _ _ _ _ (by omega)]
  exact upF_ne _ _ _ _ (by omega)

theorem push_sinv (s : BS) (sm : Nat → Int) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int)
    (h0 : 0 ∈ O) (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O)
    (hSI : SInv s sm n (h + 1) k lo) : SInv (push s k) (pushSS s sm k) n (h + 1) k lo := by
  by_cases hlv : s.lv k = INF
  · exact push_sinv_add s sm n B hB h k lo O h0 hI hS hlv hSI
  · exact push_sinv_set s sm n B hB h k lo O h0 hI hS hlv hSI

end Proofs.Cpp.SegmentTreeBeatsMath
