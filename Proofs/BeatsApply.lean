import Proofs.BeatsCapMin
namespace Proofs.BeatsModel

structure NodeInv2 (nd : Nd) (tg : Tag) (cl cr : Nd) (xl xr ys : List Int) : Prop where
  desc : Desc nd ys
  eq : ys = pend tg nd (xl ++ xr)
  dl : Desc cl xl
  dr : Desc cr xr
  nel : xl ≠ []
  ner : xr ≠ []
  rl : InRange xl
  rr : InRange xr
  ry : InRange ys
  rngv : ∀ v, tg.lval = some v → -INF < v ∧ v < INF
  rnga : tg.lval = none → ∀ w ∈ xl ++ xr, -INF < w + tg.ladd ∧ w + tg.ladd < INF
  capl : tg.lval = none → CapOk nd cl tg.ladd
  capr : tg.lval = none → CapOk nd cr tg.ladd

def tagMax (tg : Tag) (x : Int) : Tag := ⟨tg.lval.map (fun v => min v x), tg.ladd⟩
def tagMin (tg : Tag) (x : Int) : Tag := ⟨tg.lval.map (fun v => max v x), tg.ladd⟩

theorem ys_ne (tg : Tag) (nd : Nd) (xl xr : List Int) (hl : xl ≠ []) : ∃ v, v ∈ pend tg nd (xl ++ xr) := by
  apply List.exists_mem_of_ne_nil
  intro h
  have := pend_length tg nd (xl ++ xr)
  rw [h] at this
  have h0 : xl.length = 0 := by simp at this; omega
  exact hl (List.length_eq_zero_iff.mp h0)

theorem applyMax_nodeInv (nd : Nd) (tg : Tag) (cl cr : Nd) (xl xr ys : List Int) (h : NodeInv2 nd tg cl cr xl xr ys)
    (x : Int) (hs : nd.smx < x) (hlt : x < nd.mx) :
    NodeInv2 (updMax nd x) (tagMax tg x) cl cr xl xr (ys.map (fun v => min v x)) := by
  obtain ⟨vy, hvy⟩ : ∃ v, v ∈ ys := by rw [h.eq]; exact ys_ne tg nd xl xr h.nel
  obtain ⟨cn1, cn2, cn3, cn4, cn5, cn6⟩ := Desc_cons nd ys vy hvy h.ry h.desc
  have hnsmx : -INF ≤ nd.smx := by rw [h.desc.2.1]; exact smxL_ge ys
  have hx : -INF < x := by omega
  have hmnx : nd.mx ≠ nd.mn → nd.mn < x := by
    intro hne
    have := (mn_le_smx nd ys vy hvy h.ry h.desc (by omega)).2
    omega
  refine ⟨updMax_desc nd ys x vy hvy h.ry h.desc hs hlt, ?_, h.dl, h.dr, h.nel, h.ner, h.rl, h.rr, ?_, ?_, ?_, ?_, ?_⟩
  · -- the true array
    have heq := h.eq
    unfold pend tagMax at *
    cases hl : tg.lval with
    | some v =>
      rw [hl] at heq
      simp only [Option.map]
      rw [heq]
      simp only [List.map_append, List.map_map]
      rfl
    | none =>
      rw [hl] at heq
      simp only [Option.map]
      rw [heq]
      simp only [List.map_map]
      apply List.map_congr_left
      intro z _
      simp only [Function.comp, updMax_mx, updMax_mn]
      by_cases hmm : nd.mx = nd.mn
      · rw [if_pos hmm]; omega
      · rw [if_neg hmm]; have := hmnx hmm; omega
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have := h.ry u hu
    exact ⟨Int.lt_min.mpr ⟨this.1, hx⟩, Int.lt_of_le_of_lt (Int.min_le_left _ _) this.2⟩
  · intro v hv
    simp only [tagMax] at hv
    cases hl : tg.lval with
    | none => rw [hl] at hv; simp at hv
    | some v0 =>
      rw [hl] at hv
      simp only [Option.map, Option.some.injEq] at hv
      have := h.rngv v0 hl
      rw [← hv]
      exact ⟨Int.lt_min.mpr ⟨this.1, hx⟩, Int.lt_of_le_of_lt (Int.min_le_left _ _) this.2⟩
  · intro hl
    have : tg.lval = none := by
      simp only [tagMax] at hl
      cases hl' : tg.lval with
      | none => rfl
      | some _ => rw [hl'] at hl; simp at hl
    exact h.rnga this
  · intro hl
    have : tg.lval = none := by
      simp only [tagMax] at hl
      cases hl' : tg.lval with
      | none => rfl
      | some _ => rw [hl'] at hl; simp at hl
    obtain ⟨vl, hvl⟩ := List.exists_mem_of_ne_nil _ h.nel
    exact capOk_max nd cl tg.ladd xl ys (xl ++ xr) (fun w hw => List.mem_append.mpr (Or.inl hw)) h.dl h.rl vl hvl
      (by rw [h.eq]; unfold pend; rw [this]) h.desc h.ry vy hvy (fun w hw => h.rnga this w (List.mem_append.mpr (Or.inl hw)))
      (h.capl this) x hs hlt
  · intro hl
    have : tg.lval = none := by
      simp only [tagMax] at hl
      cases hl' : tg.lval with
      | none => rfl
      | some _ => rw [hl'] at hl; simp at hl
    obtain ⟨vr, hvr⟩ := List.exists_mem_of_ne_nil _ h.ner
    exact capOk_max nd cr tg.ladd xr ys (xl ++ xr) (fun w hw => List.mem_append.mpr (Or.inr hw)) h.dr h.rr vr hvr
      (by rw [h.eq]; unfold pend; rw [this]) h.desc h.ry vy hvy (fun w hw => h.rnga this w (List.mem_append.mpr (Or.inr hw)))
      (h.capr this) x hs hlt


theorem smn_le_mx (nd : Nd) (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hd : Desc nd xs)
    (hlt : nd.mn < nd.mx) : nd.smn ≤ nd.mx := by
  have hm := mxL_mem xs v0 hv0 (fun w hw => (hr w hw).1)
  have hmem : mxL xs ∈ xs.filter (fun v => decide (mnL xs < v)) :=
    List.mem_filter.mpr ⟨hm, by simpa using (by rw [← hd.1, ← hd.2.2.2.1]; exact hlt : mnL xs < mxL xs)⟩
  rw [hd.2.2.2.2.1, hd.1]
  exact mnL_le _ _ hmem

theorem updMin_mn (nd : Nd) (x : Int) : (updMin nd x).mn = x := by
  unfold updMin negNd; simp [updMax_mx]
theorem updMin_smn (nd : Nd) (x : Int) : (updMin nd x).smn = nd.smn := by
  unfold updMin negNd; simp [updMax_smx]
theorem updMin_mx (nd : Nd) (x : Int) : (updMin nd x).mx = if nd.mx = nd.mn then x else nd.mx := by
  unfold updMin negNd; simp only [updMax_mn]
  by_cases h : nd.mx = nd.mn
  · simp [h]
  · have : ¬ (-nd.mn = -nd.mx) := by omega
    simp [h, this]

theorem applyMin_nodeInv (nd : Nd) (tg : Tag) (cl cr : Nd) (xl xr ys : List Int) (h : NodeInv2 nd tg cl cr xl xr ys)
    (x : Int) (hs : x < nd.smn) (hlt : nd.mn < x) :
    NodeInv2 (updMin nd x) (tagMin tg x) cl cr xl xr (ys.map (fun v => max v x)) := by
  obtain ⟨vy, hvy⟩ : ∃ v, v ∈ ys := by rw [h.eq]; exact ys_ne tg nd xl xr h.nel
  obtain ⟨cn1, cn2, cn3, cn4, cn5, cn6⟩ := Desc_cons nd ys vy hvy h.ry h.desc
  have hsmn_le : nd.mn < nd.mx → nd.smn ≤ nd.mx := fun hl => smn_le_mx nd ys vy hvy h.ry h.desc hl
  have hsI : nd.smn ≤ INF := by rw [h.desc.2.2.2.2.1]; exact mnL_le_INF _
  have hx : x < INF := by omega
  have hmxx : nd.mx ≠ nd.mn → x < nd.mx := by
    intro hne
    have := hsmn_le (by omega)
    omega
  have hmnr : -INF < nd.mn := by
    rw [h.desc.2.2.2.1]; exact (h.ry _ (mnL_mem ys vy hvy (fun w hw => (h.ry w hw).2))).1
  have hxl : -INF < x := by omega
  refine ⟨updMin_desc nd ys x vy hvy h.ry h.desc hs hlt, ?_, h.dl, h.dr, h.nel, h.ner, h.rl, h.rr, ?_, ?_, ?_, ?_, ?_⟩
  · have heq := h.eq
    unfold pend tagMin at *
    cases hl : tg.lval with
    | some v =>
      rw [hl] at heq
      simp only [Option.map]
      rw [heq]
      simp only [List.map_append, List.map_map]
      rfl
    | none =>
      rw [hl] at heq
      simp only [Option.map]
      rw [heq]
      simp only [List.map_map]
      apply List.map_congr_left
      intro z _
      simp only [Function.comp, updMin_mx, updMin_mn]
      by_cases hmm : nd.mx = nd.mn
      · rw [if_pos hmm]; omega
      · rw [if_neg hmm]; have := hmxx hmm; omega
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have := h.ry u hu
    exact ⟨Int.lt_of_lt_of_le this.1 (Int.le_max_left _ _), Int.max_lt.mpr ⟨this.2, hx⟩⟩
  · intro v hv
    simp only [tagMin] at hv
    cases hl : tg.lval with
    | none => rw [hl] at hv; simp at hv
    | some v0 =>
      rw [hl] at hv
      simp only [Option.map, Option.some.injEq] at hv
      have := h.rngv v0 hl
      rw [← hv]
      exact ⟨Int.lt_of_lt_of_le this.1 (Int.le_max_left _ _), Int.max_lt.mpr ⟨this.2, hx⟩⟩
  · intro hl
    have : tg.lval = none := by
      simp only [tagMin] at hl
      cases hl' : tg.lval with
      | none => rfl
      | some _ => rw [hl'] at hl; simp at hl
    exact h.rnga this
  · intro hl
    have : tg.lval = none := by
      simp only [tagMin] at hl
      cases hl' : tg.lval with
      | none => rfl
      | some _ => rw [hl'] at hl; simp at hl
    obtain ⟨vl, hvl⟩ := List.exists_mem_of_ne_nil _ h.nel
    exact capOk_min nd cl tg.ladd xl ys (xl ++ xr) (fun w hw => List.mem_append.mpr (Or.inl hw)) h.dl h.rl vl hvl
      (by rw [h.eq]; unfold pend; rw [this]) h.desc h.ry vy hvy (fun w hw => h.rnga this w (List.mem_append.mpr (Or.inl hw)))
      (h.capl this) x hs hlt
  · intro hl
    have : tg.lval = none := by
      simp only [tagMin] at hl
      cases hl' : tg.lval with
      | none => rfl
      | some _ => rw [hl'] at hl; simp at hl
    obtain ⟨vr, hvr⟩ := List.exists_mem_of_ne_nil _ h.ner
    exact capOk_min nd cr tg.ladd xr ys (xl ++ xr) (fun w hw => List.mem_append.mpr (Or.inr hw)) h.dr h.rr vr hvr
      (by rw [h.eq]; unfold pend; rw [this]) h.desc h.ry vy hvy (fun w hw => h.rnga this w (List.mem_append.mpr (Or.inr hw)))
      (h.capr this) x hs hlt

end Proofs.BeatsModel
