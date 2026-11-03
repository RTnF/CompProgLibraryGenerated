import Proofs.BeatsApply
namespace Proofs.BeatsModel

def tagAdd (tg : Tag) (x : Int) : Tag :=
  ⟨tg.lval.map (fun v => v + x), match tg.lval with | none => tg.ladd + x | some _ => tg.ladd⟩
def tagSet (x : Int) : Tag := ⟨some x, 0⟩

theorem capOk_add (nd c : Nd) (a x : Int) (xs ys : List Int) (hdn : Desc nd ys) (hdc : Desc c xs)
    (hy : ∀ w ∈ ys, -INF < w + x ∧ w + x < INF) (hra : ∀ w ∈ xs, -INF < w + a ∧ w + a < INF)
    (hcap : CapOk nd c a) : CapOk (addNd nd x) c (a + x) := by
  obtain ⟨h1, h2⟩ := hcap
  unfold CapOk
  refine ⟨?_, ?_⟩
  · intro hp
    have hp' : nd.mx < c.mx + a := by simp only [addNd] at hp; omega
    have := h1 hp'
    by_cases hc : c.smx = -INF
    · have : smxA c (a + x) = -INF := by unfold smxA; rw [if_pos hc]; exact hc
      rw [this]
      simp only [addNd]
      by_cases hn : nd.smx = -INF
      · rw [if_pos hn]; omega
      · rw [if_neg hn]
        have hm : nd.smx ∈ ys := by rw [hdn.2.1]; exact smxL_mem ys (by rw [← hdn.2.1]; exact hn)
        have := (hy _ hm).1
        omega
    · have hm : c.smx ∈ xs := by rw [hdc.2.1]; exact smxL_mem xs (by rw [← hdc.2.1]; exact hc)
      have hr := (hra _ hm).1
      have hsA : smxA c a = c.smx + a := by unfold smxA; rw [if_neg hc]
      have hsA2 : smxA c (a + x) = c.smx + (a + x) := by unfold smxA; rw [if_neg hc]
      have hn : nd.smx ≠ -INF := by omega
      simp only [addNd]
      rw [if_neg hn, hsA2]
      omega
  · intro hp
    have hp' : c.mn + a < nd.mn := by simp only [addNd] at hp; omega
    have := h2 hp'
    by_cases hc : c.smn = INF
    · have : smnA c (a + x) = INF := by unfold smnA; rw [if_pos hc]; exact hc
      rw [this]
      simp only [addNd]
      by_cases hn : nd.smn = INF
      · rw [if_pos hn]; omega
      · rw [if_neg hn]
        have hm : nd.smn ∈ ys := by rw [hdn.2.2.2.2.1]; exact smnL_mem ys (by rw [← hdn.2.2.2.2.1]; exact hn)
        have := (hy _ hm).2
        omega
    · have hm : c.smn ∈ xs := by rw [hdc.2.2.2.2.1]; exact smnL_mem xs (by rw [← hdc.2.2.2.2.1]; exact hc)
      have hr := (hra _ hm).2
      have hsA : smnA c a = c.smn + a := by unfold smnA; rw [if_neg hc]
      have hsA2 : smnA c (a + x) = c.smn + (a + x) := by unfold smnA; rw [if_neg hc]
      have hn : nd.smn ≠ INF := by omega
      simp only [addNd]
      rw [if_neg hn, hsA2]
      omega

theorem applyAdd_nodeInv (nd : Nd) (tg : Tag) (cl cr : Nd) (xl xr ys : List Int) (h : NodeInv2 nd tg cl cr xl xr ys)
    (x : Int) (hy : ∀ w ∈ ys, -INF < w + x ∧ w + x < INF)
    (hv : ∀ v, tg.lval = some v → -INF < v + x ∧ v + x < INF)
    (ha : tg.lval = none → ∀ w ∈ xl ++ xr, -INF < w + (tg.ladd + x) ∧ w + (tg.ladd + x) < INF) :
    NodeInv2 (addNd nd x) (tagAdd tg x) cl cr xl xr (ys.map (fun v => v + x)) := by
  obtain ⟨vy, hvy⟩ : ∃ v, v ∈ ys := by rw [h.eq]; exact ys_ne tg nd xl xr h.nel
  refine ⟨addNd_desc nd ys x vy hvy h.ry (fun v hv => ⟨Int.le_of_lt (hy v hv).1, Int.le_of_lt (hy v hv).2⟩) h.desc,
    ?_, h.dl, h.dr, h.nel, h.ner, h.rl, h.rr, ?_, ?_, ?_, ?_, ?_⟩
  · have heq := h.eq
    unfold pend tagAdd at *
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
      simp only [Function.comp, addNd]
      omega
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    exact hy u hu
  · intro v hv'
    simp only [tagAdd] at hv'
    cases hl : tg.lval with
    | none => rw [hl] at hv'; simp at hv'
    | some v0 =>
      rw [hl] at hv'
      simp only [Option.map, Option.some.injEq] at hv'
      rw [← hv']
      exact hv v0 hl
  · intro hl
    have : tg.lval = none := by
      simp only [tagAdd] at hl
      cases hl' : tg.lval with
      | none => rfl
      | some _ => rw [hl'] at hl; simp at hl
    have := ha this
    simp only [tagAdd, this]
    cases hl' : tg.lval with
    | none => simpa using ha hl'
    | some _ => simp [hl'] at *
  · intro hl
    have h0 : tg.lval = none := by
      simp only [tagAdd] at hl
      cases hl' : tg.lval with
      | none => rfl
      | some _ => rw [hl'] at hl; simp at hl
    obtain ⟨vl, hvl⟩ := List.exists_mem_of_ne_nil _ h.nel
    have e : (tagAdd tg x).ladd = tg.ladd + x := by simp [tagAdd, h0]
    rw [e]
    exact capOk_add nd cl tg.ladd x xl ys h.desc h.dl hy (fun w hw => h.rnga h0 w (List.mem_append.mpr (Or.inl hw))) (h.capl h0)
  · intro hl
    have h0 : tg.lval = none := by
      simp only [tagAdd] at hl
      cases hl' : tg.lval with
      | none => rfl
      | some _ => rw [hl'] at hl; simp at hl
    have e : (tagAdd tg x).ladd = tg.ladd + x := by simp [tagAdd, h0]
    rw [e]
    exact capOk_add nd cr tg.ladd x xr ys h.desc h.dr hy (fun w hw => h.rnga h0 w (List.mem_append.mpr (Or.inr hw))) (h.capr h0)

theorem applySet_nodeInv (nd : Nd) (tg : Tag) (cl cr : Nd) (xl xr ys : List Int) (h : NodeInv2 nd tg cl cr xl xr ys)
    (x : Int) (hx : -INF < x ∧ x < INF) :
    NodeInv2 (setNd ys.length x) (tagSet x) cl cr xl xr (List.replicate ys.length x) := by
  have hlen : ys.length = (xl ++ xr).length := by rw [h.eq]; exact pend_length _ _ _
  have hpos : 0 < ys.length := by
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ h.nel
    have := List.length_pos_of_mem hv
    rw [hlen]; simp; omega
  refine ⟨setNd_desc ys.length x hx.1 hx.2 hpos, ?_, h.dl, h.dr, h.nel, h.ner, h.rl, h.rr, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pend tagSet
    simp only []
    rw [hlen, List.map_append, List.map_const', List.map_const', List.length_append, List.replicate_append_replicate]
  · intro w hw; rw [(List.mem_replicate.mp hw).2]; exact hx
  · intro v hv; simp only [tagSet, Option.some.injEq] at hv; rw [← hv]; exact hx
  · intro hl; simp [tagSet] at hl
  · intro hl; simp [tagSet] at hl
  · intro hl; simp [tagSet] at hl

end Proofs.BeatsModel
