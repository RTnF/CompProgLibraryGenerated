import Proofs.BeatsLoop8
namespace Proofs.BeatsModel

/-- The summary fields of a node are elements of its array (or a sentinel). -/
theorem desc_mem (nd : Nd) (xs : List Int) (hd : Desc nd xs) (hr : InRange xs) (hne : xs ≠ []) :
    nd.mx ∈ xs ∧ nd.mn ∈ xs ∧ (nd.smx ≠ -INF → nd.smx ∈ xs) ∧ (nd.smn ≠ INF → nd.smn ∈ xs) := by
  obtain ⟨v0, hv0⟩ := List.exists_mem_of_ne_nil xs hne
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; exact mxL_mem xs v0 hv0 (fun w hw => (hr w hw).1)
  · rw [h4]; exact mnL_mem xs v0 hv0 (fun w hw => (hr w hw).2)
  · intro h; rw [h2] at h ⊢; exact smxL_mem xs h
  · intro h; rw [h5] at h ⊢; exact smnL_mem xs h

/-- Every sum the `push` of a parent tag `a` computes on one child stays strictly inside `(-INF, INF)`
(`(-2·INF, 2·INF)` for the combined tag), given the side conditions of `Inv.push_child`. -/
theorem child_bounds (c : BT) (xc : List Int) (hc : Inv c xc) (a : Int)
    (hra : ∀ w ∈ xc, -INF < w + a ∧ w + a < INF)
    (hov1 : ∀ v, c.lval = some v → -INF < v + a ∧ v + a < INF)
    (hov2 : c.lval = none → ∀ w ∈ c.kids, -INF < w + (c.ladd + a) ∧ w + (c.ladd + a) < INF) :
    (-INF < c.nd.mx + a ∧ c.nd.mx + a < INF) ∧ (-INF < c.nd.mn + a ∧ c.nd.mn + a < INF) ∧
    (c.nd.smx ≠ -INF → -INF < c.nd.smx + a ∧ c.nd.smx + a < INF) ∧
    (c.nd.smn ≠ INF → -INF < c.nd.smn + a ∧ c.nd.smn + a < INF) ∧
    (c.lval = none → -2 * INF < c.ladd + a ∧ c.ladd + a < 2 * INF) ∧
    (∀ v, c.lval = some v → -INF < v + a ∧ v + a < INF) := by
  have hm := desc_mem c.nd xc hc.desc hc.range hc.ne
  refine ⟨hra _ hm.1, hra _ hm.2.1, fun h => hra _ (hm.2.2.1 h), fun h => hra _ (hm.2.2.2 h), ?_, hov1⟩
  intro hl
  cases c with
  | leaf nd =>
    simp only [BT.ladd, Int.zero_add]
    obtain ⟨w, hw⟩ : ∃ w, w ∈ xc := List.exists_mem_of_ne_nil xc hc.ne
    have h1 := hra w hw
    have h2 := hc.range w hw
    omega
  | node nd tg l r =>
    obtain ⟨w, hw⟩ : ∃ w, w ∈ (BT.node nd tg l r).kids := by
      apply List.exists_mem_of_ne_nil
      cases hc with
      | node _ _ _ _ xl xr ys hn hl hr =>
        simp only [BT.kids]
        intro h
        have := hl.ne
        have hxl : arr l = xl := hl.eq_arr.symm
        rw [hxl] at h
        simp at h
        exact this h.1
    have h1 := hov2 hl w hw
    have h2 : -INF < w ∧ w < INF := by
      cases hc with
      | node _ _ _ _ xl xr ys hn hl' hr' =>
        simp only [BT.kids] at hw
        rcases List.mem_append.mp hw with h | h
        · exact hl'.range w (by rwa [← hl'.eq_arr] at h)
        · exact hr'.range w (by rwa [← hr'.eq_arr] at h)
    simp only [BT.ladd] at *
    omega

end Proofs.BeatsModel
