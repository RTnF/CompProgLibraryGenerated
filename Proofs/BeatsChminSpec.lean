import Proofs.BeatsChmin
namespace Proofs.BeatsModel

def Sk.size : Sk → Nat
  | .leaf => 1
  | .node l r => l.size + r.size

theorem BT.size_skel (t : BT) : t.size = t.skel.size := by
  induction t with
  | leaf nd => rfl
  | node nd tg l r ihl ihr => simp [BT.size, BT.skel, Sk.size, ihl, ihr]

theorem Shape.size {lo hi : Nat} {sk : Sk} (h : Shape lo hi sk) : sk.size = hi - lo := by
  induction sk generalizing lo hi with
  | leaf => simp [Shape] at h; simp [Sk.size]; omega
  | node l r ihl ihr =>
    obtain ⟨h0, h1, h2⟩ := h
    simp only [Sk.size]
    rw [ihl h1, ihr h2]; omega

theorem mnL_single (y : Int) (hy : y < INF) : mnL [y] = y := by
  apply Int.le_antisymm
  · exact mnL_le [y] y (by simp)
  · exact mnL_ge [y] y (by omega) (fun v hv => by rw [List.mem_singleton.mp hv]; exact Int.le_refl _)

theorem mxL_single (y : Int) (hy : -INF < y) : mxL [y] = y := by
  apply Int.le_antisymm
  · exact mxL_le [y] y (by omega) (fun v hv => by rw [List.mem_singleton.mp hv]; exact Int.le_refl _)
  · exact mxL_ge [y] y (by simp)

theorem leaf_smx (nd : Nd) (y : Int) (hd : Desc nd [y]) (hr : InRange [y]) : nd.smx = -INF := by
  have hy := hr y (by simp)
  rw [hd.2.1]
  exact allEq_smx [y] (by rw [mnL_single y hy.2, mxL_single y hy.1])

theorem Inv.push_parts {nd : Nd} {tg : Tag} {l r : BT} {ys : List Int} (h : Inv (.node nd tg l r) ys)
    (hov : PushSafe (.node nd tg l r)) :
    ∃ xl xr, Inv (applyTag tg nd l) xl ∧ Inv (applyTag tg nd r) xr ∧ ys = xl ++ xr := by
  obtain ⟨hov1l, hov2l, hov1r, hov2r⟩ := hov
  cases h with
  | node nd tg l r xl xr ys hn hl hr =>
    obtain ⟨vy, hvy⟩ : ∃ v, v ∈ ys := by rw [hn.eq]; exact ys_ne tg nd xl xr hn.nel
    obtain ⟨cn1, cn2, cn3, cn4, cn5, cn6⟩ := Desc_cons nd ys vy hvy hn.ry hn.desc
    have hL := Inv.push_child (nd := nd) (tg := tg) hl hn.rngv (fun h0 w hw => hn.rnga h0 w (List.mem_append.mpr (Or.inl hw)))
      hov1l hov2l hn.capl cn1 cn2 cn3 cn4 cn6 cn5
    have hR := Inv.push_child (nd := nd) (tg := tg) hr hn.rngv (fun h0 w hw => hn.rnga h0 w (List.mem_append.mpr (Or.inr hw)))
      hov1r hov2r hn.capr cn1 cn2 cn3 cn4 cn6 cn5
    exact ⟨_, _, hL, hR, by rw [hn.eq, pend_append]⟩


theorem Inv.chmin (a b : Nat) (x : Int) (hx : -INF < x) :
    ∀ (t : BT) (lo hi : Nat) (ys : List Int), Inv t ys → Shape lo hi t.skel → chminSafe a b x t lo hi →
      Inv (chminBT a b x t lo hi) (rangeMin lo a b x ys)
  | .leaf nd, lo, hi, ys, h, hsh, _ => by
    cases h with
    | leaf nd y hd hr =>
      have hhi : hi = lo + 1 := hsh
      unfold chminBT
      by_cases hc : b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x
      · rw [if_pos hc]
        have : rangeMin lo a b x [y] = [y] := by
          by_cases hm : nd.mx ≤ x
          · apply rangeMin_small
            intro v hv
            rw [List.mem_singleton.mp hv]
            have := mxL_ge [y] y (by simp)
            have h1 : nd.mx = mxL [y] := hd.1
            omega
          · apply rangeMin_id
            intro i hi' ⟨h1, h2⟩
            simp at hi'
            omega
        rw [this]; exact Inv.leaf nd y hd hr
      · rw [if_neg hc]
        have hlt : x < nd.mx := by omega
        have hcov : ∀ i, i < [y].length → (a ≤ lo + i ∧ lo + i < b) := by
          intro i hi'; simp at hi'; omega
        rw [rangeMin_all lo a b x [y] hcov]
        have := (Inv.leaf nd y hd hr).capMax x (fun _ => by
          show nd.smx < x
          rw [leaf_smx nd y hd hr]; exact hx)
        simpa [capMaxBT, BT.nd, hlt] using this
  | .node nd tg l r, lo, hi, ys, h, hsh, hsafe => by
    unfold chminBT
    unfold chminSafe at hsafe
    have hlen : ys.length = hi - lo := by
      rw [h.size, BT.size_skel]; exact Shape.size hsh
    by_cases hc : b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x
    · rw [if_pos hc]
      have : rangeMin lo a b x ys = ys := by
        by_cases hm : nd.mx ≤ x
        · apply rangeMin_small
          intro v hv
          have := mxL_ge ys v hv
          have h1 : nd.mx = mxL ys := h.desc.1
          omega
        · apply rangeMin_id
          intro i hi' ⟨h1, h2⟩
          have : i < ys.length := hi'
          omega
      rw [this]; exact h
    · rw [if_neg hc]
      rw [if_neg hc] at hsafe
      by_cases hc2 : a ≤ lo ∧ hi ≤ b ∧ nd.smx < x
      · rw [if_pos hc2]
        have hlt : x < nd.mx := by omega
        have hcov : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b) := by
          intro i hi'; omega
        rw [rangeMin_all lo a b x ys hcov]
        have := h.capMax x (fun _ => hc2.2.2)
        exact this
      · rw [if_neg hc2]
        rw [if_neg hc2] at hsafe
        obtain ⟨hps, hsl, hsr⟩ := hsafe
        obtain ⟨xl, xr, hL, hR, hys⟩ := Inv.push_parts h hps
        obtain ⟨hlo, hshl, hshr⟩ := hsh
        have hshl' : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel := by rw [skel_applyTag]; exact hshl
        have hshr' : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel := by rw [skel_applyTag]; exact hshr
        have ihl := Inv.chmin a b x hx (applyTag tg nd l) lo ((lo + hi) / 2) xl hL hshl' hsl
        have ihr := Inv.chmin a b x hx (applyTag tg nd r) ((lo + hi) / 2) hi xr hR hshr' hsr
        have hxl : xl.length = (lo + hi) / 2 - lo := by
          rw [hL.size, BT.size_skel, hshl'.size] <;> try omega
        have := Inv.update ihl ihr nd noTag
        rw [hys, rangeMin_append, hxl]
        have e : lo + ((lo + hi) / 2 - lo) = (lo + hi) / 2 := by omega
        rw [e]
        exact this
termination_by t _ _ _ _ _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

end Proofs.BeatsModel
