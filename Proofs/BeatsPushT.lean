import Proofs.BeatsTree
namespace Proofs.BeatsModel

theorem addBT_nd (x : Int) (c : BT) : (addBT x c).nd = addNd c.nd x := by cases c <;> rfl

/-- Apply a node's pending tag to one child. -/
def applyTag (tg : Tag) (nd : Nd) (c : BT) : BT :=
  match tg.lval with
  | some v => setBT v c
  | none => capMinBT nd.mn (capMaxBT nd.mx (addBT tg.ladd c))

theorem Inv.push_child {nd : Nd} {tg : Tag} {xc : List Int} {c : BT} (hc : Inv c xc)
    (hrv : ∀ v, tg.lval = some v → -INF < v ∧ v < INF)
    (hra : tg.lval = none → ∀ w ∈ xc, -INF < w + tg.ladd ∧ w + tg.ladd < INF)
    (hov1 : tg.lval = none → ∀ v, c.lval = some v → -INF < v + tg.ladd ∧ v + tg.ladd < INF)
    (hov2 : tg.lval = none → c.lval = none → ∀ w ∈ c.kids, -INF < w + (c.ladd + tg.ladd) ∧ w + (c.ladd + tg.ladd) < INF)
    (hcap : tg.lval = none → CapOk nd c.nd tg.ladd)
    (hlt : nd.smx < nd.mx) (hle : nd.mn ≤ nd.mx) (hmnsmx : nd.smx ≠ -INF → nd.mn ≤ nd.smx) (hns : nd.mn < nd.smn)
    (hnn : nd.mn < INF) (hpm : -INF < nd.mx) :
    Inv (applyTag tg nd c) (pend tg nd xc) := by
  unfold applyTag pend
  cases hl : tg.lval with
  | some v =>
    have := Inv.set hc v (hrv v hl)
    have e : xc.map (fun _ => v) = List.replicate xc.length v := by
      apply List.eq_replicate_iff.mpr; simp
    simp only [hl]
    rw [e]; exact this
  | none =>
    have h0 := hra hl
    have hcap' := hcap hl
    -- after the addition
    have i1 := Inv.add hc tg.ladd h0 (hov1 hl) (hov2 hl)
    have s1 : nd.mx < (addBT tg.ladd c).nd.mx → (addBT tg.ladd c).nd.smx < nd.mx := by
      intro hp
      rw [addBT_nd] at hp
      have hp' : nd.mx < c.nd.mx + tg.ladd := hp
      have := hcap'.1 hp'
      have e : (addBT tg.ladd c).nd.smx = smxA c.nd tg.ladd := by rw [addBT_nd]; rfl
      rw [e]; omega
    have i2 := i1.capMax nd.mx s1
    have s2 : (capMaxBT nd.mx (addBT tg.ladd c)).nd.mn < nd.mn → nd.mn < (capMaxBT nd.mx (addBT tg.ladd c)).nd.smn := by
      intro hp
      obtain ⟨v0, hv0⟩ := List.exists_mem_of_ne_nil _ hc.ne
      have hs2 := hs2_of_cap nd c.nd tg.ladd xc v0 hv0 hc.range h0 hc.desc hcap' hlt hns hle hmnsmx hnn hpm
      exact hs2 _ i2.desc hp
    have i3 := i2.capMin nd.mn s2
    simp only [hl]
    exact i3


/-- `push` of an internal node: apply the pending tag to both children and clear it. -/
def pushBT : BT → BT
  | .leaf nd => .leaf nd
  | .node nd tg l r => .node nd noTag (applyTag tg nd l) (applyTag tg nd r)

theorem applyTag_nd_range (tg : Tag) (nd : Nd) (c : BT) : True := trivial

theorem Inv.push {nd : Nd} {tg : Tag} {l r : BT} {ys : List Int} (h : Inv (.node nd tg l r) ys)
    (hov1l : tg.lval = none → ∀ v, l.lval = some v → -INF < v + tg.ladd ∧ v + tg.ladd < INF)
    (hov2l : tg.lval = none → l.lval = none → ∀ w ∈ l.kids, -INF < w + (l.ladd + tg.ladd) ∧ w + (l.ladd + tg.ladd) < INF)
    (hov1r : tg.lval = none → ∀ v, r.lval = some v → -INF < v + tg.ladd ∧ v + tg.ladd < INF)
    (hov2r : tg.lval = none → r.lval = none → ∀ w ∈ r.kids, -INF < w + (r.ladd + tg.ladd) ∧ w + (r.ladd + tg.ladd) < INF) :
    Inv (pushBT (.node nd tg l r)) ys := by
  cases h with
  | node nd tg l r xl xr ys hn hl hr =>
    obtain ⟨vy, hvy⟩ : ∃ v, v ∈ ys := by rw [hn.eq]; exact ys_ne tg nd xl xr hn.nel
    obtain ⟨cn1, cn2, cn3, cn4, cn5, cn6⟩ := Desc_cons nd ys vy hvy hn.ry hn.desc
    have hL := Inv.push_child (nd := nd) (tg := tg) hl hn.rngv (fun h0 w hw => hn.rnga h0 w (List.mem_append.mpr (Or.inl hw)))
      hov1l hov2l hn.capl cn1 cn2 cn3 cn4 cn6 cn5
    have hR := Inv.push_child (nd := nd) (tg := tg) hr hn.rngv (fun h0 w hw => hn.rnga h0 w (List.mem_append.mpr (Or.inr hw)))
      hov1r hov2r hn.capr cn1 cn2 cn3 cn4 cn6 cn5
    have hys : ys = pend tg nd xl ++ pend tg nd xr := by rw [hn.eq, pend_append]
    have hsub1 : ∀ w ∈ pend tg nd xl, w ∈ ys := fun w hw => by rw [hys]; exact List.mem_append.mpr (Or.inl hw)
    have hsub2 : ∀ w ∈ pend tg nd xr, w ∈ ys := fun w hw => by rw [hys]; exact List.mem_append.mpr (Or.inr hw)
    simp only [pushBT]
    refine Inv.node nd noTag _ _ (pend tg nd xl) (pend tg nd xr) ys ?_ hL hR
    refine ⟨hn.desc, ?_, hL.desc, hR.desc, hL.ne, hR.ne, hL.range, hR.range, hn.ry, ?_, ?_, ?_, ?_⟩
    · rw [← hys]; exact (pend_noTag nd ys hn.desc).symm
    · intro v hv; simp [noTag] at hv
    · intro _ w hw
      have : w ∈ ys := by
        rcases List.mem_append.mp hw with h | h
        · exact hsub1 w h
        · exact hsub2 w h
      have := hn.ry w this
      simpa [noTag] using this
    · intro _
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · exfalso
        have h1 : (applyTag tg nd l).nd.mx = mxL (pend tg nd xl) := hL.desc.1
        have h2 : mxL (pend tg nd xl) ≤ mxL ys := mxL_mono _ _ hsub1
        have h3 : nd.mx = mxL ys := hn.desc.1
        simp only [noTag] at hp
        omega
      · exfalso
        have h1 : (applyTag tg nd l).nd.mn = mnL (pend tg nd xl) := hL.desc.2.2.2.1
        have h2 : mnL ys ≤ mnL (pend tg nd xl) := by
          have := mnL_cases (pend tg nd xl)
          rcases this with h | h
          · rw [h]; exact mnL_le_INF _
          · exact mnL_le _ _ (hsub1 _ h)
        have h3 : nd.mn = mnL ys := hn.desc.2.2.2.1
        simp only [noTag] at hp
        omega
    · intro _
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · exfalso
        have h1 : (applyTag tg nd r).nd.mx = mxL (pend tg nd xr) := hR.desc.1
        have h2 : mxL (pend tg nd xr) ≤ mxL ys := mxL_mono _ _ hsub2
        have h3 : nd.mx = mxL ys := hn.desc.1
        simp only [noTag] at hp
        omega
      · exfalso
        have h1 : (applyTag tg nd r).nd.mn = mnL (pend tg nd xr) := hR.desc.2.2.2.1
        have h2 : mnL ys ≤ mnL (pend tg nd xr) := by
          have := mnL_cases (pend tg nd xr)
          rcases this with h | h
          · rw [h]; exact mnL_le_INF _
          · exact mnL_le _ _ (hsub2 _ h)
        have h3 : nd.mn = mnL ys := hn.desc.2.2.2.1
        simp only [noTag] at hp
        omega

end Proofs.BeatsModel
