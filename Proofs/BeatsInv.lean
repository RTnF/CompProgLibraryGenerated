import Proofs.BeatsNode
namespace Proofs.BeatsModel

/-- Second maximum/minimum of a child after the pending addition `a` (the sentinels stay put). -/
def smxA (c : Nd) (a : Int) : Int := if c.smx = -INF then c.smx else c.smx + a
def smnA (c : Nd) (a : Int) : Int := if c.smn = INF then c.smn else c.smn + a

/-- The cap conditions of the beats invariant between a node and a child. -/
def CapOk (nd c : Nd) (a : Int) : Prop :=
  (nd.mx < c.mx + a → smxA c a ≤ nd.smx) ∧ (c.mn + a < nd.mn → nd.smn ≤ smnA c a)

theorem mn_le_smx (c : Nd) (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hd : Desc c xs)
    (hlt : c.mn < c.mx) : -INF < c.mn ∧ c.mn ≤ c.smx := by
  have hm := mnL_mem xs v0 hv0 (fun w hw => (hr w hw).2)
  refine ⟨?_, ?_⟩
  · rw [hd.2.2.2.1]; exact (hr _ hm).1
  · rw [hd.2.1, hd.2.2.2.1]
    exact le_smxL xs _ hm (by rw [← hd.2.2.2.1, ← hd.1]; exact hlt)

/-- `hs2` of `pushAdd_desc` follows from `CapOk`, when the node's summary is consistent (`mn ≤ mx`, `smx < mx`, `mn < smn`)
and the child, after the addition, stays inside `(-INF, INF)`. -/
theorem hs2_of_cap (nd c : Nd) (a : Int) (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs)
    (hx : ∀ v ∈ xs, -INF < v + a ∧ v + a < INF) (hd : Desc c xs) (hcap : CapOk nd c a)
    (hsm : nd.smx < nd.mx) (hns : nd.mn < nd.smn) (hle : nd.mn ≤ nd.mx) (hmnsmx : nd.smx ≠ -INF → nd.mn ≤ nd.smx) (hnn : nd.mn < INF) (hpm : -INF < nd.mx) :
    ∀ c2 : Nd, Desc c2 ((xs.map (fun v => v + a)).map (fun v => min v nd.mx)) → c2.mn < nd.mn → nd.mn < c2.smn := by
  intro c2 hc2 hlt
  have d1 := addNd_desc c xs a v0 hv0 hr (fun v hv => ⟨Int.le_of_lt (hx v hv).1, Int.le_of_lt (hx v hv).2⟩) hd
  have hr1 : InRange (xs.map (fun v => v + a)) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    exact hx u hu
  have hv1 : v0 + a ∈ xs.map (fun v => v + a) := List.mem_map.mpr ⟨_, hv0, rfl⟩
  have hc2' := capMax_desc (addNd c a) _ nd.mx (v0 + a) hv1 hr1 d1 (by
    intro hlt'
    have := hcap.1
    have h1 : nd.mx < c.mx + a := hlt'
    have := (hcap.1 h1)
    show (if c.smx = -INF then c.smx else c.smx + a) < nd.mx
    have : smxA c a ≤ nd.smx := hcap.1 h1
    unfold smxA at this
    omega)
  -- c2 and capMax agree on the summary of the same list, hence field by field
  have hmn : c2.mn = (capMax (addNd c a) nd.mx).mn := by rw [hc2.2.2.2.1, hc2'.2.2.2.1]
  have hsn : c2.smn = (capMax (addNd c a) nd.mx).smn := by rw [hc2.2.2.2.2.1, hc2'.2.2.2.2.1]
  rw [hsn]; rw [hmn] at hlt
  unfold capMax at hlt ⊢
  by_cases hc : nd.mx < (addNd c a).mx
  · rw [if_pos hc] at hlt ⊢
    unfold updMax at hlt ⊢
    by_cases h1 : (addNd c a).mx = (addNd c a).mn
    · rw [if_pos h1] at hlt ⊢
      -- all equal: the new minimum is `nd.mx`, so `c2.mn < nd.mn` forces `nd.mx < nd.mn`, impossible
      simp only [] at hlt ⊢
      omega
    · rw [if_neg h1] at hlt ⊢
      by_cases h2 : (addNd c a).mx = (addNd c a).smn
      · rw [if_pos h2] at hlt ⊢
        simp only [] at hlt ⊢
        -- two values: `smn` becomes `nd.mx`; the child has a second maximum, so `nd.smx ≥ ...`
        have hcs := hcap.1 hc
        have hcl : c.mn < c.mx := by
          have : (addNd c a).mx ≠ (addNd c a).mn := h1
          have h1' : c.mx + a ≠ c.mn + a := this
          have hle1 : c.mn ≤ c.mx := by
            rw [hd.1, hd.2.2.2.1]; exact Int.le_trans (mnL_le xs v0 hv0) (mxL_ge xs v0 hv0)
          omega
        obtain ⟨hg, hh⟩ := mn_le_smx c xs v0 hv0 hr hd hcl
        have hmnm : c.mn ∈ xs := by rw [hd.2.2.2.1]; exact mnL_mem xs v0 hv0 (fun w hw => (hr w hw).2)
        have hmnx := (hx _ hmnm).1
        have hsne : c.smx ≠ -INF := by omega
        have hsA : smxA c a = c.smx + a := by unfold smxA; rw [if_neg hsne]
        have hmn1 : (addNd c a).mn = c.mn + a := rfl
        have hndsmx : nd.smx ≠ -INF := by omega
        have := hmnsmx hndsmx
        omega
      · rw [if_neg h2] at hlt ⊢
        simp only [] at hlt ⊢
        have hcc := hcap.2 (show c.mn + a < nd.mn from hlt)
        show nd.mn < smnA c a
        omega
  · rw [if_neg hc] at hlt ⊢
    have hcc := hcap.2 (show c.mn + a < nd.mn from hlt)
    show nd.mn < smnA c a
    omega

end Proofs.BeatsModel
