import Proofs.BeatsLem
namespace Proofs.BeatsModel

theorem updMax_mx (nd : Nd) (x : Int) : (updMax nd x).mx = x := by
  unfold updMax; split <;> try rfl
  split <;> rfl
theorem updMax_smx (nd : Nd) (x : Int) : (updMax nd x).smx = nd.smx := by
  unfold updMax; split <;> try rfl
  split <;> rfl
theorem updMax_mn (nd : Nd) (x : Int) : (updMax nd x).mn = if nd.mx = nd.mn then x else nd.mn := by
  unfold updMax; split
  · rename_i h; simp [h]
  · rename_i h; split <;> simp [h]
theorem updMax_smn (nd : Nd) (x : Int) :
    (updMax nd x).smn = if nd.mx = nd.mn then nd.smn else if nd.mx = nd.smn then x else nd.smn := by
  unfold updMax; split
  · rename_i h; simp [h]
  · rename_i h; split
    · rename_i h2; simp [h, h2]
    · rename_i h2; simp [h, h2]

/-- The first half of `CapOk` survives `update_node_max` on the node. -/
theorem capOk_max (nd c : Nd) (a : Int) (xs ys : List Int) (zs : List Int) (hsub : ∀ w ∈ xs, w ∈ zs)
    (hdc : Desc c xs) (hrc : InRange xs) (v0 : Int) (hv0 : v0 ∈ xs)
    (hys : ys = ((zs.map (fun w => w + a)).map (fun w => min w nd.mx)).map (fun w => max w nd.mn))
    (hdn : Desc nd ys) (hrn : InRange ys) (vy : Int) (hvy : vy ∈ ys)
    (hra : ∀ w ∈ xs, -INF < w + a ∧ w + a < INF) (hcap : CapOk nd c a) (x : Int) (hs : nd.smx < x) (hlt : x < nd.mx) :
    CapOk (updMax nd x) c a := by
  obtain ⟨cn1, cn2, cn3, cn4, cn5, cn6⟩ := Desc_cons nd ys vy hvy hrn hdn
  obtain ⟨cc1, cc2, cc3, cc4, cc5, cc6⟩ := Desc_cons c xs v0 hv0 hrc hdc
  have hnsmx : -INF ≤ nd.smx := by rw [hdn.2.1]; exact smxL_ge ys
  unfold CapOk
  rw [updMax_mx, updMax_smx, updMax_mn, updMax_smn]
  refine ⟨?_, ?_⟩
  · intro hp
    -- the second maximum of the child after the addition
    by_cases hinf : c.smx = -INF
    · have : smxA c a = -INF := by unfold smxA; rw [if_pos hinf]; exact hinf
      omega
    · have hmem : c.smx ∈ xs := by rw [hdc.2.1]; exact smxL_mem xs (by rw [← hdc.2.1]; exact hinf)
      have hsA : smxA c a = c.smx + a := by unfold smxA; rw [if_neg hinf]
      have hera := hra _ hmem
      -- it lies below the node's maximum
      have hbelow : c.smx + a < nd.mx := by
        by_cases hq : nd.mx < c.mx + a
        · have := hcap.1 hq; omega
        · omega
      by_cases hge : nd.mn ≤ c.smx + a
      · -- it is an element of the true array below the maximum
        have hin : c.smx + a ∈ ys := by
          rw [hys]
          have h1 : c.smx + a ∈ zs.map (fun w => w + a) := List.mem_map.mpr ⟨_, hsub _ hmem, rfl⟩
          have h2 : min (c.smx + a) nd.mx ∈ (zs.map (fun w => w + a)).map (fun w => min w nd.mx) := List.mem_map.mpr ⟨_, h1, rfl⟩
          have h3 : max (min (c.smx + a) nd.mx) nd.mn ∈
              ((zs.map (fun w => w + a)).map (fun w => min w nd.mx)).map (fun w => max w nd.mn) := List.mem_map.mpr ⟨_, h2, rfl⟩
          rwa [Int.min_eq_left (by omega), Int.max_eq_left hge] at h3
        have := le_smxL ys _ hin (by rw [← hdn.1]; omega)
        rw [← hdn.2.1] at this
        omega
      · by_cases hmm : nd.mx = nd.mn
        · exfalso
          have hmnc : c.mn ≤ c.smx := (mn_le_smx c xs v0 hv0 hrc hdc (by
            have : c.smx ≠ -INF := hinf
            have := cc3 this
            have : c.smx < c.mx := cc1
            omega)).2
          have hp2 := hcap.2 (by omega)
          have hsn : nd.smn = INF := by rw [hdn.2.2.2.2.1]; exact allEq_smn ys (by rw [← hdn.1, ← hdn.2.2.2.1]; omega)
          have hq : c.smn = INF := by
            have hge2 : INF ≤ smnA c a := by omega
            by_cases hq : c.smn = INF
            · exact hq
            · have hm2 : c.smn ∈ xs := by rw [hdc.2.2.2.2.1]; exact smnL_mem xs (by rw [← hdc.2.2.2.2.1]; exact hq)
              have := hra _ hm2
              have hsA2 : smnA c a = c.smn + a := by unfold smnA; rw [if_neg hq]
              omega
          have := smn_inf_eq xs v0 hv0 hrc (by rw [← hdc.2.2.2.2.1]; exact hq)
          have := allEq_smx xs this
          rw [← hdc.2.1] at this
          exact hinf this
        · have hlt2 : nd.mn < nd.mx := by omega
          have := (mn_le_smx nd ys vy hvy hrn hdn hlt2).2
          omega
  · intro hp
    by_cases hmm : nd.mx = nd.mn
    · rw [if_pos hmm] at hp ⊢
      have := hcap.2 (by omega)
      exact this
    · rw [if_neg hmm] at hp ⊢
      have := hcap.2 hp
      by_cases h2 : nd.mx = nd.smn
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; exact this

end Proofs.BeatsModel
