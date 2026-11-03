import Proofs.BeatsCap
namespace Proofs.BeatsModel

theorem CapOk_neg (nd c : Nd) (a : Int) (h : CapOk nd c a) : CapOk (negNd nd) (negNd c) (-a) := by
  obtain ⟨h1, h2⟩ := h
  unfold CapOk smxA smnA at *
  refine ⟨?_, ?_⟩
  · intro hp
    have hp' : c.mn + a < nd.mn := by simp only [negNd] at hp; omega
    have := h2 hp'
    simp only [negNd]
    by_cases hq : c.smn = INF
    · simp [hq] at this ⊢; omega
    · simp [hq] at this ⊢; omega
  · intro hp
    have hp' : nd.mx < c.mx + a := by simp only [negNd] at hp; omega
    have := h1 hp'
    simp only [negNd]
    by_cases hq : c.smx = -INF
    · simp [hq] at this ⊢; omega
    · simp [hq] at this ⊢; omega

theorem negNd_negNd_p (c : Nd) : negNd (negNd c) = c := negNd_negNd c

theorem clamp_comm (u mx mn : Int) (h : mn ≤ mx) : max (min u mx) mn = min (max u mn) mx := by omega

/-- Dual of `capOk_max`. -/
theorem capOk_min (nd c : Nd) (a : Int) (xs ys zs : List Int) (hsub : ∀ w ∈ xs, w ∈ zs)
    (hdc : Desc c xs) (hrc : InRange xs) (v0 : Int) (hv0 : v0 ∈ xs)
    (hys : ys = ((zs.map (fun w => w + a)).map (fun w => min w nd.mx)).map (fun w => max w nd.mn))
    (hdn : Desc nd ys) (hrn : InRange ys) (vy : Int) (hvy : vy ∈ ys)
    (hra : ∀ w ∈ xs, -INF < w + a ∧ w + a < INF) (hcap : CapOk nd c a) (x : Int) (hs : x < nd.smn) (hlt : nd.mn < x) :
    CapOk (updMin nd x) c a := by
  have hrN : ∀ l : List Int, InRange l → InRange (l.map (fun v => -v)) := by
    intro l hl w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have := hl u hu; omega
  have hcons := (Desc_cons nd ys vy hvy hrn hdn).2.1
  have hys' : ys.map (fun v => -v) = (((zs.map (fun v => -v)).map (fun w => w + -a)).map (fun w => min w (negNd nd).mx)).map
      (fun w => max w (negNd nd).mn) := by
    rw [hys]
    simp only [List.map_map]
    apply List.map_congr_left
    intro z _
    simp only [Function.comp, negNd]
    have := clamp_comm (z + a) nd.mx nd.mn hcons
    omega
  have := capOk_max (negNd nd) (negNd c) (-a) (xs.map (fun v => -v)) (ys.map (fun v => -v)) (zs.map (fun v => -v))
    (fun w hw => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      exact List.mem_map.mpr ⟨u, hsub u hu, rfl⟩)
    (Desc_neg c xs hdc) (hrN xs hrc) (-v0) (List.mem_map.mpr ⟨_, hv0, rfl⟩) hys' (Desc_neg nd ys hdn) (hrN ys hrn)
    (-vy) (List.mem_map.mpr ⟨_, hvy, rfl⟩)
    (fun w hw => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have := hra u hu; omega)
    (CapOk_neg nd c a hcap) (-x) (by show -nd.smn < -x; omega) (by show -x < -nd.mn; omega)
  have h2 := CapOk_neg _ _ _ this
  have e : -(-a) = a := by omega
  rw [e, negNd_negNd] at h2
  exact h2

end Proofs.BeatsModel
