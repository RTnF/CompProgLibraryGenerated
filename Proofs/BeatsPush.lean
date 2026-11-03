import Proofs.BeatsAll
namespace Proofs.BeatsModel

theorem map_min_id (xs : List Int) (M : Int) (h : ∀ v ∈ xs, v ≤ M) : xs.map (fun v => min v M) = xs :=
  (List.map_congr_left (fun v hv => Int.min_eq_left (h v hv))).trans (List.map_id _)

theorem map_max_id (xs : List Int) (m : Int) (h : ∀ v ∈ xs, m ≤ v) : xs.map (fun v => max v m) = xs :=
  (List.map_congr_left (fun v hv => Int.max_eq_left (h v hv))).trans (List.map_id _)

/-- `if (x < max_v) update_node_max(x)`. -/
def capMax (c : Nd) (x : Int) : Nd := if x < c.mx then updMax c x else c
/-- `if (min_v < x) update_node_min(x)`. -/
def capMin (c : Nd) (x : Int) : Nd := if c.mn < x then updMin c x else c

theorem capMax_desc (c : Nd) (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hd : Desc c xs)
    (hs : x < c.mx → c.smx < x) : Desc (capMax c x) (xs.map (fun v => min v x)) := by
  unfold capMax
  by_cases hc : x < c.mx
  · rw [if_pos hc]; exact updMax_desc c xs x v0 hv0 hr hd (hs hc) hc
  · rw [if_neg hc, map_min_id]
    · exact hd
    · intro v hv
      have := mxL_ge xs v hv
      have h1 : c.mx = mxL xs := hd.1
      omega

theorem capMin_desc (c : Nd) (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hd : Desc c xs)
    (hs : c.mn < x → x < c.smn) : Desc (capMin c x) (xs.map (fun v => max v x)) := by
  unfold capMin
  by_cases hc : c.mn < x
  · rw [if_pos hc]; exact updMin_desc c xs x v0 hv0 hr hd (hs hc) hc
  · rw [if_neg hc, map_max_id]
    · exact hd
    · intro v hv
      have := mnL_le xs v hv
      have h1 : c.mn = mnL xs := hd.2.2.2.1
      omega

/-- `push` for one child that is not set: add the pending `ladd`, then cap by the parent's maximum and minimum. -/
def pushAdd (c : Nd) (a pmx pmn : Int) : Nd := capMin (capMax (addNd c a) pmx) pmn

theorem pushAdd_desc (c : Nd) (xs : List Int) (a pmx pmn v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs)
    (hx : ∀ v ∈ xs, -INF < v + a ∧ v + a < INF) (hd : Desc c xs) (hpm : -INF < pmx)
    -- the beats invariant: capping touches only maxima, and then only minima
    (hs1 : pmx < c.mx + a → (if c.smx = -INF then c.smx else c.smx + a) < pmx)
    (hs2 : ∀ c2 : Nd, Desc c2 ((xs.map (fun v => v + a)).map (fun v => min v pmx)) → c2.mn < pmn → pmn < c2.smn) :
    Desc (pushAdd c a pmx pmn) (((xs.map (fun v => v + a)).map (fun v => min v pmx)).map (fun v => max v pmn)) := by
  have hr1 : InRange (xs.map (fun v => v + a)) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    exact hx u hu
  have hv1 : v0 + a ∈ xs.map (fun v => v + a) := List.mem_map.mpr ⟨_, hv0, rfl⟩
  have d1 := addNd_desc c xs a v0 hv0 hr (fun v hv => ⟨Int.le_of_lt (hx v hv).1, Int.le_of_lt (hx v hv).2⟩) hd
  have hr2 : InRange ((xs.map (fun v => v + a)).map (fun v => min v pmx)) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have := hr1 u hu
    exact ⟨Int.lt_min.mpr ⟨this.1, hpm⟩, Int.lt_of_le_of_lt (Int.min_le_left _ _) this.2⟩
  have hv2 : min (v0 + a) pmx ∈ (xs.map (fun v => v + a)).map (fun v => min v pmx) := List.mem_map.mpr ⟨_, hv1, rfl⟩
  have d2 := capMax_desc (addNd c a) _ pmx (v0 + a) hv1 hr1 d1 hs1
  exact capMin_desc _ _ pmn _ hv2 hr2 d2 (fun h => hs2 _ d2 h)

end Proofs.BeatsModel
