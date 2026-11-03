import Proofs.BeatsMax
namespace Proofs.BeatsModel

theorem mnL_le_INF (xs : List Int) : mnL xs ≤ INF := foldl_min_le _ _

theorem mxL_neg (xs : List Int) : mxL (xs.map (fun v => -v)) = - mnL xs := by
  have hI := mnL_le_INF xs
  rcases mnL_cases xs with h | h
  · apply Int.le_antisymm
    · apply mxL_le _ _ (by omega)
      intro w hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have := mnL_le xs u hu; omega
    · have := foldl_max_ge (xs.map (fun v => -v)) (-INF); unfold mxL; omega
  · apply Int.le_antisymm
    · apply mxL_le _ _ (by omega)
      intro w hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have := mnL_le xs u hu; omega
    · exact mxL_ge _ _ (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem mnL_neg (xs : List Int) : mnL (xs.map (fun v => -v)) = - mxL xs := by
  have hI : -INF ≤ mxL xs := foldl_max_ge _ _
  rcases mxL_cases xs with h | h
  · apply Int.le_antisymm
    · have := foldl_min_le (xs.map (fun v => -v)) INF; unfold mnL; omega
    · apply mnL_ge _ _ (by omega)
      intro w hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have := mxL_ge xs u hu; omega
  · apply Int.le_antisymm
    · exact mnL_le _ _ (List.mem_map.mpr ⟨_, h, rfl⟩)
    · apply mnL_ge _ _ (by omega)
      intro w hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have := mxL_ge xs u hu; omega

theorem smxL_neg (xs : List Int) : smxL (xs.map (fun v => -v)) = - smnL xs := by
  have e : (xs.map (fun v => -v)).filter (fun v => decide (v < mxL (xs.map (fun v => -v)))) =
      (xs.filter (fun v => decide (mnL xs < v))).map (fun v => -v) := by
    rw [mxL_neg, List.filter_map]
    congr 1
    apply List.filter_congr
    intro v _
    simp only [Function.comp, decide_eq_decide]; omega
  unfold smxL smnL
  rw [e, mxL_neg]

theorem smnL_neg (xs : List Int) : smnL (xs.map (fun v => -v)) = - smxL xs := by
  have e : (xs.map (fun v => -v)).filter (fun v => decide (mnL (xs.map (fun v => -v)) < v)) =
      (xs.filter (fun v => decide (v < mxL xs))).map (fun v => -v) := by
    rw [mnL_neg, List.filter_map]
    congr 1
    apply List.filter_congr
    intro v _
    simp only [Function.comp, decide_eq_decide]; omega
  unfold smxL smnL
  rw [e, mnL_neg]

theorem cmxL_neg (xs : List Int) : cmxL (xs.map (fun v => -v)) = cmnL xs := by
  unfold cmxL cmnL
  rw [mxL_neg, List.countP_map]
  apply List.countP_congr
  intro v _
  simp only [Function.comp, decide_eq_true_eq]; omega

theorem cmnL_neg (xs : List Int) : cmnL (xs.map (fun v => -v)) = cmxL xs := by
  unfold cmxL cmnL
  rw [mnL_neg, List.countP_map]
  apply List.countP_congr
  intro v _
  simp only [Function.comp, decide_eq_true_eq]; omega


def negNd (nd : Nd) : Nd := { mx := -nd.mn, smx := -nd.smn, mc := nd.mnc, mn := -nd.mx, smn := -nd.smx, mnc := nd.mc }

theorem negNd_negNd (nd : Nd) : negNd (negNd nd) = nd := by
  cases nd; simp [negNd]

theorem Desc_neg (nd : Nd) (xs : List Int) (h : Desc nd xs) : Desc (negNd nd) (xs.map (fun v => -v)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show -nd.mn = _; rw [mxL_neg, h4]
  · show -nd.smn = _; rw [smxL_neg, h5]
  · show nd.mnc = _; rw [cmxL_neg, h6]
  · show -nd.mx = _; rw [mnL_neg, h1]
  · show -nd.smx = _; rw [smnL_neg, h2]
  · show nd.mc = _; rw [cmnL_neg, h3]

theorem map_neg_neg (xs : List Int) : (xs.map (fun v => -v)).map (fun v => -v) = xs := by
  rw [List.map_map]
  have : ((fun v : Int => -v) ∘ fun v => -v) = id := by funext v; simp
  rw [this, List.map_id]

def updMin (nd : Nd) (x : Int) : Nd := negNd (updMax (negNd nd) (-x))

theorem updMin_desc (nd : Nd) (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hd : Desc nd xs)
    (hs : x < nd.smn) (hlt : nd.mn < x) : Desc (updMin nd x) (xs.map (fun v => max v x)) := by
  have hr' : InRange (xs.map (fun v => -v)) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have := hr u hu; omega
  have h1 := updMax_desc (negNd nd) (xs.map (fun v => -v)) (-x) (-v0) (List.mem_map.mpr ⟨_, hv0, rfl⟩) hr' (Desc_neg nd xs hd)
    (by show -nd.smn < -x; omega) (by show -x < -nd.mn; omega)
  have h2 := Desc_neg _ _ h1
  have e : ((xs.map (fun v => -v)).map (fun v => min v (-x))).map (fun v => -v) = xs.map (fun v => max v x) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    simp only [Function.comp]; omega
  rw [e] at h2
  exact h2

end Proofs.BeatsModel
