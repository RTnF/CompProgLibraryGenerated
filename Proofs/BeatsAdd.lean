import Proofs.BeatsMerge
namespace Proofs.BeatsModel

def addNd (nd : Nd) (x : Int) : Nd :=
  { mx := nd.mx + x, smx := if nd.smx = -INF then nd.smx else nd.smx + x, mc := nd.mc,
    mn := nd.mn + x, smn := if nd.smn = INF then nd.smn else nd.smn + x, mnc := nd.mnc }

/-- For a nonempty list within range, shifting every element by `x` shifts the maximum. -/
theorem mxL_add (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hx : ∀ v ∈ xs, -INF ≤ v + x ∧ v + x ≤ INF) :
    mxL (xs.map (fun v => v + x)) = mxL xs + x := by
  have hm := mxL_mem xs v0 hv0 (fun w hw => (hr w hw).1)
  apply Int.le_antisymm
  · apply mxL_le _ _ (by have := (hx _ hm).1; omega)
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have := mxL_ge xs u hu; omega
  · exact mxL_ge _ _ (List.mem_map.mpr ⟨_, hm, rfl⟩)

theorem mnL_add (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hx : ∀ v ∈ xs, -INF ≤ v + x ∧ v + x ≤ INF) :
    mnL (xs.map (fun v => v + x)) = mnL xs + x := by
  have hm := mnL_mem xs v0 hv0 (fun w hw => (hr w hw).2)
  apply Int.le_antisymm
  · exact mnL_le _ _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
  · apply mnL_ge _ _ (by have := (hx _ hm).2; omega)
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have := mnL_le xs u hu; omega

theorem smxL_add (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hx : ∀ v ∈ xs, -INF ≤ v + x ∧ v + x ≤ INF) :
    smxL (xs.map (fun v => v + x)) = if smxL xs = -INF then smxL xs else smxL xs + x := by
  have hM := mxL_add xs x v0 hv0 hr hx
  have e : (xs.map (fun v => v + x)).filter (fun v => decide (v < mxL (xs.map (fun v => v + x)))) =
      (xs.filter (fun v => decide (v < mxL xs))).map (fun v => v + x) := by
    rw [hM, List.filter_map]
    congr 1
    apply List.filter_congr
    intro v _
    simp only [Function.comp, decide_eq_decide]; omega
  unfold smxL
  rw [e]
  by_cases hne : (xs.filter (fun v => decide (v < mxL xs))) = []
  · rw [hne]; simp [mxL_nil]
  · obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
    have hr' : InRange (xs.filter (fun v => decide (v < mxL xs))) := fun u hu => hr u (List.mem_filter.mp hu).1
    rw [mxL_add _ x w hw hr' (fun u hu => hx u (List.mem_filter.mp hu).1)]
    have hne' : mxL (xs.filter (fun v => decide (v < mxL xs))) ≠ -INF := by
      have := mxL_mem _ w hw (fun u hu => (hr' u hu).1)
      have := (hr' _ this).1; omega
    rw [if_neg hne']


theorem smnL_add (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hx : ∀ v ∈ xs, -INF ≤ v + x ∧ v + x ≤ INF) :
    smnL (xs.map (fun v => v + x)) = if smnL xs = INF then smnL xs else smnL xs + x := by
  have hM := mnL_add xs x v0 hv0 hr hx
  have e : (xs.map (fun v => v + x)).filter (fun v => decide (mnL (xs.map (fun v => v + x)) < v)) =
      (xs.filter (fun v => decide (mnL xs < v))).map (fun v => v + x) := by
    rw [hM, List.filter_map]
    congr 1
    apply List.filter_congr
    intro v _
    simp only [Function.comp, decide_eq_decide]; omega
  unfold smnL
  rw [e]
  by_cases hne : (xs.filter (fun v => decide (mnL xs < v))) = []
  · rw [hne]; simp [mnL_nil]
  · obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
    have hr' : InRange (xs.filter (fun v => decide (mnL xs < v))) := fun u hu => hr u (List.mem_filter.mp hu).1
    rw [mnL_add _ x w hw hr' (fun u hu => hx u (List.mem_filter.mp hu).1)]
    have hne' : mnL (xs.filter (fun v => decide (mnL xs < v))) ≠ INF := by
      have := mnL_mem _ w hw (fun u hu => (hr' u hu).2)
      have := (hr' _ this).2; omega
    rw [if_neg hne']

theorem cmxL_add (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hx : ∀ v ∈ xs, -INF ≤ v + x ∧ v + x ≤ INF) :
    cmxL (xs.map (fun v => v + x)) = cmxL xs := by
  unfold cmxL
  rw [mxL_add xs x v0 hv0 hr hx, List.countP_map]
  apply List.countP_congr
  intro v _
  simp only [Function.comp, decide_eq_true_eq]; omega

theorem cmnL_add (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hx : ∀ v ∈ xs, -INF ≤ v + x ∧ v + x ≤ INF) :
    cmnL (xs.map (fun v => v + x)) = cmnL xs := by
  unfold cmnL
  rw [mnL_add xs x v0 hv0 hr hx, List.countP_map]
  apply List.countP_congr
  intro v _
  simp only [Function.comp, decide_eq_true_eq]; omega

/-- `add_all` keeps the summary of a nonempty list. -/
theorem addNd_desc (nd : Nd) (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs)
    (hx : ∀ v ∈ xs, -INF ≤ v + x ∧ v + x ≤ INF) (hd : Desc nd xs) : Desc (addNd nd x) (xs.map (fun v => v + x)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show nd.mx + x = _; rw [mxL_add xs x v0 hv0 hr hx, h1]
  · show (if nd.smx = -INF then nd.smx else nd.smx + x) = _; rw [smxL_add xs x v0 hv0 hr hx, h2]
  · show nd.mc = _; rw [cmxL_add xs x v0 hv0 hr hx, h3]
  · show nd.mn + x = _; rw [mnL_add xs x v0 hv0 hr hx, h4]
  · show (if nd.smn = INF then nd.smn else nd.smn + x) = _; rw [smnL_add xs x v0 hv0 hr hx, h5]
  · show nd.mnc = _; rw [cmnL_add xs x v0 hv0 hr hx, h6]

end Proofs.BeatsModel
