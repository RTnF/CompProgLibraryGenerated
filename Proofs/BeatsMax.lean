import Proofs.BeatsMin
namespace Proofs.BeatsModel

def updMax (nd : Nd) (x : Int) : Nd :=
  if nd.mx = nd.mn then { nd with mx := x, mn := x }
  else if nd.mx = nd.smn then { nd with mx := x, smn := x }
  else { nd with mx := x }

theorem smxL_ge (xs : List Int) : -INF ≤ smxL xs := foldl_max_ge _ _

theorem mxL_le_mx (xs : List Int) (v : Int) (hv : v ∈ xs) : v ≤ mxL xs := mxL_ge xs v hv

/-- Elements below the maximum are at most the second maximum. -/
theorem le_smxL (xs : List Int) (v : Int) (hv : v ∈ xs) (h : v < mxL xs) : v ≤ smxL xs :=
  mxL_ge _ _ (List.mem_filter.mpr ⟨hv, by simpa using h⟩)

theorem mnL_lt_mxL_or (xs : List Int) (v : Int) (hv : v ∈ xs) : mnL xs ≤ v ∧ v ≤ mxL xs :=
  ⟨mnL_le xs v hv, mxL_ge xs v hv⟩

/-- Case 1: all elements equal. -/
theorem chmin_case1 (xs : List Int) (x : Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hmm : mxL xs = mnL xs)
    (hs : smxL xs < x) (hlt : x < mxL xs) :
    mnL (xs.map (fun v => min v x)) = x ∧ smnL (xs.map (fun v => min v x)) = smnL xs ∧
      cmnL (xs.map (fun v => min v x)) = cmnL xs := by
  have hx : -INF < x := by have := smxL_ge xs; omega
  have hall : ∀ v ∈ xs, v = mxL xs := fun v hv => by
    have := mnL_lt_mxL_or xs v hv; omega
  have hmap : ∀ w ∈ xs.map (fun v => min v x), w = x := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    rw [hall u hu]; exact Int.min_eq_right (by omega)
  have hne : x ∈ xs.map (fun v => min v x) := by
    have : min v0 x ∈ xs.map (fun v => min v x) := List.mem_map.mpr ⟨_, hv0, rfl⟩
    rwa [hmap _ this] at this
  have e1 : mnL (xs.map (fun v => min v x)) = x := by
    apply Int.le_antisymm
    · exact mnL_le _ _ hne
    · exact mnL_ge _ _ (by have := hr v0 hv0; have := hall v0 hv0; omega) (fun w hw => Int.le_of_eq (hmap w hw).symm)
  refine ⟨e1, ?_, ?_⟩
  · have a : (xs.map (fun v => min v x)).filter (fun v => decide (mnL (xs.map (fun v => min v x)) < v)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w hw
      rw [e1, hmap w hw]; simp
    have b : xs.filter (fun v => decide (mnL xs < v)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w hw
      have := hall w hw; simp; omega
    unfold smnL; rw [a, b]
  · unfold cmnL
    rw [e1]
    have h1 : (xs.map (fun v => min v x)).countP (fun v => decide (v = x)) = (xs.map (fun v => min v x)).length :=
      List.countP_eq_length.mpr (fun w hw => by simp [hmap w hw])
    have h2 : xs.countP (fun v => decide (v = mnL xs)) = xs.length :=
      List.countP_eq_length.mpr (fun w hw => by have := hall w hw; simp; omega)
    rw [h1, h2, List.length_map]

/-- The elements strictly above the minimum, mapped, keep the relation to the minimum. -/
theorem filter_map_gt (xs : List Int) (x m : Int) (hx : m < x) :
    (xs.map (fun v => min v x)).filter (fun v => decide (m < v)) = (xs.filter (fun v => decide (m < v))).map (fun v => min v x) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro v _
  simp only [Function.comp, decide_eq_decide]
  constructor
  · intro h
    have := Int.min_le_left v x
    omega
  · intro h; exact Int.lt_min.mpr ⟨h, hx⟩

/-- Case 3: `smn < mx`, so the minimum side is untouched. -/
theorem chmin_case3 (xs : List Int) (x : Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hne : mxL xs ≠ mnL xs)
    (hsm : mxL xs ≠ smnL xs) (hs : smxL xs < x) (hlt : x < mxL xs) :
    mnL (xs.map (fun v => min v x)) = mnL xs ∧ smnL (xs.map (fun v => min v x)) = smnL xs ∧
      cmnL (xs.map (fun v => min v x)) = cmnL xs := by
  have hx : -INF < x := by have := smxL_ge xs; omega
  have hrI : ∀ w ∈ xs, w < INF := fun w hw => (hr w hw).2
  have hmn : mnL xs < x := by
    have hmx : mxL xs ∈ xs := mxL_mem xs v0 hv0 (fun w hw => (hr w hw).1)
    have hmnx : mnL xs < mxL xs := by have := mnL_le xs _ hmx; omega
    have hmnm : mnL xs ∈ xs := mnL_mem xs v0 hv0 hrI
    have := le_smxL xs _ hmnm hmnx
    omega
  have e1 : mnL (xs.map (fun v => min v x)) = mnL xs := mnL_map_min xs x v0 hv0 hrI hmn
  -- the second minimum is a member below the maximum
  have hmx : mxL xs ∈ xs := mxL_mem xs v0 hv0 (fun w hw => (hr w hw).1)
  have hmnx : mnL xs < mxL xs := by have := mnL_le xs _ hmx; omega
  have hys : mxL xs ∈ xs.filter (fun v => decide (mnL xs < v)) := List.mem_filter.mpr ⟨hmx, by simpa using hmnx⟩
  have hsmem : smnL xs ∈ xs.filter (fun v => decide (mnL xs < v)) :=
    mnL_mem _ _ hys (fun w hw => hrI w (List.mem_filter.mp hw).1)
  have hsmle : smnL xs ≤ mxL xs := mnL_le _ _ hys
  have hsmlt : smnL xs < mxL xs := by omega
  have hsx : smnL xs ≤ smxL xs := le_smxL xs _ (List.mem_filter.mp hsmem).1 hsmlt
  have hmnsm : mnL xs < smnL xs := by have := (List.mem_filter.mp hsmem).2; simpa using this
  refine ⟨e1, ?_, ?_⟩
  · unfold smnL
    rw [e1, filter_map_gt xs x _ hmn]
    exact mnL_map_min _ x _ hsmem (fun w hw => hrI w (List.mem_filter.mp hw).1) (show smnL xs < x by omega)
  · unfold cmnL
    rw [e1, List.countP_map]
    apply List.countP_congr
    intro v hv
    simp only [Function.comp, decide_eq_true_eq]
    constructor
    · intro h
      by_cases hvx : v < x
      · rw [Int.min_eq_left (by omega)] at h; exact h
      · rw [Int.min_eq_right (by omega)] at h; omega
    · intro h; rw [Int.min_eq_left (by omega)]; exact h


/-- Case 2: exactly two distinct values (`mx = smn`). -/
theorem chmin_case2 (xs : List Int) (x : Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hne : mxL xs ≠ mnL xs)
    (hsm : mxL xs = smnL xs) (hs : smxL xs < x) (hlt : x < mxL xs) :
    mnL (xs.map (fun v => min v x)) = mnL xs ∧ smnL (xs.map (fun v => min v x)) = x ∧
      cmnL (xs.map (fun v => min v x)) = cmnL xs := by
  have hx : -INF < x := by have := smxL_ge xs; omega
  have hrI : ∀ w ∈ xs, w < INF := fun w hw => (hr w hw).2
  have hmx : mxL xs ∈ xs := mxL_mem xs v0 hv0 (fun w hw => (hr w hw).1)
  have hmnx : mnL xs < mxL xs := by have := mnL_le xs _ hmx; omega
  have hmn : mnL xs < x := by
    have hmnm : mnL xs ∈ xs := mnL_mem xs v0 hv0 hrI
    have := le_smxL xs _ hmnm hmnx
    omega
  have e1 : mnL (xs.map (fun v => min v x)) = mnL xs := mnL_map_min xs x v0 hv0 hrI hmn
  have hys : mxL xs ∈ xs.filter (fun v => decide (mnL xs < v)) := List.mem_filter.mpr ⟨hmx, by simpa using hmnx⟩
  have hall : ∀ w ∈ xs.filter (fun v => decide (mnL xs < v)), w = mxL xs := by
    intro w hw
    have h1 := List.mem_filter.mp hw
    have h2 : smnL xs ≤ w := mnL_le _ _ hw
    have h3 := mxL_ge xs w h1.1
    omega
  refine ⟨e1, ?_, ?_⟩
  · unfold smnL
    rw [e1, filter_map_gt xs x _ hmn]
    have hmem : x ∈ (xs.filter (fun v => decide (mnL xs < v))).map (fun v => min v x) := by
      have : min (mxL xs) x ∈ (xs.filter (fun v => decide (mnL xs < v))).map (fun v => min v x) :=
        List.mem_map.mpr ⟨_, hys, rfl⟩
      rwa [Int.min_eq_right (by omega)] at this
    have hall' : ∀ w ∈ (xs.filter (fun v => decide (mnL xs < v))).map (fun v => min v x), w = x := by
      intro w hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      rw [hall u hu]; exact Int.min_eq_right (by omega)
    apply Int.le_antisymm
    · exact mnL_le _ _ hmem
    · exact mnL_ge _ x (by have := hrI _ hmx; omega) (fun w hw => Int.le_of_eq (hall' w hw).symm)
  · unfold cmnL
    rw [e1, List.countP_map]
    apply List.countP_congr
    intro v hv
    simp only [Function.comp, decide_eq_true_eq]
    constructor
    · intro h
      by_cases hvx : v < x
      · rw [Int.min_eq_left (by omega)] at h; exact h
      · rw [Int.min_eq_right (by omega)] at h; omega
    · intro h; rw [Int.min_eq_left (by omega)]; exact h

/-- `update_node_max` keeps the summary: if `x` lies strictly between the second maximum and the maximum, the summary of the
list with every element capped at `x` is `updMax`. -/
theorem updMax_desc (nd : Nd) (xs : List Int) (x v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hd : Desc nd xs)
    (hs : nd.smx < x) (hlt : x < nd.mx) : Desc (updMax nd x) (xs.map (fun v => min v x)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  have hs' : smxL xs < x := by rw [← h2]; exact hs
  have hlt' : x < mxL xs := by rw [← h1]; exact hlt
  have hx : -INF < x := by have := smxL_ge xs; omega
  have hM := mxL_map_min xs x hx hlt'
  have hS := smxL_map_min xs x hx hlt' hs'
  have hC := cmxL_map_min xs x hx hlt' hs'
  unfold updMax
  by_cases hc1 : nd.mx = nd.mn
  · rw [if_pos hc1]
    obtain ⟨a, b, c⟩ := chmin_case1 xs x v0 hv0 hr (by rw [← h1, ← h4]; exact hc1) hs' hlt'
    exact ⟨hM.symm, by rw [hS]; exact h2, by rw [hC]; exact h3, a.symm, by rw [b]; exact h5, by rw [c]; exact h6⟩
  · rw [if_neg hc1]
    have hne : mxL xs ≠ mnL xs := by rw [← h1, ← h4]; exact hc1
    by_cases hc2 : nd.mx = nd.smn
    · rw [if_pos hc2]
      obtain ⟨a, b, c⟩ := chmin_case2 xs x v0 hv0 hr hne (by rw [← h1, ← h5]; exact hc2) hs' hlt'
      exact ⟨hM.symm, by rw [hS]; exact h2, by rw [hC]; exact h3, by rw [a]; exact h4, b.symm, by rw [c]; exact h6⟩
    · rw [if_neg hc2]
      obtain ⟨a, b, c⟩ := chmin_case3 xs x v0 hv0 hr hne (by rw [← h1, ← h5]; exact hc2) hs' hlt'
      exact ⟨hM.symm, by rw [hS]; exact h2, by rw [hC]; exact h3, by rw [a]; exact h4, by rw [b]; exact h5, by rw [c]; exact h6⟩

end Proofs.BeatsModel
