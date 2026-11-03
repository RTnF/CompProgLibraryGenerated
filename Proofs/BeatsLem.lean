import Proofs.BeatsCons
namespace Proofs.BeatsModel

theorem smxL_mem (xs : List Int) (h : smxL xs ≠ -INF) : smxL xs ∈ xs := by
  unfold smxL at h ⊢
  rcases mxL_cases (xs.filter (fun v => decide (v < mxL xs))) with h' | h'
  · exact absurd h' h
  · exact (List.mem_filter.mp h').1

theorem smnL_mem (xs : List Int) (h : smnL xs ≠ INF) : smnL xs ∈ xs := by
  unfold smnL at h ⊢
  rcases mnL_cases (xs.filter (fun v => decide (mnL xs < v))) with h' | h'
  · exact absurd h' h
  · exact (List.mem_filter.mp h').1

/-- If the minimum equals the maximum, the second extremes are the sentinels. -/
theorem allEq_smn (xs : List Int) (h : mnL xs = mxL xs) : smnL xs = INF := by
  unfold smnL
  rw [filter_none _ _ (fun v hv => by
    have := mxL_ge xs v hv; simp; omega)]
  rfl

theorem allEq_smx (xs : List Int) (h : mnL xs = mxL xs) : smxL xs = -INF := by
  unfold smxL
  rw [filter_none _ _ (fun v hv => by
    have := mnL_le xs v hv; simp; omega)]
  rfl

/-- `smn = INF` means all elements are equal. -/
theorem smn_inf_eq (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (h : smnL xs = INF) : mnL xs = mxL xs := by
  have hm := mxL_mem xs v0 hv0 (fun w hw => (hr w hw).1)
  refine Classical.byContradiction (fun hne => ?_)
  have hlt : mnL xs < mxL xs := by have := mnL_le_mxL xs v0 hv0; omega
  have hmem : mxL xs ∈ xs.filter (fun v => decide (mnL xs < v)) := List.mem_filter.mpr ⟨hm, by simpa using hlt⟩
  have := mnL_le _ _ hmem
  unfold smnL at h
  have := (hr _ hm).2
  omega

theorem smx_ninf_eq (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (h : smxL xs = -INF) : mnL xs = mxL xs := by
  have hm := mnL_mem xs v0 hv0 (fun w hw => (hr w hw).2)
  refine Classical.byContradiction (fun hne => ?_)
  have hlt : mnL xs < mxL xs := by have := mnL_le_mxL xs v0 hv0; omega
  have hmem : mnL xs ∈ xs.filter (fun v => decide (v < mxL xs)) := List.mem_filter.mpr ⟨hm, by simpa using hlt⟩
  have := mxL_ge _ _ hmem
  unfold smxL at h
  have := (hr _ hm).1
  omega

end Proofs.BeatsModel
