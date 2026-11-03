import Proofs.BeatsInv
namespace Proofs.BeatsModel

theorem smxL_lt (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) : smxL xs < mxL xs := by
  have hm := mxL_mem xs v0 hv0 (fun w hw => (hr w hw).1)
  have hmr := (hr _ hm).1
  unfold smxL
  rcases mxL_cases (xs.filter (fun v => decide (v < mxL xs))) with h | h
  · rw [h]; omega
  · have := (List.mem_filter.mp h).2; simpa using this

theorem mnL_lt_smnL (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) : mnL xs < smnL xs := by
  have hm := mnL_mem xs v0 hv0 (fun w hw => (hr w hw).2)
  have hmr := (hr _ hm).2
  unfold smnL
  rcases mnL_cases (xs.filter (fun v => decide (mnL xs < v))) with h | h
  · rw [h]; omega
  · have := (List.mem_filter.mp h).2; simpa using this

theorem mnL_le_mxL (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) : mnL xs ≤ mxL xs :=
  Int.le_trans (mnL_le xs v0 hv0) (mxL_ge xs v0 hv0)

/-- The summary of a nonempty in-range list is consistent. -/
theorem Desc_cons (nd : Nd) (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs) (hd : Desc nd xs) :
    nd.smx < nd.mx ∧ nd.mn ≤ nd.mx ∧ (nd.smx ≠ -INF → nd.mn ≤ nd.smx) ∧ nd.mn < nd.smn ∧ -INF < nd.mx ∧ nd.mn < INF := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  have hmx := mxL_mem xs v0 hv0 (fun w hw => (hr w hw).1)
  have hmn := mnL_mem xs v0 hv0 (fun w hw => (hr w hw).2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, h2]; exact smxL_lt xs v0 hv0 hr
  · rw [h1, h4]; exact mnL_le_mxL xs v0 hv0
  · intro hne
    rw [h2] at hne
    rw [h4, h2]
    -- the second maximum is a member below the maximum, hence at least the minimum
    unfold smxL at hne ⊢
    rcases mxL_cases (xs.filter (fun v => decide (v < mxL xs))) with h | h
    · exact absurd h hne
    · exact mnL_le xs _ (List.mem_filter.mp h).1
  · rw [h4, h5]; exact mnL_lt_smnL xs v0 hv0 hr
  · rw [h1]; exact (hr _ hmx).1
  · rw [h4]; exact (hr _ hmn).2

end Proofs.BeatsModel
