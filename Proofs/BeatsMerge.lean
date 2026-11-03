import Proofs.BeatsNeg
namespace Proofs.BeatsModel

theorem mxL_mono (xs zs : List Int) (h : ∀ v ∈ xs, v ∈ zs) : mxL xs ≤ mxL zs := by
  rcases mxL_cases xs with h1 | h1
  · rw [h1]; exact foldl_max_ge _ _
  · exact mxL_ge _ _ (h _ h1)

theorem mxL_append (xs ys : List Int) : mxL (xs ++ ys) = max (mxL xs) (mxL ys) := by
  have hx : -INF ≤ mxL xs := foldl_max_ge _ _
  apply Int.le_antisymm
  · apply mxL_le _ _ (Int.le_trans hx (Int.le_max_left _ _))
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact Int.le_trans (mxL_ge _ _ h) (Int.le_max_left _ _)
    · exact Int.le_trans (mxL_ge _ _ h) (Int.le_max_right _ _)
  · apply Int.max_le.mpr
    exact ⟨mxL_mono _ _ (fun v hv => List.mem_append.mpr (Or.inl hv)),
      mxL_mono _ _ (fun v hv => List.mem_append.mpr (Or.inr hv))⟩

theorem filter_all (xs : List Int) (p : Int → Bool) (h : ∀ v ∈ xs, p v = true) : xs.filter p = xs := by
  rw [List.filter_eq_self]; exact h

theorem filter_none (xs : List Int) (p : Int → Bool) (h : ∀ v ∈ xs, p v = false) : xs.filter p = [] := by
  rw [List.filter_eq_nil_iff]; intro v hv; simp [h v hv]

/-- Merge of the max side. -/
def mergeMax (a b : Nd) : Int × Int × Int :=
  if a.mx < b.mx then (b.mx, max a.mx b.smx, b.mc)
  else if b.mx < a.mx then (a.mx, max a.smx b.mx, a.mc)
  else (a.mx, max a.smx b.smx, a.mc + b.mc)

theorem merge_max_desc (a b : Nd) (xs ys : List Int) (ha : Desc a xs) (hb : Desc b ys) :
    (mergeMax a b).1 = mxL (xs ++ ys) ∧ (mergeMax a b).2.1 = smxL (xs ++ ys) ∧ (mergeMax a b).2.2 = cmxL (xs ++ ys) := by
  obtain ⟨a1, a2, a3, _⟩ := ha
  obtain ⟨b1, b2, b3, _⟩ := hb
  have hM := mxL_append xs ys
  unfold mergeMax
  rw [a1, a2, a3, b1, b2, b3]
  by_cases h1 : mxL xs < mxL ys
  · rw [if_pos h1]
    have hM' : mxL (xs ++ ys) = mxL ys := by rw [hM]; exact Int.max_eq_right (by omega)
    refine ⟨hM'.symm, ?_, ?_⟩
    · show max (mxL xs) (smxL ys) = smxL (xs ++ ys)
      unfold smxL
      rw [hM', List.filter_append, mxL_append, filter_all xs _ (fun v hv => by simpa using Int.lt_of_le_of_lt (mxL_ge xs v hv) h1)]
    · have hc : cmxL ys = cmxL (xs ++ ys) := by
        unfold cmxL
        have z : xs.countP (fun v => decide (v = mxL ys)) = 0 := List.countP_eq_zero.mpr (fun v hv => by
          have := mxL_ge xs v hv
          have h' : v ≠ mxL ys := by omega
          simpa using h')
        rw [hM', List.countP_append, z]
        simp
      show (cmxL ys : Int) = (cmxL (xs ++ ys) : Int)
      exact_mod_cast hc
  · rw [if_neg h1]
    by_cases h2 : mxL ys < mxL xs
    · rw [if_pos h2]
      have hM' : mxL (xs ++ ys) = mxL xs := by rw [hM]; exact Int.max_eq_left (by omega)
      refine ⟨hM'.symm, ?_, ?_⟩
      · show max (smxL xs) (mxL ys) = smxL (xs ++ ys)
        unfold smxL
        rw [hM', List.filter_append, mxL_append, filter_all ys _ (fun v hv => by simpa using Int.lt_of_le_of_lt (mxL_ge ys v hv) h2)]
      · have hc : cmxL xs = cmxL (xs ++ ys) := by
          unfold cmxL
          have z : ys.countP (fun v => decide (v = mxL xs)) = 0 := List.countP_eq_zero.mpr (fun v hv => by
            have := mxL_ge ys v hv
            have h' : v ≠ mxL xs := by omega
            simpa using h')
          rw [hM', List.countP_append, z]
          simp
        show (cmxL xs : Int) = (cmxL (xs ++ ys) : Int)
        exact_mod_cast hc
    · rw [if_neg h2]
      have heq : mxL xs = mxL ys := by omega
      have hM' : mxL (xs ++ ys) = mxL xs := by rw [hM]; exact Int.max_eq_left (by omega)
      refine ⟨hM'.symm, ?_, ?_⟩
      · show max (smxL xs) (smxL ys) = smxL (xs ++ ys)
        unfold smxL
        rw [hM', List.filter_append, mxL_append, ← heq]
      · have hc : cmxL xs + cmxL ys = cmxL (xs ++ ys) := by
          unfold cmxL
          rw [hM', List.countP_append, ← heq]
        show (cmxL xs : Int) + (cmxL ys : Int) = (cmxL (xs ++ ys) : Int)
        exact_mod_cast hc


/-- The merge of two child summaries (`SegmentTreeBeats::update`); the min side is the max side of the negated summaries. -/
def mergeNd (a b : Nd) : Nd :=
  let p := mergeMax a b
  let q := mergeMax (negNd a) (negNd b)
  { mx := p.1, smx := p.2.1, mc := p.2.2, mn := -q.1, smn := -q.2.1, mnc := q.2.2 }

theorem mergeNd_desc (a b : Nd) (xs ys : List Int) (ha : Desc a xs) (hb : Desc b ys) :
    Desc (mergeNd a b) (xs ++ ys) := by
  obtain ⟨p1, p2, p3⟩ := merge_max_desc a b xs ys ha hb
  obtain ⟨q1, q2, q3⟩ := merge_max_desc (negNd a) (negNd b) _ _ (Desc_neg a xs ha) (Desc_neg b ys hb)
  have e : xs.map (fun v => -v) ++ ys.map (fun v => -v) = (xs ++ ys).map (fun v => -v) := (List.map_append).symm
  rw [e] at q1 q2 q3
  rw [mxL_neg] at q1
  rw [smxL_neg] at q2
  rw [cmxL_neg] at q3
  refine ⟨p1, p2, p3, ?_, ?_, ?_⟩
  · show -(mergeMax (negNd a) (negNd b)).1 = _; omega
  · show -(mergeMax (negNd a) (negNd b)).2.1 = _; omega
  · show (mergeMax (negNd a) (negNd b)).2.2 = _; omega

end Proofs.BeatsModel
