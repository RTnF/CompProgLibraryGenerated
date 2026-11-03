import Proofs.BeatsCalc
namespace Proofs.BeatsModel

theorem mnL_append (xs ys : List Int) : mnL (xs ++ ys) = min (mnL xs) (mnL ys) := by
  have hx : mnL xs ≤ INF := foldl_min_le _ _
  apply Int.le_antisymm
  · refine Int.le_min.mpr ⟨?_, ?_⟩
    · rcases mnL_cases xs with h | h
      · rw [h]; exact mnL_le_INF _
      · exact mnL_le _ _ (List.mem_append.mpr (Or.inl h))
    · rcases mnL_cases ys with h | h
      · rw [h]; exact mnL_le_INF _
      · exact mnL_le _ _ (List.mem_append.mpr (Or.inr h))
  · apply mnL_ge _ _ (Int.le_trans (Int.min_le_left _ _) hx)
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact Int.le_trans (Int.min_le_left _ _) (mnL_le _ _ h)
    · exact Int.le_trans (Int.min_le_right _ _) (mnL_le _ _ h)

theorem mnL_inf (ys : List Int) (h : ∀ v ∈ ys, v = INF) : mnL ys = INF := by
  apply Int.le_antisymm
  · exact foldl_min_le _ _
  · exact mnL_ge ys INF (Int.le_refl _) (fun v hv => Int.le_of_eq (h v hv).symm)

/-- The maximum of the elements at positions `[a, b)` of the array held at `[lo, ..)` (`INF` if none). -/
def rangeMinOf (lo a b : Nat) (ys : List Int) : Int :=
  mnL (ys.mapIdx (fun i v => if a ≤ lo + i ∧ lo + i < b then v else INF))

theorem rangeMinOf_append (lo a b : Nat) (xs ys : List Int) :
    rangeMinOf lo a b (xs ++ ys) = min (rangeMinOf lo a b xs) (rangeMinOf (lo + xs.length) a b ys) := by
  unfold rangeMinOf
  rw [List.mapIdx_append, mnL_append]
  congr 2
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx, Nat.add_assoc, Nat.add_comm i xs.length]

theorem rangeMinOf_none (lo a b : Nat) (ys : List Int) (h : ∀ i, i < ys.length → ¬(a ≤ lo + i ∧ lo + i < b)) :
    rangeMinOf lo a b ys = INF := by
  unfold rangeMinOf
  apply mnL_inf
  intro v hv
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hv
  rw [← e]
  simp only [List.getElem_mapIdx]
  rw [if_neg (h i (by simpa using hi))]

theorem rangeMinOf_all (lo a b : Nat) (ys : List Int) (h : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b)) :
    rangeMinOf lo a b ys = mnL ys := by
  unfold rangeMinOf
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx]
    rw [if_pos (h i (by simpa using h1))]

/-- `calc_max(a, b)`: the pushes along the way rebuild the tree; the answer is the maximum of the covered nodes. -/
def calcMinBT (a b : Nat) : BT → Nat → Nat → BT × Int
  | .leaf nd, lo, hi => if b ≤ lo ∨ hi ≤ a then (.leaf nd, INF) else (.leaf nd, nd.mn)
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a then (.node nd tg l r, INF)
    else if a ≤ lo ∧ hi ≤ b then (.node nd tg l r, nd.mn)
    else
      let p := calcMinBT a b (applyTag tg nd l) lo ((lo + hi) / 2)
      let q := calcMinBT a b (applyTag tg nd r) ((lo + hi) / 2) hi
      (.node nd noTag p.1 q.1, min p.2 q.2)
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

theorem Inv.calcMin (a b : Nat) :
    ∀ (t : BT) (lo hi : Nat) (ys : List Int), Inv t ys → Shape lo hi t.skel → calcSafe a b t lo hi →
      Inv (calcMinBT a b t lo hi).1 ys ∧ (calcMinBT a b t lo hi).2 = rangeMinOf lo a b ys
  | .leaf nd, lo, hi, ys, h, hsh, _ => by
    cases h with
    | leaf nd y hd hr =>
      have hhi : hi = lo + 1 := hsh
      unfold calcMinBT
      by_cases hc : b ≤ lo ∨ hi ≤ a
      · rw [if_pos hc]
        refine ⟨Inv.leaf nd y hd hr, ?_⟩
        symm; apply rangeMinOf_none
        intro i hi' ⟨h1, h2⟩
        simp at hi'; omega
      · rw [if_neg hc]
        refine ⟨Inv.leaf nd y hd hr, ?_⟩
        rw [rangeMinOf_all lo a b [y] (by intro i hi'; simp at hi'; omega)]
        exact hd.2.2.2.1
  | .node nd tg l r, lo, hi, ys, h, hsh, hsafe => by
    unfold calcMinBT
    unfold calcSafe at hsafe
    have hlen : ys.length = hi - lo := by
      rw [h.size, BT.size_skel]; exact Shape.size hsh
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc]
      refine ⟨h, ?_⟩
      symm; apply rangeMinOf_none
      intro i hi' ⟨h1, h2⟩
      have : i < ys.length := hi'
      omega
    · rw [if_neg hc]
      rw [if_neg hc] at hsafe
      by_cases hc2 : a ≤ lo ∧ hi ≤ b
      · rw [if_pos hc2]
        refine ⟨h, ?_⟩
        rw [rangeMinOf_all lo a b ys (by intro i hi'; omega)]
        exact h.desc.2.2.2.1
      · rw [if_neg hc2]
        rw [if_neg hc2] at hsafe
        obtain ⟨hps, hsl, hsr⟩ := hsafe
        obtain ⟨hov1l, hov2l, hov1r, hov2r⟩ := hps
        obtain ⟨xl, xr, hL, hR, hys⟩ := Inv.push_parts h ⟨hov1l, hov2l, hov1r, hov2r⟩
        have hp := Inv.push h hov1l hov2l hov1r hov2r
        simp only [pushBT] at hp
        cases hp with
        | node nd' tg' l' r' xl' xr' ys' hn' hl' hr' =>
          have e1 : xl' = xl := by rw [hl'.eq_arr, hL.eq_arr]
          have e2 : xr' = xr := by rw [hr'.eq_arr, hR.eq_arr]
          subst e1; subst e2
          obtain ⟨hlo, hshl, hshr⟩ := hsh
          have hshl' : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel := by rw [skel_applyTag]; exact hshl
          have hshr' : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel := by rw [skel_applyTag]; exact hshr
          obtain ⟨ihl, vl⟩ := Inv.calcMin a b (applyTag tg nd l) lo ((lo + hi) / 2) xl' hL hshl' hsl
          obtain ⟨ihr, vr⟩ := Inv.calcMin a b (applyTag tg nd r) ((lo + hi) / 2) hi xr' hR hshr' hsr
          have hxl : xl'.length = (lo + hi) / 2 - lo := by
            rw [hL.size, BT.size_skel, hshl'.size] <;> try omega
          have dl : (calcMinBT a b (applyTag tg nd l) lo ((lo + hi) / 2)).1.nd = (applyTag tg nd l).nd :=
            Desc_unique ihl.desc hL.desc
          have dr : (calcMinBT a b (applyTag tg nd r) ((lo + hi) / 2) hi).1.nd = (applyTag tg nd r).nd :=
            Desc_unique ihr.desc hR.desc
          refine ⟨?_, ?_⟩
          · refine Inv.node nd noTag _ _ xl' xr' ys ?_ ihl ihr
            rw [dl, dr]; exact hn'
          · show min _ _ = _
            rw [vl, vr, hys, rangeMinOf_append, hxl]
            have e : lo + ((lo + hi) / 2 - lo) = (lo + hi) / 2 := by omega
            rw [e]
termination_by t _ _ _ _ _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)


end Proofs.BeatsModel
