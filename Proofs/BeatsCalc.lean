import Proofs.BeatsChmax
namespace Proofs.BeatsModel

theorem Desc_unique {a b : Nd} {xs : List Int} (ha : Desc a xs) (hb : Desc b xs) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  cases a; cases b
  simp only [] at *
  simp [a1, a2, a3, a4, a5, a6] at *
  simp [b1, b2, b3, b4, b5, b6]

/-- The maximum of the elements at positions `[a, b)` of the array held at `[lo, ..)` (`-INF` if none). -/
def rangeMaxOf (lo a b : Nat) (ys : List Int) : Int :=
  mxL (ys.mapIdx (fun i v => if a ≤ lo + i ∧ lo + i < b then v else -INF))

theorem rangeMaxOf_append (lo a b : Nat) (xs ys : List Int) :
    rangeMaxOf lo a b (xs ++ ys) = max (rangeMaxOf lo a b xs) (rangeMaxOf (lo + xs.length) a b ys) := by
  unfold rangeMaxOf
  rw [List.mapIdx_append, mxL_append]
  congr 2
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx, Nat.add_assoc, Nat.add_comm i xs.length]

theorem mxL_negInf (ys : List Int) (h : ∀ v ∈ ys, v = -INF) : mxL ys = -INF := by
  apply Int.le_antisymm
  · exact mxL_le ys (-INF) (Int.le_refl _) (fun v hv => Int.le_of_eq (h v hv))
  · exact foldl_max_ge _ _

theorem rangeMaxOf_none (lo a b : Nat) (ys : List Int) (h : ∀ i, i < ys.length → ¬(a ≤ lo + i ∧ lo + i < b)) :
    rangeMaxOf lo a b ys = -INF := by
  unfold rangeMaxOf
  apply mxL_negInf
  intro v hv
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hv
  rw [← e]
  simp only [List.getElem_mapIdx]
  rw [if_neg (h i (by simpa using hi))]

theorem rangeMaxOf_all (lo a b : Nat) (ys : List Int) (h : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b)) :
    rangeMaxOf lo a b ys = mxL ys := by
  unfold rangeMaxOf
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx]
    rw [if_pos (h i (by simpa using h1))]

/-- `calc_max(a, b)`: the pushes along the way rebuild the tree; the answer is the maximum of the covered nodes. -/
def calcMaxBT (a b : Nat) : BT → Nat → Nat → BT × Int
  | .leaf nd, lo, hi => if b ≤ lo ∨ hi ≤ a then (.leaf nd, -INF) else (.leaf nd, nd.mx)
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a then (.node nd tg l r, -INF)
    else if a ≤ lo ∧ hi ≤ b then (.node nd tg l r, nd.mx)
    else
      let p := calcMaxBT a b (applyTag tg nd l) lo ((lo + hi) / 2)
      let q := calcMaxBT a b (applyTag tg nd r) ((lo + hi) / 2) hi
      (.node nd noTag p.1 q.1, max p.2 q.2)
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

def calcSafe (a b : Nat) : BT → Nat → Nat → Prop
  | .leaf _, _, _ => True
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a then True
    else if a ≤ lo ∧ hi ≤ b then True
    else PushSafe (.node nd tg l r) ∧ calcSafe a b (applyTag tg nd l) lo ((lo + hi) / 2) ∧
      calcSafe a b (applyTag tg nd r) ((lo + hi) / 2) hi
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)


theorem Inv.calcMax (a b : Nat) :
    ∀ (t : BT) (lo hi : Nat) (ys : List Int), Inv t ys → Shape lo hi t.skel → calcSafe a b t lo hi →
      Inv (calcMaxBT a b t lo hi).1 ys ∧ (calcMaxBT a b t lo hi).2 = rangeMaxOf lo a b ys
  | .leaf nd, lo, hi, ys, h, hsh, _ => by
    cases h with
    | leaf nd y hd hr =>
      have hhi : hi = lo + 1 := hsh
      unfold calcMaxBT
      by_cases hc : b ≤ lo ∨ hi ≤ a
      · rw [if_pos hc]
        refine ⟨Inv.leaf nd y hd hr, ?_⟩
        symm; apply rangeMaxOf_none
        intro i hi' ⟨h1, h2⟩
        simp at hi'; omega
      · rw [if_neg hc]
        refine ⟨Inv.leaf nd y hd hr, ?_⟩
        rw [rangeMaxOf_all lo a b [y] (by intro i hi'; simp at hi'; omega)]
        exact hd.1
  | .node nd tg l r, lo, hi, ys, h, hsh, hsafe => by
    unfold calcMaxBT
    unfold calcSafe at hsafe
    have hlen : ys.length = hi - lo := by
      rw [h.size, BT.size_skel]; exact Shape.size hsh
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc]
      refine ⟨h, ?_⟩
      symm; apply rangeMaxOf_none
      intro i hi' ⟨h1, h2⟩
      have : i < ys.length := hi'
      omega
    · rw [if_neg hc]
      rw [if_neg hc] at hsafe
      by_cases hc2 : a ≤ lo ∧ hi ≤ b
      · rw [if_pos hc2]
        refine ⟨h, ?_⟩
        rw [rangeMaxOf_all lo a b ys (by intro i hi'; omega)]
        exact h.desc.1
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
          obtain ⟨ihl, vl⟩ := Inv.calcMax a b (applyTag tg nd l) lo ((lo + hi) / 2) xl' hL hshl' hsl
          obtain ⟨ihr, vr⟩ := Inv.calcMax a b (applyTag tg nd r) ((lo + hi) / 2) hi xr' hR hshr' hsr
          have hxl : xl'.length = (lo + hi) / 2 - lo := by
            rw [hL.size, BT.size_skel, hshl'.size] <;> try omega
          have dl : (calcMaxBT a b (applyTag tg nd l) lo ((lo + hi) / 2)).1.nd = (applyTag tg nd l).nd :=
            Desc_unique ihl.desc hL.desc
          have dr : (calcMaxBT a b (applyTag tg nd r) ((lo + hi) / 2) hi).1.nd = (applyTag tg nd r).nd :=
            Desc_unique ihr.desc hR.desc
          refine ⟨?_, ?_⟩
          · refine Inv.node nd noTag _ _ xl' xr' ys ?_ ihl ihr
            rw [dl, dr]; exact hn'
          · show max _ _ = _
            rw [vl, vr, hys, rangeMaxOf_append, hxl]
            have e : lo + ((lo + hi) / 2 - lo) = (lo + hi) / 2 := by omega
            rw [e]
termination_by t _ _ _ _ _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

end Proofs.BeatsModel
