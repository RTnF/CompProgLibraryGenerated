import Proofs.BeatsSetRange
namespace Proofs.BeatsModel

theorem rangeMap_fix (f : Int → Int) (lo a b : Nat) (ys : List Int) (h : ∀ v ∈ ys, f v = v) : rangeMap f lo a b ys = ys := by
  unfold rangeMap
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx]
    split
    · exact h _ (List.getElem_mem _)
    · rfl

theorem leaf_smn (nd : Nd) (y : Int) (hd : Desc nd [y]) (hr : InRange [y]) : nd.smn = INF := by
  have hy := hr y (by simp)
  rw [hd.2.2.2.2.1]
  exact allEq_smn [y] (by rw [mnL_single y hy.2, mxL_single y hy.1])

def chmaxBT (a b : Nat) (x : Int) : BT → Nat → Nat → BT
  | .leaf nd, lo, hi => if b ≤ lo ∨ hi ≤ a ∨ x ≤ nd.mn then .leaf nd else .leaf (updMin nd x)
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a ∨ x ≤ nd.mn then .node nd tg l r
    else if a ≤ lo ∧ hi ≤ b ∧ x < nd.smn then capMinBT x (.node nd tg l r)
    else updateBT (.node nd noTag (chmaxBT a b x (applyTag tg nd l) lo ((lo + hi) / 2))
      (chmaxBT a b x (applyTag tg nd r) ((lo + hi) / 2) hi))
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

def chmaxSafe (a b : Nat) (x : Int) : BT → Nat → Nat → Prop
  | .leaf _, _, _ => True
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a ∨ x ≤ nd.mn then True
    else if a ≤ lo ∧ hi ≤ b ∧ x < nd.smn then True
    else PushSafe (.node nd tg l r) ∧ chmaxSafe a b x (applyTag tg nd l) lo ((lo + hi) / 2) ∧
      chmaxSafe a b x (applyTag tg nd r) ((lo + hi) / 2) hi
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

theorem Inv.chmax (a b : Nat) (x : Int) (hx : x < INF) :
    ∀ (t : BT) (lo hi : Nat) (ys : List Int), Inv t ys → Shape lo hi t.skel → chmaxSafe a b x t lo hi →
      Inv (chmaxBT a b x t lo hi) (rangeMap (fun v => max v x) lo a b ys)
  | .leaf nd, lo, hi, ys, h, hsh, _ => by
    cases h with
    | leaf nd y hd hr =>
      have hhi : hi = lo + 1 := hsh
      unfold chmaxBT
      by_cases hc : b ≤ lo ∨ hi ≤ a ∨ x ≤ nd.mn
      · rw [if_pos hc]
        have : rangeMap (fun v => max v x) lo a b [y] = [y] := by
          by_cases hm : x ≤ nd.mn
          · apply rangeMap_fix
            intro v hv
            rw [List.mem_singleton.mp hv]
            have := mnL_le [y] y (by simp)
            have h1 : nd.mn = mnL [y] := hd.2.2.2.1
            exact Int.max_eq_left (by omega)
          · apply rangeMap_id
            intro i hi' ⟨h1, h2⟩
            simp at hi'
            omega
        rw [this]; exact Inv.leaf nd y hd hr
      · rw [if_neg hc]
        have hlt : nd.mn < x := by omega
        have hcov : ∀ i, i < [y].length → (a ≤ lo + i ∧ lo + i < b) := by
          intro i hi'; simp at hi'; omega
        rw [rangeMap_all _ lo a b [y] hcov]
        have := (Inv.leaf nd y hd hr).capMin x (fun _ => by
          show x < nd.smn
          rw [leaf_smn nd y hd hr]; exact hx)
        simpa [capMinBT, BT.nd, hlt] using this
  | .node nd tg l r, lo, hi, ys, h, hsh, hsafe => by
    unfold chmaxBT
    unfold chmaxSafe at hsafe
    have hlen : ys.length = hi - lo := by
      rw [h.size, BT.size_skel]; exact Shape.size hsh
    by_cases hc : b ≤ lo ∨ hi ≤ a ∨ x ≤ nd.mn
    · rw [if_pos hc]
      have : rangeMap (fun v => max v x) lo a b ys = ys := by
        by_cases hm : x ≤ nd.mn
        · apply rangeMap_fix
          intro v hv
          have := mnL_le ys v hv
          have h1 : nd.mn = mnL ys := h.desc.2.2.2.1
          exact Int.max_eq_left (by omega)
        · apply rangeMap_id
          intro i hi' ⟨h1, h2⟩
          have : i < ys.length := hi'
          omega
      rw [this]; exact h
    · rw [if_neg hc]
      rw [if_neg hc] at hsafe
      by_cases hc2 : a ≤ lo ∧ hi ≤ b ∧ x < nd.smn
      · rw [if_pos hc2]
        have hlt : nd.mn < x := by omega
        have hcov : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b) := by
          intro i hi'; omega
        rw [rangeMap_all _ lo a b ys hcov]
        exact h.capMin x (fun _ => hc2.2.2)
      · rw [if_neg hc2]
        rw [if_neg hc2] at hsafe
        obtain ⟨hps, hsl, hsr⟩ := hsafe
        obtain ⟨xl, xr, hL, hR, hys⟩ := Inv.push_parts h hps
        obtain ⟨hlo, hshl, hshr⟩ := hsh
        have hshl' : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel := by rw [skel_applyTag]; exact hshl
        have hshr' : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel := by rw [skel_applyTag]; exact hshr
        have ihl := Inv.chmax a b x hx (applyTag tg nd l) lo ((lo + hi) / 2) xl hL hshl' hsl
        have ihr := Inv.chmax a b x hx (applyTag tg nd r) ((lo + hi) / 2) hi xr hR hshr' hsr
        have hxl : xl.length = (lo + hi) / 2 - lo := by
          rw [hL.size, BT.size_skel, hshl'.size] <;> try omega
        have := Inv.update ihl ihr nd noTag
        rw [hys, rangeMap_append, hxl]
        have e : lo + ((lo + hi) / 2 - lo) = (lo + hi) / 2 := by omega
        rw [e]
        exact this
termination_by t _ _ _ _ _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

end Proofs.BeatsModel
