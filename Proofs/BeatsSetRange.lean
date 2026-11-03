import Proofs.BeatsAddSet
namespace Proofs.BeatsModel

def setRec (a b : Nat) (x : Int) : BT → Nat → Nat → BT
  | .leaf nd, lo, hi => if b ≤ lo ∨ hi ≤ a then .leaf nd else setBT x (.leaf nd)
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a then .node nd tg l r
    else if a ≤ lo ∧ hi ≤ b then setBT x (.node nd tg l r)
    else updateBT (.node nd noTag (setRec a b x (applyTag tg nd l) lo ((lo + hi) / 2))
      (setRec a b x (applyTag tg nd r) ((lo + hi) / 2) hi))
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

def setSafeRec (a b : Nat) (x : Int) : BT → Nat → Nat → Prop
  | .leaf _, _, _ => True
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a then True
    else if a ≤ lo ∧ hi ≤ b then True
    else PushSafe (.node nd tg l r) ∧ setSafeRec a b x (applyTag tg nd l) lo ((lo + hi) / 2) ∧
      setSafeRec a b x (applyTag tg nd r) ((lo + hi) / 2) hi
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

theorem Inv.set_range (a b : Nat) (x : Int) (hx : -INF < x ∧ x < INF) :
    ∀ (t : BT) (lo hi : Nat) (ys : List Int), Inv t ys → Shape lo hi t.skel → setSafeRec a b x t lo hi →
      Inv (setRec a b x t lo hi) (rangeMap (fun _ => x) lo a b ys)
  | .leaf nd, lo, hi, ys, h, hsh, _ => by
    have hhi : hi = lo + 1 := hsh
    have hl : ys.length = 1 := by rw [h.size]; rfl
    unfold setRec
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc]
      have : rangeMap (fun _ => x) lo a b ys = ys := by
        apply rangeMap_id
        intro i hi' ⟨h1, h2⟩
        have : i < ys.length := hi'
        omega
      rw [this]; exact h
    · rw [if_neg hc]
      have hcov : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b) := by intro i hi'; omega
      rw [rangeMap_all _ lo a b ys hcov, List.map_const']
      exact h.set x hx
  | .node nd tg l r, lo, hi, ys, h, hsh, hsafe => by
    unfold setRec
    unfold setSafeRec at hsafe
    have hlen : ys.length = hi - lo := by
      rw [h.size, BT.size_skel]; exact Shape.size hsh
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc]
      have : rangeMap (fun _ => x) lo a b ys = ys := by
        apply rangeMap_id
        intro i hi' ⟨h1, h2⟩
        have : i < ys.length := hi'
        omega
      rw [this]; exact h
    · rw [if_neg hc]
      rw [if_neg hc] at hsafe
      by_cases hc2 : a ≤ lo ∧ hi ≤ b
      · rw [if_pos hc2]
        have hcov : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b) := by intro i hi'; omega
        rw [rangeMap_all _ lo a b ys hcov, List.map_const']
        exact h.set x hx
      · rw [if_neg hc2]
        rw [if_neg hc2] at hsafe
        obtain ⟨hps, hsl, hsr⟩ := hsafe
        obtain ⟨xl, xr, hL, hR, hys⟩ := Inv.push_parts h hps
        obtain ⟨hlo, hshl, hshr⟩ := hsh
        have hshl' : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel := by rw [skel_applyTag]; exact hshl
        have hshr' : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel := by rw [skel_applyTag]; exact hshr
        have ihl := Inv.set_range a b x hx (applyTag tg nd l) lo ((lo + hi) / 2) xl hL hshl' hsl
        have ihr := Inv.set_range a b x hx (applyTag tg nd r) ((lo + hi) / 2) hi xr hR hshr' hsr
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
