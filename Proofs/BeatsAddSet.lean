import Proofs.BeatsChminSpec
namespace Proofs.BeatsModel

/-- Apply `f` at the positions of `[a, b)` of the array held at `[lo, ..)`. -/
def rangeMap (f : Int → Int) (lo a b : Nat) (ys : List Int) : List Int :=
  ys.mapIdx (fun i v => if a ≤ lo + i ∧ lo + i < b then f v else v)

theorem rangeMap_append (f : Int → Int) (lo a b : Nat) (xs ys : List Int) :
    rangeMap f lo a b (xs ++ ys) = rangeMap f lo a b xs ++ rangeMap f (lo + xs.length) a b ys := by
  unfold rangeMap
  rw [List.mapIdx_append]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx, Nat.add_assoc, Nat.add_comm i xs.length]

theorem rangeMap_id (f : Int → Int) (lo a b : Nat) (ys : List Int) (h : ∀ i, i < ys.length → ¬(a ≤ lo + i ∧ lo + i < b)) :
    rangeMap f lo a b ys = ys := by
  unfold rangeMap
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx]
    rw [if_neg (h i (by simpa using h1))]

theorem rangeMap_all (f : Int → Int) (lo a b : Nat) (ys : List Int) (h : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b)) :
    rangeMap f lo a b ys = ys.map f := by
  unfold rangeMap
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx, List.getElem_map]
    rw [if_pos (h i (by simpa using h1))]

/-- The conditions under which `add_all` on this node is overflow-free. -/
def AddSafe (x : Int) (t : BT) : Prop :=
  (∀ w ∈ arr t, -INF < w + x ∧ w + x < INF) ∧
  (∀ v, t.lval = some v → -INF < v + x ∧ v + x < INF) ∧
  (t.lval = none → ∀ w ∈ t.kids, -INF < w + (t.ladd + x) ∧ w + (t.ladd + x) < INF)

def addRec (a b : Nat) (x : Int) : BT → Nat → Nat → BT
  | .leaf nd, lo, hi => if b ≤ lo ∨ hi ≤ a then .leaf nd else addBT x (.leaf nd)
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a then .node nd tg l r
    else if a ≤ lo ∧ hi ≤ b then addBT x (.node nd tg l r)
    else updateBT (.node nd noTag (addRec a b x (applyTag tg nd l) lo ((lo + hi) / 2))
      (addRec a b x (applyTag tg nd r) ((lo + hi) / 2) hi))
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

def addSafeRec (a b : Nat) (x : Int) : BT → Nat → Nat → Prop
  | .leaf nd, lo, hi => if b ≤ lo ∨ hi ≤ a then True else AddSafe x (.leaf nd)
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a then True
    else if a ≤ lo ∧ hi ≤ b then AddSafe x (.node nd tg l r)
    else PushSafe (.node nd tg l r) ∧ addSafeRec a b x (applyTag tg nd l) lo ((lo + hi) / 2) ∧
      addSafeRec a b x (applyTag tg nd r) ((lo + hi) / 2) hi
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

theorem Inv.add_range (a b : Nat) (x : Int) :
    ∀ (t : BT) (lo hi : Nat) (ys : List Int), Inv t ys → Shape lo hi t.skel → addSafeRec a b x t lo hi →
      Inv (addRec a b x t lo hi) (rangeMap (fun v => v + x) lo a b ys)
  | .leaf nd, lo, hi, ys, h, hsh, hsafe => by
    have hhi : hi = lo + 1 := hsh
    unfold addRec
    unfold addSafeRec at hsafe
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc]
      have : rangeMap (fun v => v + x) lo a b ys = ys := by
        apply rangeMap_id
        intro i hi' ⟨h1, h2⟩
        have : i < ys.length := hi'
        have hl : ys.length = 1 := by rw [h.size]; rfl
        omega
      rw [this]; exact h
    · rw [if_neg hc]
      rw [if_neg hc] at hsafe
      have hl : ys.length = 1 := by rw [h.size]; rfl
      have hcov : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b) := by intro i hi'; omega
      rw [rangeMap_all _ lo a b ys hcov]
      have hs := hsafe
      exact h.add x (by rw [h.eq_arr]; exact hs.1) hs.2.1 hs.2.2
  | .node nd tg l r, lo, hi, ys, h, hsh, hsafe => by
    unfold addRec
    unfold addSafeRec at hsafe
    have hlen : ys.length = hi - lo := by
      rw [h.size, BT.size_skel]; exact Shape.size hsh
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc]
      have : rangeMap (fun v => v + x) lo a b ys = ys := by
        apply rangeMap_id
        intro i hi' ⟨h1, h2⟩
        have : i < ys.length := hi'
        omega
      rw [this]; exact h
    · rw [if_neg hc]
      rw [if_neg hc] at hsafe
      by_cases hc2 : a ≤ lo ∧ hi ≤ b
      · rw [if_pos hc2]
        rw [if_pos hc2] at hsafe
        have hcov : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b) := by intro i hi'; omega
        rw [rangeMap_all _ lo a b ys hcov]
        exact h.add x (by rw [h.eq_arr]; exact hsafe.1) hsafe.2.1 hsafe.2.2
      · rw [if_neg hc2]
        rw [if_neg hc2] at hsafe
        obtain ⟨hps, hsl, hsr⟩ := hsafe
        obtain ⟨xl, xr, hL, hR, hys⟩ := Inv.push_parts h hps
        obtain ⟨hlo, hshl, hshr⟩ := hsh
        have hshl' : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel := by rw [skel_applyTag]; exact hshl
        have hshr' : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel := by rw [skel_applyTag]; exact hshr
        have ihl := Inv.add_range a b x (applyTag tg nd l) lo ((lo + hi) / 2) xl hL hshl' hsl
        have ihr := Inv.add_range a b x (applyTag tg nd r) ((lo + hi) / 2) hi xr hR hshr' hsr
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
