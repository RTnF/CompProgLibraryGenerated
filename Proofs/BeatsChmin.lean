import Proofs.BeatsShape
namespace Proofs.BeatsModel

/-- The effect of `chmin(a, b, x)` on the array held at positions `[lo, lo + ys.length)`. -/
def rangeMin (lo a b : Nat) (x : Int) (ys : List Int) : List Int :=
  ys.mapIdx (fun i v => if a ≤ lo + i ∧ lo + i < b then min v x else v)

theorem rangeMin_append (lo a b : Nat) (x : Int) (xs ys : List Int) :
    rangeMin lo a b x (xs ++ ys) = rangeMin lo a b x xs ++ rangeMin (lo + xs.length) a b x ys := by
  unfold rangeMin
  rw [List.mapIdx_append]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx, Nat.add_assoc, Nat.add_comm i xs.length]

theorem rangeMin_id (lo a b : Nat) (x : Int) (ys : List Int) (h : ∀ i, i < ys.length → ¬(a ≤ lo + i ∧ lo + i < b)) :
    rangeMin lo a b x ys = ys := by
  unfold rangeMin
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx]
    rw [if_neg (h i (by simpa using h1))]

theorem rangeMin_small (lo a b : Nat) (x : Int) (ys : List Int) (h : ∀ v ∈ ys, v ≤ x) : rangeMin lo a b x ys = ys := by
  unfold rangeMin
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx]
    split
    · exact Int.min_eq_left (h _ (List.getElem_mem _))
    · rfl

theorem rangeMin_all (lo a b : Nat) (x : Int) (ys : List Int) (h : ∀ i, i < ys.length → (a ≤ lo + i ∧ lo + i < b)) :
    rangeMin lo a b x ys = ys.map (fun v => min v x) := by
  unfold rangeMin
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx, List.getElem_map]
    rw [if_pos (h i (by simpa using h1))]

/-- Pushing a node is overflow-free (the range side conditions of `Inv.push`). -/
def PushSafe : BT → Prop
  | .leaf _ => True
  | .node _ tg l r =>
    (tg.lval = none → ∀ v, l.lval = some v → -INF < v + tg.ladd ∧ v + tg.ladd < INF) ∧
    (tg.lval = none → l.lval = none → ∀ w ∈ l.kids, -INF < w + (l.ladd + tg.ladd) ∧ w + (l.ladd + tg.ladd) < INF) ∧
    (tg.lval = none → ∀ v, r.lval = some v → -INF < v + tg.ladd ∧ v + tg.ladd < INF) ∧
    (tg.lval = none → r.lval = none → ∀ w ∈ r.kids, -INF < w + (r.ladd + tg.ladd) ∧ w + (r.ladd + tg.ladd) < INF)

/-- `chmin(a, b, x)` on the subtree `t` covering positions `[lo, hi)`. -/
def chminBT (a b : Nat) (x : Int) : BT → Nat → Nat → BT
  | .leaf nd, lo, hi => if b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x then .leaf nd else .leaf (updMax nd x)
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x then .node nd tg l r
    else if a ≤ lo ∧ hi ≤ b ∧ nd.smx < x then capMaxBT x (.node nd tg l r)
    else updateBT (.node nd noTag (chminBT a b x (applyTag tg nd l) lo ((lo + hi) / 2))
      (chminBT a b x (applyTag tg nd r) ((lo + hi) / 2) hi))
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

def chminSafe (a b : Nat) (x : Int) : BT → Nat → Nat → Prop
  | .leaf _, _, _ => True
  | .node nd tg l r, lo, hi =>
    if b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x then True
    else if a ≤ lo ∧ hi ≤ b ∧ nd.smx < x then True
    else PushSafe (.node nd tg l r) ∧ chminSafe a b x (applyTag tg nd l) lo ((lo + hi) / 2) ∧
      chminSafe a b x (applyTag tg nd r) ((lo + hi) / 2) hi
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

end Proofs.BeatsModel
