import Proofs.BeatsApply2
namespace Proofs.BeatsModel

/-- A segment tree without padding: a leaf holds one element, an internal node has a pending tag and two children. -/
inductive BT where
  | leaf (nd : Nd)
  | node (nd : Nd) (tg : Tag) (l r : BT)

def BT.nd : BT → Nd
  | .leaf nd => nd
  | .node nd _ _ _ => nd

def BT.size : BT → Nat
  | .leaf _ => 1
  | .node _ _ l r => l.size + r.size

/-- `Inv t ys`: the tree `t` represents the array `ys` (with all pending operations of its ancestors not yet applied). -/
inductive Inv : BT → List Int → Prop
  | leaf (nd : Nd) (y : Int) : Desc nd [y] → InRange [y] → Inv (.leaf nd) [y]
  | node (nd : Nd) (tg : Tag) (l r : BT) (xl xr ys : List Int) :
      NodeInv2 nd tg l.nd r.nd xl xr ys → Inv l xl → Inv r xr → Inv (.node nd tg l r) ys

theorem Inv.desc {t : BT} {ys : List Int} (h : Inv t ys) : Desc t.nd ys := by
  cases h with
  | leaf nd y hd _ => exact hd
  | node nd tg l r xl xr ys hn _ _ => exact hn.desc

theorem Inv.range {t : BT} {ys : List Int} (h : Inv t ys) : InRange ys := by
  cases h with
  | leaf nd y _ hr => exact hr
  | node nd tg l r xl xr ys hn _ _ => exact hn.ry

theorem Inv.ne {t : BT} {ys : List Int} (h : Inv t ys) : ys ≠ [] := by
  cases h with
  | leaf nd y _ _ => simp
  | node nd tg l r xl xr ys hn _ _ =>
    obtain ⟨v, hv⟩ : ∃ v, v ∈ ys := by rw [hn.eq]; exact ys_ne tg nd xl xr hn.nel
    intro h; rw [h] at hv; simp at hv

theorem Inv.size {t : BT} {ys : List Int} (h : Inv t ys) : ys.length = t.size := by
  induction h with
  | leaf nd y _ _ => rfl
  | node nd tg l r xl xr ys hn _ _ ihl ihr =>
    rw [hn.eq, pend_length, List.length_append, ihl, ihr]; rfl

/-- `update_all` on a subtree. -/
def setBT (v : Int) : BT → BT
  | .leaf _ => .leaf (setNd 1 v)
  | .node nd tg l r => .node (setNd (l.size + r.size : Nat) v) (tagSet v) l r

theorem Inv.set {t : BT} {ys : List Int} (h : Inv t ys) (v : Int) (hv : -INF < v ∧ v < INF) :
    Inv (setBT v t) (List.replicate ys.length v) := by
  cases h with
  | leaf nd y _ _ =>
    exact Inv.leaf _ v (setNd_desc 1 v hv.1 hv.2 (by omega)) (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact hv)
  | node nd tg l r xl xr ys hn hl hr =>
    have := applySet_nodeInv nd tg l.nd r.nd xl xr ys hn v hv
    have hs : ys.length = l.size + r.size := by
      exact (Inv.node nd tg l r xl xr ys hn hl hr).size
    simp only [setBT]
    rw [hs] at this ⊢
    exact Inv.node _ _ l r xl xr _ this hl hr


/-- The array a tree represents on its own (with its own pending tag applied to the children). -/
def arr : BT → List Int
  | .leaf nd => [nd.mx]
  | .node nd tg l r => pend tg nd (arr l ++ arr r)

def BT.kids : BT → List Int
  | .leaf _ => []
  | .node _ _ l r => arr l ++ arr r

def BT.lval : BT → Option Int
  | .leaf _ => none
  | .node _ tg _ _ => tg.lval

def BT.ladd : BT → Int
  | .leaf _ => 0
  | .node _ tg _ _ => tg.ladd

theorem Inv.eq_arr {t : BT} {ys : List Int} (h : Inv t ys) : ys = arr t := by
  induction h with
  | leaf nd y hd hr =>
    have hy := hr y (by simp)
    have h1 : nd.mx = max (-INF) y := hd.1
    show [y] = [nd.mx]
    rw [h1]; congr 1; omega
  | node nd tg l r xl xr ys hn _ _ ihl ihr =>
    show ys = pend tg nd (arr l ++ arr r)
    rw [hn.eq, ← ihl, ← ihr]

/-- `add_all` on a subtree. -/
def addBT (x : Int) : BT → BT
  | .leaf nd => .leaf (addNd nd x)
  | .node nd tg l r => .node (addNd nd x) (tagAdd tg x) l r

theorem Inv.add {t : BT} {ys : List Int} (h : Inv t ys) (x : Int)
    (hy : ∀ w ∈ ys, -INF < w + x ∧ w + x < INF)
    (hv : ∀ v, t.lval = some v → -INF < v + x ∧ v + x < INF)
    (ha : t.lval = none → ∀ w ∈ t.kids, -INF < w + (t.ladd + x) ∧ w + (t.ladd + x) < INF) :
    Inv (addBT x t) (ys.map (fun v => v + x)) := by
  cases h with
  | leaf nd y hd hr =>
    have := hy y (by simp)
    exact Inv.leaf _ (y + x) (addNd_desc nd [y] x y (by simp) hr (fun v hv => by
        rw [List.mem_singleton.mp hv]; exact ⟨Int.le_of_lt this.1, Int.le_of_lt this.2⟩) hd)
      (fun w hw => by rw [List.mem_singleton.mp hw]; exact this)
  | node nd tg l r xl xr ys hn hl hr =>
    have hA := hl.eq_arr; have hB := hr.eq_arr
    exact Inv.node _ _ l r xl xr _ (applyAdd_nodeInv nd tg l.nd r.nd xl xr ys hn x hy hv (by
      intro h0
      have := ha (by simpa [BT.lval] using h0)
      simpa [BT.kids, BT.ladd, hA, hB] using this)) hl hr


/-- `if (x < max_v) update_node_max(x)` on a subtree. -/
def capMaxBT (x : Int) (t : BT) : BT :=
  if x < t.nd.mx then
    match t with
    | .leaf nd => .leaf (updMax nd x)
    | .node nd tg l r => .node (updMax nd x) (tagMax tg x) l r
  else t

/-- `if (min_v < x) update_node_min(x)` on a subtree. -/
def capMinBT (x : Int) (t : BT) : BT :=
  if t.nd.mn < x then
    match t with
    | .leaf nd => .leaf (updMin nd x)
    | .node nd tg l r => .node (updMin nd x) (tagMin tg x) l r
  else t

theorem Inv.capMax {t : BT} {ys : List Int} (h : Inv t ys) (x : Int) (hs : x < t.nd.mx → t.nd.smx < x) :
    Inv (capMaxBT x t) (ys.map (fun v => min v x)) := by
  unfold capMaxBT
  by_cases hc : x < t.nd.mx
  · rw [if_pos hc]
    have hs' := hs hc
    cases h with
    | leaf nd y hd hr =>
      have hnsmx : -INF ≤ nd.smx := by rw [hd.2.1]; exact smxL_ge _
      have hx : -INF < x := by simp only [BT.nd] at hs'; omega
      have := updMax_desc nd [y] x y (by simp) hr hd (by simpa [BT.nd] using hs') (by simpa [BT.nd] using hc)
      exact Inv.leaf _ (min y x) this (fun w hw => by
        rw [List.mem_singleton.mp hw]
        have := hr y (by simp)
        exact ⟨Int.lt_min.mpr ⟨this.1, hx⟩, Int.lt_of_le_of_lt (Int.min_le_left _ _) this.2⟩)
    | node nd tg l r xl xr ys hn hl hr =>
      exact Inv.node _ _ l r xl xr _ (applyMax_nodeInv nd tg l.nd r.nd xl xr ys hn x (by simpa [BT.nd] using hs')
        (by simpa [BT.nd] using hc)) hl hr
  · rw [if_neg hc]
    have : ys.map (fun v => min v x) = ys := by
      apply map_min_id
      intro v hv
      have := mxL_ge ys v hv
      have h1 : t.nd.mx = mxL ys := h.desc.1
      omega
    rw [this]; exact h

theorem Inv.capMin {t : BT} {ys : List Int} (h : Inv t ys) (x : Int) (hs : t.nd.mn < x → x < t.nd.smn) :
    Inv (capMinBT x t) (ys.map (fun v => max v x)) := by
  unfold capMinBT
  by_cases hc : t.nd.mn < x
  · rw [if_pos hc]
    have hs' := hs hc
    cases h with
    | leaf nd y hd hr =>
      have hnsmn : nd.smn ≤ INF := by rw [hd.2.2.2.2.1]; exact mnL_le_INF _
      have hx : x < INF := by simp only [BT.nd] at hs'; omega
      have hmn : -INF < nd.mn := by
        rw [hd.2.2.2.1]; exact (hr _ (mnL_mem [y] y (by simp) (fun w hw => (hr w hw).2))).1
      have := updMin_desc nd [y] x y (by simp) hr hd (by simpa [BT.nd] using hs') (by simpa [BT.nd] using hc)
      exact Inv.leaf _ (max y x) this (fun w hw => by
        rw [List.mem_singleton.mp hw]
        have := hr y (by simp)
        exact ⟨Int.lt_of_lt_of_le this.1 (Int.le_max_left _ _), Int.max_lt.mpr ⟨this.2, hx⟩⟩)
    | node nd tg l r xl xr ys hn hl hr =>
      exact Inv.node _ _ l r xl xr _ (applyMin_nodeInv nd tg l.nd r.nd xl xr ys hn x (by simpa [BT.nd] using hs')
        (by simpa [BT.nd] using hc)) hl hr
  · rw [if_neg hc]
    have : ys.map (fun v => max v x) = ys := by
      apply map_max_id
      intro v hv
      have := mnL_le ys v hv
      have h1 : t.nd.mn = mnL ys := h.desc.2.2.2.1
      omega
    rw [this]; exact h

end Proofs.BeatsModel
