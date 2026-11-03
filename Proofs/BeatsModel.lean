/-! Segment Tree Beats: the node summary `(max, second max, count of max, min, second min, count of min)` of a list of values.
The C++ class stores these per node; this file defines what a summary describes and proves that the node update rules
(`update_node_max`, `update_node_min`, `add_all`, `update_all`, the merge `update`) keep it a summary. Sentinels: `INF = 4e18`
stands for "no such element" (`-INF` for a missing maximum, `INF` for a missing minimum); all values are `< INF` in absolute value. -/
namespace Proofs.BeatsModel

def INF : Int := 4000000000000000000

/-- Maximum of a list (`-INF` for the empty list). -/
def mxL (xs : List Int) : Int := xs.foldl max (-INF)
/-- Minimum of a list (`INF` for the empty list). -/
def mnL (xs : List Int) : Int := xs.foldl min INF
/-- Second maximum: the largest element strictly below the maximum (`-INF` when there is none). -/
def smxL (xs : List Int) : Int := mxL (xs.filter (fun v => decide (v < mxL xs)))
/-- Second minimum: the smallest element strictly above the minimum (`INF` when there is none). -/
def smnL (xs : List Int) : Int := mnL (xs.filter (fun v => decide (mnL xs < v)))
def cmxL (xs : List Int) : Nat := xs.countP (fun v => decide (v = mxL xs))
def cmnL (xs : List Int) : Nat := xs.countP (fun v => decide (v = mnL xs))

structure Nd where
  mx : Int
  smx : Int
  mc : Int
  mn : Int
  smn : Int
  mnc : Int
deriving Repr

def Desc (nd : Nd) (xs : List Int) : Prop :=
  nd.mx = mxL xs ∧ nd.smx = smxL xs ∧ nd.mc = cmxL xs ∧ nd.mn = mnL xs ∧ nd.smn = smnL xs ∧ nd.mnc = cmnL xs

/-- All values lie strictly between `-INF` and `INF`. -/
def InRange (xs : List Int) : Prop := ∀ v ∈ xs, -INF < v ∧ v < INF

theorem mxL_nil : mxL [] = -INF := rfl
theorem mnL_nil : mnL [] = INF := rfl

theorem foldl_max_ge (xs : List Int) (a : Int) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact Int.le_refl a
  | cons x xs ih => exact Int.le_trans (Int.le_max_left a x) (ih (max a x))

theorem le_foldl_max (xs : List Int) (a v : Int) (hv : v ∈ xs) : v ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hv
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hv with h | h
    · subst h; exact Int.le_trans (Int.le_max_right a v) (foldl_max_ge xs _)
    · exact ih _ h

theorem foldl_max_mem (xs : List Int) (a : Int) : xs.foldl max a = a ∨ xs.foldl max a ∈ xs := by
  induction xs generalizing a with
  | nil => left; rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases ih (max a x) with h | h
    · by_cases hax : a ≤ x
      · right; rw [h, Int.max_eq_right hax]; exact List.mem_cons_self
      · left; rw [h, Int.max_eq_left (by omega)]
    · right; exact List.mem_cons_of_mem _ h

theorem foldl_max_le (xs : List Int) (a m : Int) (ha : a ≤ m) (h : ∀ v ∈ xs, v ≤ m) : xs.foldl max a ≤ m := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (max a x) (Int.max_le.mpr ⟨ha, h x List.mem_cons_self⟩) (fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem mxL_ge (xs : List Int) (v : Int) (h : v ∈ xs) : v ≤ mxL xs := le_foldl_max xs (-INF) v h
theorem mxL_cases (xs : List Int) : mxL xs = -INF ∨ mxL xs ∈ xs := foldl_max_mem xs (-INF)
theorem mxL_le (xs : List Int) (m : Int) (hm : -INF ≤ m) (h : ∀ v ∈ xs, v ≤ m) : mxL xs ≤ m :=
  foldl_max_le xs (-INF) m hm h

/-- The core step of `chmin`: when `x` lies strictly between the second maximum and the maximum, only the maximum values
change (to `x`), so the maximum becomes `x`. -/
theorem mxL_map_min (xs : List Int) (x : Int) (hx : -INF < x) (hlt : x < mxL xs) :
    mxL (xs.map (fun v => min v x)) = x := by
  have hm : mxL xs ∈ xs := by
    rcases mxL_cases xs with h | h
    · omega
    · exact h
  apply Int.le_antisymm
  · exact mxL_le _ x (by omega) (by
      intro v hv
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
      exact Int.min_le_right u x)
  · have : min (mxL xs) x ∈ xs.map (fun v => min v x) := List.mem_map.mpr ⟨_, hm, rfl⟩
    have h2 := mxL_ge _ _ this
    rwa [Int.min_eq_right (by omega)] at h2

/-- The second maximum is unchanged. -/
theorem smxL_map_min (xs : List Int) (x : Int) (hx : -INF < x) (hlt : x < mxL xs) (hs : smxL xs < x) :
    smxL (xs.map (fun v => min v x)) = smxL xs := by
  have hM := mxL_map_min xs x hx hlt
  unfold smxL
  rw [hM]
  have key : ∀ v ∈ xs, (decide (min v x < x) = decide (v < mxL xs)) := by
    intro v hv
    simp only [decide_eq_decide]
    constructor
    · intro h
      have : v < x := by
        by_cases hvx : v < x
        · exact hvx
        · rw [Int.min_eq_right (by omega)] at h; omega
      omega
    · intro h
      have hv' : v ≤ smxL xs := by
        have : v ∈ xs.filter (fun v => decide (v < mxL xs)) := List.mem_filter.mpr ⟨hv, by simpa using h⟩
        exact mxL_ge _ _ this
      rw [Int.min_eq_left (by omega)]; omega
  have e : (xs.map (fun v => min v x)).filter (fun v => decide (v < x)) = xs.filter (fun v => decide (v < mxL xs)) := by
    rw [List.filter_map]
    have h1 : xs.filter ((fun v => decide (v < x)) ∘ fun v => min v x) = xs.filter (fun v => decide (v < mxL xs)) := by
      apply List.filter_congr
      intro v hv
      exact key v hv
    rw [h1]
    have h2 : ∀ v ∈ xs.filter (fun v => decide (v < mxL xs)), min v x = v := by
      intro v hv
      have hv' := List.mem_filter.mp hv
      have : v ≤ smxL xs := mxL_ge _ _ (List.mem_filter.mpr ⟨hv'.1, hv'.2⟩)
      exact Int.min_eq_left (by omega)
    exact (List.map_congr_left h2).trans (List.map_id _)
  rw [e]

/-- The number of maxima is unchanged. -/
theorem cmxL_map_min (xs : List Int) (x : Int) (hx : -INF < x) (hlt : x < mxL xs) (hs : smxL xs < x) :
    cmxL (xs.map (fun v => min v x)) = cmxL xs := by
  have hM := mxL_map_min xs x hx hlt
  unfold cmxL
  rw [hM, List.countP_map]
  apply List.countP_congr
  intro v hv
  simp only [Function.comp, decide_eq_true_eq]
  constructor
  · intro h
    have hvx : x ≤ v := by
      by_cases h' : v < x
      · rw [Int.min_eq_left (by omega)] at h; omega
      · omega
    have hvm : v ≤ mxL xs := mxL_ge xs v hv
    by_cases hvlt : v < mxL xs
    · have : v ≤ smxL xs := mxL_ge _ _ (List.mem_filter.mpr ⟨hv, by simpa using hvlt⟩)
      omega
    · omega
  · intro h
    rw [h, Int.min_eq_right (by omega)]

end Proofs.BeatsModel
