import Proofs.BeatsModel
namespace Proofs.BeatsModel

theorem foldl_min_le (xs : List Int) (a : Int) : xs.foldl min a ≤ a := by
  induction xs generalizing a with
  | nil => exact Int.le_refl a
  | cons x xs ih => exact Int.le_trans (ih (min a x)) (Int.min_le_left a x)

theorem foldl_min_le_mem (xs : List Int) (a v : Int) (hv : v ∈ xs) : xs.foldl min a ≤ v := by
  induction xs generalizing a with
  | nil => simp at hv
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hv with h | h
    · subst h; exact Int.le_trans (foldl_min_le xs _) (Int.min_le_right a v)
    · exact ih _ h

theorem foldl_min_mem (xs : List Int) (a : Int) : xs.foldl min a = a ∨ xs.foldl min a ∈ xs := by
  induction xs generalizing a with
  | nil => left; rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases ih (min a x) with h | h
    · by_cases hax : x ≤ a
      · right; rw [h, Int.min_eq_right hax]; exact List.mem_cons_self
      · left; rw [h, Int.min_eq_left (by omega)]
    · right; exact List.mem_cons_of_mem _ h

theorem foldl_min_ge (xs : List Int) (a m : Int) (ha : m ≤ a) (h : ∀ v ∈ xs, m ≤ v) : m ≤ xs.foldl min a := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (min a x) (Int.le_min.mpr ⟨ha, h x List.mem_cons_self⟩) (fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem mnL_le (xs : List Int) (v : Int) (h : v ∈ xs) : mnL xs ≤ v := foldl_min_le_mem xs INF v h
theorem mnL_cases (xs : List Int) : mnL xs = INF ∨ mnL xs ∈ xs := foldl_min_mem xs INF
theorem mnL_ge (xs : List Int) (m : Int) (hm : m ≤ INF) (h : ∀ v ∈ xs, m ≤ v) : m ≤ mnL xs :=
  foldl_min_ge xs INF m hm h

/-- `mnL` of a nonempty list of values below `INF` is a member. -/
theorem mnL_mem (xs : List Int) (v : Int) (hv : v ∈ xs) (hr : ∀ w ∈ xs, w < INF) : mnL xs ∈ xs := by
  rcases mnL_cases xs with h | h
  · have := mnL_le xs v hv; have := hr v hv; omega
  · exact h

theorem mxL_mem (xs : List Int) (v : Int) (hv : v ∈ xs) (hr : ∀ w ∈ xs, -INF < w) : mxL xs ∈ xs := by
  rcases mxL_cases xs with h | h
  · have := mxL_ge xs v hv; have := hr v hv; omega
  · exact h

/-- Mapping `min · x` with `x` above `m` keeps the minimum when `m` is the minimum of a list. -/
theorem mnL_map_min (xs : List Int) (x : Int) (v : Int) (hv : v ∈ xs) (hr : ∀ w ∈ xs, w < INF) (hx : mnL xs < x) :
    mnL (xs.map (fun v => min v x)) = mnL xs := by
  have hm := mnL_mem xs v hv hr
  apply Int.le_antisymm
  · have : min (mnL xs) x ∈ xs.map (fun v => min v x) := List.mem_map.mpr ⟨_, hm, rfl⟩
    have h2 := mnL_le _ _ this
    rwa [Int.min_eq_left (by omega)] at h2
  · apply mnL_ge _ _ (by have := hr v hv; have := mnL_le xs v hv; omega)
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    exact Int.le_min.mpr ⟨mnL_le xs u hu, by omega⟩

end Proofs.BeatsModel
