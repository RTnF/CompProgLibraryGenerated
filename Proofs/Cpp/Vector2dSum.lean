import Proofs.Cpp.Gen.Vector2dSum
import Proofs.Cpp.Lib.Basic

/-! # `vector2d_sum` (library/array/vector2d_sum.hpp)

The sum of all elements of a vector of rows over any additive monoid `T`, in `1 + rows + elements` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.Vector2dSum

/-- The sum of the rows `0, ..., k - 1`. -/
def rowsSum {T : Type} [AddMonoid T] (g : Array (Array T)) (k : Nat) : T :=
  ((g.toList.take k).map (fun r => r.toList.sum)).sum

/-- The number of elements in the rows `0, ..., k - 1`. -/
def rowsLen {T : Type} (g : Array (Array T)) (k : Nat) : Nat := ((g.toList.take k).map Array.size).sum

theorem rowsSum_succ {T : Type} [AddMonoid T] [Inhabited T] (g : Array (Array T)) (k : Nat) (hk : k < g.size) :
    rowsSum g (k + 1) = rowsSum g k + g[k]!.toList.sum := by
  simp [rowsSum, List.take_succ, getElem!_pos, hk]

theorem rowsLen_succ {T : Type} [Inhabited T] (g : Array (Array T)) (k : Nat) (hk : k < g.size) :
    rowsLen g (k + 1) = rowsLen g k + g[k]!.size := by
  simp [rowsLen, List.take_succ, getElem!_pos, hk]

theorem vector2d_sum_spec {T : Type} [AddMonoid T] [Inhabited T] (g : Array (Array T)) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.vector2d_sum g
    ⦃⇓ r c => ⌜r = rowsSum g g.size ∧ c = t0 + 1 + g.size + rowsLen g g.size⌝⦄ := by
  mvcgen [cp.vector2d_sum]
  case inv1 =>
    exact ⇓⟨xs, s⟩ c => ⌜s = rowsSum g xs.prefix.length ∧ c = t0 + 1 + xs.prefix.length + rowsLen g xs.prefix.length⌝
  case inv2 =>
    rename_i pref cur suff hcur b c hinv cols
    exact ⇓⟨ys, s⟩ c' => ⌜s = b + (ys.prefix.map (get (get g cur))).sum ∧ c' = c + 1 + ys.prefix.length⌝
  all_goals simp_all +zetaDelta [size]
  · exact ⟨add_assoc _ _ _, by omega⟩
  · have hl := range_prefix_length ‹range 0 (size g) = _ ++ _ :: _›
    have e := range_cursor ‹range 0 (size g) = _ ++ _ :: _›
    subst e
    simp [size] at hl
    simp only [zero_add, get_natCast, range_zero_map_get, range_zero_length] at *
    rw [rowsSum_succ _ _ hl, rowsLen_succ _ _ hl]
    exact ⟨by simp, by omega⟩
  all_goals simp [rowsSum, rowsLen]

end Proofs.Cpp.Vector2dSum
