import Proofs.Cpp.Prelude
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Facts about the operations of `Proofs.Cpp.Prelude` shared by the component proofs. -/

namespace Proofs.Cpp

theorem range_length (a b : Int) : (range a b).length = (b - a).toNat := by
  simp [range]

theorem range_zero_size {α : Type} (x : Array α) : range 0 (size x) = (List.range x.size).map (fun k : Nat => (k : Int)) := by
  simp [range, size]

theorem range_map_get {α : Type} [Inhabited α] (x : Array α) :
    (range 0 (size x)).map (get x) = x.toList := by
  apply List.ext_getElem
  · simp [range, size]
  · intro i h h2
    simp [range, get, size] at *
    exact getElem!_pos x i h2

end Proofs.Cpp
