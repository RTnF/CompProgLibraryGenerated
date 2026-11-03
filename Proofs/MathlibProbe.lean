import Mathlib.Tactic.Ring

namespace Proofs.MathlibProbe

theorem square_expand (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

end Proofs.MathlibProbe
