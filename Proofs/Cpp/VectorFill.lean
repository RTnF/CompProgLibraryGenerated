import Proofs.Cpp.Gen.VectorFill
import Proofs.Cpp.Lib.Basic

/-! # `vector_fill` (library/array/vector_fill.hpp)

Every element of `x` becomes `value`; the size is unchanged; `x.size + 1` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.VectorFill

theorem vector_fill_spec {T : Type} [Inhabited T] (x : Array T) (value : T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.vector_fill x value
    ⦃⇓ r c => ⌜r = Array.replicate x.size value ∧ c = t0 + x.size + 1⌝⦄ := by
  mvcgen [cp.vector_fill]
  case inv1 =>
    exact ⇓⟨xs, y⟩ c => ⌜y.size = x.size ∧ (∀ i, i < xs.prefix.length → y[i]! = value) ∧
                         c = t0 + 1 + xs.prefix.length⌝
  all_goals simp_all +zetaDelta [size]
  · have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    subst e
    obtain ⟨hsz, hv, hc⟩ := ‹_ ∧ _ ∧ _›
    simp [size] at hl
    refine ⟨fun i hi => ?_, by omega⟩
    rw [getElemBang_set _ _ _ _ (by simp; omega)]
    simp only [toNat_zero_add]
    split
    · rfl
    · exact hv i (by omega)
  · obtain ⟨hsz, hv, hc⟩ := ‹_ ∧ _ ∧ _›
    try simp [range] at hv hc
    refine ⟨Array.ext (by simp [hsz]) (fun i h1 h2 => ?_), by omega⟩
    have := hv i (by omega)
    simp [getElem!_pos, h1] at this
    simp [this]

end Proofs.Cpp.VectorFill
