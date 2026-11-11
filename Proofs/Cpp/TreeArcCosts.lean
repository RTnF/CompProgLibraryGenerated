import Proofs.Cpp.Gen.TreeArcCosts
import Proofs.Cpp.Lib.Basic

/-! # `tree_arc_costs` (library/tree/tree_arc_costs.hpp)

The costs of the arcs of an edge list: `ac[2i] = ac[2i + 1] = cost[i]`; `m + 1` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeArcCosts

theorem step {Cost : Type} [Inhabited Cost] (ac : Array Cost) (c : Cost) (L : Nat) (hsz : 2 * L + 1 < ac.size)
    (ac0 : Array Cost) (cost : Array Cost)
    (hdone : ∀ i, i < L → ac[2 * i]! = cost[i]! ∧ ac[2 * i + 1]! = cost[i]!)
    (hrest : ∀ k, 2 * L ≤ k → ac[k]! = ac0[k]!) (hc : c = cost[L]!) :
    let ac' := set (set ac (2 * (L : Int)) c) (2 * (L : Int) + 1) c
    ac'.size = ac.size ∧ (∀ i, i < L + 1 → ac'[2 * i]! = cost[i]! ∧ ac'[2 * i + 1]! = cost[i]!) ∧
      (∀ k, 2 * (L + 1) ≤ k → ac'[k]! = ac0[k]!) := by
  intro ac'
  have e1 : (2 * (L : Int)).toNat = 2 * L := by omega
  have e2 : (2 * (L : Int) + 1).toNat = 2 * L + 1 := by omega
  have g : ∀ k, ac'[k]! = if k = 2 * L + 1 then c else if k = 2 * L then c else ac[k]! := by
    intro k
    simp only [ac']
    rw [getElem!_set _ _ _ _ (by simp; omega), getElem!_set _ _ _ _ (by omega), e1, e2]
  refine ⟨by simp [ac'], fun i hi => ?_, fun k hk => ?_⟩
  · rw [g, g]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
    · simp only [show 2 * i ≠ 2 * L + 1 by omega, show 2 * i ≠ 2 * L by omega,
        show 2 * i + 1 ≠ 2 * L + 1 by omega, show 2 * i + 1 ≠ 2 * L by omega, ite_false]
      exact hdone i h
    · subst h; simp [hc]
  · rw [g]; simp only [show k ≠ 2 * L + 1 by omega, show k ≠ 2 * L by omega, ite_false]; exact hrest k (by omega)

/-- `tree_arc_costs(cost, ac, m)`: `ac[2i] = ac[2i+1] = cost[i]` for `i < m`, the rest of `ac` is kept;
`m + 1` steps. -/
theorem tree_arc_costs_spec {Cost : Type} [Inhabited Cost] (cost ac : Array Cost) (m : Int) (hm : 0 ≤ m)
    (hac : 2 * m ≤ ac.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_arc_costs cost ac m
    ⦃⇓ r c => ⌜r.size = ac.size ∧ (∀ i, i < m.toNat → r[2 * i]! = cost[i]! ∧ r[2 * i + 1]! = cost[i]!) ∧
               (∀ k, 2 * m.toNat ≤ k → r[k]! = ac[k]!) ∧ c = t0 + 1 + m.toNat⌝⦄ := by
  mvcgen [cp.tree_arc_costs]
  case inv1 =>
    exact ⇓⟨xs, a⟩ c => ⌜a.size = ac.size ∧ (∀ i, i < xs.prefix.length → a[2 * i]! = cost[i]! ∧ a[2 * i + 1]! = cost[i]!) ∧
      (∀ k, 2 * xs.prefix.length ≤ k → a[k]! = ac[k]!) ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · have e := range_cursor ‹range 0 m = _ ++ _ :: _›
    simp at e
    subst e
    obtain ⟨hsz, hdone, hrest, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have hl := range_prefix_length ‹range 0 m = _ ++ _ :: _›
    obtain ⟨_, s2, s3⟩ := step _ _ _ (by omega) ac cost hdone hrest rfl
    simp only [get_natCast] at *
    exact ⟨hsz, s2, s3, by omega⟩
  · omega
  · obtain ⟨hsz, hdone, hrest, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    simp only [range_length, Int.sub_zero] at hdone hrest hc
    exact ⟨hsz, fun i hi => hdone i (by omega), hrest, hc⟩

end Proofs.Cpp.TreeArcCosts
