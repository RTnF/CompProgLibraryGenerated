import Proofs.Cpp.Gen.TreeArcs
import Proofs.Cpp.Lib.Basic

/-! # `tree_arcs` (library/tree/tree_arcs.hpp)

The arcs of an edge list: edge `i` becomes the arcs `2i` and `2i + 1` in both directions; `m + 1` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeArcs

/-- Writing the pair of slots `2L`, `2L + 1` extends the filled prefix by one pair. -/
theorem step {α : Type} [Inhabited α] (ac ac0 : Array α) (f g : Nat → α) (L : Nat) (hsz : 2 * L + 1 < ac.size)
    (hdone : ∀ i, i < L → ac[2 * i]! = f i ∧ ac[2 * i + 1]! = g i)
    (hrest : ∀ k, 2 * L ≤ k → ac[k]! = ac0[k]!) :
    let ac' := set (set ac (2 * (L : Int)) (f L)) (2 * (L : Int) + 1) (g L)
    ac'.size = ac.size ∧ (∀ i, i < L + 1 → ac'[2 * i]! = f i ∧ ac'[2 * i + 1]! = g i) ∧
      (∀ k, 2 * (L + 1) ≤ k → ac'[k]! = ac0[k]!) := by
  intro ac'
  have e1 : (2 * (L : Int)).toNat = 2 * L := by omega
  have e2 : (2 * (L : Int) + 1).toNat = 2 * L + 1 := by omega
  have gk : ∀ k, ac'[k]! = if k = 2 * L + 1 then g L else if k = 2 * L then f L else ac[k]! := by
    intro k
    simp only [ac']
    rw [getElem!_set _ _ _ _ (by simp; omega), getElem!_set _ _ _ _ (by omega), e1, e2]
  refine ⟨by simp [ac'], fun i hi => ?_, fun k hk => ?_⟩
  · rw [gk, gk]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
    · simp only [show 2 * i ≠ 2 * L + 1 by omega, show 2 * i ≠ 2 * L by omega,
        show 2 * i + 1 ≠ 2 * L + 1 by omega, show 2 * i + 1 ≠ 2 * L by omega, ite_false]
      exact hdone i h
    · subst h; simp
  · rw [gk]; simp only [show k ≠ 2 * L + 1 by omega, show k ≠ 2 * L by omega, ite_false]; exact hrest k (by omega)

/-- `tree_arcs_from_list(from, to, af, at, m)`: edge `i` becomes the arcs `2i` (`from[i] → to[i]`) and
`2i + 1` (`to[i] → from[i]`) for `i < m`; the rest of `af`, `at` is kept; `m + 1` steps. -/
theorem tree_arcs_spec (from_ to_ af at_ : Array Int) (m : Int) (hm : 0 ≤ m)
    (haf : 2 * m ≤ af.size) (hat : 2 * m ≤ at_.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_arcs_from_list from_ to_ af at_ m
    ⦃⇓ r c => ⌜r.1.size = af.size ∧ r.2.size = at_.size ∧
               (∀ i, i < m.toNat → r.1[2 * i]! = from_[i]! ∧ r.1[2 * i + 1]! = to_[i]!) ∧
               (∀ i, i < m.toNat → r.2[2 * i]! = to_[i]! ∧ r.2[2 * i + 1]! = from_[i]!) ∧
               (∀ k, 2 * m.toNat ≤ k → r.1[k]! = af[k]! ∧ r.2[k]! = at_[k]!) ∧ c = t0 + 1 + m.toNat⌝⦄ := by
  mvcgen [cp.tree_arcs_from_list]
  case inv1 =>
    exact ⇓⟨xs, p⟩ c => ⌜p.1.size = af.size ∧ p.2.size = at_.size ∧
      (∀ i, i < xs.prefix.length → p.1[2 * i]! = from_[i]! ∧ p.1[2 * i + 1]! = to_[i]!) ∧
      (∀ i, i < xs.prefix.length → p.2[2 * i]! = to_[i]! ∧ p.2[2 * i + 1]! = from_[i]!) ∧
      (∀ k, 2 * xs.prefix.length ≤ k → p.1[k]! = af[k]! ∧ p.2[k]! = at_[k]!) ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · have e := range_cursor ‹range 0 m = _ ++ _ :: _›
    simp at e
    subst e
    obtain ⟨hs1, hs2, hd1, hd2, hrest, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _›
    have hl := range_prefix_length ‹range 0 m = _ ++ _ :: _›
    obtain ⟨_, a2, a3⟩ := step _ af (fun i => from_[i]!) (fun i => to_[i]!) _ (by omega) hd1
      (fun k hk => (hrest k hk).1)
    obtain ⟨_, b2, b3⟩ := step _ at_ (fun i => to_[i]!) (fun i => from_[i]!) _ (by omega) hd2
      (fun k hk => (hrest k hk).2)
    simp only [get_natCast] at *
    exact ⟨hs1, hs2, a2, b2, fun k hk => ⟨a3 k hk, b3 k hk⟩, by omega⟩
  · omega
  · obtain ⟨hs1, hs2, hd1, hd2, hrest, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _›
    simp only [range_length, Int.sub_zero] at hd1 hd2 hrest hc
    exact ⟨hs1, hs2, fun i hi => hd1 i (by omega), fun i hi => hd2 i (by omega), hrest, hc⟩

end Proofs.Cpp.TreeArcs
