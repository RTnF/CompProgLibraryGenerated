import Proofs.Cpp.Gen.TreeHeight
import Proofs.Cpp.Lib.Basic

/-! # `tree_height` (library/tree/tree_height.hpp)

`h[i]` is the larger of the two candidate heights (`pick`); `n + 1` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeHeight

/-- The value `tree_height` writes: `b` if `a < b`, otherwise `a` (the larger one under a linear order). -/
def pick {Cost : Type} [LT Cost] [DecidableLT Cost] (a b : Cost) : Cost := if a < b then b else a

/-- On `Int`, `pick` is `max` (the original `std::max(a, b)`). -/
theorem pick_eq_max (a b : Int) : pick a b = max a b := by
  unfold pick; split <;> omega

/-- Writing slot `L` extends the filled prefix by one. -/
theorem step {α : Type} [Inhabited α] (a a0 : Array α) (f : Nat → α) (L : Nat) (hsz : L < a.size)
    (hdone : ∀ i, i < L → a[i]! = f i) (hrest : ∀ k, L ≤ k → a[k]! = a0[k]!) :
    (∀ i, i < L + 1 → (set a (L : Int) (f L))[i]! = f i) ∧
      (∀ k, L + 1 ≤ k → (set a (L : Int) (f L))[k]! = a0[k]!) := by
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · rw [getElem!_set _ _ _ _ (by simpa using hsz)]
    by_cases h : i = L
    · simp [h]
    · simp only [Int.toNat_natCast, h, ite_false]; exact hdone i (by omega)
  · rw [getElem!_set _ _ _ _ (by simpa using hsz)]
    simp only [Int.toNat_natCast, show k ≠ L by omega, ite_false]; exact hrest k (by omega)

/-- `tree_height(d0, d1, h, n)`: `h[i] = pick d0[i] d1[i]` for `i < n`, the rest of `h` is kept; `n + 1` steps. -/
theorem tree_height_spec {Cost : Type} [Inhabited Cost] [LT Cost] [DecidableLT Cost] (d0 d1 h : Array Cost) (n : Int)
    (hn : 0 ≤ n) (hh : n ≤ h.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_height d0 d1 h n
    ⦃⇓ r c => ⌜r.size = h.size ∧ (∀ i, i < n.toNat → r[i]! = pick d0[i]! d1[i]!) ∧
               (∀ k, n.toNat ≤ k → r[k]! = h[k]!) ∧ c = t0 + 1 + n.toNat⌝⦄ := by
  mvcgen [cp.tree_height]
  case inv1 =>
    exact ⇓⟨xs, a⟩ c => ⌜a.size = h.size ∧ (∀ i, i < xs.prefix.length → a[i]! = pick d0[i]! d1[i]!) ∧
      (∀ k, xs.prefix.length ≤ k → a[k]! = h[k]!) ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  all_goals (try (have e := range_cursor ‹range 0 n = _ ++ _ :: _›; simp at e; subst e))
  all_goals (try simp only [get_natCast] at *)
  · obtain ⟨hsz, hdone, hrest, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have hl := range_prefix_length ‹range 0 n = _ ++ _ :: _›
    have := step _ h (fun i => pick d0[i]! d1[i]!) _ (by omega) hdone hrest
    simp only [pick, if_pos ‹d0[_]! < d1[_]!›] at this
    exact ⟨hsz, this.1, this.2, by omega⟩
  · obtain ⟨hsz, hdone, hrest, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have hl := range_prefix_length ‹range 0 n = _ ++ _ :: _›
    have := step _ h (fun i => pick d0[i]! d1[i]!) _ (by omega) hdone hrest
    simp only [pick, if_neg ‹¬d0[_]! < d1[_]!›] at this
    exact ⟨hsz, this.1, this.2, by omega⟩
  · omega
  · obtain ⟨hsz, hdone, hrest, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    simp only [range_length, Int.sub_zero] at hdone hrest hc
    exact ⟨hsz, fun i hi => hdone i (by omega), fun k hk => hrest k (by omega), hc⟩

end Proofs.Cpp.TreeHeight
