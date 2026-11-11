import Proofs.Cpp.Gen.TreePath
import Proofs.Cpp.Lib.Basic

/-! # `tree_path` (library/tree/tree_path.hpp)

The path from `to` up to `from` along the parent array (`up`); `m + 2` steps for a path of `m` edges. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreePath

/-- The vertex `j` steps above `v` along `parent`. -/
def up (parent : Array Int) (v : Int) : Nat → Int
  | 0 => v
  | j + 1 => parent[(up parent v j).toNat]!

theorem brk (parent out o : Array Int) (from_ to_ k v : Int) (m s t0 : Nat)
    (hfirst : ∀ j, j < m → ¬up parent to_ j = from_)
    (h : 0 ≤ k ∧ k ≤ m ∧ v = up parent to_ k.toNat ∧ o.size = out.size ∧
      (∀ j : Nat, (j : Int) < k → o[j]! = up parent to_ j) ∧ (∀ j : Nat, k ≤ j → o[j]! = out[j]!) ∧
      s = t0 + 1 + k.toNat) (hv : v = from_) :
    k = m ∧ v = from_ ∧ o.size = out.size ∧ (∀ j, j < m → o[j]! = up parent to_ j) ∧
      (∀ j, m ≤ j → o[j]! = out[j]!) ∧ s + 1 = t0 + 2 + m := by
  obtain ⟨h0, hk, hv', hsz, hd, hr, hc⟩ := h
  have : k = m := by
    by_contra hne
    exact hfirst k.toNat (by omega) (by rw [← hv', hv])
  subst this
  exact ⟨rfl, hv, hsz, fun j hj => hd j (by omega), fun j hj => hr j (by omega), by omega⟩

theorem cont (parent out o : Array Int) (from_ to_ k v : Int) (m s t0 : Nat)
    (hm : up parent to_ m = from_) (hout : m + 1 ≤ out.size)
    (h : 0 ≤ k ∧ k ≤ m ∧ v = up parent to_ k.toNat ∧ o.size = out.size ∧
      (∀ j : Nat, (j : Int) < k → o[j]! = up parent to_ j) ∧ (∀ j : Nat, k ≤ j → o[j]! = out[j]!) ∧
      s = t0 + 1 + k.toNat) (hv : ¬v = from_) :
    (0 ≤ k + 1 ∧ k + 1 ≤ m ∧ get parent v = up parent to_ (k + 1).toNat ∧ o.size = out.size ∧
      (∀ j : Nat, (j : Int) < k + 1 → (set o k v)[j]! = up parent to_ j) ∧
      (∀ j : Nat, k + 1 ≤ j → (set o k v)[j]! = out[j]!) ∧ s + 1 = t0 + 1 + (k + 1).toNat) ∧
    m - (k + 1).toNat < m - k.toNat := by
  obtain ⟨h0, hk, hv', hsz, hd, hr, hc⟩ := h
  have hlt : k < m := by
    rcases Int.lt_or_eq_of_le hk with h | h
    · exact h
    · exact absurd (by rw [hv', h]; simpa using hm) hv
  have e : (k + 1).toNat = k.toNat + 1 := by omega
  have hw : ∀ j : Nat, (set o k v)[j]! = if j = k.toNat then v else o[j]! :=
    fun j => getElem!_set _ _ _ _ (by omega)
  refine ⟨⟨by omega, by omega, by rw [e, up, ← hv']; rfl, by simp [hsz], fun j hj => ?_, fun j hj => ?_,
    by omega⟩, by omega⟩
  · rw [hw]
    by_cases hj' : j = k.toNat
    · simp [hj', hv']
    · simp only [hj', ite_false]; exact hd j (by omega)
  · rw [hw]; simp only [show j ≠ k.toNat by omega, ite_false]; exact hr j (by omega)

theorem post (parent out o : Array Int) (from_ to_ k v : Int) (m s t0 : Nat) (hout : m + 1 ≤ out.size)
    (h : k = m ∧ v = from_ ∧ o.size = out.size ∧ (∀ j, j < m → o[j]! = up parent to_ j) ∧
      (∀ j, m ≤ j → o[j]! = out[j]!) ∧ s = t0 + 2 + m)
    (hm : up parent to_ m = from_) :
    k = m ∧ o.size = out.size ∧ (∀ j, j ≤ m → (set o k from_)[j]! = up parent to_ j) ∧
      (∀ j, m + 1 ≤ j → (set o k from_)[j]! = out[j]!) ∧ s = t0 + 2 + m := by
  obtain ⟨hk, -, hsz, hd, hr, hc⟩ := h
  subst hk
  have hw : ∀ j : Nat, (set o (m : Int) from_)[j]! = if j = m then from_ else o[j]! := by
    intro j; rw [getElem!_set _ _ _ _ (by simp; omega)]; simp
  refine ⟨rfl, hsz, fun j hj => ?_, fun j hj => ?_, hc⟩
  · rw [hw]
    by_cases hj' : j = m
    · simp [hj', hm]
    · simp only [hj', ite_false]; exact hd j (by omega)
  · rw [hw]; simp only [show j ≠ m by omega, ite_false]; exact hr j (by omega)

/-- `tree_path(parent, out, from, to)`, where following `parent` from `to` reaches `from` after exactly `m` steps
and not before: writes `out[j] = up parent to j` for `j ≤ m` (so `out[0] = to`, `out[m] = from`), keeps the rest of
`out` and returns `m + 1`; `m + 2` steps. -/
theorem tree_path_spec (parent out : Array Int) (from_ to_ : Int) (m : Nat)
    (hm : up parent to_ m = from_) (hfirst : ∀ j, j < m → up parent to_ j ≠ from_)
    (hout : m + 1 ≤ out.size) (hsmall : m < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_path parent out from_ to_
    ⦃⇓ r c => ⌜r.1 = m + 1 ∧ r.2.size = out.size ∧ (∀ j, j ≤ m → r.2[j]! = up parent to_ j) ∧
               (∀ k, m + 1 ≤ k → r.2[k]! = out[k]!) ∧ c = t0 + 2 + m⌝⦄ := by
  mvcgen [cp.tree_path]
  case inv =>
    exact ⟨fun ⟨o, k, v⟩ c => ⌜0 ≤ k ∧ k ≤ m ∧ v = up parent to_ k.toNat ∧ o.size = out.size ∧
             (∀ j, j < k.toNat → o[j]! = up parent to_ j) ∧ (∀ j, k.toNat ≤ j → o[j]! = out[j]!) ∧
             c = t0 + 1 + k.toNat⌝,
           fun ⟨o, k, v⟩ c => ⌜k = m ∧ v = from_ ∧ o.size = out.size ∧
             (∀ j, j < m → o[j]! = up parent to_ j) ∧ (∀ j, m ≤ j → o[j]! = out[j]!) ∧ c = t0 + 2 + m⌝,
           fun ⟨_, k, _⟩ => m - k.toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  · exact brk _ _ _ _ _ _ _ _ _ _ hfirst ‹_› ‹_›
  · exact cont _ _ _ _ _ _ _ _ _ _ hm hout ‹_› ‹_›
  · simp [up]; omega
  · exact post _ _ _ _ _ _ _ _ _ _ hout ‹_› hm

end Proofs.Cpp.TreePath
