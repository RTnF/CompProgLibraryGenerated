import Proofs.Cpp.Gen.TreeFindRoot
import Proofs.Cpp.Lib.Basic

/-! # `tree_find_root` (library/tree/tree_find_root.hpp)

The root search of a parent array: the result is the last index `i < n` with `parent[i] == i` or
`parent[i] < 0` (`lastRoot`), or `-1`; `n + 1` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeFindRoot

/-- Index `i` marks a root: its parent is itself or negative. -/
def IsRoot (parent : Array Int) (i : Nat) : Prop := parent[i]! = i ∨ parent[i]! < 0

instance (parent : Array Int) (i : Nat) : Decidable (IsRoot parent i) := by unfold IsRoot; infer_instance

/-- The last root index below `k`, or `-1`. -/
def lastRoot (parent : Array Int) : Nat → Int
  | 0 => -1
  | k + 1 => if IsRoot parent k then k else lastRoot parent k

theorem lastRoot_spec (parent : Array Int) (k : Nat) :
    (lastRoot parent k = -1 ∧ ∀ i, i < k → ¬ IsRoot parent i) ∨
    (∃ r : Nat, lastRoot parent k = r ∧ r < k ∧ IsRoot parent r ∧ ∀ j, r < j → j < k → ¬ IsRoot parent j) := by
  induction k with
  | zero => left; simp [lastRoot]
  | succ k ih =>
    by_cases h : IsRoot parent k
    · right; exact ⟨k, by simp [lastRoot, h], by omega, h, fun j h1 h2 => by omega⟩
    · rcases ih with ⟨h1, h2⟩ | ⟨r, h1, h2, h3, h4⟩
      · left; refine ⟨by simp [lastRoot, h, h1], fun i hi => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | hi
        · exact h2 i hi
        · subst hi; exact h
      · right; refine ⟨r, by simp [lastRoot, h, h1], by omega, h3, fun j hj1 hj2 => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj2) with hj | hj
        · exact h4 j hj1 hj
        · subst hj; exact h

/-- `tree_find_root(parent, n)`: the last root index below `n` (`-1` if there is none), in `n + 1` steps. -/
theorem tree_find_root_spec (parent : Array Int) (n : Int) (hn : 0 ≤ n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_find_root parent n ⦃⇓ r c => ⌜r = lastRoot parent n.toNat ∧ c = t0 + 1 + n.toNat⌝⦄ := by
  mvcgen [cp.tree_find_root]
  case inv1 => exact ⇓⟨xs, r⟩ c => ⌜r = lastRoot parent xs.prefix.length ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  all_goals (try (have e := range_cursor ‹range 0 n = _ ++ _ :: _›; simp at e; subst e))
  all_goals (try simp only [get_natCast] at *)
  · refine ⟨?_, by omega⟩; simp [lastRoot, IsRoot, *]
  · refine ⟨?_, by omega⟩; simp [lastRoot, IsRoot, *]
  · refine ⟨?_, by omega⟩
    simp only [lastRoot]
    rw [if_neg]
    · exact (‹_ = lastRoot parent _ ∧ _›).1
    · simp only [IsRoot, not_or, not_lt]; constructor <;> assumption
  · simp [lastRoot]; assumption
  · simp [range_length] at *; omega

end Proofs.Cpp.TreeFindRoot
