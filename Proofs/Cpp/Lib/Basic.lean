import Proofs.Cpp.Prelude
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Facts about the operations of `Proofs.Cpp.Prelude` shared by the component proofs. -/

open Std.Do

namespace Proofs.Cpp


/-- A total-correctness triple from the tick count `t0` gives the run's result. -/
theorem run_of_triple {α : Type} {x : M α} {t0 : Nat} {P : α → Nat → Prop}
    (h : ⦃fun c => ⌜c = t0⌝⦄ x ⦃⇓ r c => ⌜P r c⌝⦄) : ∃ r c, x.run t0 = some (r, c) ∧ P r c := by
  have h' := (Triple.iff.mp h) t0
  simp [wp] at h'
  revert h'
  cases hx : StateT.run x t0 with
  | none => intro h'; exact h'.elim
  | some p => intro h'; exact ⟨p.1, p.2, rfl, h'⟩

/-- A triple from a computed run. -/
theorem triple_of_run {α : Type} {x : M α} {t0 : Nat} {P : α → Nat → Prop} (r : α) (c : Nat)
    (hx : x.run t0 = some (r, c)) (hp : P r c) : ⦃fun c => ⌜c = t0⌝⦄ x ⦃⇓ r c => ⌜P r c⌝⦄ := by
  apply Triple.iff.mpr
  intro s hs
  simp at hs; subst hs
  simp [wp, hx]
  exact hp


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

namespace Proofs.Cpp

/-! ## Vector reads and writes -/

@[simp] theorem size_set {α : Type} (v : Array α) (i : Int) (x : α) : (set v i x).size = v.size := by
  simp [set]

theorem getElem!_set {α : Type} [Inhabited α] (v : Array α) (i : Int) (x : α) (k : Nat)
    (hk : i.toNat < v.size) : (set v i x)[k]! = if k = i.toNat then x else v[k]! := by
  unfold set
  by_cases h : k = i.toNat
  · subst h; simp [hk]
  · simp only [h, ite_false]
    by_cases hk2 : k < v.size
    · simp [getElem!_pos, hk2, Ne.symm h]
    · simp [getElem!_neg, hk2]

theorem get_eq {α : Type} [Inhabited α] (v : Array α) (i : Int) : get v i = v[i.toNat]! := rfl

end Proofs.Cpp

namespace Proofs.Cpp

/-- The element at a cursor of `range a b` is `a` plus the length of the prefix. -/
theorem range_cursor {a b cur : Int} {pref suff : List Int} (h : range a b = pref ++ cur :: suff) :
    cur = a + pref.length := by
  have hl : pref.length < (range a b).length := by rw [h]; simp
  have e := congrArg (fun l => l[pref.length]?) h
  simp only [List.getElem?_append_right (Nat.le_refl pref.length), Nat.sub_self, List.getElem?_cons_zero] at e
  simp only [range, List.length_map, List.length_range] at e hl
  rw [List.getElem?_map, List.getElem?_range hl] at e
  simp at e
  omega

theorem range_prefix_length {a b : Int} {pref suff : List Int} {cur : Int} (h : range a b = pref ++ cur :: suff) :
    pref.length < (b - a).toNat := by
  have := congrArg List.length h
  simp [range] at this
  omega

end Proofs.Cpp

namespace Proofs.Cpp

theorem toNat_add_natCast (a : Int) (n : Nat) (ha : 0 ≤ a) : (a + (n : Int)).toNat = a.toNat + n := by omega

@[simp] theorem toNat_one_add (n : Nat) : (1 + (n : Int)).toNat = n + 1 := by omega

@[simp] theorem toNat_zero_add (n : Nat) : (0 + (n : Int)).toNat = n := by omega

end Proofs.Cpp

namespace Proofs.Cpp

@[simp] theorem range_zero_map_get {α : Type} [Inhabited α] (v : Array α) :
    (range 0 (v.size : Int)).map (get v) = v.toList := range_map_get v

@[simp] theorem range_zero_length (n : Nat) : (range 0 (n : Int)).length = n := by simp [range]

@[simp] theorem get_natCast {α : Type} [Inhabited α] (v : Array α) (n : Nat) : get v (n : Int) = v[n]! := rfl

end Proofs.Cpp
