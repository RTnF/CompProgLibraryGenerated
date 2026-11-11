import Proofs.Cpp.Prelude
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

namespace Proofs.Cpp

/-- `std::bit_width`: `0` for `0`, otherwise `log2 n + 1`. -/
def bitWidth (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

@[simp] theorem bitWidth_zero : bitWidth 0 = 0 := rfl

theorem bitWidth_div_two (n : Nat) (h : 0 < n) : bitWidth (n / 2) + 1 = bitWidth n := by
  unfold bitWidth
  by_cases h1 : n = 1
  · subst h1; rfl
  · have h2 : 2 ≤ n := by omega
    rw [Nat.log2_def n]; simp only [h2, ite_true]
    simp [show n / 2 ≠ 0 by omega, show n ≠ 0 by omega]

theorem bitWidth_mono {a b : Nat} (h : a ≤ b) : bitWidth a ≤ bitWidth b := by
  unfold bitWidth
  by_cases ha : a = 0
  · simp [ha]
  · have hb : b ≠ 0 := by omega
    simp only [ha, hb, ite_false]
    have : Nat.log2 a ≤ Nat.log2 b := by
      rw [Nat.le_log2 hb]; exact Nat.le_trans (Nat.log2_self_le ha) h
    omega

theorem bitWidth_lt_pow (n k : Nat) (h : n < 2 ^ k) : bitWidth n ≤ k := by
  unfold bitWidth
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false]
    have := (Nat.log2_lt hn).mpr h
    omega

theorem lt_bitWidth {m n : Nat} (h : 2 ^ m ≤ n) : m < bitWidth n := by
  have hn : n ≠ 0 := by have := Nat.one_le_two_pow (n := m); omega
  unfold bitWidth; simp only [hn, ite_false]
  have := (Nat.le_log2 hn).mpr h; omega

/-! ## Iterating a map (`f^[k] x`) -/

theorem iter_add (f : Int → Int) (m k : Nat) (x : Int) : f^[m + k] x = f^[m] (f^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc]; exact ih (f x)

theorem iter_range (f : Int → Int) (n : Int) (hf : ∀ x, 0 ≤ x → x < n → 0 ≤ f x ∧ f x < n) (m : Nat) :
    ∀ x, 0 ≤ x → x < n → 0 ≤ f^[m] x ∧ f^[m] x < n := by
  induction m with
  | zero => intro x h0 h1; exact ⟨h0, h1⟩
  | succ m ih => intro x h0 h1; have := hf x h0 h1; exact ih (f x) this.1 this.2

/-- Once two paths along `f` meet they stay together. -/
theorem met_mono (f : Int → Int) (u v : Int) {m m' : Nat} (h : f^[m] u = f^[m] v) (hm : m ≤ m') :
    f^[m'] u = f^[m'] v := by
  rw [show m' = (m' - m) + m by omega, iter_add, iter_add, h]

end Proofs.Cpp

namespace Proofs.Cpp

/-! ## The number of iterations of Euclid's algorithm -/

/-- A bound on the remaining iterations: the product of the pair halves on each step with `b ≤ a`. -/
def gcdCost (a b : Nat) : Nat := if b = 0 then 0 else (if b ≤ a then 1 else 2) + Nat.log2 (a * b)

theorem log2_mono'' (a b : Nat) (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp [Nat.log2_zero]
  · rw [Nat.le_log2 (by omega)]; exact Nat.le_trans (Nat.log2_self_le (by omega)) h

@[simp] theorem gcdCost_zero (a : Nat) : gcdCost a 0 = 0 := by simp [gcdCost]

theorem gcdCost_step (a b : Nat) (hb : 0 < b) : 1 + gcdCost b (a % b) ≤ gcdCost a b := by
  have hr : a % b < b := Nat.mod_lt _ hb
  by_cases hba : b ≤ a
  · by_cases hr0 : a % b = 0
    · simp [gcdCost, hr0, show b ≠ 0 by omega, hba]
    · have hq : 1 ≤ a / b := Nat.div_pos hba hb
      have hdm := Nat.mod_add_div a b
      have hbq : b ≤ b * (a / b) := Nat.le_mul_of_pos_right b hq
      have h2 : 2 * (a % b) ≤ a := by omega
      have hpos : 0 < b * (a % b) := Nat.mul_pos hb (by omega)
      have hl : Nat.log2 (2 * (b * (a % b))) = Nat.log2 (b * (a % b)) + 1 := Nat.log2_two_mul (by omega)
      have hm : 2 * (b * (a % b)) ≤ a * b := by
        have := Nat.mul_le_mul_left b h2
        rw [Nat.mul_comm a b]
        calc 2 * (b * (a % b)) = b * (2 * (a % b)) := by rw [← Nat.mul_assoc, Nat.mul_comm 2 b, Nat.mul_assoc]
          _ ≤ b * a := this
      have := log2_mono'' _ _ hm
      simp [gcdCost, hr0, show b ≠ 0 by omega, hba, show a % b ≤ b by omega]
      omega
  · have e : a % b = a := Nat.mod_eq_of_lt (by omega)
    by_cases ha : a = 0
    · simp [gcdCost, e, ha, show b ≠ 0 by omega]
    · simp [gcdCost, e, ha, show b ≠ 0 by omega, hba, show a ≤ b by omega, Nat.mul_comm b a]
      omega

end Proofs.Cpp

namespace Proofs.Cpp

theorem getElem!_push {α : Type} [Inhabited α] (v : Array α) (x : α) (j : Nat) :
    (v.push x)[j]! = if j < v.size then v[j]! else if j = v.size then x else default := by
  by_cases h1 : j < v.size
  · simp [h1, getElem!_pos, Array.getElem_push_lt, Nat.lt_succ_of_lt h1]
  · by_cases h2 : j = v.size
    · subst h2; simp [getElem!_pos]
    · simp [h1, h2, getElem!_neg, show ¬ j < v.size + 1 by omega]

@[simp] theorem size_get_set_self {α : Type} [Inhabited α] (v : Array (Array α)) (i : Nat) (x : Array α)
    (hi : i < v.size) : (set v (i : Int) x)[i]! = x := by
  rw [getElem!_set _ _ _ _ (by simpa using hi)]; simp

end Proofs.Cpp

namespace Proofs.Cpp

/-! ## The last element of a vector -/

theorem back_of_toList {α : Type} [Inhabited α] (ret : Array α) (L : List α) (p : α) (h : ret.toList = L ++ [p]) :
    back ret = p := by
  have hsz : ret.size = L.length + 1 := by rw [← Array.length_toList, h]; simp
  simp only [back, Array.back!, hsz, Nat.add_sub_cancel]
  rw [getElem!_pos ret L.length (by omega), ← Array.getElem_toList]
  simp [h]

theorem get_last_of_toList {α : Type} [Inhabited α] (ret : Array α) (L : List α) (p : α) (h : ret.toList = L ++ [p]) :
    get ret (size ret - 1) = p := by
  have hsz : ret.size = L.length + 1 := by rw [← Array.length_toList, h]; simp
  simp only [get_eq, size, hsz]
  rw [show ((L.length + 1 : Nat) : Int) - 1 = (L.length : Int) by omega, Int.toNat_natCast,
    getElem!_pos ret L.length (by omega), ← Array.getElem_toList]
  simp [h]

theorem set_last_toList {α : Type} (ret : Array α) (L : List α) (p q : α) (h : ret.toList = L ++ [p]) :
    (set ret (size ret - 1) q).toList = L ++ [q] := by
  have hsz : ret.size = L.length + 1 := by rw [← Array.length_toList, h]; simp
  simp only [set, size, hsz]
  rw [show ((L.length + 1 : Nat) : Int) - 1 = (L.length : Int) by omega, Int.toNat_natCast, Array.set!,
    Array.toList_setIfInBounds, h, List.set_append_right _ _ (by simp)]
  simp

end Proofs.Cpp
