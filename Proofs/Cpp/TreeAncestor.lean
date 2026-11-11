import Proofs.Cpp.Gen.TreeAncestor
import Proofs.Cpp.Lib.Basic

/-! # `tree_ancestor` (library/tree/tree_ancestor.hpp)

The `i`-th ancestor from a doubling table: `f^i(v)` when `anc[k][x] = f^(2^k)(x)`; `bitWidth i + 2` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeAncestor

/-- `anc` is the doubling table of `f` on `[0, n)` for the levels used by `i`: `anc[k][x] = f^(2^k)(x)`. -/
def TabOK (anc : Array (Array Int)) (f : Int → Int) (n : Int) (i : Nat) : Prop :=
  ∀ k : Nat, 2 ^ k ≤ i → ∀ x : Int, 0 ≤ x → x < n → (anc[k]!)[x.toNat]! = f^[2 ^ k] x

theorem mod_two_pow_succ (I K : Nat) :
    I % 2 ^ (K + 1) = I % 2 ^ K + (if I / 2 ^ K % 2 = 1 then 2 ^ K else 0) := by
  rw [Nat.pow_succ, Nat.mod_mul]
  have : I / 2 ^ K % 2 < 2 := Nat.mod_lt _ (by omega)
  split <;> rename_i h
  · rw [h]; omega
  · rw [show I / 2 ^ K % 2 = 0 by omega]; omega

theorem bit_eq (I K : Nat) : mod (div (I : Int) ((2 ^ K : Nat) : Int)) 2 = ((I / 2 ^ K % 2 : Nat) : Int) := by
  simp only [div, mod]
  rw [show Int.tdiv (I : Int) ((2 ^ K : Nat) : Int) = ((I / 2 ^ K : Nat) : Int) by simp]
  rfl

theorem brk (f : Int → Int) (v w k j : Int) (I s t0 : Nat)
    (h : 0 ≤ k ∧ j = 2 ^ k.toNat ∧ k ≤ (bitWidth I : Int) ∧ w = f^[I % 2 ^ k.toNat] v ∧ 0 ≤ w ∧ w < n ∧
      s = t0 + 1 + k.toNat) (hlt : (I : Int) < j) :
    w = f^[I] v ∧ s + 1 = t0 + 2 + bitWidth I := by
  obtain ⟨hk, hj, hkb, hw, -, -, hc⟩ := h
  subst hj
  have hlt' : I < 2 ^ k.toNat := by exact_mod_cast hlt
  have := bitWidth_lt_pow I k.toNat hlt'
  refine ⟨by rw [hw, Nat.mod_eq_of_lt hlt'], by omega⟩

theorem cont (anc : Array (Array Int)) (f : Int → Int) (n v w k j : Int) (I s t0 : Nat)
    (hf : ∀ x, 0 ≤ x → x < n → 0 ≤ f x ∧ f x < n) (hv : 0 ≤ v ∧ v < n) (htab : TabOK anc f n I)
    (h : 0 ≤ k ∧ j = 2 ^ k.toNat ∧ k ≤ (bitWidth I : Int) ∧ w = f^[I % 2 ^ k.toNat] v ∧ 0 ≤ w ∧ w < n ∧
      s = t0 + 1 + k.toNat) (hle : j ≤ (I : Int)) (b : Bool) (hb : b = decide (mod (div (I : Int) j) 2 = 1)) :
    let w' := if b then get (get anc k) w else w
    (0 ≤ k + 1 ∧ j * 2 = 2 ^ (k + 1).toNat ∧ k + 1 ≤ (bitWidth I : Int) ∧
      w' = f^[I % 2 ^ (k + 1).toNat] v ∧ 0 ≤ w' ∧ w' < n ∧ s + 1 = t0 + 1 + (k + 1).toNat) ∧
    bitWidth I - (k + 1).toNat < bitWidth I - k.toNat := by
  intro w'
  obtain ⟨hk, hj, hkb, hw, hw0, hwn, hc⟩ := h
  have e : (k + 1).toNat = k.toNat + 1 := by omega
  have hj' : j = ((2 ^ k.toNat : Nat) : Int) := by rw [hj]; push_cast; rfl
  have hle' : 2 ^ k.toNat ≤ I := by rw [hj'] at hle; exact_mod_cast hle
  have hlt := lt_bitWidth hle'
  rw [hj', bit_eq] at hb
  have hm := mod_two_pow_succ I k.toNat
  have hstep : w' = f^[I % 2 ^ (k.toNat + 1)] v := by
    simp only [w']
    by_cases hbit : I / 2 ^ k.toNat % 2 = 1
    · have : b = true := by rw [hb]; simp [hbit]
      rw [this, if_pos rfl, hm, if_pos hbit, Nat.add_comm, iter_add, ← hw]
      have := htab k.toNat hle' w hw0 hwn
      simp only [get]; exact this
    · have : b = false := by rw [hb]; simp only [decide_eq_false_iff_not]; exact_mod_cast hbit
      rw [this, hm, ite_eq_right_iff.mpr (fun h => absurd h hbit), Nat.add_zero, ← hw]; rfl
  have hr : 0 ≤ w' ∧ w' < n := by
    rw [hstep]; exact iter_range f n hf _ v hv.1 hv.2
  refine ⟨⟨by omega, by rw [hj, e, Int.pow_succ], by omega, by rw [e]; exact hstep, hr.1, hr.2,
    by omega⟩, by omega⟩

/-- `tree_ancestor(anc, v, i) = f^i(v)` when `anc` is the doubling table of `f` (a map of `[0, n)` into itself);
`bitWidth i + 2` steps (`O(log i)`). -/
theorem tree_ancestor_spec (anc : Array (Array Int)) (f : Int → Int) (n v i : Int)
    (hf : ∀ x, 0 ≤ x → x < n → 0 ≤ f x ∧ f x < n) (hv : 0 ≤ v ∧ v < n) (hi : 0 ≤ i) (hi2 : i < 2 ^ 30)
    (htab : TabOK anc f n i.toNat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_ancestor anc v i
    ⦃⇓ r c => ⌜r = f^[i.toNat] v ∧ c = t0 + 2 + bitWidth i.toNat⌝⦄ := by
  obtain ⟨I, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  have hw : bitWidth I ≤ 30 := bitWidth_lt_pow I 30 (by exact_mod_cast hi2)
  clear hi hi2
  simp only [Int.toNat_natCast] at *
  mvcgen [cp.tree_ancestor]
  case inv =>
    exact ⟨fun ⟨w, k, j⟩ c => ⌜0 ≤ k ∧ j = 2 ^ k.toNat ∧ k.toNat ≤ bitWidth I ∧
             w = f^[I % 2 ^ k.toNat] v ∧ 0 ≤ w ∧ w < n ∧ c = t0 + 1 + k.toNat⌝,
           fun ⟨w, _, _⟩ c => ⌜w = f^[I] v ∧ c = t0 + 2 + bitWidth I⌝,
           fun ⟨_, k, _⟩ => bitWidth I - k.toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  · exact brk f v _ _ _ _ _ _ ‹_› ‹_›
  · exact cont anc f n v _ _ _ _ _ _ hf hv htab ‹_› ‹_› true (by simpa using ‹mod _ _ = 1›)
  · exact cont anc f n v _ _ _ _ _ _ hf hv htab ‹_› ‹_› false (by simpa using ‹¬mod _ _ = 1›)
  · exact ⟨⟨by simp [Nat.mod_one], hv.1, hv.2, ‹_›⟩, by omega⟩
  · exact ‹_ ∧ _›

end Proofs.Cpp.TreeAncestor
