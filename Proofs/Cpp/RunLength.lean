import Proofs.Cpp.Gen.RunLength
import Proofs.Cpp.Lib.Rle

/-! # `run_length` (library/string/run_length.hpp)

The runs of `v` (`rle v`) are written to `values[0, m)` and `counts[0, m)`, the rest of both buffers is kept, and the
number `m` of runs is returned; at most `n + 1` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.RunLength

variable {T : Type} [Inhabited T] [DecidableEq T]

/-- The pairs stored in the first `m` positions of the two buffers. -/
def pairsOf (vals : Array T) (cnts : Array Int) (m : Nat) : List (T × Int) :=
  (List.range m).map (fun k => (vals[k]!, cnts[k]!))

theorem pairsOf_snoc (vals : Array T) (cnts : Array Int) (m : Nat) (x : T) (c : Int) (hv : m < vals.size)
    (hc : m < cnts.size) :
    pairsOf (set vals (m : Int) x) (set cnts (m : Int) c) (m + 1) = pairsOf vals cnts m ++ [(x, c)] := by
  unfold pairsOf
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro k hk
    simp at hk
    rw [getElem!_set _ _ _ _ (by simpa using hv), getElem!_set _ _ _ _ (by simpa using hc)]
    simp [show k ≠ m by omega]
  · simp only [List.map_cons, List.map_nil]
    rw [getElem!_set _ _ _ _ (by simpa using hv), getElem!_set _ _ _ _ (by simpa using hc)]
    simp

theorem run_length_spec (v vals : Array T) (cnts : Array Int) (hv : v.size ≤ vals.size) (hc : v.size ≤ cnts.size)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.run_length v vals cnts
    ⦃⇓ r c => ⌜0 ≤ r.1 ∧ pairsOf r.2.1 r.2.2 r.1.toNat = rle v.toList ∧ r.2.1.size = vals.size ∧
               r.2.2.size = cnts.size ∧ (∀ k, r.1.toNat ≤ k → r.2.1[k]! = vals[k]! ∧ r.2.2[k]! = cnts[k]!) ∧
               c ≤ t0 + 1 + v.size⌝⦄ := by
  mvcgen [cp.run_length]
  case inv1 =>
    exact ⇓⟨xs, va, co, pre, cnt, m⟩ c =>
      ⌜0 ≤ m ∧ m.toNat ≤ xs.prefix.length ∧ va.size = vals.size ∧ co.size = cnts.size ∧
        (∀ k, m.toNat ≤ k → va[k]! = vals[k]! ∧ co[k]! = cnts[k]!) ∧
        ((xs.prefix = [] ∧ cnt = 0 ∧ pre = get v 0) ∨
          (pairsOf va co m.toNat ++ [(pre, cnt)] = rle (xs.prefix.map (get v)) ∧ m.toNat < xs.prefix.length)) ∧
        c = t0 + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · -- empty v
    have : v = ([] : List T).toArray := Array.eq_empty_of_size_eq_zero (by simp [Proofs.Cpp.size] at *; omega)
    subst this
    exact ⟨by simp [pairsOf, rle, rrle], by omega⟩
  · -- the same value continues the run
    set m := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.2.2.2 with hm
    set va := (‹Array T × Array ℤ × T × ℤ × ℤ›).1 with hva
    set co := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.1 with hco
    set pr := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.2.1 with hpr
    set cn := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.2.2.1 with hcn
    obtain ⟨h0, hml, hvs, hcs, hkeep, hinv, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (_ ∨ _) ∧ _›
    have heq : _ = get v _ := ‹(_ : T) = get v _›
    refine ⟨h0, ?_, hvs, hcs, hkeep, ?_, ?_⟩
    · omega
    rotate_left
    · omega
    rcases hinv with ⟨hp, h0c, hpre⟩ | ⟨hrle, hlt⟩
    · have e := range_cursor ‹range _ _ = _ ++ _ :: _›
      subst hp
      simp at e hml
      subst e
      have hm0 : m = 0 := by omega
      simp [hm0, pairsOf, h0c, rle, rrle, rrStep, heq]
    · rw [rle_snoc_last _ _ _ _ hrle.symm]
      simp only [heq, ite_true]
      exact ⟨by simp, by omega⟩
  · -- a new run starts: the closed run is written at position m
    set m := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.2.2.2 with hm
    set va := (‹Array T × Array ℤ × T × ℤ × ℤ›).1 with hva
    set co := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.1 with hco
    set pr := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.2.1 with hpr
    set cn := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.2.2.1 with hcn
    obtain ⟨h0, hml, hvs, hcs, hkeep, hinv, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (_ ∨ _) ∧ _›
    have hne : ¬ (_ : T) = get v _ := ‹¬ _ = get v _›
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    simp +zetaDelta [Proofs.Cpp.size] at hl e
    rcases hinv with ⟨hp, h0c, hpre⟩ | ⟨hrle, hlt⟩
    · subst hp; simp at e; rw [e] at hne; exact absurd hpre hne
    · have hmv : m.toNat < va.size := by omega
      have hmc : m.toNat < co.size := by omega
      have hsnoc := pairsOf_snoc va co m.toNat pr cn hmv hmc
      rw [show ((m.toNat : Nat) : Int) = m by omega] at hsnoc
      refine ⟨by omega, by omega, by simp [hvs], by simp [hcs], fun k hk => ?_, ⟨?_, by omega⟩, by omega⟩
      · rw [getElem!_set _ _ _ _ (by omega), getElem!_set _ _ _ _ (by omega)]
        simp only [show k ≠ m.toNat by omega, ite_false]
        exact hkeep k (by omega)
      · rw [show (m + 1).toNat = m.toNat + 1 by omega, hsnoc, rle_snoc_last _ _ _ _ hrle.symm, if_neg hne]
        simp
  · omega
  · -- the last run is written
    set m := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.2.2.2 with hm
    set va := (‹Array T × Array ℤ × T × ℤ × ℤ›).1 with hva
    set co := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.1 with hco
    set pr := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.2.1 with hpr
    set cn := (‹Array T × Array ℤ × T × ℤ × ℤ›).2.2.2.1 with hcn
    obtain ⟨h0, hml, hvs, hcs, hkeep, hinv, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (_ ∨ _) ∧ _›
    have hsz : v.size ≠ 0 := by simpa [Proofs.Cpp.size] using ‹¬ size v = 0›
    have hlen : (range 0 (size v)).length = v.size := by simp [range, Proofs.Cpp.size]
    have hmap : (range 0 (size v)).map (get v) = v.toList := by simp [Proofs.Cpp.size]
    simp only [hlen, hmap] at hinv hml hc
    rcases hinv with ⟨hp, _⟩ | ⟨hrle, hlt⟩
    · exfalso; have := congrArg List.length hp; rw [hlen] at this; exact hsz (by simpa using this)
    · have hmv : m.toNat < va.size := by omega
      have hmc : m.toNat < co.size := by omega
      have hsnoc := pairsOf_snoc va co m.toNat pr cn hmv hmc
      rw [show ((m.toNat : Nat) : Int) = m by omega] at hsnoc
      refine ⟨by omega, ?_, by simp [hvs], by simp [hcs], fun k hk => ?_, by omega⟩
      · rw [show (m + 1).toNat = m.toNat + 1 by omega, hsnoc, hrle]
      · rw [getElem!_set _ _ _ _ (by omega), getElem!_set _ _ _ _ (by omega)]
        simp only [show k ≠ m.toNat by omega, ite_false]
        exact hkeep k (by omega)

end Proofs.Cpp.RunLength
