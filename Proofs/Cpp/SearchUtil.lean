import Proofs.Cpp.Gen.SearchUtil
import Proofs.Cpp.Lib.Rle

/-! # `count` and `lower_bound_index` (library/array/search_util.hpp)

`count` counts the elements equal to `value` in an index range (`idx_end = -1` is the end of the vector);
`lower_bound_index` is the first index whose element is not less than `x` in a sorted vector, by binary
search in at most `bitWidth n + 2` steps. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.SearchUtil

/-- The end of the range of `count`: `idx_end`, or the size for `-1`. -/
def countEnd {T : Type} (v : Array T) (e : Int) : Int := if e = -1 then v.size else e

theorem count_spec {T : Type} [Inhabited T] [DecidableEq T] (v : Array T) (value : T) (b e : Int) (hb : 0 ≤ b)
    (hbe : b ≤ countEnd v e) (he : countEnd v e ≤ v.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.count v value b e
    ⦃⇓ r c => ⌜r = ((range b (countEnd v e)).filter (fun i => get v i = value)).length ∧
               c = t0 + 1 + (countEnd v e - b).toNat⌝⦄ := by
  mvcgen [cp.count]
  case inv1 =>
    exact ⇓⟨xs, n⟩ c => ⌜n = (xs.prefix.filter (fun i => get v i = value)).length ∧ c = t0 + 1 + xs.prefix.length⌝
  case inv2 =>
    exact ⇓⟨xs, n⟩ c => ⌜n = (xs.prefix.filter (fun i => get v i = value)).length ∧ c = t0 + 1 + xs.prefix.length⌝
  all_goals simp_all +zetaDelta [countEnd, size]
  all_goals first | omega | simp [range_length]

/-- `counts(v)`: the runs of equal values of `v` with their lengths (`rle`); for a sorted `v` these are
the distinct values with their numbers of occurrences (`rle_ok`, `unrle_rle`). At most `2 n + 1` steps. -/
theorem counts_spec {T : Type} [Inhabited T] [DecidableEq T] (v : Array T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.counts v
    ⦃⇓ r c => ⌜r.toList = rle v.toList ∧ c ≤ t0 + 1 + 2 * v.size⌝⦄ := by
  mvcgen [cp.counts]
  case inv1 =>
    exact ⇓⟨xs, ret⟩ c => ⌜ret.toList = rle (xs.prefix.map (get v)) ∧ c ≤ t0 + 1 + 2 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨hr, hc⟩ := ‹_ = rle _ ∧ _›
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    simp at e
    subst e
    refine ⟨?_, by omega⟩
    rw [← Array.toList_push]
    exact counts_push _ _ _ hr ((‹_ ∨ _›).imp (fun h => by simpa using h) id)
  · obtain ⟨hr, hc⟩ := ‹_ = rle _ ∧ _›
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    simp at e
    subst e
    obtain ⟨h0, he⟩ := ‹¬ _ ∧ _›
    refine ⟨counts_bump _ _ _ hr (by simpa using h0) he, by omega⟩
  · exact ⟨by simp [rle, rrle], by omega⟩
  · obtain ⟨hr, hc⟩ := ‹_ ∧ _›
    simp [size] at hr hc
    exact ⟨hr, by simpa [range] using hc⟩

/-- The vector is sorted. -/
def Sorted {T : Type} [LinearOrder T] [Inhabited T] (a : Array T) : Prop :=
  ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!

theorem bw_half (d : Nat) (h : 0 < d) : bitWidth (d / 2) + 1 ≤ bitWidth d ∧ bitWidth (d - d / 2 - 1) + 1 ≤ bitWidth d := by
  have := bitWidth_div_two d h
  exact ⟨by omega, by have := bitWidth_mono (show d - d / 2 - 1 ≤ d / 2 by omega); omega⟩

theorem lower_bound_index_spec {T : Type} [LinearOrder T] [Inhabited T] (a : Array T) (x : T)
    (hs : Sorted a) (hn : a.size < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.lower_bound_index a x
    ⦃⇓ r c => ⌜0 ≤ r ∧ r ≤ a.size ∧ (∀ i : Nat, (i : Int) < r → a[i]! < x) ∧
               (∀ i : Nat, r ≤ (i : Int) → i < a.size → x ≤ a[i]!) ∧ c ≤ t0 + 2 + bitWidth a.size⌝⦄ := by
  mvcgen [cp.lower_bound_index]
  case inv =>
    exact ⟨fun ⟨lo, hi⟩ c => ⌜0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ a.size ∧ (∀ i : Nat, (i : Int) < lo → a[i]! < x) ∧
                               (∀ i : Nat, hi ≤ (i : Int) → i < a.size → x ≤ a[i]!) ∧
                               c + bitWidth (hi - lo).toNat ≤ t0 + 1 + bitWidth a.size⌝,
           fun ⟨lo, _⟩ c => ⌜0 ≤ lo ∧ lo ≤ a.size ∧ (∀ i : Nat, (i : Int) < lo → a[i]! < x) ∧
                               (∀ i : Nat, lo ≤ (i : Int) → i < a.size → x ≤ a[i]!) ∧ c ≤ t0 + 2 + bitWidth a.size⌝,
           fun ⟨lo, hi⟩ => (hi - lo).toNat⟩
  all_goals simp +zetaDelta [fuel, size, div] at *
  · -- stop
    obtain ⟨h0, hlh, hh, hlo, hhi, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _›
    generalize (‹Int × Int›).1 = lo at *
    generalize (‹Int × Int›).2 = hi at *
    have : hi = lo := by omega
    subst this
    exact ⟨h0, hh, hlo, hhi, by omega⟩
  · -- the middle element is less than x
    obtain ⟨h0, hlh, hh, hlo, hhi, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _›
    have hm := of_decide_eq_true ‹decide (get a _ < x) = true›
    set lo := (‹Int × Int›).1 with hlo'
    set hi := (‹Int × Int›).2 with hhi'
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at *
    rw [get_eq] at hm
    obtain ⟨_, hb⟩ := bw_half (hi - lo).toNat (by omega)
    refine ⟨⟨by omega, by omega, hh, fun i hi' => ?_, hhi, ?_⟩, by omega⟩
    · rcases Int.lt_or_le (i : Int) lo with h | h
      · exact hlo i h
      · exact lt_of_le_of_lt (hs i _ (by omega) (by omega)) hm
    · have e : (hi - (lo + (hi - lo) / 2 + 1)).toNat = (hi - lo).toNat - (hi - lo).toNat / 2 - 1 := by omega
      rw [e]; omega
  · -- the middle element is at least x
    obtain ⟨h0, hlh, hh, hlo, hhi, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _›
    have hm := not_lt.mp (of_decide_eq_false ‹decide (get a _ < x) = false›)
    set lo := (‹Int × Int›).1 with hlo'
    set hi := (‹Int × Int›).2 with hhi'
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at *
    rw [get_eq] at hm
    obtain ⟨hb, _⟩ := bw_half (hi - lo).toNat (by omega)
    refine ⟨⟨h0, by omega, by omega, hlo, fun i hi' hin => ?_, ?_⟩, by omega⟩
    · exact le_trans hm (hs _ i (by omega) hin)
    · have e : ((hi - lo) / 2).toNat = (hi - lo).toNat / 2 := by omega
      rw [e]; omega
  · -- before the loop
    refine ⟨⟨?_, by omega⟩, by omega⟩
    · intro i h1 h2; omega
  · exact ‹_›

end Proofs.Cpp.SearchUtil
