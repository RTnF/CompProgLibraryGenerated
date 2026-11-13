import Proofs.Cpp.Gen.Doubling
import Proofs.Cpp.BitWidthU64

/-! # `doubling` (library/array/doubling.hpp) -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.Doubling

@[spec] theorem bit_width_wp (value : UInt64) {Q : PostCond Int PS} :
    ⦃fun t => Q.1 (bitWidth value.toNat : Int) (t + 2 + bitWidth value.toNat)⦄ cp.bit_width_u64 value ⦃Q⦄ := by
  have W := wp_of_triple (Q := Q) (fun t0 => Proofs.Cpp.BitWidthU64.bit_width_u64_spec value t0)
  apply Triple.iff.mpr
  intro s hs
  apply (Triple.iff.mp W) s
  intro r t' ⟨hE, ht'⟩
  rw [hE, ht']
  exact hs

/-- Row `i` of the table: `f^(2^i)` with `f x = v[x]`. -/
def F (v : Array Int) (i : Nat) (j : Int) : Int := (fun x => v[x.toNat]!)^[2 ^ i] j

/-- Rows `0 .. K-1` of the table are complete; the rows from `K` are empty. -/
def DI (v : Array Int) (ret : Array (Array Int)) (w K : Nat) : Prop :=
  ret.size = w ∧ (∀ i, i < K → i < w → ret[i]!.size = v.size ∧ ∀ j, j < v.size → ret[i]![j]! = F v i j) ∧
    (∀ i, K ≤ i → i < w → ret[i]! = ([] : List Int).toArray)

/-- Row `i` has its first `J` entries; the rows below are complete and the rows above empty. -/
def RI (v : Array Int) (ret : Array (Array Int)) (w i J : Nat) : Prop :=
  ret.size = w ∧ (∀ i', i' < i → ret[i']!.size = v.size ∧ ∀ j, j < v.size → ret[i']![j]! = F v i' j) ∧
    ret[i]!.size = J ∧ (∀ j, j < J → ret[i]![j]! = F v i j) ∧ (∀ i', i < i' → i' < w → ret[i']! = ([] : List Int).toArray)

theorem F_range (v : Array Int) (hv : ∀ i, i < v.size → 0 ≤ v[i]! ∧ v[i]! < v.size) (i : Nat) (j : Int)
    (h0 : 0 ≤ j) (h1 : j < v.size) : 0 ≤ F v i j ∧ F v i j < v.size :=
  iter_range _ _ (fun x hx0 hx1 => hv x.toNat (by omega) |>.imp id (by omega)) _ _ h0 h1

theorem F_succ (v : Array Int) (i : Nat) (hi : 1 ≤ i) (j : Int) : F v i j = F v (i - 1) (F v (i - 1) j) := by
  unfold F
  rw [← iter_add]
  congr 1
  have : i = (i - 1) + 1 := by omega
  conv => lhs; rw [this, Nat.pow_succ]
  omega

theorem F_zero (v : Array Int) (j : Int) : F v 0 j = v[j.toNat]! := rfl

theorem ri_step (v : Array Int) (hv : ∀ i, i < v.size → 0 ≤ v[i]! ∧ v[i]! < v.size) (ret : Array (Array Int))
    (w i J : Nat) (H : RI v ret w i J) (hi1 : 1 ≤ i) (hiw : i < w) (hJ : J < v.size) (ci cj : Int) (hci : ci = i)
    (hcj : cj = J) :
    RI v (set ret ci ((get ret ci).push (get (get ret (ci - 1)) (get (get ret (ci - 1)) cj)))) w i (J + 1) := by
  subst hci hcj
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  have e1 : ((i : Int) - 1).toNat = i - 1 := by omega
  obtain ⟨r1, r2⟩ := h2 (i - 1) (by omega)
  have g1 : get (get ret ((i : Int) - 1)) (J : Int) = F v (i - 1) J := by
    simp only [get, e1, Int.toNat_natCast]; exact r2 J hJ
  have hr := F_range v hv (i - 1) J (by omega) (by omega)
  have g2 : get (get ret ((i : Int) - 1)) (F v (i - 1) J) = F v i J := by
    simp only [get, e1]; rw [r2 _ (by omega), F_succ v i hi1]; congr 1; omega
  rw [g1, g2]
  have hg : ∀ k, (set ret (i : Int) ((get ret (i : Int)).push (F v i J)))[k]! =
      if k = i then (get ret (i : Int)).push (F v i J) else ret[k]! := by
    intro k; rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp
  have gi : get ret (i : Int) = ret[i]! := by simp [get]
  refine ⟨by simp [h1], fun i' hi' => ?_, ?_, fun j hj => ?_, fun i' hi' hw' => ?_⟩
  · rw [hg, if_neg (by omega)]; exact h2 i' hi'
  · rw [hg, if_pos rfl, gi]; simp [h3]
  · rw [hg, if_pos rfl, gi, getElemBang_push]
    split
    · exact h4 j (by omega)
    · rw [if_pos (by omega)]; congr 1; omega
  · rw [hg, if_neg (by omega)]; exact h5 i' hi' hw'

theorem chk (v : Array Int) (hv : ∀ i, i < v.size → 0 ≤ v[i]! ∧ v[i]! < v.size) (pref suff : List Int) (cur : Int)
    (hr : range 0 (size v) = pref ++ cur :: suff) : 0 ≤ get v cur ∧ get v cur < size v := by
  have e := range_cursor hr
  have hl := congrArg List.length hr
  simp [range_length, size] at hl e
  subst e
  have := hv pref.length (by omega)
  simp [get, size]; omega

theorem doubling_spec (v : Array Int) (kmax : UInt64) (hk : 0 < kmax.toNat) (hn : v.size < 2 ^ 31)
    (hv : ∀ i, i < v.size → 0 ≤ v[i]! ∧ v[i]! < v.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.doubling v kmax
    ⦃⇓ r c => ⌜r.size = bitWidth kmax.toNat ∧
      (∀ i, i < r.size → r[i]!.size = v.size ∧ ∀ j, j < v.size → r[i]![j]! = F v i j) ∧
      c ≤ t0 + 3 + 2 * v.size + 3 * bitWidth kmax.toNat + bitWidth kmax.toNat * (1 + 2 * v.size)⌝⦄ := by
  mvcgen [cp.doubling]
  case inv1 => exact ⇓⟨xs, _⟩ c => ⌜c = t0 + 1 + xs.prefix.length⌝
  case inv2 =>
    rename_i _ s0 _ _ _ _
    exact ⇓⟨xs, ret⟩ c => ⌜DI v ret (bitWidth kmax.toNat) (1 + xs.prefix.length) ∧
      c = s0 + 2 + 2 * bitWidth kmax.toNat + v.size + xs.prefix.length * (1 + 2 * v.size)⌝
  case inv3 =>
    rename_i pref _ _ _ _ s2 _
    exact ⇓⟨ys, ret⟩ c => ⌜RI v ret (bitWidth kmax.toNat) (1 + pref.length) ys.prefix.length ∧
      c = s2 + 1 + 2 * ys.prefix.length⌝
  all_goals simp +zetaDelta at *
  case vc1.step.isTrue.isTrue => omega
  case vc2.step.isTrue.isFalse =>
    have := chk v hv _ _ _ ‹range 0 _ = _ ++ _ :: _›
    omega
  case vc3.step.isFalse =>
    have := chk v hv _ _ _ ‹range 0 _ = _ ++ _ :: _›
    omega
  case vc4.isTrue.isTrue.pre => assumption
  case vc5.step =>
    have hbw : 1 ≤ bitWidth kmax.toNat := Nat.lt_of_lt_of_le (by simp [bitWidth]) (bitWidth_mono hk)
    obtain ⟨H, hc⟩ := ‹RI _ _ _ _ _ ∧ _›
    have hr1 := ‹range 1 _ = _ ++ _ :: _›
    have hr0 := ‹range 0 _ = _ ++ _ :: _›
    have e1 := range_cursor hr1
    have e0 := range_cursor hr0
    have hl1 := congrArg List.length hr1
    have hl0 := congrArg List.length hr0
    simp +zetaDelta [range_length, size] at hl1 hl0 e1 e0
    refine ⟨ri_step v hv _ _ _ _ H (by omega) (by omega) (by omega) _ _ (by rw [e1]; push_cast; ring) e0, by omega⟩
  case vc6.step.pre =>
    obtain ⟨H, hc⟩ := ‹DI _ _ _ _ ∧ _›
    have hr1 := ‹range 1 _ = _ ++ _ :: _›
    have hl1 := congrArg List.length hr1
    simp +zetaDelta [range_length, size] at hl1
    obtain ⟨d1, d2, d3⟩ := H
    exact ⟨d1, fun i' hi' => d2 i' hi' (by omega), by rw [d3 _ (Nat.le_refl _) (by omega)]; rfl,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun i' hi' hw' => d3 i' (by omega) hw'⟩
  case vc7.step.post.success =>
    obtain ⟨H, hc⟩ := ‹RI _ _ _ _ _ ∧ _›
    obtain ⟨H2, hc2⟩ := ‹DI _ _ _ _ ∧ _›
    have hr1 := ‹range 1 _ = _ ++ _ :: _›
    have hl1 := congrArg List.length hr1
    simp +zetaDelta [range_length, size] at hl1 hc H
    obtain ⟨r1, r2, r3, r4, r5⟩ := H
    refine ⟨⟨r1, fun i hi hw => ?_, fun i hi hw => r5 i (by omega) hw⟩, by rw [hc, hc2]; ring⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (1 + _) + 1 by omega) with h | h
    · exact r2 i h
    · subst h; exact ⟨r3, r4⟩
  case vc9.isTrue.isTrue.post.success.pre =>
    refine ⟨⟨by simp [replicate], fun i hi hw => ?_, fun i hi hw => ?_⟩, by omega⟩
    · have : i = 0 := by omega
      subst this
      rw [getElemBang_set _ _ _ _ (by simp [replicate]; omega)]
      simp [F_zero]
    · rw [getElemBang_set _ _ _ _ (by simp [replicate]; omega), if_neg (by omega)]
      simp [replicate]; rw [getElem!_pos _ _ (by simp; omega)]; simp
  case vc10.isTrue.isTrue.post.success.post.success =>
    have hbw : 1 ≤ bitWidth kmax.toNat := Nat.lt_of_lt_of_le (by simp [bitWidth]) (bitWidth_mono hk)
    obtain ⟨H, hc⟩ := ‹DI _ _ _ _ ∧ _›
    simp [range_length] at H hc
    obtain ⟨d1, d2, -⟩ := H
    refine ⟨d1, fun i hi => d2 i (by omega) (by omega), ?_⟩
    rw [d1]
    have : bitWidth kmax.toNat - 1 + 1 = bitWidth kmax.toNat := by omega
    have h0 := ‹_ = t0 + 1 + (range 0 (size v)).length›
    simp [range_length, size] at h0
    have hm : 1 + 2 * v.size ≤ bitWidth kmax.toNat * (1 + 2 * v.size) := Nat.le_mul_of_pos_left _ hbw
    rw [Nat.sub_mul, Nat.one_mul] at hc
    have hc2 := ‹_ = _ + 2 + 2 * bitWidth kmax.toNat + v.size + _›
    omega
  case vc13.isTrue.isFalse =>
    rename_i h
    simp [size] at h
    have := UInt64.lt_iff_toNat_lt.mp h
    simp only [UInt64.ofInt, UInt64.toNat_ofNat'] at this
    omega
  case vc14.isFalse =>
    rename_i h; subst h; simp at hk

end Proofs.Cpp.Doubling
