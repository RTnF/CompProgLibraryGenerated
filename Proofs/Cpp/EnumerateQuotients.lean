import Proofs.Cpp.Gen.EnumerateQuotients
import Proofs.Cpp.Lib.Basic
import Proofs.EnumerateQuotientsMath
import Mathlib.Data.Nat.Sqrt

/-! # `enumerate_quotients` (library/number_theory/enumerate_quotients.hpp)

The model refines `qlist n K` of `Proofs.EnumerateQuotientsMath`, where `K` is the result of the binary
search (`KOK`). The result is the ascending list of the positive values `n / x` (`qlist_spec`), and the
number of ticks is at most `t0 + 36 + 3 * (n / K + K - 1) ≤ t0 + 42 + 6 * sqrt n`. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.EnumerateQuotientsMath

namespace Proofs.Cpp.EnumerateQuotients

abbrev L (a : Array UInt64) : List Nat := a.toList.map UInt64.toNat

/-- The facts on `K = ok` after the binary search. -/
def KOK (n K : Nat) : Prop := 1 ≤ K ∧ K ≤ 2 ^ 32 ∧ n ≤ K * (K + 1) ∧ (K = 1 ∨ (K - 1) * K < n)

theorem two64 : (2:Nat) ^ 64 = 18446744073709551616 := by norm_num

theorem sum_mod (ok ng : UInt64) (ha : ok.toNat ≤ 2 ^ 32) (hb : ng.toNat < ok.toNat) :
    (ok.toNat + ng.toNat) % 18446744073709551616 = ok.toNat + ng.toNat :=
  Nat.mod_eq_of_lt (by omega)

theorem mid_toNat (ok ng : UInt64) (ha : ok.toNat ≤ 2 ^ 32) (hb : ng.toNat < ok.toNat) :
    ((ok + ng) / 2 * ((ok + ng) / 2 + 1)).toNat =
      (ok.toNat + ng.toNat) / 2 * ((ok.toNat + ng.toNat) / 2 + 1) := by
  have hk : (ok.toNat + ng.toNat) / 2 < 2 ^ 32 := by omega
  have hp : (ok.toNat + ng.toNat) / 2 * ((ok.toNat + ng.toNat) / 2 + 1) < 2 ^ 64 :=
    calc _ ≤ (2 ^ 32 - 1) * 2 ^ 32 := Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 64 := by norm_num
  have e1 : ((ok + ng) / 2).toNat = (ok.toNat + ng.toNat) / 2 := by
    rw [UInt64.toNat_div, UInt64.toNat_add, two64, sum_mod ok ng ha hb]; rfl
  have e2 : ((ok + ng) / 2 + 1).toNat = (ok.toNat + ng.toNat) / 2 + 1 := by
    rw [UInt64.toNat_add, e1, two64, UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_mul, e1, e2, Nat.mod_eq_of_lt hp]

theorem sub_toNat (ok ng : UInt64) (hb : ng.toNat < ok.toNat) : (ok - ng).toNat = ok.toNat - ng.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt hb))

theorem gap_le (ok ng : UInt64) (hb : ng.toNat < ok.toNat) (h : ok - ng ≤ 1) : ok.toNat - ng.toNat ≤ 1 := by
  have := UInt64.le_iff_toNat_le.mp h
  rwa [sub_toNat _ _ hb, UInt64.toNat_one] at this

theorem gap_gt (ok ng : UInt64) (hb : ng.toNat < ok.toNat) (h : 1 < ok - ng) : 1 < ok.toNat - ng.toNat := by
  have := UInt64.lt_iff_toNat_lt.mp h
  rwa [sub_toNat _ _ hb, UInt64.toNat_one] at this

theorem bs_done (n a b s t0 : Nat)
    (H : b < a ∧ a ≤ 2 ^ 32 ∧ n ≤ a * (a + 1) ∧ (b = 0 ∨ b * (b + 1) < n) ∧ s + bitWidth (a - b - 1) ≤ t0 + 1 + 32)
    (h : a - b ≤ 1) : KOK n a ∧ s ≤ t0 + 33 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  have ha : a = b + 1 := by omega
  subst ha
  refine ⟨⟨by omega, h2, h3, ?_⟩, by simp at h5; omega⟩
  rcases h4 with h4 | h4
  · left; omega
  · right; simpa using h4

theorem bw_step (a b k : Nat) (h : 1 < a - b) (hk : k = (a + b) / 2) :
    bitWidth (k - b - 1) + 1 ≤ bitWidth (a - b - 1) ∧ bitWidth (a - k - 1) + 1 ≤ bitWidth (a - b - 1) := by
  have hb := bitWidth_div_two (a - b - 1) (by omega)
  constructor
  · rw [← hb]; exact Nat.add_le_add_right (bitWidth_mono (by omega)) 1
  · rw [← hb]; exact Nat.add_le_add_right (bitWidth_mono (by omega)) 1

theorem bs_left (n a b s t0 : Nat)
    (H : b < a ∧ a ≤ 2 ^ 32 ∧ n ≤ a * (a + 1) ∧ (b = 0 ∨ b * (b + 1) < n) ∧ s + bitWidth (a - b - 1) ≤ t0 + 1 + 32)
    (h : 1 < a - b) (hk : n ≤ (a + b) / 2 * ((a + b) / 2 + 1)) :
    (b < (a + b) / 2 ∧ (a + b) / 2 ≤ 2 ^ 32 ∧ n ≤ (a + b) / 2 * ((a + b) / 2 + 1) ∧ (b = 0 ∨ b * (b + 1) < n) ∧
      s + 1 + bitWidth ((a + b) / 2 - b - 1) ≤ t0 + 1 + 32) ∧ (a + b) / 2 - b < a - b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  have := (bw_step a b _ h rfl).1
  exact ⟨⟨by omega, by omega, hk, h4, by omega⟩, by omega⟩

theorem bs_right (n a b s t0 : Nat)
    (H : b < a ∧ a ≤ 2 ^ 32 ∧ n ≤ a * (a + 1) ∧ (b = 0 ∨ b * (b + 1) < n) ∧ s + bitWidth (a - b - 1) ≤ t0 + 1 + 32)
    (h : 1 < a - b) (hk : (a + b) / 2 * ((a + b) / 2 + 1) < n) :
    ((a + b) / 2 < a ∧ a ≤ 2 ^ 32 ∧ n ≤ a * (a + 1) ∧ (a + b < 2 ∨ (a + b) / 2 * ((a + b) / 2 + 1) < n) ∧
      s + 1 + bitWidth (a - (a + b) / 2 - 1) ≤ t0 + 1 + 32) ∧ a - (a + b) / 2 < a - b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  have := (bw_step a b _ h rfl).2
  exact ⟨⟨by omega, h2, h3, Or.inr hk, by omega⟩, by omega⟩

theorem L_push (a : Array UInt64) (x : UInt64) : L (a.push x) = L a ++ [x.toNat] := by simp [L]

theorem p_small (n K : Nat) (hK : KOK n K) (hn : n < 2 ^ 64) : n / K + 1 < 2 ^ 64 := by
  obtain ⟨h1, -, h3, -⟩ := hK
  rcases Nat.lt_or_ge K 2 with h | h
  · have : K = 1 := by omega
    subst this; simp at h3 ⊢; omega
  · have : n / K ≤ n / 2 := Nat.div_le_div_left h (by omega)
    omega

theorem div_toNat (n K : UInt64) : (n / K).toNat = n.toNat / K.toNat := UInt64.toNat_div n K

theorem first_exit (n K i : UInt64) (s s1 : Nat) (ret : Array UInt64)
    (H : 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat / K.toNat + 1 ∧ L ret = firstPart (i.toNat - 1) ∧ s = s1 + 2 * (i.toNat - 1))
    (h : n / K < i) : L ret = firstPart (n.toNat / K.toNat) ∧ s = s1 + 2 * (n.toNat / K.toNat) := by
  have h' := UInt64.lt_iff_toNat_lt.mp h
  rw [div_toNat] at h'
  have e : i.toNat - 1 = n.toNat / K.toNat := by omega
  rw [← e]; exact ⟨H.2.2.1, H.2.2.2⟩

theorem first_step (n K i : UInt64) (s s1 : Nat) (ret : Array UInt64) (hK : KOK n.toNat K.toNat)
    (H : 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat / K.toNat + 1 ∧ L ret = firstPart (i.toNat - 1) ∧ s = s1 + 2 * (i.toNat - 1))
    (h : i ≤ n / K) :
    (1 ≤ (i.toNat + 1) % 18446744073709551616 ∧ (i.toNat + 1) % 18446744073709551616 ≤ n.toNat / K.toNat + 1 ∧
      L (ret.push i) = firstPart ((i.toNat + 1) % 18446744073709551616 - 1) ∧
      s + 1 + 1 = s1 + 2 * ((i.toNat + 1) % 18446744073709551616 - 1)) ∧
    n.toNat / K.toNat + 1 - (i.toNat + 1) % 18446744073709551616 < n.toNat / K.toNat + 1 - i.toNat := by
  have h' := UInt64.le_iff_toNat_le.mp h
  rw [div_toNat] at h'
  have hp := p_small _ _ hK n.toNat_lt
  rw [two64] at hp
  rw [Nat.mod_eq_of_lt (by omega)]
  obtain ⟨h1, h2, h3, h4⟩ := H
  have e : i.toNat + 1 - 1 = (i.toNat - 1) + 1 := by omega
  refine ⟨⟨by omega, by omega, ?_, by omega⟩, by omega⟩
  rw [L_push, h3, e, firstPart_succ, Nat.sub_add_cancel h1]

theorem second_exit (n K i : UInt64) (s s1 : Nat) (ret : Array UInt64)
    (H : i.toNat ≤ K.toNat - 1 ∧ L ret = firstPart (n.toNat / K.toNat) ++ (secondPart n.toNat K.toNat).take (K.toNat - 1 - i.toNat) ∧
      s = s1 + 2 * (K.toNat - 1 - i.toNat))
    (h : i = 0) : L ret = qlist n.toNat K.toNat ∧ s = s1 + 2 * (K.toNat - 1) := by
  subst h
  obtain ⟨-, h2, h3⟩ := H
  simp only [UInt64.toNat_zero, Nat.sub_zero, secondPart_take_all] at h2 h3
  exact ⟨h2, h3⟩

theorem second_step (n K i : UInt64) (s s1 : Nat) (ret : Array UInt64)
    (H : i.toNat ≤ K.toNat - 1 ∧ L ret = firstPart (n.toNat / K.toNat) ++ (secondPart n.toNat K.toNat).take (K.toNat - 1 - i.toNat) ∧
      s = s1 + 2 * (K.toNat - 1 - i.toNat))
    (h : ¬i = 0) :
    ((i - 1).toNat ≤ K.toNat - 1 ∧
      L (ret.push (n / i)) = firstPart (n.toNat / K.toNat) ++ (secondPart n.toNat K.toNat).take (K.toNat - 1 - (i - 1).toNat) ∧
      s + 1 + 1 = s1 + 2 * (K.toNat - 1 - (i - 1).toNat)) ∧ (i - 1).toNat < i.toNat := by
  have hi : 1 ≤ i.toNat := by
    rcases Nat.eq_zero_or_pos i.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) h
    · exact h0
  have e : (i - 1).toNat = i.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hi))]; rfl
  obtain ⟨h1, h2, h3⟩ := H
  rw [e]
  have e2 : K.toNat - 1 - (i.toNat - 1) = (K.toNat - 1 - i.toNat) + 1 := by omega
  refine ⟨⟨by omega, ?_, by omega⟩, by omega⟩
  rw [L_push, h2, e2, secondPart_take_succ _ _ _ (by omega), List.append_assoc, div_toNat]
  congr 4; omega

theorem km1 (K : UInt64) (h : 1 ≤ K.toNat) : (K - 1).toNat = K.toNat - 1 := by
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using h))]; rfl

theorem size_bound (n K : Nat) (hK : KOK n K) : n / K + (K - 1) ≤ 2 * Nat.sqrt n + 2 := by
  obtain ⟨h1, -, h3, h4⟩ := hK
  have hq : n / K ≤ K + 1 := Nat.div_le_of_le_mul h3
  have hs : K - 1 ≤ Nat.sqrt n := by
    rcases h4 with h4 | h4
    · omega
    · exact Nat.le_sqrt.mpr (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) h4))
  omega

/-- `enumerate_quotients n` returns the ascending list of the positive values `n / x` (`x ≥ 1`),
in `O(√n)` ticks. Every `uint64_t` value of `n` is covered. -/
theorem enumerate_quotients_spec (n : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.enumerate_quotients n
    ⦃⇓ r c => ⌜(L r).Pairwise (· < ·) ∧ (∀ q, q ∈ L r ↔ 1 ≤ q ∧ ∃ x, 1 ≤ x ∧ n.toNat / x = q) ∧
      c ≤ t0 + 42 + 6 * Nat.sqrt n.toNat⌝⦄ := by
  mvcgen [cp.enumerate_quotients]
  case vc1.inv =>
    exact ⟨fun ⟨ok, ng⟩ c => ⌜ng.toNat < ok.toNat ∧ ok.toNat ≤ 2 ^ 32 ∧ n.toNat ≤ ok.toNat * (ok.toNat + 1) ∧
        (ng.toNat = 0 ∨ ng.toNat * (ng.toNat + 1) < n.toNat) ∧
        c + bitWidth (ok.toNat - ng.toNat - 1) ≤ t0 + 1 + 32⌝,
      fun ⟨ok, _⟩ c => ⌜KOK n.toNat ok.toNat ∧ c ≤ t0 + 2 + 32⌝,
      fun ⟨ok, ng⟩ => ok.toNat - ng.toNat⟩
  case vc6.inv =>
    rename_i r1 _ _ _ s1 _
    exact ⟨fun ⟨ret, i⟩ c => ⌜1 ≤ i.toNat ∧ i.toNat ≤ n.toNat / r1.1.toNat + 1 ∧ L ret = firstPart (i.toNat - 1) ∧
        c = s1 + 2 * (i.toNat - 1)⌝,
      fun ⟨ret, _⟩ c => ⌜L ret = firstPart (n.toNat / r1.1.toNat) ∧ c = s1 + 2 * (n.toNat / r1.1.toNat) + 1⌝,
      fun ⟨_, i⟩ => n.toNat / r1.1.toNat + 1 - i.toNat⟩
  case vc10.inv =>
    rename_i r1 _ _ _ _ _ _ _ _ s2 _
    exact ⟨fun ⟨ret, i⟩ c => ⌜i.toNat ≤ r1.1.toNat - 1 ∧
        L ret = firstPart (n.toNat / r1.1.toNat) ++ (secondPart n.toNat r1.1.toNat).take (r1.1.toNat - 1 - i.toNat) ∧
        c = s2 + 2 * (r1.1.toNat - 1 - i.toNat)⌝,
      fun ⟨ret, _⟩ c => ⌜L ret = qlist n.toNat r1.1.toNat ∧ c = s2 + 2 * (r1.1.toNat - 1) + 1⌝,
      fun ⟨_, i⟩ => i.toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  case vc2.step.isTrue =>
    rename_i b _ _ s H h
    exact bs_done _ _ _ _ _ H (gap_le _ _ H.1 h)
  case vc3.step.isFalse.isTrue =>
    rename_i b _ _ s H _ h1 h
    have hm := UInt64.le_iff_toNat_le.mp h
    rw [mid_toNat _ _ H.2.1 H.1] at hm
    rw [sum_mod _ _ H.2.1 H.1]
    exact bs_left _ _ _ _ _ H (gap_gt _ _ H.1 h1) hm
  case vc4.step.isFalse.isFalse =>
    rename_i b _ _ s H _ h1 h
    have hm := UInt64.lt_iff_toNat_lt.mp h
    rw [mid_toNat _ _ H.2.1 H.1] at hm
    rw [sum_mod _ _ H.2.1 H.1]
    exact bs_right _ _ _ _ _ H (gap_gt _ _ H.1 h1) hm
  case vc5.pre =>
    rename_i s h
    have := n.toNat_lt
    have := bitWidth_lt_pow 4294967295 32 (by norm_num)
    rw [two64] at *; omega
  case vc7.step.isTrue =>
    rename_i r _ _ _ s1 hK b _ _ s H h
    exact first_exit n r.1 b.2 _ _ _ H h
  case vc8.step.isFalse =>
    rename_i r _ _ _ s1 hK b _ _ s H _ _ h
    exact first_step n r.1 b.2 _ _ _ hK.1 H h
  case vc9.post.success.pre =>
    rename_i r _ _ _ s1 hK
    have := n.toNat_lt
    rw [two64] at this
    exact ⟨by simp [L, firstPart], Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this⟩
  case vc11.step.isTrue =>
    rename_i r1 _ _ _ _ _ _ _ _ _ _ b _ _ s H h
    exact second_exit n r1.1 b.2 _ _ _ H h
  case vc12.step.isFalse =>
    rename_i r1 _ _ _ _ _ _ _ _ _ _ b _ _ s H _ _ h
    exact second_step n r1.1 b.2 _ _ _ H h
  case vc13.post.success.post.success.pre =>
    rename_i r1 _ _ _ _ hK r _ _ _ h
    have := n.toNat_lt
    rw [km1 _ hK.1.1, Nat.sub_self, List.take_zero, List.append_nil]
    rw [two64] at this
    exact ⟨⟨Nat.le_refl _, h.1, rfl⟩, by have := hK.1.2.1; omega⟩
  case vc14.post.success.post.success.post.success =>
    rename_i r1 _ _ _ _ hK _ _ _ _ h1 r _ _ h
    have hl : r.1.size = n.toNat / r1.1.toNat + (r1.1.toNat - 1) := by
      rw [← qlist_length, ← h.1]; simp [L]
    have := size_bound _ _ hK.1
    have hq := qlist_spec _ _ hK.1.1 hK.1.2.2.1 hK.1.2.2.2
    rw [h.1]
    exact ⟨hq.1, fun q => by have := hq.2 q; rw [← h.1] at this; simpa [L] using this, by omega⟩

end Proofs.Cpp.EnumerateQuotients
