import Proofs.Cpp.Gen.InvGcd
import Proofs.Cpp.Lib.Basic
import Proofs.InvGcdMath
import Proofs.Cpp.SafeMod

/-! # `inv_gcd` (library/number_theory/inv_gcd.hpp)

For `1 ≤ b`, `inv_gcd(a, b) = (g, x)` with `g = gcd(b, a mod b)`, `0 ≤ x < b / g` and `x * a ≡ g (mod b)`;
at most `gcdCost b (a mod b) + 4` steps (`O(log b)`). The loop invariant is `Proofs.InvGcdMath.Inv`. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.InvGcdMath

namespace Proofs.Cpp.InvGcd

/-- One division step of Euclid's algorithm on nonnegative integers. -/
theorem loop_facts (S T : Int) (hs : 0 ≤ S) (hT : 0 < T) :
    S.tdiv T = ((S.toNat / T.toNat : Nat) : Int) ∧ (S - T * S.tdiv T).toNat = S.toNat % T.toNat ∧
    0 ≤ S - T * S.tdiv T ∧ S - T * S.tdiv T < T := by
  obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le hs
  obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hT)
  have hq : (s : Int).tdiv (t : Int) = ((s / t : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg hs]; norm_cast
  have hm := Nat.div_add_mod s t
  have hlt := Nat.mod_lt s (by omega : 0 < t)
  simp only [Int.toNat_natCast, hq]
  have e : (s : Int) - (t : Int) * ((s / t : Nat) : Int) = ((s % t : Nat) : Int) := by
    have : ((t * (s / t) + s % t : Nat) : Int) = (s : Int) := by rw [hm]
    push_cast at this; omega
  rw [e]
  refine ⟨trivial, by simp; omega, by omega, by omega⟩

/-- `b ∣ x * a - g` only depends on `a` modulo `b`. -/
theorem dvd_mod_iff (a b x g : Int) : b ∣ x * (a % b) - g ↔ b ∣ x * a - g := by
  have e : x * a - g = (x * (a % b) - g) + b * (x * (a / b)) := by
    have := Int.mul_ediv_add_emod a b
    calc x * a - g = x * (b * (a / b) + a % b) - g := by rw [this]
      _ = _ := by ring
  rw [e]
  constructor
  · intro h; exact Int.dvd_add h (Int.dvd_mul_right _ _)
  · intro h; have := Int.dvd_sub h (Int.dvd_mul_right b (x * (a / b))); simpa using this

/-- The returned pair, from the state where the loop stops. -/
theorem inv_post (a b : Int) (hb : 0 < b) (r1 m0 m1 : Int) (hs : 0 ≤ r1)
    (hI : Inv b.toNat (a % b).toNat r1.toNat 0 m0 m1) :
    r1 = (Nat.gcd b.toNat (a % b).toNat : Int) ∧
      0 ≤ (if m0 < 0 then m0 + b.tdiv r1 else m0) ∧ (if m0 < 0 then m0 + b.tdiv r1 else m0) < b / r1 ∧
      b ∣ (if m0 < 0 then m0 + b.tdiv r1 else m0) * a - r1 := by
  obtain ⟨hg, hsb, hspos, _, _⟩ := inv_final _ _ _ _ _ (by omega) hI
  have hout := inv_out _ _ _ _ _ (by omega) hI
  simp only at hout
  have hr1 : ((r1.toNat : Nat) : Int) = r1 := Int.toNat_of_nonneg hs
  have hbn : ((b.toNat : Nat) : Int) = b := Int.toNat_of_nonneg (by omega)
  have ha : (((a % b).toNat : Nat) : Int) = a % b := Int.toNat_of_nonneg (Int.emod_nonneg a (by omega))
  have hdiv : ((b.toNat / r1.toNat : Nat) : Int) = b / r1 := by
    rw [Int.natCast_ediv, hbn, hr1]
  have htdiv : b.tdiv r1 = b / r1 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  rw [hdiv, hbn, ha, hr1] at hout
  rw [htdiv]
  refine ⟨by rw [← hg, hr1], hout.1, hout.2.1, ?_⟩
  exact (dvd_mod_iff a b _ r1).mp hout.2.2

theorem inv_gcd_spec (a b : Int) (hb : 0 < b) (hb' : b < 2 ^ 63) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.inv_gcd a b
    ⦃⇓ r c => ⌜r.1 = (Nat.gcd b.toNat (a % b).toNat : Int) ∧ 0 ≤ r.2 ∧ r.2 < b / r.1 ∧ b ∣ r.2 * a - r.1 ∧
               c ≤ t0 + 4 + gcdCost b.toNat (a % b).toNat⌝⦄ := by
  mvcgen [cp.inv_gcd]
  case inv =>
    exact ⟨fun ⟨s, t, m0, m1⟩ c => ⌜0 ≤ s ∧ 0 ≤ t ∧ Inv b.toNat (a % b).toNat s.toNat t.toNat m0 m1 ∧
                                     c + gcdCost s.toNat t.toNat ≤ t0 + 3 + gcdCost b.toNat (a % b).toNat⌝,
           fun ⟨s, t, m0, m1⟩ c => ⌜0 ≤ s ∧ t = 0 ∧ Inv b.toNat (a % b).toNat s.toNat 0 m0 m1 ∧
                                     c ≤ t0 + 4 + gcdCost b.toNat (a % b).toNat⌝,
           fun ⟨_, t, _, _⟩ => t.toNat⟩
  all_goals simp +zetaDelta [fuel, mod, div] at *
  · -- a ≡ 0 (mod b)
    have h0 : a % b = 0 := ‹_›
    refine ⟨by simp [h0]; omega, by rw [Int.ediv_self (by omega)]; omega, by omega⟩
  · -- the loop stops
    obtain ⟨hs, ht, hI, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have ht0 : (‹ℤ × ℤ × ℤ × ℤ›).2.1 = 0 := ‹_›
    simp only [ht0, Int.toNat_zero, gcdCost_zero] at hI hc
    exact ⟨hs, ht0, hI, by omega⟩
  · -- one iteration
    obtain ⟨hs, ht, hI, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have ht0 : ¬ (‹ℤ × ℤ × ℤ × ℤ›).2.1 = 0 := ‹_›
    set S := (‹ℤ × ℤ × ℤ × ℤ›).1 with hS
    set T := (‹ℤ × ℤ × ℤ × ℤ›).2.1 with hT
    have hTpos : 0 < T := by omega
    obtain ⟨hq, hr, hr0, hrT⟩ := loop_facts S T hs hTpos
    have hstep := inv_step _ _ _ _ _ _ (by omega) hI (by omega)
    have hcost := gcdCost_step S.toNat T.toNat (by omega)
    rw [hr, hq]
    rw [hq] at hr0 hrT
    exact ⟨⟨by omega, by omega, hstep, by omega⟩, hrT, hTpos⟩
  · refine ⟨⟨by omega, Int.emod_nonneg a (by omega), inv_init _ _ (by omega) (by
      have := Int.emod_lt_of_pos a hb; omega), by omega⟩, by have := Int.emod_lt_of_pos a hb; omega⟩
  · obtain ⟨hs, ht, hI, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have h := inv_post a b hb _ _ _ hs hI
    rw [if_pos ‹_›] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hc⟩
  · obtain ⟨hs, ht, hI, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have h := inv_post a b hb _ _ _ hs hI
    have hm0 : 0 ≤ (‹ℤ × ℤ × ℤ × ℤ›).2.2.1 := ‹_›
    rw [if_neg (not_lt.mpr hm0)] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hc⟩

end Proofs.Cpp.InvGcd
