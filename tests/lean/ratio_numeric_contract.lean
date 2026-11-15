-- Appended to the freshly generated staging helpers; imports Lib.Basic first.
open Std.Do Proofs.Cpp Proofs.Cpp.Gen

theorem ratio_euclid_log_bound (a b : Nat) :
    gcdCost a b ≤ 2 + Nat.log2 (a * b) := by
  simp only [gcdCost]
  split_ifs <;> omega

@[spec] theorem ratio_gcd_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbound : b.toNat < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ratio_gcd_nonnegative a b
    ⦃⇓ r c => ⌜r = (Int.gcd a b : Int) ∧
      c ≤ t0 + 2 + gcdCost a.toNat b.toNat⌝⦄ := by
  mvcgen [cp.ratio_gcd_nonnegative]
  case inv =>
    exact ⟨fun ⟨x, y⟩ c => ⌜0 ≤ x ∧ 0 ≤ y ∧
      Int.gcd x y = Int.gcd a b ∧
      c + gcdCost x.toNat y.toNat ≤ t0 + 1 + gcdCost a.toNat b.toNat⌝,
      fun ⟨x, _⟩ c => ⌜x = (Int.gcd a b : Int) ∧
        c ≤ t0 + 2 + gcdCost a.toNat b.toNat⌝,
      fun ⟨_, y⟩ => y.toNat⟩
  all_goals simp +zetaDelta [fuel] at *
  · obtain ⟨hx, hy, hg, hc⟩ := ‹_ ∧ _›
    have hz : (‹Int × Int›).2 = 0 := ‹_›
    simp only [hz, Int.gcd_zero_right] at hg
    have hv : (‹Int × Int›).1 = (Int.gcd a b : Int) := by
      rw [← hg, Int.natAbs_of_nonneg hx]
    simp only [hz, Int.toNat_zero, gcdCost_zero] at hc
    exact ⟨hv, by omega⟩
  · obtain ⟨hx, hy, hg, hc⟩ := ‹_ ∧ _›
    have hn : (‹Int × Int›).2 ≠ 0 := ‹_›
    have hp : 0 < (‹Int × Int›).2 := by omega
    have hr := Int.emod_nonneg (‹Int × Int›).1 hn
    have hlt := Int.emod_lt_of_pos (‹Int × Int›).1 hp
    have hcost := gcdCost_step (‹Int × Int›).1.toNat (‹Int × Int›).2.toNat (by omega)
    rw [← Int.toNat_emod hx hy] at hcost
    have hrec : Int.gcd (‹Int × Int›).2 ((‹Int × Int›).1 % (‹Int × Int›).2) = Int.gcd a b := by
      rw [← hg]
      simp only [Int.gcd]
      have hxabs : (‹Int × Int›).1.natAbs = (‹Int × Int›).1.toNat := by omega
      have hyabs : (‹Int × Int›).2.natAbs = (‹Int × Int›).2.toNat := by omega
      have hrabs : ((‹Int × Int›).1 % (‹Int × Int›).2).natAbs =
          ((‹Int × Int›).1 % (‹Int × Int›).2).toNat := by omega
      rw [hxabs, hyabs, hrabs, Int.toNat_emod hx hy]
      conv_lhs => rw [Nat.gcd_comm]
      rw [← Nat.gcd_rec]
      exact Nat.gcd_comm _ _
    exact ⟨⟨hy, hr, hrec, by omega⟩, hlt, hp⟩
  · exact ⟨⟨ha, hb, by omega⟩, hbound⟩
  · exact ‹_ ∧ _›

/-- Magnitudes fit the existing bounded while semantics (all signed 64-bit inputs). -/
@[spec] theorem ratio_gcd_signed (a b : Int) (hbound : b.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ratio_gcd a b
    ⦃⇓ r c => ⌜r = (Int.gcd a b : Int) ∧
      c ≤ t0 + 3 + gcdCost a.natAbs b.natAbs⌝⦄ := by
  mvcgen [cp.ratio_gcd]
  all_goals simp_all +zetaDelta [fuel]
  all_goals have haabs : (0 ≤ a → a.toNat = a.natAbs) ∧
      (a < 0 → (-a).toNat = a.natAbs) := by constructor <;> intro h <;> omega
  all_goals have hbabs : (0 ≤ b → b.toNat = b.natAbs) ∧
      (b < 0 → (-b).toNat = b.natAbs) := by constructor <;> intro h <;> omega
  all_goals simp_all
  all_goals omega

@[spec] theorem ratio_lcm_signed (a b : Int) (hbound : b.natAbs < fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ratio_lcm a b
    ⦃⇓ r c => ⌜r = (Int.lcm a b : Int) ∧
      c ≤ t0 + 3 + gcdCost a.natAbs b.natAbs⌝⦄ := by
  mvcgen [cp.ratio_lcm]
  all_goals simp_all +zetaDelta [fuel]
  all_goals have haabs : (0 ≤ a → a.toNat = a.natAbs) ∧
      (a < 0 → (-a).toNat = a.natAbs) := by constructor <;> intro h <;> omega
  all_goals have hbabs : (0 ≤ b → b.toNat = b.natAbs) ∧
      (b < 0 → (-b).toNat = b.natAbs) := by constructor <;> intro h <;> omega
  all_goals have hf := Proofs.Cpp.RatioMath.lcm_magnitude_formula a b
  all_goals have han : (a.natAbs : Int) = if 0 ≤ a then a else -a := by split <;> omega
  all_goals have hbn : (b.natAbs : Int) = if 0 ≤ b then b else -b := by split <;> omega
  all_goals rw [han, hbn] at hf
  all_goals simp_all
  all_goals first
    | (have hz : a = 0 ∨ b = 0 := by assumption
       rcases hz with hz | hz <;> simp_all [Int.lcm_def] <;> omega)
    | omega
    | (split_ifs at hf <;> omega)
