import Proofs.Cpp.Gen.IsPrime
import Proofs.Cpp.Lib.Basic
import Proofs.IsPrimeMath

/-! # `is_prime` (library/number_theory/is_prime.hpp) -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Fermat Proofs.IsPrimeMath

namespace Proofs.Cpp.IsPrime

theorem sub_toNat (m x : UInt64) (hx : x.toNat < m.toNat) : (m - x).toNat = m.toNat - x.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt hx))

/-- `r + x` reduced modulo `m` when it would reach `m`. -/
theorem addmod_ge (r x m : UInt64) (hr : r.toNat < m.toNat) (hx : x.toNat < m.toNat) (h : m - x ≤ r) :
    (r - (m - x)).toNat = (r.toNat + x.toNat) % m.toNat ∧ (r.toNat + x.toNat) % m.toNat < m.toNat := by
  have h' := UInt64.le_iff_toNat_le.mp h
  rw [sub_toNat m x hx] at h'
  rw [UInt64.toNat_sub_of_le _ _ h, sub_toNat m x hx]
  refine ⟨?_, Nat.mod_lt _ (by omega)⟩
  have e : r.toNat + x.toNat = (r.toNat - (m.toNat - x.toNat)) + m.toNat := by omega
  rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem addmod_lt (r x m : UInt64) (hr : r.toNat < m.toNat) (hx : x.toNat < m.toNat) (h : r < m - x) :
    (r.toNat + x.toNat) % 18446744073709551616 = (r.toNat + x.toNat) % m.toNat ∧
      (r.toNat + x.toNat) % m.toNat < m.toNat := by
  have h' := UInt64.lt_iff_toNat_lt.mp h
  rw [sub_toNat m x hx] at h'
  have hm := m.toNat_lt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨rfl, by omega⟩

theorem mm_odd (R X Y M : Nat) (hy : Y % 2 = 1) :
    ((R + X) % M + (X + X) % M * (Y / 2)) % M = (R + X * Y) % M := by
  rw [← Nat.add_mod_mod, Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod]
  congr 1
  have : Y = 2 * (Y / 2) + 1 := by omega
  conv => rhs; rw [this]
  ring

theorem mm_even (R X Y M : Nat) (hy : ¬Y % 2 = 1) :
    (R + (X + X) % M * (Y / 2)) % M = (R + X * Y) % M := by
  rw [← Nat.add_mod_mod, Nat.mod_mul_mod, Nat.add_mod_mod]
  congr 1
  have : Y = 2 * (Y / 2) := by omega
  conv => rhs; rw [this]
  ring

theorem bw_y (y : UInt64) (h : ¬y = 0) : bitWidth (y.toNat / 2) + 1 = bitWidth y.toNat ∧ y.toNat / 2 < y.toNat := by
  have : 0 < y.toNat := by
    rcases Nat.eq_zero_or_pos y.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) h
    · exact h0
  exact ⟨bitWidth_div_two _ this, by omega⟩

theorem mul_mod_spec (a b m : UInt64) (ha : a.toNat < m.toNat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mul_mod_u64 a b m
    ⦃⇓ r c => ⌜r.toNat = a.toNat * b.toNat % m.toNat ∧ c = t0 + 2 + bitWidth b.toNat⌝⦄ := by
  mvcgen [cp.mul_mod_u64]
  case inv =>
    exact ⟨fun ⟨r, x, y⟩ c => ⌜r.toNat < m.toNat ∧ x.toNat < m.toNat ∧
        (r.toNat + x.toNat * y.toNat) % m.toNat = a.toNat * b.toNat % m.toNat ∧
        c + bitWidth y.toNat = t0 + 1 + bitWidth b.toNat⌝,
      fun ⟨r, _, _⟩ c => ⌜r.toNat = a.toNat * b.toNat % m.toNat ∧ c = t0 + 2 + bitWidth b.toNat⌝,
      fun ⟨_, _, y⟩ => y.toNat⟩
  all_goals simp +zetaDelta at *
  case vc2.step.isTrue =>
    obtain ⟨h1, -, h3, h4⟩ := ‹_ ∧ _›
    have hy : _ = (0 : UInt64) := ‹_›
    rw [hy] at h3 h4
    simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt h1, bitWidth_zero] at h3 h4
    exact ⟨h3, by omega⟩
  case vc3.step.isFalse.isTrue.isTrue.isTrue =>
    obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _›
    rename_i hy0 hy hr hx
    obtain ⟨er, lr⟩ := addmod_ge _ _ _ h1 h2 hr
    obtain ⟨ex, lx⟩ := addmod_ge _ _ _ h2 h2 hx
    obtain ⟨bw, lt⟩ := bw_y _ hy0
    rw [er, ex, mm_odd _ _ _ _ (by simpa using congrArg UInt64.toNat hy)]
    refine ⟨⟨lr, lx, h3, ?_⟩, lt⟩
    rw [← bw] at h4; omega
  case vc4.step.isFalse.isTrue.isTrue.isFalse =>
    obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _›
    rename_i hy0 hy hr hx
    obtain ⟨er, lr⟩ := addmod_ge _ _ _ h1 h2 hr
    obtain ⟨ex, lx⟩ := addmod_lt _ _ _ h2 h2 hx
    obtain ⟨bw, lt⟩ := bw_y _ hy0
    rw [er, ex, mm_odd _ _ _ _ (by simpa using congrArg UInt64.toNat hy)]
    refine ⟨⟨lr, lx, h3, ?_⟩, lt⟩
    rw [← bw] at h4; omega
  case vc5.step.isFalse.isTrue.isFalse.isTrue =>
    obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _›
    rename_i hy0 hy hr hx
    obtain ⟨er, lr⟩ := addmod_lt _ _ _ h1 h2 hr
    obtain ⟨ex, lx⟩ := addmod_ge _ _ _ h2 h2 hx
    obtain ⟨bw, lt⟩ := bw_y _ hy0
    rw [er, ex, mm_odd _ _ _ _ (by simpa using congrArg UInt64.toNat hy)]
    refine ⟨⟨lr, lx, h3, ?_⟩, lt⟩
    rw [← bw] at h4; omega
  case vc6.step.isFalse.isTrue.isFalse.isFalse =>
    obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _›
    rename_i hy0 hy hr hx
    obtain ⟨er, lr⟩ := addmod_lt _ _ _ h1 h2 hr
    obtain ⟨ex, lx⟩ := addmod_lt _ _ _ h2 h2 hx
    obtain ⟨bw, lt⟩ := bw_y _ hy0
    rw [er, ex, mm_odd _ _ _ _ (by simpa using congrArg UInt64.toNat hy)]
    refine ⟨⟨lr, lx, h3, ?_⟩, lt⟩
    rw [← bw] at h4; omega
  case vc7.step.isFalse.isFalse.isTrue =>
    obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _›
    rename_i hy0 hy hx
    obtain ⟨ex, lx⟩ := addmod_ge _ _ _ h2 h2 hx
    obtain ⟨bw, lt⟩ := bw_y _ hy0
    rw [ex, mm_even _ _ _ _ (fun e => hy (UInt64.toNat_inj.mp (by simpa using e)))]
    refine ⟨⟨h1, lx, h3, ?_⟩, lt⟩
    rw [← bw] at h4; omega
  case vc8.step.isFalse.isFalse.isFalse =>
    obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _›
    rename_i hy0 hy hx
    obtain ⟨ex, lx⟩ := addmod_lt _ _ _ h2 h2 hx
    obtain ⟨bw, lt⟩ := bw_y _ hy0
    rw [ex, mm_even _ _ _ _ (fun e => hy (UInt64.toNat_inj.mp (by simpa using e)))]
    refine ⟨⟨h1, lx, h3, ?_⟩, lt⟩
    rw [← bw] at h4; omega
  case vc9.pre =>
    refine ⟨⟨by omega, ha, ‹_›⟩, ?_⟩
    have := b.toNat_lt; simp only [fuel]; omega
  case vc10.post.success => exact ‹_ ∧ _›

/-- The result of `mul_mod_u64 a b m`. -/
def mm (a b m : UInt64) : UInt64 := UInt64.ofNat (a.toNat * b.toNat % m.toNat)

theorem mm_toNat (a b m : UInt64) (hm : 0 < m.toNat) : (mm a b m).toNat = a.toNat * b.toNat % m.toNat := by
  unfold mm
  rw [UInt64.toNat_ofNat']
  have := m.toNat_lt
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hm) this)

@[spec] theorem mul_mod_wp (a b m : UInt64) (ha : a.toNat < m.toNat) {Q : PostCond UInt64 PS} :
    ⦃fun t => Q.1 (mm a b m) (t + 2 + bitWidth b.toNat)⦄ cp.mul_mod_u64 a b m ⦃Q⦄ := by
  have W := wp_of_triple (Q := Q) (fun t0 => mul_mod_spec a b m ha t0)
  apply Triple.iff.mpr
  intro s hs
  apply (Triple.iff.mp W) s
  intro r t' ⟨hE, ht'⟩
  have : r = mm a b m := UInt64.toNat_inj.mp (by rw [mm_toNat _ _ _ (by omega)]; exact hE)
  rw [this, ht']
  exact hs

/-- The ticks of the loop of `pow_mod_u64` from the state `(b, e)`. -/
def powLoop (m b e : Nat) : Nat :=
  if e = 0 then 1 else 1 + (if e % 2 = 1 then 2 + bitWidth b else 0) + (2 + bitWidth b) + powLoop m (b * b % m) (e / 2)
termination_by e
decreasing_by omega

theorem powLoop_succ (m b e : Nat) (he : e ≠ 0) :
    powLoop m b e = 1 + (if e % 2 = 1 then 2 + bitWidth b else 0) + (2 + bitWidth b) + powLoop m (b * b % m) (e / 2) := by
  rw [powLoop]; simp [he]

theorem pw_odd (P B E M : Nat) (he : E % 2 = 1) : P * B % M * (B * B % M) ^ (E / 2) % M = P * B ^ E % M := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]
  congr 1
  have : E = 2 * (E / 2) + 1 := by omega
  conv => rhs; rw [this, Nat.pow_succ, Nat.pow_mul]
  ring

theorem pw_even (P B E M : Nat) (he : ¬E % 2 = 1) : P * (B * B % M) ^ (E / 2) % M = P * B ^ E % M := by
  rw [Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]
  congr 1
  have : E = 2 * (E / 2) := by omega
  conv => rhs; rw [this, Nat.pow_mul]
  ring

theorem pow_mod_spec (x y m : UInt64) (hx : x.toNat < m.toNat) (hm : 2 ≤ m.toNat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.pow_mod_u64 x y m
    ⦃⇓ r c => ⌜r.toNat = x.toNat ^ y.toNat % m.toNat ∧ c = t0 + 1 + powLoop m.toNat x.toNat y.toNat⌝⦄ := by
  mvcgen [cp.pow_mod_u64]
  case inv =>
    exact ⟨fun ⟨pm, b, e⟩ c => ⌜pm.toNat < m.toNat ∧ b.toNat < m.toNat ∧
        pm.toNat * b.toNat ^ e.toNat % m.toNat = x.toNat ^ y.toNat % m.toNat ∧
        c + powLoop m.toNat b.toNat e.toNat = t0 + 1 + powLoop m.toNat x.toNat y.toNat⌝,
      fun ⟨pm, _, _⟩ c => ⌜pm.toNat = x.toNat ^ y.toNat % m.toNat ∧ c = t0 + 1 + powLoop m.toNat x.toNat y.toNat⌝,
      fun ⟨_, _, e⟩ => e.toNat⟩
  all_goals simp +zetaDelta at *
  case vc2.step.isTrue =>
    obtain ⟨h1, -, h3, h4⟩ := ‹_ ∧ _›
    have hy : _ = (0 : UInt64) := ‹_›
    rw [hy] at h3 h4
    simp only [UInt64.toNat_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt h1] at h3 h4
    rw [powLoop] at h4; simp at h4
    exact ⟨h3, by omega⟩
  case vc3.ha => exact (‹_ ∧ _›).1
  case vc4.ha => obtain ⟨_, h2, _⟩ := ‹_ ∧ _›; exact h2
  case vc6.ha => obtain ⟨_, h2, _⟩ := ‹_ ∧ _›; exact h2
  case vc5.step.isFalse.isTrue =>
    obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _›
    rename_i hy0 hy
    have hy' := congrArg UInt64.toNat hy
    simp only [UInt64.toNat_mod, UInt64.toNat_ofNat, UInt64.toNat_one] at hy'
    obtain ⟨bw, lt⟩ := bw_y _ hy0
    rw [mm_toNat _ _ _ (by omega), mm_toNat _ _ _ (by omega)]
    rw [powLoop_succ _ _ _ (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) lt)), if_pos hy'] at h4
    refine ⟨⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega), by rw [pw_odd _ _ _ _ hy']; exact h3, by linarith⟩, lt⟩
  case vc7.step.isFalse.isFalse =>
    obtain ⟨h1, h2, h3, h4⟩ := ‹_ ∧ _›
    rename_i hy0 hy
    have hy' : ¬_ % 2 = 1 := fun e => hy (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨bw, lt⟩ := bw_y _ hy0
    rw [mm_toNat _ _ _ (by omega)]
    rw [powLoop_succ _ _ _ (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) lt)), if_neg hy'] at h4
    refine ⟨⟨h1, Nat.mod_lt _ (by omega), by rw [pw_even _ _ _ _ hy']; exact h3, ?_⟩, lt⟩
    linarith
  case vc8.pre =>
    refine ⟨⟨by omega, hx, ‹_›⟩, ?_⟩
    have := y.toNat_lt; simp only [fuel]; omega
  case vc9.post.success => exact ‹_ ∧ _›

/-- The result of `pow_mod_u64 x y m`. -/
def pw (x y m : UInt64) : UInt64 := UInt64.ofNat (x.toNat ^ y.toNat % m.toNat)

theorem pw_toNat (x y m : UInt64) (hm : 0 < m.toNat) : (pw x y m).toNat = x.toNat ^ y.toNat % m.toNat := by
  unfold pw
  rw [UInt64.toNat_ofNat']
  have := m.toNat_lt
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hm) this)

@[spec] theorem pow_mod_wp (x y m : UInt64) (hx : x.toNat < m.toNat) (hm : 2 ≤ m.toNat) {Q : PostCond UInt64 PS} :
    ⦃fun t => Q.1 (pw x y m) (t + 1 + powLoop m.toNat x.toNat y.toNat)⦄ cp.pow_mod_u64 x y m ⦃Q⦄ := by
  have W := wp_of_triple (Q := Q) (fun t0 => pow_mod_spec x y m hx hm t0)
  apply Triple.iff.mpr
  intro s hs
  apply (Triple.iff.mp W) s
  intro r t' ⟨hE, ht'⟩
  have : r = pw x y m := UInt64.toNat_inj.mp (by rw [pw_toNat _ _ _ (by omega)]; exact hE)
  rw [this, ht']
  exact hs

/-- The ticks of the squaring loop of `mr_witness` from the state `(x, cf, i)`. -/
def wl (n r x i : Nat) (cf : Bool) : Nat :=
  if i + 1 < r ∧ cf = true then 1 + (2 + bitWidth x) + wl n r (x * x % n) (i + 1) (decide (x * x % n ≠ n - 1)) else 1
termination_by r - i
decreasing_by omega

/-- The ticks of `mr_witness n d r a`. -/
def witCost (n d r a : Nat) : Nat :=
  2 + powLoop n a d + (if a ^ d % n = 1 ∨ a ^ d % n = n - 1 then 0 else wl n r (a ^ d % n) 0 true)

theorem wrun_step (n r k x i : Nat) (h : i + 1 < r) :
    wrun n r (k + 1) (x, true, i) = wrun n r k (x * x % n, decide (x * x % n ≠ n - 1), i + 1) := by
  simp [wrun, h]

theorem wrun_stop (n r k x i : Nat) (cf : Bool) (h : ¬(i + 1 < r ∧ cf = true)) : wrun n r k (x, cf, i) = (x, cf, i) := by
  cases k with
  | zero => rfl
  | succ k => simp only [wrun]; rw [if_neg h]

theorem wl_step (n r x i : Nat) (h : i + 1 < r) :
    wl n r x i true = 1 + (2 + bitWidth x) + wl n r (x * x % n) (i + 1) (decide (x * x % n ≠ n - 1)) := by
  rw [wl]; simp [h]

theorem wl_stop (n r x i : Nat) (cf : Bool) (h : ¬(i + 1 < r ∧ cf = true)) : wl n r x i cf = 1 := by
  rw [wl]; rw [if_neg h]

theorem eq_one_iff (u : UInt64) : u = 1 ↔ u.toNat = 1 :=
  ⟨fun h => by rw [h]; rfl, fun h => UInt64.toNat_inj.mp (by rw [h]; rfl)⟩

theorem eq_pred_iff (u n : UInt64) (hn : 1 ≤ n.toNat) : u = n - 1 ↔ u.toNat = n.toNat - 1 := by
  have e : (n - 1).toNat = n.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hn))]; rfl
  exact ⟨fun h => by rw [h, e], fun h => UInt64.toNat_inj.mp (by rw [h, e])⟩

theorem witness_step (n r x i c base : Nat) (W : Nat × Bool × Nat) (cf' : Bool) (hn : 2 ≤ n) (hi : i + 1 < r) (hx : x < n)
    (hW : wrun n r (r - i) (x, true, i) = W) (hc : c + wl n r x i true = base)
    (hcf : cf' = decide (x * x % n ≠ n - 1)) :
    x * x % n < n ∧ wrun n r (r - (i + 1)) (x * x % n, cf', i + 1) = W ∧
      c + 1 + 2 + bitWidth x + wl n r (x * x % n) (i + 1) cf' = base := by
  have e : r - i = (r - (i + 1)) + 1 := by omega
  rw [e, wrun_step _ _ _ _ _ hi] at hW
  rw [wl_step _ _ _ _ hi] at hc
  subst hcf
  exact ⟨Nat.mod_lt _ (by omega), hW, by omega⟩

theorem stop_of (i r : Int) (cf : Bool) (h0 : 0 ≤ i) (hx : r ≤ i + 1 ∨ cf = false) :
    ¬(i.toNat + 1 < r.toNat ∧ cf = true) := by
  rintro ⟨h, h'⟩
  rcases hx with e | e
  · omega
  · rw [e] at h'; exact Bool.false_ne_true h'

theorem istep (i r : Int) (h0 : 0 ≤ i) (hlt : i + 1 < r) :
    i.toNat + 1 < r.toNat ∧ 0 ≤ i + 1 ∧ (i + 1).toNat = i.toNat + 1 ∧ r.toNat - (i.toNat + 1) < r.toNat - i.toNat := by
  omega

theorem mr_witness_spec (n d a : UInt64) (r : Int) (hn : 2 ≤ n.toNat) (ha : a.toNat < n.toNat) (hr : 0 ≤ r)
    (hr2 : r < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.mr_witness n d r a
    ⦃⇓ w c => ⌜w = mrwx n.toNat r.toNat (a.toNat ^ d.toNat % n.toNat) ∧
      c = t0 + witCost n.toNat d.toNat r.toNat a.toNat⌝⦄ := by
  mvcgen [cp.mr_witness]
  case inv =>
    exact ⟨fun ⟨x, cf, i⟩ c => ⌜0 ≤ i ∧ x.toNat < n.toNat ∧
        wrun n.toNat r.toNat (r.toNat - i.toNat) (x.toNat, cf, i.toNat) =
          wrun n.toNat r.toNat r.toNat (a.toNat ^ d.toNat % n.toNat, true, 0) ∧
        c + wl n.toNat r.toNat x.toNat i.toNat cf = t0 + 2 + powLoop n.toNat a.toNat d.toNat + wl n.toNat r.toNat (a.toNat ^ d.toNat % n.toNat) 0 true⌝,
      fun ⟨_, cf, _⟩ c => ⌜cf = (wrun n.toNat r.toNat r.toNat (a.toNat ^ d.toNat % n.toNat, true, 0)).2.1 ∧
        c = t0 + 2 + powLoop n.toNat a.toNat d.toNat + wl n.toNat r.toNat (a.toNat ^ d.toNat % n.toNat) 0 true⌝,
      fun ⟨_, _, i⟩ => r.toNat - i.toNat⟩
  all_goals simp +zetaDelta at *
  case vc4.step.isTrue =>
    rename_i H _ _ hx
    obtain ⟨h0, h1, h3, h4⟩ := H
    have hs := stop_of _ _ _ h0 hx
    rw [wrun_stop _ _ _ _ _ _ hs] at h3
    rw [wl_stop _ _ _ _ _ hs] at h4
    exact ⟨by rw [← h3], by omega⟩
  case vc5.ha =>
    rename_i H _ _ _
    exact H.2.1
  case vc6.step.isFalse.isTrue =>
    rename_i H _ _ _ _ _ hc hm
    obtain ⟨h0, h1, h3, h4⟩ := H
    obtain ⟨hlt, hcf⟩ := hc
    rw [hcf] at h3 h4
    have hmm := (eq_pred_iff _ _ (by omega)).mp hm
    rw [mm_toNat _ _ _ (by omega)] at hmm ⊢
    obtain ⟨i1, i2, i3, i4⟩ := istep _ _ h0 hlt
    rw [i3]
    obtain ⟨a1, a2, a3⟩ := witness_step _ _ _ _ _ _ _ false hn i1 h1 h3 h4 (by simp [hmm])
    exact ⟨⟨i2, a1, a2, a3⟩, i4⟩
  case vc7.step.isFalse.isFalse =>
    rename_i H _ _ _ _ _ hc hm
    obtain ⟨h0, h1, h3, h4⟩ := H
    obtain ⟨hlt, hcf⟩ := hc
    rw [hcf] at h3 h4 ⊢
    have hmm := mt (eq_pred_iff _ _ (by omega)).mpr hm
    rw [mm_toNat _ _ _ (by omega)] at hmm ⊢
    obtain ⟨i1, i2, i3, i4⟩ := istep _ _ h0 hlt
    rw [i3]
    obtain ⟨a1, a2, a3⟩ := witness_step _ _ _ _ _ _ _ true hn i1 h1 h3 h4 (by simp [hmm])
    exact ⟨⟨i2, a1, a2, a3⟩, i4⟩
  case vc8.isTrue.isTrue.pre =>
    rw [pw_toNat _ _ _ (by omega)]
    refine ⟨⟨Nat.mod_lt _ (by omega), rfl, by omega⟩, ?_⟩
    simp only [fuel]; omega
  case vc9.isTrue.isTrue.post.success.isTrue =>
    rename_i hcf _ H m1 m2
    obtain ⟨h1, h2⟩ := H
    have n1 := mt (eq_one_iff _).mpr m1
    have n2 := mt (eq_pred_iff _ _ (by omega)).mpr m2
    rw [pw_toNat _ _ _ (by omega)] at n1 n2
    unfold mrwx witCost
    rw [if_neg n1, if_neg n2, if_neg (by omega), ← h1, hcf]
    exact ⟨rfl, by omega⟩
  case vc10.isTrue.isTrue.post.success.isFalse =>
    rename_i H m1 m2 hcf
    obtain ⟨h1, h2⟩ := H
    have n1 := mt (eq_one_iff _).mpr m1
    have n2 := mt (eq_pred_iff _ _ (by omega)).mpr m2
    rw [pw_toNat _ _ _ (by omega)] at n1 n2
    unfold mrwx witCost
    rw [if_neg n1, if_neg n2, if_neg (by omega), ← h1, hcf]
    exact ⟨rfl, by omega⟩
  case vc11.isTrue.isFalse =>
    have n2 := (eq_pred_iff _ _ (by omega)).mp ‹pw a d n = n - 1›
    rw [pw_toNat _ _ _ (by omega)] at n2
    unfold mrwx witCost
    simp only [n2, ite_true, or_true]
    refine ⟨by split <;> rfl, by omega⟩
  case vc12.isFalse =>
    have n1 := (eq_one_iff _).mp ‹pw a d n = 1›
    rw [pw_toNat _ _ _ (by omega)] at n1
    unfold mrwx witCost
    simp only [n1, ite_true, true_or]
    exact ⟨trivial, by omega⟩

@[spec] theorem mr_witness_wp (n d a : UInt64) (r : Int) (hn : 2 ≤ n.toNat) (ha : a.toNat < n.toNat) (hr : 0 ≤ r)
    (hr2 : r < 2 ^ 31) {Q : PostCond Bool PS} :
    ⦃fun t => Q.1 (mrwx n.toNat r.toNat (a.toNat ^ d.toNat % n.toNat)) (t + witCost n.toNat d.toNat r.toNat a.toNat)⦄
      cp.mr_witness n d r a ⦃Q⦄ := by
  have W := wp_of_triple (Q := Q) (fun t0 => mr_witness_spec n d a r hn ha hr hr2 t0)
  apply Triple.iff.mpr
  intro s hs
  apply (Triple.iff.mp W) s
  intro w t' ⟨hE, ht'⟩
  rw [hE, ht']
  exact hs

theorem mr_base_eq (i : Int) (hi : 0 ≤ i) : cp.mr_base i = (do Cpp.tick; pure (UInt64.ofNat (mrb i.toNat))) := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ 11 ≤ i := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals try (subst h; simp [cp.mr_base, mrb]; done)
  have e : mrb i.toNat = 37 := by
    unfold mrb; rw [if_neg (show i.toNat ≠ 0 by omega), if_neg (show i.toNat ≠ 1 by omega), if_neg (show i.toNat ≠ 2 by omega), if_neg (show i.toNat ≠ 3 by omega), if_neg (show i.toNat ≠ 4 by omega), if_neg (show i.toNat ≠ 5 by omega), if_neg (show i.toNat ≠ 6 by omega), if_neg (show i.toNat ≠ 7 by omega), if_neg (show i.toNat ≠ 8 by omega), if_neg (show i.toNat ≠ 9 by omega), if_neg (show i.toNat ≠ 10 by omega)]
  simp only [cp.mr_base, e, decide_eq_true_eq, show ¬i = 0 by omega, show ¬i = 1 by omega, show ¬i = 2 by omega, show ¬i = 3 by omega, show ¬i = 4 by omega, show ¬i = 5 by omega, show ¬i = 6 by omega, show ¬i = 7 by omega, show ¬i = 8 by omega, show ¬i = 9 by omega, show ¬i = 10 by omega, ite_false]
  rfl

@[spec] theorem mr_base_wp (i : Int) (hi : 0 ≤ i) {Q : PostCond UInt64 PS} :
    ⦃fun t => Q.1 (UInt64.ofNat (mrb i.toNat)) (t + 1)⦄ cp.mr_base i ⦃Q⦄ := by
  rw [mr_base_eq i hi]
  mvcgen

theorem bw64 (b : Nat) (hb : b < 2 ^ 64) : bitWidth b ≤ 64 := bitWidth_lt_pow b 64 hb

theorem powLoop_le (m : Nat) (hm : 0 < m) (hm2 : m ≤ 2 ^ 64) :
    ∀ e b, b < 2 ^ 64 → powLoop m b e ≤ 1 + 133 * bitWidth e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro b hb
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; rw [powLoop]; simp
    · rw [powLoop_succ _ _ _ (by omega)]
      have h1 := ih (e / 2) (by omega) (b * b % m) (by have := Nat.mod_lt (b * b) hm; omega)
      have h2 := bitWidth_div_two e h
      have h3 := bw64 b hb
      split <;> omega

theorem wl_le (n r : Nat) (hn : 0 < n) (hn2 : n ≤ 2 ^ 64) :
    ∀ k i x cf, r - i = k → x < 2 ^ 64 → wl n r x i cf ≤ 1 + 67 * k := by
  intro k
  induction k with
  | zero =>
    intro i x cf hk hx
    rw [wl, if_neg (by omega)]
  | succ k ih =>
    intro i x cf hk hx
    rw [wl]
    split
    · have h1 := ih (i + 1) (x * x % n) (decide (x * x % n ≠ n - 1)) (by omega)
        (by have := Nat.mod_lt (x * x) hn; omega)
      have h3 := bw64 x hx
      omega
    · omega

theorem witCost_le (n d r a : Nat) (hn : 0 < n) (hn2 : n ≤ 2 ^ 64) (hd : d < 2 ^ 64) (ha : a < 2 ^ 64)
    (hr : r ≤ 64) : witCost n d r a ≤ 12804 := by
  unfold witCost
  have h1 := powLoop_le n hn hn2 d a ha
  have h2 := bw64 d hd
  have h3 := wl_le n r hn hn2 (r - 0) 0 (a ^ d % n) true rfl (by have := Nat.mod_lt (a ^ d) hn; omega)
  split <;> omega

/-- The loop invariant of the base loop of `is_prime`: `res` records that none of the first `bi` bases is bad. -/
def OK (n d r bi : Nat) (res : Bool) : Prop := res = true ↔ ∀ j, j < bi → ¬ badBase n d r j

theorem ok_step (N D R B : Nat) (res res' : Bool) (hok : OK N D R B res)
    (h : res' = true ↔ (res = true ∧ ¬ badBase N D R B)) : OK N D R (B + 1) res' := by
  unfold OK at *
  rw [h, hok]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact h1 j hj
    · exact hj ▸ h2
  · intro h1
    exact ⟨fun j hj => h1 j (by omega), h1 B (by omega)⟩

theorem r_lt (D R N : Nat) (hD : 1 ≤ D) (h : D * 2 ^ R = N - 1) (hN : N < 2 ^ 64) : R < 64 := by
  by_contra hR
  have h1 : 2 ^ 64 ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ R ≤ D * 2 ^ R := Nat.le_mul_of_pos_left _ hD
  omega

theorem mrb_toNat (j : Nat) : (UInt64.ofNat (mrb j)).toNat = mrb j := by
  rw [UInt64.toNat_ofNat']; have := (mrb_le j).2; exact Nat.mod_eq_of_lt (by omega)

theorem mrb_mod (j : Nat) : mrb j % 18446744073709551616 = mrb j := by
  have := (mrb_le j).2; exact Nat.mod_eq_of_lt (by omega)

theorem base_le_iff (j : Nat) (n : UInt64) (hn : 2 ≤ n.toNat) :
    UInt64.ofNat (mrb j) ≤ n - 2 ↔ mrb j ≤ n.toNat - 2 := by
  have e : (n - 2).toNat = n.toNat - 2 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hn))]; rfl
  rw [UInt64.le_iff_toNat_le, mrb_toNat, e]

theorem mod2_toNat (d : UInt64) : d % 2 = 0 ↔ d.toNat % 2 = 0 := by
  constructor
  · intro e; have := congrArg UInt64.toNat e; simpa using this
  · intro e; apply UInt64.toNat_inj.mp; simpa using e

theorem odd_n (n : UInt64) (h : ¬n % 2 = 0 ∧ 1 < n) : n.toNat % 2 = 1 ∧ 3 ≤ n.toNat := by
  have h1 := mt (mod2_toNat n).mpr h.1
  have h2 := UInt64.lt_iff_toNat_lt.mp h.2
  rw [UInt64.toNat_one] at h2
  omega

theorem bistep (b : Int) (h0 : 0 ≤ b) (h : b < 12) :
    0 ≤ b + 1 ∧ b + 1 ≤ 12 ∧ (b + 1).toNat = b.toNat + 1 ∧ 12 - (b.toNat + 1) < 12 - b.toNat ∧ b.toNat < 12 := by
  omega

theorem witCost_mrb (n d r j : Nat) (hn : 0 < n) (hn2 : n < 2 ^ 64) (hd : d < 2 ^ 64) (hr : r < 64) :
    witCost n d r (mrb j) ≤ 12804 :=
  witCost_le n d r (mrb j) hn (by omega) hd (by have := (mrb_le j).2; omega) (by omega)

theorem cost_step (s s1 B W : Nat) (hB : B < 12) (hc : s + (12 - B) * 12810 ≤ s1 + 153720) (hW : W ≤ 12804) :
    s + 1 + 1 + W + (12 - (B + 1)) * 12810 ≤ s1 + 153720 := by omega

theorem is_prime_spec (n : UInt64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.is_prime n
    ⦃⇓ res c => ⌜(IsPrime n.toNat → res = true) ∧ (MRWitnessSet → res = true → IsPrime n.toNat) ∧
      c ≤ t0 + 160000⌝⦄ := by
  mvcgen [cp.is_prime]
  case vc3.inv =>
    exact ⟨fun ⟨r, d⟩ c => ⌜0 ≤ r ∧ 1 ≤ d.toNat ∧ d.toNat * 2 ^ r.toNat = n.toNat - 1 ∧
        c + bitWidth d.toNat ≤ t0 + 1 + 64⌝,
      fun ⟨r, d⟩ c => ⌜0 ≤ r ∧ d.toNat % 2 = 1 ∧ d.toNat * 2 ^ r.toNat = n.toNat - 1 ∧ c ≤ t0 + 66⌝,
      fun ⟨_, d⟩ => d.toNat⟩
  case vc7.inv =>
    rename_i r1 _ _ s _
    exact ⟨fun ⟨res, bi⟩ c => ⌜0 ≤ bi ∧ bi ≤ 12 ∧ OK n.toNat r1.2.toNat r1.1.toNat bi.toNat res ∧
        c + (12 - bi.toNat) * 12810 ≤ s + 12 * 12810⌝,
      fun ⟨res, _⟩ c => ⌜OK n.toNat r1.2.toNat r1.1.toNat 12 res ∧ c ≤ s + 12 * 12810 + 1⌝,
      fun ⟨_, bi⟩ => 12 - bi.toNat⟩
  all_goals simp +zetaDelta at *
  case vc1.isTrue =>
    rename_i h; subst h
    exact ⟨fun _ => isPrime_two, by omega⟩
  case vc2.isFalse.isTrue =>
    rename_i n2 h
    refine ⟨fun hp => ?_, by omega⟩
    have hn2 : n.toNat ≠ 2 := fun e => n2 (UInt64.toNat_inj.mp (by rw [e]; rfl))
    have := odd_of_prime _ hp hn2
    have := hp.1
    rcases h with h | h
    · have := congrArg UInt64.toNat h; simp at this; omega
    · have := UInt64.le_iff_toNat_le.mp h; simp at this; omega
  case vc4.step.isTrue =>
    rename_i H _ _ hd
    obtain ⟨h0, h1, h2, h3⟩ := H
    have hd' := mt (mod2_toNat _).mpr hd
    have : 1 ≤ bitWidth _ := Nat.lt_of_lt_of_le (by simp [bitWidth]) (bitWidth_mono h1)
    exact ⟨h0, by omega, h2, by omega⟩
  case vc5.step.isFalse =>
    rename_i H _ _ _ _ hd
    obtain ⟨h0, h1, h2, h3⟩ := H
    have hd' := (mod2_toNat _).mp hd
    have hb := bitWidth_div_two _ (Nat.lt_of_lt_of_le Nat.zero_lt_one h1)
    have e1 : (_ + 1 : Int).toNat = _ := Int.toNat_add_nat h0 1
    rw [e1, Nat.pow_succ]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try omega
    rw [← h2]
    have : _ = 2 * (_ / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd')).symm
    conv => rhs; rw [this]
    ring
  case vc6.isFalse.isFalse.pre =>
    rename_i _ h
    obtain ⟨o1, o2⟩ := odd_n n h
    have e : (n - 1).toNat = n.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; rfl
    have := bw64 _ (Nat.lt_trans (by omega : n.toNat - 1 < n.toNat) n.toNat_lt)
    rw [e]
    refine ⟨⟨by omega, rfl, by omega⟩, ?_⟩
    have := n.toNat_lt; simp only [fuel]; omega
  case vc8.step.isTrue =>
    rename_i H _ _ hge
    obtain ⟨h0, h1, h2, h3⟩ := H
    have e := Int.le_antisymm h1 hge
    rw [e] at h2 h3
    exact ⟨h2, by simpa using h3⟩
  case vc9.hi => rename_i H _ _ _; exact H.1
  case vc10.hn => rename_i hodd _ _; have := odd_n n hodd; omega
  case vc11.ha =>
    rename_i hodd _ hle
    have := odd_n n hodd
    rw [mrb_mod]; have := (base_le_iff _ n (by omega)).mp hle; omega
  case vc12.hr => exact (‹(0 : Int) ≤ _ ∧ (_ : Nat) % 2 = 1 ∧ _›).1
  case vc13.hr2 =>
    obtain ⟨h0, h1, h2, -⟩ := ‹(0 : Int) ≤ _ ∧ (_ : Nat) % 2 = 1 ∧ _›
    have := r_lt _ _ _ (by omega) h2 n.toNat_lt
    omega
  case vc14.step.isFalse.isTrue.isTrue =>
    obtain ⟨r0, r1, r2, -⟩ := ‹(0 : Int) ≤ _ ∧ (_ : Nat) % 2 = 1 ∧ _›
    rename_i H _ _ _ _ _ hodd hb hle hw
    obtain ⟨h0, h1, h2, h3⟩ := H
    obtain ⟨o1, o2⟩ := odd_n n hodd
    obtain ⟨b1, b2, b3, b4, b5⟩ := bistep _ h0 hb
    have hR := r_lt _ _ _ (by omega) r2 n.toNat_lt
    rw [mrb_mod] at hw ⊢
    rw [b3]
    refine ⟨⟨b1, b2, ok_step _ _ _ _ _ _ h2 ?_, ?_⟩, b4⟩
    swap
    · exact cost_step _ _ _ _ b5 h3 (witCost_mrb _ _ _ _ (by omega) n.toNat_lt (UInt64.toNat_lt _) hR)
    have hbad : badBase _ _ _ _ := ⟨(base_le_iff _ n (by omega)).mp hle, hw⟩
    simp [hbad]
  case vc15.step.isFalse.isTrue.isFalse =>
    obtain ⟨r0, r1, r2, -⟩ := ‹(0 : Int) ≤ _ ∧ (_ : Nat) % 2 = 1 ∧ _›
    rename_i H _ _ _ _ _ hodd hb hle hw
    obtain ⟨h0, h1, h2, h3⟩ := H
    obtain ⟨o1, o2⟩ := odd_n n hodd
    obtain ⟨b1, b2, b3, b4, b5⟩ := bistep _ h0 hb
    have hR := r_lt _ _ _ (by omega) r2 n.toNat_lt
    rw [mrb_mod] at hw ⊢
    rw [b3]
    refine ⟨⟨b1, b2, ok_step _ _ _ _ _ _ h2 ?_, ?_⟩, b4⟩
    swap
    · exact cost_step _ _ _ _ b5 h3 (witCost_mrb _ _ _ _ (by omega) n.toNat_lt (UInt64.toNat_lt _) hR)
    have hbad : ¬ badBase _ _ _ _ := fun hb => by rw [hb.2] at hw; exact Bool.false_ne_true hw.symm
    simp [hbad]
  case vc16.step.isFalse.isFalse =>
    rename_i H _ _ _ _ hodd hb hgt
    obtain ⟨h0, h1, h2, h3⟩ := H
    obtain ⟨o1, o2⟩ := odd_n n hodd
    obtain ⟨b1, b2, b3, b4, b5⟩ := bistep _ h0 hb
    rw [b3]
    refine ⟨⟨b1, b2, ok_step _ _ _ _ _ _ h2 ?_, cost_step _ _ _ 0 b5 h3 (by omega)⟩, b4⟩
    refine ⟨fun h => ⟨h, fun hb => ?_⟩, fun h => h.1⟩
    exact absurd ((base_le_iff _ n (by omega)).mpr hb.1) (UInt64.not_le.mpr hgt)
  case vc17.isFalse.isFalse.post.success.pre =>
    exact ⟨by simp [OK], by simp [fuel]⟩
  case vc18.isFalse.isFalse.post.success.post.success =>
    obtain ⟨r0, r1, r2, r3⟩ := ‹(0 : Int) ≤ _ ∧ (_ : Nat) % 2 = 1 ∧ _›
    rename_i H _ hodd
    obtain ⟨hok, hc⟩ := H
    obtain ⟨o1, o2⟩ := odd_n n hodd
    refine ⟨fun hp => hok.mpr (fun j _ => not_bad_of_prime _ _ _ j hp r2.symm), fun hW hres => ?_, by omega⟩
    by_contra hp
    obtain ⟨j, hj, hbad⟩ := hW _ (by omega) n.toNat_lt o1 hp _ _ r2.symm r1
    exact hok.mp hres j hj hbad

end Proofs.Cpp.IsPrime
