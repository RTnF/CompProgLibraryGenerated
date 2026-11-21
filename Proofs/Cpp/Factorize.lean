import Proofs.Cpp.Gen.Factorize
import Proofs.Cpp.Lib.Basic
import Proofs.Cpp.GcdU64
import Proofs.Cpp.IsPrime
import Proofs.Cpp.Lib.Rle
import Mathlib.Data.List.Nodup
import Proofs.Math.FactorizeMath

/-! # `factorize`, `factorize_count`, `divisors` (library/number_theory/factorize.hpp)

Pollard's rho method with trial division as the fallback. `n ≥ 1` is the precondition (the original loops forever at
`n = 0`). Proved: the factors multiply to `n`, are at least 2 and sorted, and are prime under `MRWitnessSet` (the
hypothesis of `is_prime`); `factorize_count` gives their runs; `divisors` returns divisors of `n` in increasing
order, all of them exactly once under `MRWitnessSet`. Time `O(n)` for every call (`Kc * n` ticks); the expected
`O(n^{1/4})` of rho is not proved. -/

namespace Proofs.Cpp.Factorize
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.FactorizeMath
open Proofs.Fermat (IsPrime)

theorem gcdCost_le (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : gcdCost a b ≤ 130 := by
  unfold gcdCost
  split
  · omega
  · have hab : a * b < 2 ^ 128 := by
      calc a * b < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
        _ = 2 ^ 128 := by norm_num
    by_cases h0 : a * b = 0
    · rw [h0]; simp [Nat.log2_zero]; split <;> omega
    · have := (Nat.log2_lt h0).mpr hab
      split <;> omega

theorem ofNat_ofInt (a : Nat) (h : a < 2 ^ 64) : (UInt64.ofInt (a : Int)).toNat = a := by
  unfold UInt64.ofInt
  rw [UInt64.toNat_ofNat']
  rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp; omega

theorem mod_toInt (a n : Nat) : Cpp.mod (a : Int) (n : Int) = ((a % n : Nat) : Int) := by
  unfold Cpp.mod; rw [Int.tmod_eq_emod_of_nonneg (by omega)]; push_cast; rfl

theorem f_spec (x c n : UInt64) (hn : 0 < n.toNat) (t0 : Nat) :
    ⦃fun t => ⌜t = t0⌝⦄ cp.factorize_f x c n
    ⦃⇓ r t => ⌜r.toNat = (x.toNat * x.toNat + c.toNat) % n.toNat ∧ t = t0 + 1⌝⦄ := by
  mvcgen [cp.factorize_f]
  rename_i t ht
  refine ⟨?_, by omega⟩
  have hlt : (x.toNat * x.toNat + c.toNat) % n.toNat < 2 ^ 64 := by
    have := Nat.mod_lt (x.toNat * x.toNat + c.toNat) hn; have := n.toNat_lt; omega
  have e := mod_toInt (x.toNat * x.toNat + c.toNat) n.toNat
  push_cast at e
  rw [e, ← Int.natCast_mul, ← Int.natCast_add, ← Int.natCast_emod, ofNat_ofInt _ hlt]

def Fm (c n : Nat) : Nat → Nat := fun v => (v * v + c) % n

def dist (x y : Nat) : Nat := if y < x then x - y else y - x

/-- The invariant of the rho loop. -/
def RI (m c n : UInt64) (t0 : Nat) (x y d : UInt64) (t : Nat) : Prop :=
  ∃ i, x.toNat = walk (Fm c.toNat n.toNat) i ∧ y.toNat = walk (Fm c.toNat n.toNat) (2 * i) ∧
    (∀ j, 1 ≤ j → j < i → ¬ Meet (Fm c.toNat n.toNat) j) ∧
    (1 ≤ i → d.toNat = Nat.gcd (dist x.toNat y.toNat) m.toNat) ∧ (i = 0 → d = 1) ∧ i ≤ n.toNat ∧
    t ≤ t0 + 1 + 136 * i

def RD (m n : UInt64) (t0 : Nat) (d : UInt64) (t : Nat) : Prop :=
  d.toNat ≠ 1 ∧ d.toNat ∣ m.toNat ∧ 0 < d.toNat ∧ t ≤ t0 + 2 + 136 * n.toNat

noncomputable def rmu (c n x y d : UInt64) : Nat :=
  if d = 1 then n.toNat - firstIdx (Fm c.toNat n.toNat) x.toNat y.toNat else 0

theorem Fm_lt (c n : Nat) (hn : 0 < n) : ∀ v, Fm c n v < n := fun v => Nat.mod_lt _ hn

theorem dist_toNat (a b : UInt64) :
    (if decide (a > b) = true then a - b else b - a).toNat = dist a.toNat b.toNat := by
  unfold dist
  by_cases h : b < a
  · have : b.toNat < a.toNat := UInt64.lt_iff_toNat_lt.mp h
    simp [h, this, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)]
  · have : ¬ b.toNat < a.toNat := fun h' => h (UInt64.lt_iff_toNat_lt.mpr h')
    simp [h, this, UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp h)]

theorem gcd_dist_zero (m : Nat) (hm : 2 ≤ m) (x : Nat) : Nat.gcd (dist x x) m ≠ 1 := by
  simp [dist]; omega

/-- At an iteration that continues (`d = 1`), the index is `firstIdx` and below `n`. -/
theorem ri_cont (m c n : UInt64) (hn : 3 ≤ n.toNat) (hm : 2 ≤ m.toNat) (t0 : Nat) (x y d : UInt64) (t i : Nat)
    (hx : x.toNat = walk (Fm c.toNat n.toNat) i) (hy : y.toNat = walk (Fm c.toNat n.toNat) (2 * i))
    (hno : ∀ j, 1 ≤ j → j < i → ¬ Meet (Fm c.toNat n.toNat) j)
    (hd : 1 ≤ i → d.toNat = Nat.gcd (dist x.toNat y.toNat) m.toNat) (hd1 : d = 1) :
    (∀ j, 1 ≤ j → j ≤ i → ¬ Meet (Fm c.toNat n.toNat) j) ∧ i < n.toNat := by
  have hall : ∀ j, 1 ≤ j → j ≤ i → ¬ Meet (Fm c.toNat n.toNat) j := by
    intro j h1 h2 hmt
    rcases Nat.lt_or_ge j i with h | h
    · exact hno j h1 h hmt
    · have e : j = i := by omega
      subst e
      have := hd h1
      unfold Meet at hmt
      have hxy : x.toNat = y.toNat := by rw [hx, hy]; exact hmt
      rw [hd1, ← hxy] at this
      exact gcd_dist_zero m.toNat hm x.toNat (by simpa using this.symm)
  exact ⟨hall, lt_of_noMeet _ n.toNat i (by omega) (Fm_lt _ _ (by omega)) hall⟩

theorem ri_exit (m c n : UInt64) (hn : 3 ≤ n.toNat) (hm : 2 ≤ m.toNat) (t0 : Nat) (x y d : UInt64) (t : Nat)
    (h : RI m c n t0 x y d t) (hd : d ≠ 1) : RD m n t0 d (t + 1) := by
  obtain ⟨i, hx, hy, hno, hdg, h0, hi, ht⟩ := h
  have hi1 : 1 ≤ i := Nat.pos_of_ne_zero (fun e => hd (h0 e))
  have hd' := hdg hi1
  have hne : d.toNat ≠ 1 := fun e => hd (UInt64.toNat_inj.mp (by simpa using e))
  refine ⟨hne, by rw [hd']; exact Nat.gcd_dvd_right _ _, by rw [hd']; exact Nat.gcd_pos_of_pos_right _ (by omega), ?_⟩
  have := Nat.mul_le_mul_left 136 hi
  omega

theorem ri_step (m c n : UInt64) (hn : 3 ≤ n.toNat) (hm : 2 ≤ m.toNat) (t0 : Nat) (x y d : UInt64) (t : Nat)
    (h : RI m c n t0 x y d t) (hd : d = 1) (x' y1 y' d' : UInt64) (t' : Nat)
    (hx' : x'.toNat = (x.toNat * x.toNat + c.toNat) % n.toNat)
    (hy1 : y1.toNat = (y.toNat * y.toNat + c.toNat) % n.toNat)
    (hy' : y'.toNat = (y1.toNat * y1.toNat + c.toNat) % n.toNat)
    (hd' : d'.toNat = Nat.gcd (dist x'.toNat y'.toNat) m.toNat) (ht' : t' ≤ t + 136) :
    RI m c n t0 x' y' d' t' ∧ rmu c n x' y' d' < rmu c n x y d := by
  obtain ⟨i, hx, hy, hno, hdg, h0, hi, ht⟩ := h
  obtain ⟨hall, hlt⟩ := ri_cont m c n hn hm t0 x y d t i hx hy hno hdg hd
  have ex : x'.toNat = walk (Fm c.toNat n.toNat) (i + 1) := by
    rw [hx']; unfold walk; rw [Function.iterate_succ_apply']; unfold walk at hx; rw [← hx]; rfl
  have ey : y'.toNat = walk (Fm c.toNat n.toNat) (2 * (i + 1)) := by
    rw [hy', hy1]; unfold walk
    rw [show 2 * (i + 1) = (2 * i + 1) + 1 by ring, Function.iterate_succ_apply', Function.iterate_succ_apply']
    unfold walk at hy; rw [← hy]; rfl
  refine ⟨⟨i + 1, ex, ey, fun j h1 h2 => hall j h1 (by omega), fun _ => hd', fun e => by omega, by omega,
    by omega⟩, ?_⟩
  have hf : firstIdx (Fm c.toNat n.toNat) x.toNat y.toNat = i := by
    rw [hx, hy]; exact firstIdx_eq _ i hall
  unfold rmu
  rw [if_pos hd, hf]
  by_cases hd1 : d' = 1
  · rw [if_pos hd1]
    obtain ⟨hall', -⟩ := ri_cont m c n hn hm t0 x' y' d' t' (i + 1) ex ey
      (fun j h1 h2 => hall j h1 (by omega)) (fun _ => hd') hd1
    rw [ex, ey, firstIdx_eq _ (i + 1) hall']
    omega
  · rw [if_neg hd1]; omega

theorem rho_spec (m c n : UInt64) (hn : 3 ≤ n.toNat) (hm : 2 ≤ m.toNat) (t0 : Nat) :
    ⦃fun t => ⌜t = t0⌝⦄ cp.factorize_rho m c n
    ⦃⇓ r t => ⌜(r.toNat = 0 ∨ (1 < r.toNat ∧ r.toNat < m.toNat ∧ r.toNat ∣ m.toNat)) ∧
      t ≤ t0 + 2 + 136 * n.toNat⌝⦄ := by
  mvcgen [cp.factorize_rho, f_spec, Proofs.Cpp.GcdU64.gcd_u64_spec]
  case vc1.inv =>
    exact ⟨fun b t => ⌜RI m c n t0 b.1 b.2.1 b.2.2 t⌝, fun b t => ⌜RD m n t0 b.2.2 t⌝,
      fun b => rmu c n b.1 b.2.1 b.2.2⟩
  case vc2.step.isTrue =>
    exact ri_exit m c n hn hm t0 _ _ _ _ ‹RI _ _ _ _ _ _ _ _› (by simpa using ‹(!decide _) = true›)
  case vc6 =>
    rename_i s5 h6 b x0 bs y0 d0 s4 hc h4 r3 s3 h3 r2 s2 h2 r1 s1 h1 r s h
    obtain ⟨e3, t3⟩ := h3
    obtain ⟨e2, t2⟩ := h2
    obtain ⟨e1, t1⟩ := h1
    obtain ⟨eg, tg⟩ := h
    have hd : b.2.2 = 1 := by simpa using h4
    rw [dist_toNat] at eg tg
    have := gcdCost_le (dist r3.toNat r1.toNat) m.toNat
      (by unfold dist; split <;> (have := r3.toNat_lt; have := r1.toNat_lt; omega)) m.toNat_lt
    exact ri_step m c n hn hm t0 _ _ _ _ hc hd r3 r2 r1 r s e3 e2 e1 eg (by omega)
  case vc7.pre =>
    rename_i s h
    refine ⟨⟨0, by simp [walk], by simp [walk], fun j h1 h2 => by omega, fun h => by omega, fun _ => rfl, by omega,
      by omega⟩, ?_⟩
    show rmu c n 2 2 1 < fuel
    unfold rmu; have := n.toNat_lt; simp only [fuel]; split <;> omega
  case vc8.post.success =>
    rename_i s1 h1 r bs d0 s h
    obtain ⟨hne, hdv, hpos, ht⟩ := h
    change d0.toNat ≠ 1 at hne; change d0.toNat ∣ m.toNat at hdv; change 0 < d0.toNat at hpos
    refine ⟨?_, ht⟩
    have hle := Nat.le_of_dvd (by omega) hdv
    by_cases e : d0 = m
    · left; simp [e]
    · right
      have : d0.toNat ≠ m.toNat := fun h => e (UInt64.toNat_inj.mp h)
      simp only [e, decide_false, Bool.false_eq_true, ite_false]
      exact ⟨by omega, by omega, hdv⟩
  all_goals omega

theorem of_dec2_true {p : Prop} [Decidable p] (h : (!!decide p) = true) : p := by simpa using h
theorem of_dec2_false {p : Prop} [Decidable p] (h : ¬ (!!decide p) = true) : ¬ p := by simpa using h
theorem of_dec_true {p : Prop} [Decidable p] (h : decide p = true) : p := by simpa using h
theorem of_dec_false {p : Prop} [Decidable p] (h : ¬ decide p = true) : ¬ p := by simpa using h
theorem of_ndec_true {p : Prop} [Decidable p] (h : (!decide p) = true) : ¬ p := by simpa using h
theorem of_ndec_false {p : Prop} [Decidable p] (h : ¬ (!decide p) = true) : p := by simpa using h

abbrev W : Prop := Proofs.IsPrimeMath.MRWitnessSet

def prodL (a : Array UInt64) : Nat := (a.toList.map UInt64.toNat).prod

/-- Every element is at least 2, and prime under the witness hypothesis of `is_prime`. -/
def Good (a : Array UInt64) : Prop := ∀ x ∈ a.toList, 2 ≤ x.toNat ∧ (W → IsPrime x.toNat)

theorem prodL_push (a : Array UInt64) (x : UInt64) : prodL (a.push x) = prodL a * x.toNat := by
  simp [prodL, List.prod_append]

theorem prodL_empty : prodL ([] : List UInt64).toArray = 1 := by simp [prodL]

theorem good_empty : Good ([] : List UInt64).toArray := by simp [Good]

theorem good_push (a : Array UInt64) (x : UInt64) (h : Good a) (h2 : 2 ≤ x.toNat) (hp : W → IsPrime x.toNat) :
    Good (a.push x) := by
  intro y hy
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | rfl
  · exact h y hy
  · exact ⟨h2, hp⟩

theorem pow_le_prod (l : List UInt64) (h : ∀ x ∈ l, 2 ≤ x.toNat) : 2 ^ l.length ≤ (l.map UInt64.toNat).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.prod_cons, Nat.pow_succ]
    have := h a (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) this

theorem size_lt (a : Array UInt64) (h : Good a) (m N : Nat) (hm : 1 ≤ m) (he : prodL a * m = N) (hN : N < 2 ^ 64) :
    a.size < 64 := by
  have h1 := pow_le_prod a.toList (fun x hx => (h x hx).1)
  simp only [Array.length_toList] at h1
  have : prodL a ≤ N := by rw [← he]; exact Nat.le_mul_of_pos_right _ hm
  have : 2 ^ a.size < 2 ^ 64 := by unfold prodL at this; omega
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this

theorem prodL_append (a b : Array UInt64) : prodL (a ++ b) = prodL a * prodL b := by
  simp [prodL, List.prod_append]

theorem good_append (a b : Array UInt64) (ha : Good a) (hb : Good b) : Good (a ++ b) := by
  intro x hx
  simp only [Array.toList_append, List.mem_append] at hx
  rcases hx with h | h
  · exact ha x h
  · exact hb x h

/-! ## Removing the factors 2 -/

def I1 (N t0 : Nat) (m : UInt64) (f : Array UInt64) (t : Nat) : Prop :=
  prodL f * m.toNat = N ∧ Good f ∧ 1 ≤ m.toNat ∧ t ≤ t0 + 1 + 2 * f.size

def D1 (N t0 : Nat) (m : UInt64) (f : Array UInt64) (t : Nat) : Prop :=
  prodL f * m.toNat = N ∧ Good f ∧ 1 ≤ m.toNat ∧ m.toNat % 2 = 1 ∧ t ≤ t0 + 2 + 2 * f.size

theorem and_one (m : UInt64) : (m &&& 1).toNat = m.toNat % 2 := by
  rw [UInt64.toNat_and]; simp [Nat.and_one_is_mod]

theorem shr_one (m : UInt64) : (m >>> 1).toNat = m.toNat / 2 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]

theorem two_prime : IsPrime 2 := by
  refine ⟨le_refl _, fun d hd => ?_⟩
  have := Nat.le_of_dvd (by norm_num) hd
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
  · simp at hd
  · simp
  · simp

theorem i1_step (N t0 : Nat) (m : UInt64) (f : Array UInt64) (t : Nat) (h : I1 N t0 m f t)
    (he : m &&& 1 = 0) : I1 N t0 (m >>> 1) (f.push 2) (t + 1 + 1) ∧ (m >>> 1).toNat < m.toNat := by
  obtain ⟨hp, hg, h1, ht⟩ := h
  have e := and_one m; rw [he] at e; simp at e
  have hs := shr_one m
  refine ⟨⟨?_, good_push _ _ hg (by simp) (fun _ => by simpa using two_prime), by omega, by simp; omega⟩, by omega⟩
  rw [prodL_push, hs, ← hp]; simp
  rw [Nat.mul_assoc]; congr 1; omega

theorem i1_exit (N t0 : Nat) (m : UInt64) (f : Array UInt64) (t : Nat) (h : I1 N t0 m f t)
    (he : m &&& 1 ≠ 0) : D1 N t0 m f (t + 1) := by
  obtain ⟨hp, hg, h1, ht⟩ := h
  have e := and_one m
  have : (m &&& 1).toNat ≠ 0 := fun h => he (UInt64.toNat_inj.mp (by simpa using h))
  exact ⟨hp, hg, h1, by omega, by omega⟩

/-! ## The rho attempts -/

def RhoOK (M r : Nat) : Prop := r = 0 ∨ (1 < r ∧ r < M ∧ r ∣ M)

def I2 (M : Nat) (tA : Nat) (r : UInt64) (i : Int) (t : Nat) : Prop :=
  RhoOK M r.toNat ∧ 1 ≤ i ∧ i ≤ 4 ∧ t ≤ tA + (i - 1).toNat * (3 + 136 * M)

def D2 (M : Nat) (tA : Nat) (r : UInt64) (t : Nat) : Prop :=
  RhoOK M r.toNat ∧ t ≤ tA + 1 + 3 * (3 + 136 * M)

theorem i2_step (M tA : Nat) (r : UInt64) (i : Int) (t : Nat) (h : I2 M tA r i t) (hi : i ≤ 3)
    (r' : UInt64) (t' : Nat) (hr : RhoOK M r'.toNat) (ht : t' ≤ t + 1 + 2 + 136 * M) :
    I2 M tA r' (i + 1) t' ∧ (4 - (i + 1)).toNat < (4 - i).toNat := by
  obtain ⟨-, h1, h4, hc⟩ := h
  refine ⟨⟨hr, by omega, by omega, ?_⟩, by omega⟩
  have e : (i + 1 - 1).toNat = (i - 1).toNat + 1 := by omega
  rw [e, Nat.add_mul]; omega

theorem i2_exit (M tA : Nat) (r : UInt64) (i : Int) (t : Nat) (h : I2 M tA r i t) : D2 M tA r (t + 1) := by
  obtain ⟨hr, h1, h4, hc⟩ := h
  refine ⟨hr, ?_⟩
  have : (i - 1).toNat ≤ 3 := by omega
  have := Nat.mul_le_mul_right (3 + 136 * M) this
  omega

theorem odd_div (M d : Nat) (hM : M % 2 = 1) (hd : d ∣ M) (h1 : 1 < d) (h2 : d < M) : 3 ≤ d ∧ 3 ≤ M / d ∧ d * (M / d) = M := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : 0 < d := by omega
  rw [Nat.mul_div_cancel_left _ hd0]
  have he1 : 1 < e := by
    by_contra hc
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;> simp at h2 hM
  refine ⟨?_, ?_, rfl⟩
  · by_contra hc
    have : d = 2 := by omega
    subst this; omega
  · by_contra hc
    have : e = 2 := by omega
    subst this; omega

/-! ## Trial division -/

def I3 (N M tC : Nat) (n : UInt64) (f : Array UInt64) (i : UInt64) (t : Nat) : Prop :=
  prodL f * n.toNat = N ∧ Good f ∧ 1 ≤ n.toNat ∧ n.toNat % 2 = 1 ∧ 3 ≤ i.toNat ∧ i.toNat % 2 = 1 ∧
    NoSmall n.toNat i.toNat ∧ i.toNat ≤ M + 2 ∧ n.toNat ≤ M ∧ t ≤ tC + i.toNat + 3 * f.size

def D3 (N M tC : Nat) (n : UInt64) (f : Array UInt64) (i : UInt64) (t : Nat) : Prop :=
  prodL f * n.toNat = N ∧ Good f ∧ 1 ≤ n.toNat ∧ NoSmall n.toNat i.toNat ∧ n.toNat < i.toNat * i.toNat ∧
    i.toNat ≤ M + 2 ∧ t ≤ tC + i.toNat + 3 * f.size + 1

def I4 (N M tC : Nat) (i nO : UInt64) (n : UInt64) (f : Array UInt64) (t : Nat) : Prop :=
  prodL f * n.toNat = N ∧ Good f ∧ 1 ≤ n.toNat ∧ n.toNat % 2 = 1 ∧ NoSmall n.toNat i.toNat ∧ n.toNat ≤ nO.toNat ∧
    3 ≤ i.toNat ∧ i.toNat % 2 = 1 ∧ i.toNat * i.toNat ≤ nO.toNat ∧ nO.toNat ≤ M ∧ t ≤ tC + i.toNat + 1 + 3 * f.size

def D4 (N M tC : Nat) (i nO : UInt64) (n : UInt64) (f : Array UInt64) (t : Nat) : Prop :=
  I4 N M tC i nO n f (t - 1) ∧ 1 ≤ t ∧ ¬ i.toNat ∣ n.toNat

theorem mod_toNat (a b : UInt64) : (a % b).toNat = a.toNat % b.toNat := UInt64.toNat_mod a b

theorem i4_step (N M tC : Nat) (i nO n : UInt64) (f : Array UInt64) (t : Nat) (h : I4 N M tC i nO n f t)
    (hd : n % i = 0) : I4 N M tC i nO (n / i) (f.push i) (t + 1 + 1) ∧ (n / i).toNat < n.toNat := by
  obtain ⟨hp, hg, h1, hodd, hs, hn, h3, hio, hii, hM, ht⟩ := h
  have e : n.toNat % i.toNat = 0 := by rw [← mod_toNat, hd]; rfl
  have hdv : i.toNat ∣ n.toNat := Nat.dvd_of_mod_eq_zero e
  have hpi := prime_of_least n.toNat i.toNat (by omega) (by omega) hdv hs
  obtain ⟨q, hq⟩ := hdv
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq; omega)
  have hqd : n.toNat / i.toNat = q := by rw [hq, Nat.mul_div_cancel_left _ (by omega)]
  have hdq : (n / i).toNat = q := by rw [UInt64.toNat_div]; exact hqd
  unfold I4; rw [hdq]
  have hqo : q % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one q with h | h
    · exfalso; have : n.toNat % 2 = 0 := by rw [hq, Nat.mul_mod, h]; simp
      omega
    · exact h
  have hqn : q < n.toNat := by rw [hq]; nlinarith
  refine ⟨⟨?_, good_push _ _ hg (by omega) (fun _ => hpi), by omega, hqo, ?_, by omega, h3, hio, hii, hM,
    by simp; omega⟩, hqn⟩
  · rw [prodL_push, ← hp, hq]; ring
  · have := noSmall_div n.toNat i.toNat i.toNat hs ⟨q, hq⟩
    rwa [hqd] at this

theorem i4_exit (N M tC : Nat) (i nO n : UInt64) (f : Array UInt64) (t : Nat) (h : I4 N M tC i nO n f t)
    (hd : ¬ n % i = 0) : D4 N M tC i nO n f (t + 1) := by
  refine ⟨by simpa using h, by omega, fun hdv => hd ?_⟩
  apply UInt64.toNat_inj.mp
  rw [mod_toNat]; simpa using Nat.mod_eq_zero_of_dvd hdv

theorem i3_enter (N M tC : Nat) (n : UInt64) (f : Array UInt64) (i : UInt64) (t : Nat) (h : I3 N M tC n f i t)
    (hc : i ≤ n / i) : I4 N M tC i n n f (t + 1) := by
  obtain ⟨hp, hg, h1, hodd, h3, hio, hs, hiM, hnM, ht⟩ := h
  have hc' : i.toNat ≤ n.toNat / i.toNat := by
    have := UInt64.le_iff_toNat_le.mp hc; rwa [UInt64.toNat_div] at this
  have hii : i.toNat * i.toNat ≤ n.toNat := by
    have := Nat.mul_le_mul_right i.toNat hc'
    have := Nat.div_mul_le_self n.toNat i.toNat
    omega
  exact ⟨hp, hg, h1, hodd, hs, le_refl _, h3, hio, hii, hnM, by omega⟩

theorem i3_next (N M tC : Nat) (nO : UInt64) (fO : Array UInt64) (i : UInt64) (t : Nat) (hO : I3 N M tC nO fO i t)
    (n : UInt64) (f : Array UInt64) (t' : Nat) (h : D4 N M tC i nO n f t') :
    I3 N M tC n f (i + 2) t' ∧ n.toNat + 2 - (i + 2).toNat < nO.toNat + 2 - i.toNat := by
  obtain ⟨⟨hp, hg, h1, hodd, hs, hn, h3, hio, hii, hM, ht⟩, ht1, hnd⟩ := h
  have hi3 : i.toNat * 3 ≤ nO.toNat := by nlinarith
  have hlt := nO.toNat_lt
  have e : (i + 2).toNat = i.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  unfold I3; rw [e]
  refine ⟨⟨hp, hg, h1, hodd, by omega, by omega, noSmall_step _ _ hs hnd hodd h3 hio, by omega, by omega, by omega⟩,
    by omega⟩

theorem i3_exit (N M tC : Nat) (n : UInt64) (f : Array UInt64) (i : UInt64) (t : Nat) (h : I3 N M tC n f i t)
    (hc : ¬ i ≤ n / i) : D3 N M tC n f i (t + 1) := by
  obtain ⟨hp, hg, h1, hodd, h3, hio, hs, hiM, hnM, ht⟩ := h
  have hc' : n.toNat / i.toNat < i.toNat := by
    have : ¬ i.toNat ≤ (n / i).toNat := fun h => hc (UInt64.le_iff_toNat_le.mpr h)
    rw [UInt64.toNat_div] at this; omega
  have : n.toNat < i.toNat * i.toNat := by
    have := Nat.lt_mul_div_succ n.toNat (show 0 < i.toNat by omega)
    have := Nat.mul_le_mul_left i.toNat (show n.toNat / i.toNat + 1 ≤ i.toNat by omega)
    omega
  exact ⟨hp, hg, h1, hs, this, hiM, by omega⟩

/-! ## The cost -/

def Kc : Nat := 162230

theorem cost_rec (r s M N : Nat) (hr : 3 ≤ r) (hs : 3 ≤ s) (hM : r * s = M) (hMN : M ≤ N) :
    161000 + 410 * M + Kc * r + Kc * s ≤ Kc * N := by
  unfold Kc
  subst hM
  nlinarith

/-! ## The ends of the calls -/

theorem prodL_pos (f : Array UInt64) (h : Good f) : 1 ≤ prodL f := by
  have := pow_le_prod f.toList (fun x hx => (h x hx).1)
  have := Nat.one_le_two_pow (n := f.toList.length)
  unfold prodL; omega

theorem fin_one (N t0 : Nat) (hN : N < 2 ^ 64) (m : UInt64) (f : Array UInt64) (s : Nat) (hD : D1 N t0 m f s)
    (hle : m ≤ 1) : prodL f = N ∧ Good f ∧ s + f.size ≤ t0 + Kc * N := by
  obtain ⟨hp, hg, h1, hodd, ht⟩ := hD
  have := UInt64.le_iff_toNat_le.mp hle
  have e : m.toNat = 1 := by simp at this; omega
  rw [e, Nat.mul_one] at hp
  have := size_lt f hg 1 N (le_refl _) (by rw [Nat.mul_one]; exact hp) hN
  have := prodL_pos f hg
  refine ⟨hp, hg, ?_⟩
  unfold Kc; omega

theorem fin_prime (N t0 : Nat) (hN : N < 2 ^ 64) (m : UInt64) (f : Array UInt64) (s : Nat) (hD : D1 N t0 m f s)
    (hle : ¬ m ≤ 1) (hW : W → IsPrime m.toNat) (s' : Nat) (hs : s' ≤ s + 160000) :
    prodL (f.push m) = N ∧ Good (f.push m) ∧ s' + 1 + (f.push m).size ≤ t0 + Kc * N := by
  obtain ⟨hp, hg, h1, hodd, ht⟩ := hD
  have h2 : 2 ≤ m.toNat := by
    have : ¬ m.toNat ≤ 1 := fun h => hle (UInt64.le_iff_toNat_le.mpr (by simpa using h))
    omega
  have := size_lt f hg m.toNat N (by omega) hp hN
  have := prodL_pos f hg
  have : 1 ≤ N := by rw [← hp]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨by rw [prodL_push, hp], good_push _ _ hg h2 hW, ?_⟩
  simp; unfold Kc; omega

theorem d1_ge3 (N t0 : Nat) (m : UInt64) (f : Array UInt64) (s : Nat) (hD : D1 N t0 m f s) (hle : ¬ m ≤ 1) :
    3 ≤ m.toNat := by
  obtain ⟨hp, hg, h1, hodd, ht⟩ := hD
  have : ¬ m.toNat ≤ 1 := fun h => hle (UInt64.le_iff_toNat_le.mpr (by simpa using h))
  omega

theorem d1_le (N t0 : Nat) (m : UInt64) (f : Array UInt64) (s : Nat) (hD : D1 N t0 m f s) : m.toNat ≤ N := by
  obtain ⟨hp, hg, h1, hodd, ht⟩ := hD
  have := prodL_pos f hg
  rw [← hp]; exact Nat.le_mul_of_pos_left _ this

theorem rec_pre (N t0 fu : Nat) (hN : N < 2 ^ (fu + 1)) (m : UInt64) (f : Array UInt64) (s : Nat) (hD : D1 N t0 m f s)
    (r : UInt64) (tA s3 : Nat) (hD2 : D2 m.toNat tA r s3) (hr : r ≠ 0) :
    (1 ≤ r.toNat ∧ r.toNat < 2 ^ fu) ∧ (1 ≤ (m / r).toNat ∧ (m / r).toNat < 2 ^ fu) := by
  have hle := d1_le N t0 m f s hD
  obtain ⟨hp, hg, h1, hodd, ht⟩ := hD
  obtain ⟨hrok, -⟩ := hD2
  have hr0 : r.toNat ≠ 0 := fun h => hr (UInt64.toNat_inj.mp (by simpa using h))
  rcases hrok with h | ⟨hr1, hrm, hdv⟩
  · exact absurd h hr0
  obtain ⟨h3r, h3s, hrs⟩ := odd_div m.toNat r.toNat hodd hdv hr1 hrm
  rw [UInt64.toNat_div]
  have e : 2 ^ (fu + 1) = 2 * 2 ^ fu := by rw [Nat.pow_succ]; ring
  have := Nat.mul_le_mul_left r.toNat h3s
  have := Nat.mul_le_mul_right (m.toNat / r.toNat) h3r
  rw [hrs] at *
  omega

theorem copy_step (L : List UInt64) (f1 : Array UInt64) (s0 : Nat) (pref : List Int) (cur : Int)
    (b : Array UInt64) (t : Nat) (hb : b.toList = L ++ pref.map (get f1) ∧ t = s0 + 2 * pref.length) :
    (b.push (get f1 cur)).toList = L ++ (pref ++ [cur]).map (get f1) ∧ t + 1 + 1 = s0 + 2 * (pref ++ [cur]).length := by
  obtain ⟨h1, h2⟩ := hb
  refine ⟨by simp [h1], by simp; omega⟩

theorem range_len_size (v : Array UInt64) : (range 0 (size v)).length = v.size := by simp [range_length, size]

theorem fin_rec (N t0 : Nat) (hN : N < 2 ^ 64) (m : UInt64) (f : Array UInt64) (s1 : Nat) (hD : D1 N t0 m f s1)
    (s2 : Nat) (hs2 : s2 ≤ s1 + 160000) (r : UInt64) (s3 : Nat) (hD2 : D2 m.toNat s2 r s3) (hr : r ≠ 0)
    (f1 : Array UInt64) (s4 : Nat) (hf1 : prodL f1 = r.toNat ∧ Good f1 ∧ s4 ≤ s3 + Kc * r.toNat)
    (f2 : Array UInt64) (s5 : Nat) (hf2 : prodL f2 = (m / r).toNat ∧ Good f2 ∧ s5 ≤ s4 + Kc * (m / r).toNat)
    (res : Array UInt64) (s6 : Nat) (hres : res.toList = f.toList ++ f1.toList ++ f2.toList)
    (hs6 : s6 = s5 + 2 * f1.size + 2 * f2.size) :
    prodL res = N ∧ Good res ∧ s6 + res.size ≤ t0 + Kc * N := by
  have hle := d1_le N t0 m f s1 hD
  obtain ⟨hp, hg, h1, hodd, ht⟩ := hD
  obtain ⟨hrok, ht3⟩ := hD2
  obtain ⟨hp1, hg1, ht4⟩ := hf1
  obtain ⟨hp2, hg2, ht5⟩ := hf2
  have hr0 : r.toNat ≠ 0 := fun h => hr (UInt64.toNat_inj.mp (by simpa using h))
  rcases hrok with h | ⟨hr1, hrm, hdv⟩
  · exact absurd h hr0
  obtain ⟨h3r, h3s, hrs⟩ := odd_div m.toNat r.toNat hodd hdv hr1 hrm
  have hdiv : (m / r).toNat = m.toNat / r.toNat := UInt64.toNat_div m r
  have hres' : res = f ++ f1 ++ f2 := Array.ext' (by simp [hres])
  subst hres'
  have hz0 := size_lt f hg m.toNat N h1 hp hN
  have hz1 := size_lt f1 hg1 1 r.toNat (le_refl _) (by rw [Nat.mul_one]; exact hp1) r.toNat_lt
  have hz2 := size_lt f2 hg2 1 (m / r).toNat (le_refl _) (by rw [Nat.mul_one]; exact hp2) (m / r).toNat_lt
  have hc := cost_rec r.toNat (m / r).toNat m.toNat N h3r (by rw [hdiv]; exact h3s) (by rw [hdiv]; exact hrs) hle
  refine ⟨?_, good_append _ _ (good_append _ _ hg hg1) hg2, ?_⟩
  · rw [prodL_append, prodL_append, hp1, hp2, hdiv, Nat.mul_assoc, hrs, hp]
  · simp only [Array.size_append]
    omega

theorem fin_trial (N t0 : Nat) (hN : N < 2 ^ 64) (m : UInt64) (f0 : Array UInt64) (s1 : Nat) (hD : D1 N t0 m f0 s1)
    (s2 : Nat) (hs2 : s2 ≤ s1 + 160000) (r : UInt64) (s3 : Nat) (hD2 : D2 m.toNat s2 r s3)
    (n : UInt64) (f : Array UInt64) (i : UInt64) (s : Nat) (hD3 : D3 N m.toNat s3 n f i s) :
    (1 < n → prodL (f.push n) = N ∧ Good (f.push n) ∧ s + 1 + (f.push n).size ≤ t0 + Kc * N) ∧
    (¬ 1 < n → prodL f = N ∧ Good f ∧ s + f.size ≤ t0 + Kc * N) := by
  have hle := d1_le N t0 m f0 s1 hD
  obtain ⟨hp0, hg0, h10, -, ht1⟩ := hD
  obtain ⟨-, ht3⟩ := hD2
  obtain ⟨hp, hg, h1, hs, hlt, hiM, ht⟩ := hD3
  have hz := size_lt f hg n.toNat N h1 hp hN
  have hz0 := size_lt f0 hg0 m.toNat N h10 hp0 hN
  have hN1 : 1 ≤ N := by have := prodL_pos f hg; rw [← hp]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  constructor
  · intro hn1
    have hn1' : 1 < n.toNat := UInt64.lt_iff_toNat_lt.mp hn1
    have hpr := prime_of_noSmall n.toNat i.toNat (by omega) hs hlt
    refine ⟨by rw [prodL_push, hp], good_push _ _ hg (by omega) (fun _ => hpr), ?_⟩
    simp; unfold Kc; omega
  · intro hn1
    have : ¬ 1 < n.toNat := fun h => hn1 (UInt64.lt_iff_toNat_lt.mpr h)
    have e : n.toNat = 1 := by omega
    rw [e, Nat.mul_one] at hp
    refine ⟨hp, hg, ?_⟩
    unfold Kc; omega

theorem toNat_lt_fuel (x : UInt64) : x.toNat < fuel := by have := x.toNat_lt; simp only [fuel]; omega

theorem meas_lt (x : UInt64) (k : Nat) (hk : 2 ≤ k) : x.toNat + 2 - k < fuel := by
  have := x.toNat_lt; simp only [fuel]; omega

theorem cond_rho {p q : Prop} [Decidable p] [Decidable q] (h : ¬ (!((!decide p) && decide q)) = true) : ¬ p ∧ q := by
  simpa using h

theorem i3_init (N t0 : Nat) (m : UInt64) (f : Array UInt64) (s1 : Nat) (hD : D1 N t0 m f s1) (tC : Nat) :
    I3 N m.toNat tC m f 3 tC := by
  obtain ⟨hp, hg, h1, hodd, ht⟩ := hD
  have e3 : (3 : UInt64).toNat = 3 := rfl
  refine ⟨hp, hg, h1, hodd, by decide, by decide, ?_, by omega, le_refl _, by omega⟩
  intro d h2 h3 hd
  have : d = 2 := by omega
  subst this; omega


theorem unsorted_rec_spec (fu : Nat) : ∀ (n : UInt64) (t0 : Nat), 1 ≤ n.toNat → n.toNat < 2 ^ fu →
    ⦃fun t => ⌜t = t0⌝⦄ cp.factorize_unsorted_rec fu n
    ⦃⇓ r t => ⌜prodL r = n.toNat ∧ Good r ∧ t ≤ t0 + Kc * n.toNat⌝⦄ := by
  induction fu with
  | zero => intro n t0 h1 h2; simp at h2; omega
  | succ fu ih =>
  intro n t0 h1 h2
  mvcgen [cp.factorize_unsorted_rec, Proofs.Cpp.IsPrime.is_prime_spec, rho_spec, ih]
  case vc1.inv => exact ⟨fun b t => ⌜I1 n.toNat t0 b.1 b.2 t⌝, fun b t => ⌜D1 n.toNat t0 b.1 b.2 t⌝, fun b => b.1.toNat⟩
  case vc7.inv =>
    rename_i r1 nn ff hle s1 hd1 rb hrb s hp
    exact ⟨fun b t => ⌜I2 r1.1.toNat s b.1 b.2 t⌝, fun b t => ⌜D2 r1.1.toNat s b.1 t⌝, fun b => (4 - b.2).toNat⟩
  case vc24.inv =>
    rename_i r1 nn ff hle s2 hd1 rb hrb s1 hp rr r0 hr0 s hd2
    exact ⟨fun b t => ⌜I3 n.toNat r1.1.toNat s b.1 b.2.1 b.2.2 t⌝, fun b t => ⌜D3 n.toNat r1.1.toNat s b.1 b.2.1 b.2.2 t⌝,
      fun b => b.1.toNat + 2 - b.2.2.toNat⟩
  case inv1 =>
    rename_i r1 nn ff hle s1 hd1 rb hrb s2 hp rp r0 hr0 s3 hd2 f1 s4 hf1 f2 s hf2
    exact ⇓⟨xs, fac⟩ t => ⌜fac.toList = r1.2.toList ++ xs.prefix.map (get f1) ∧ t = s + 2 * xs.prefix.length⌝
  case inv2 =>
    rename_i r1 nn ff hle s1 hd1 rb hrb s2 hp rp r0 hr0 s3 hd2 f1 s4 hf1 f2 s hf2 fc sc hc
    exact ⇓⟨xs, fac⟩ t => ⌜fac.toList = r1.2.toList ++ f1.toList ++ xs.prefix.map (get f2) ∧
      t = s + 2 * f1.size + 2 * xs.prefix.length⌝
  case vc26.inv =>
    rename_i r1 nn ff hle s2 hd1 rb hrb s1 hp rp r0 hr0 s0 hd2 b nO bs fO iO s hI3 hc
    exact ⟨fun c t => ⌜I4 n.toNat r1.1.toNat s0 b.2.2 b.1 c.1 c.2 t⌝, fun c t => ⌜D4 n.toNat r1.1.toNat s0 b.2.2 b.1 c.1 c.2 t⌝,
      fun c => c.1.toNat⟩
  case vc2.step.isTrue =>
    exact i1_exit _ _ _ _ _ ‹I1 _ _ _ _ _› (of_dec2_true ‹(!!_) = true›)
  case vc3.step.isFalse =>
    have h := i1_step _ _ _ _ _ ‹I1 _ _ _ _ _› (Classical.not_not.mp (of_dec2_false ‹¬ (!!_) = true›))
    exact ⟨h.1, h.2⟩
  case vc4.succ.pre =>
    have := n.toNat_lt
    refine ⟨⟨?_, good_empty, h1, ?_⟩, by simp only [fuel]; omega⟩
    · simp +zetaDelta [prodL]
    · simp +zetaDelta; omega
  case vc5.succ.post.success.isTrue =>
    exact fin_one _ _ n.toNat_lt _ _ _ ‹D1 _ _ _ _ _› (of_dec_true ‹decide _ = true›)
  case vc6.succ.post.success.isFalse.post.success.isTrue =>
    rename_i rb hrb s hip fac
    exact fin_prime _ _ n.toNat_lt _ _ _ ‹D1 _ _ _ _ _› (of_dec_false ‹¬ decide _ = true›) (fun w => hip.2.1 w hrb) s hip.2.2
  case vc8.step.isTrue => exact i2_exit _ _ _ _ _ ‹I2 _ _ _ _ _›
  case vc9.hn => exact d1_ge3 _ _ _ _ _ ‹D1 _ _ _ _ _› (of_dec_false ‹¬ decide (_ ≤ 1) = true›)
  case vc10.hm => exact Nat.le_trans (by decide) (d1_ge3 _ _ _ _ _ ‹D1 _ _ _ _ _› (of_dec_false ‹¬ decide (_ ≤ 1) = true›))
  case vc11.step.isFalse.post.success =>
    have hc := cond_rho ‹¬ (!((!decide _) && decide _)) = true›
    have hr := ‹(_ = 0 ∨ _) ∧ _›
    have h := i2_step _ _ _ _ _ ‹I2 _ _ _ _ _› (of_dec_true (by simpa using hc.2)) _ _ hr.1 hr.2
    exact ⟨h.1, h.2⟩
  case vc12.succ.post.success.isFalse.post.success.isFalse.pre =>
    exact ⟨⟨Or.inl (by simp), by omega, by omega, by simp⟩, by simp [fuel]⟩
  case vc17.step =>
    rename_i hrng b s hb fac
    exact copy_step _ _ _ _ _ b s hb
  case vc18.succ.post.success.isFalse.post.success.isFalse.post.success.isTrue.post.success.post.success.pre =>
    exact ⟨(List.append_nil _).symm, rfl⟩
  case vc19.step =>
    rename_i hrng b s hb fac
    exact copy_step _ _ _ _ _ b s hb
  case vc20.succ.post.success.isFalse.post.success.isFalse.post.success.isTrue.post.success.post.success.post.success.pre =>
    rename_i fc sc hc
    have hc' : fc.toList = _ ∧ sc = _ := hc
    refine ⟨?_, ?_⟩
    · rw [hc'.1, range_map_get]; simp
    · rw [hc'.2, range_len_size]; simp
  case vc21.succ.post.success.isFalse.post.success.isFalse.post.success.isTrue.post.success.post.success.post.success.post.success =>
    rename_i r7 nn ff hle s6' hD1 rb hrb s5 hip r5 r4 hr4 s4 hD2 f1 s3 hf1 f2 s2 hf2 fc sc hc fr s hres
    have hres' : fr.toList = _ ∧ s = _ := hres
    rw [range_map_get, range_len_size] at hres'
    exact fin_rec n.toNat t0 n.toNat_lt r7.1 r7.2 s6' hD1 s5 hip.2.2 r5.1 s4 hD2 (of_dec_true hr4) f1 s3 hf1 f2 s2 hf2
      fr s hres'.1 hres'.2
  case vc25.step.isTrue => exact i3_exit _ _ _ _ _ _ _ ‹I3 _ _ _ _ _ _ _› (of_ndec_true ‹(!decide _) = true›)
  case vc27.step.isTrue => exact i4_exit _ _ _ _ _ _ _ _ ‹I4 _ _ _ _ _ _ _ _› (of_ndec_true ‹(!decide _) = true›)
  case vc28.step.isFalse =>
    have h := i4_step _ _ _ _ _ _ _ _ ‹I4 _ _ _ _ _ _ _ _› (of_ndec_false ‹¬ (!decide _) = true›)
    exact ⟨h.1, h.2⟩
  case vc29.step.isFalse.pre =>
    exact ⟨i3_enter _ _ _ _ _ _ _ ‹I3 _ _ _ _ _ _ _› (of_ndec_false ‹¬ (!decide _) = true›), toNat_lt_fuel _⟩
  case vc30.step.isFalse.post.success =>
    have h := i3_next _ _ _ _ _ _ _ ‹I3 _ _ _ _ _ _ _› _ _ _ ‹D4 _ _ _ _ _ _ _ _›
    exact ⟨h.1, h.2⟩
  case vc31.succ.post.success.isFalse.post.success.isFalse.post.success.isFalse.pre =>
    exact ⟨i3_init _ _ _ _ _ ‹D1 _ _ _ _ _› _, meas_lt _ _ (by show 2 ≤ (3 : UInt64).toNat; decide)⟩
  case vc32.succ.post.success.isFalse.post.success.isFalse.post.success.isFalse.post.success.isTrue =>
    exact (fin_trial n.toNat t0 n.toNat_lt _ _ _ ‹D1 _ _ _ _ _› _ (‹(_ → _) ∧ (_ → _ → _) ∧ _›).2.2 _ _ ‹D2 _ _ _ _›
      _ _ _ _ ‹D3 _ _ _ _ _ _ _›).1 (of_dec_true ‹decide (_ > _) = true›)
  case vc33.succ.post.success.isFalse.post.success.isFalse.post.success.isFalse.post.success.isFalse =>
    exact (fin_trial n.toNat t0 n.toNat_lt _ _ _ ‹D1 _ _ _ _ _› _ (‹(_ → _) ∧ (_ → _ → _) ∧ _›).2.2 _ _ ‹D2 _ _ _ _›
      _ _ _ _ ‹D3 _ _ _ _ _ _ _›).2 (of_dec_false ‹¬ decide (_ > _) = true›)
  case vc13.a => rename_i rp r0 hr0 s3 hd2; exact (rec_pre n.toNat t0 fu h2 _ _ _ ‹D1 _ _ _ _ _› _ _ _ hd2 (of_dec_true hr0)).1.1
  case vc14.a => rename_i rp r0 hr0 s3 hd2; exact (rec_pre n.toNat t0 fu h2 _ _ _ ‹D1 _ _ _ _ _› _ _ _ hd2 (of_dec_true hr0)).1.2
  case vc15.a => rename_i rp r0 hr0 s3 hd2 f1 s4 hf1; exact (rec_pre n.toNat t0 fu h2 _ _ _ ‹D1 _ _ _ _ _› _ _ _ hd2 (of_dec_true hr0)).2.1
  case vc16.a => rename_i rp r0 hr0 s3 hd2 f1 s4 hf1; exact (rec_pre n.toNat t0 fu h2 _ _ _ ‹D1 _ _ _ _ _› _ _ _ hd2 (of_dec_true hr0)).2.2
  all_goals first | exact ExceptConds.entails_false | simp


theorem sort64_perm (x : Array UInt64) : (Cpp.sort x).toList.Perm x.toList := by
  unfold Cpp.sort; simp only [List.toList_toArray]; exact List.mergeSort_perm _ _

theorem sort64_sorted (x : Array UInt64) : (Cpp.sort x).toList.Pairwise (fun a b => a.toNat ≤ b.toNat) := by
  unfold Cpp.sort
  simp only [List.toList_toArray]
  have key : ∀ a b : UInt64, ((!decide (b < a)) = true) ↔ a.toNat ≤ b.toNat := by
    intro a b; simp [UInt64.lt_iff_toNat_lt]
  have h := List.pairwise_mergeSort (le := fun a b : UInt64 => !decide (b < a))
    (fun a b c h1 h2 => by rw [key] at h1 h2 ⊢; omega)
    (fun a b => by rw [Bool.or_eq_true, key, key]; omega) x.toList
  exact h.imp (fun h => (key _ _).mp h)

theorem sort64_size (x : Array UInt64) : (Cpp.sort x).size = x.size := by
  have := (sort64_perm x).length_eq; simpa using this

theorem prodL_perm (a b : Array UInt64) (h : a.toList.Perm b.toList) : prodL a = prodL b := by
  unfold prodL; exact (h.map _).prod_eq

theorem good_perm (a b : Array UInt64) (h : a.toList.Perm b.toList) (hb : Good b) : Good a :=
  fun x hx => hb x (h.mem_iff.mp hx)

theorem lt_pow_of_ge (n : UInt64) (k : Nat) (hk : 64 ≤ k) : n.toNat < 2 ^ k :=
  Nat.lt_of_lt_of_le n.toNat_lt (Nat.pow_le_pow_right (by norm_num) hk)

theorem fuel_ge : 64 ≤ fuel := by unfold fuel; exact Nat.le_of_lt Nat.lt_two_pow_self

theorem unsorted_spec (n : UInt64) (h1 : 1 ≤ n.toNat) (t0 : Nat) :
    ⦃fun t => ⌜t = t0⌝⦄ cp.factorize_unsorted n
    ⦃⇓ r t => ⌜prodL r = n.toNat ∧ Good r ∧ t ≤ t0 + Kc * n.toNat⌝⦄ := by
  unfold cp.factorize_unsorted
  exact unsorted_rec_spec _ n t0 h1 (lt_pow_of_ge n _ fuel_ge)

theorem sortCost_le (k : Nat) (h : k < 64) : sortCost k ≤ 448 := by
  unfold sortCost
  have : Nat.log2 k ≤ 6 := by
    by_cases hk : k = 0
    · subst hk; simp
    · have := (Nat.log2_lt hk).mpr (show k < 2 ^ 7 by omega); omega
  have := Nat.mul_le_mul (show k ≤ 63 by omega) (show Nat.log2 k + 1 ≤ 7 by omega)
  omega

/-- `factorize(n)`: the prime factors of `n` with repetition in increasing order (`n ≥ 1`; primality of the
factors under `MRWitnessSet`, the hypothesis of `is_prime`). -/
theorem factorize_spec (n : UInt64) (h1 : 1 ≤ n.toNat) (t0 : Nat) :
    ⦃fun t => ⌜t = t0⌝⦄ cp.factorize n
    ⦃⇓ r t => ⌜prodL r = n.toNat ∧ Good r ∧ r.toList.Pairwise (fun a b => a.toNat ≤ b.toNat) ∧
      t ≤ t0 + Kc * n.toNat + 600⌝⦄ := by
  mvcgen [cp.factorize, unsorted_spec]
  rename_i r s h f
  obtain ⟨hp, hg, ht⟩ := h
  have hz := size_lt r hg 1 n.toNat (le_refl _) (by rw [Nat.mul_one]; exact hp) n.toNat_lt
  have hsc := sortCost_le r.size hz
  have hperm := sort64_perm r
  refine ⟨by rw [prodL_perm _ _ hperm, hp], good_perm _ _ hperm hg, sort64_sorted r, ?_⟩
  rw [sort64_size]; omega

theorem rle_nil_iff (l : List UInt64) : rle l = [] ↔ l = [] := by
  constructor
  · intro h; by_contra hl; exact rrle_ne_nil l hl (by simpa [rle] using h)
  · rintro rfl; simp [rle, rrle]

theorem runs_len_le (r : List (UInt64 × Int)) (h : ∀ p ∈ r, 0 < p.2) : r.length ≤ (unrle r).length := by
  induction r with
  | nil => simp
  | cons p r ih =>
    simp only [unrle, List.flatMap_cons, List.length_append, List.length_replicate, List.length_cons] at *
    have := h p (by simp)
    have := ih (fun q hq => h q (by simp [hq]))
    unfold unrle at this
    omega

theorem rle_len_le (l : List UInt64) : (rle l).length ≤ l.length := by
  have := runs_len_le (rle l) (rle_ok l).1
  rwa [unrle_rle] at this

theorem of_or_dec {p q : Prop} [Decidable p] [Decidable q] (h : (decide p || decide q) = true) : p ∨ q := by
  simpa using h

theorem of_nor_dec {p q : Prop} [Decidable p] [Decidable q] (h : ¬ (decide p || decide q) = true) : ¬ p ∧ ¬ q := by
  simpa using h

theorem cnt_push (f : Array UInt64) (s0 : Nat) (pref : List Int) (cur : Int) (b : Array (UInt64 × Int)) (t : Nat)
    (hb : b.toList = rle (pref.map (get f)) ∧ t ≤ s0 + 2 * pref.length) (hc : b.size = 0 ∨ (back b).1 ≠ get f cur) :
    (b.push (get f cur, 1)).toList = rle ((pref ++ [cur]).map (get f)) ∧ t + 1 + 1 ≤ s0 + 2 * (pref ++ [cur]).length := by
  obtain ⟨h1, h2⟩ := hb
  refine ⟨?_, by simp; omega⟩
  rw [List.map_append, List.map_singleton]
  apply counts_push _ _ _ h1
  rcases hc with h | h
  · left
    have : b.toList = [] := by simpa using h
    rw [h1] at this; exact (rle_nil_iff _).mp this
  · exact Or.inr h

theorem cnt_bump (f : Array UInt64) (s0 : Nat) (pref : List Int) (cur : Int) (b : Array (UInt64 × Int)) (t : Nat)
    (hb : b.toList = rle (pref.map (get f)) ∧ t ≤ s0 + 2 * pref.length) (hc : ¬ b.size = 0 ∧ ¬ (back b).1 ≠ get f cur) :
    (set b (size b - 1) ((get b (size b - 1)).1, (get b (size b - 1)).2 + 1)).toList = rle ((pref ++ [cur]).map (get f)) ∧
      t + 1 ≤ s0 + 2 * (pref ++ [cur]).length := by
  obtain ⟨h1, h2⟩ := hb
  refine ⟨?_, by simp; omega⟩
  rw [List.map_append, List.map_singleton]
  apply counts_bump _ _ _ h1 _ (Classical.not_not.mp hc.2)
  intro hn
  rw [hn] at h1
  apply hc.1
  have : b.toList = [] := by rw [h1]; simp [rle, rrle]
  simpa using this

/-- `factorize_count(n)`: the runs `(p, e)` of the sorted prime factors of `n` (`n ≥ 1`). -/
theorem factorize_count_spec (n : UInt64) (h1 : 1 ≤ n.toNat) (t0 : Nat) :
    ⦃fun t => ⌜t = t0⌝⦄ cp.factorize_count n
    ⦃⇓ r t => ⌜(∃ f : Array UInt64, prodL f = n.toNat ∧ Good f ∧ f.toList.Pairwise (fun a b => a.toNat ≤ b.toNat) ∧
      r.toList = rle f.toList) ∧ t ≤ t0 + Kc * n.toNat + 800⌝⦄ := by
  mvcgen [cp.factorize_count, factorize_spec]
  case inv1 =>
    rename_i f res0 s hf
    exact ⇓⟨xs, res⟩ t => ⌜res.toList = rle (xs.prefix.map (get f)) ∧ t ≤ s + 2 * xs.prefix.length⌝
  case vc2.step.isTrue =>
    rename_i hr b t hb hc res
    exact cnt_push _ _ _ _ b t hb (of_or_dec hc)
  case vc3.step.isFalse =>
    rename_i hr b t hb hc res
    exact cnt_bump _ _ _ _ b t hb (of_nor_dec hc)
  case vc4.post.success.pre => exact ⟨by simp +zetaDelta [rle, rrle], by simp⟩
  case vc5.post.success.post.success =>
    rename_i f res0 s hf r t hr
    have hr' : r.toList = _ ∧ t ≤ _ := hr
    rw [range_map_get, range_len_size] at hr'
    obtain ⟨hp, hg, hs, ht⟩ := hf
    have hz := size_lt f hg 1 n.toNat (le_refl _) (by rw [Nat.mul_one]; exact hp) n.toNat_lt
    have hl := rle_len_le f.toList
    rw [← hr'.1] at hl
    simp at hl
    exact ⟨⟨f, hp, hg, hs, hr'.1⟩, by omega⟩
  all_goals first | exact ExceptConds.entails_false | simp


/-! ## The divisors generated by the depth-first search -/

/-- `gen L f`: `f * p_0^j_0 * ... ` for all `j_l ≤ e_l`, in the order of the search. -/
def gen : List (Nat × Nat) → Nat → List Nat
  | [], f => [f]
  | (p, e) :: t, f => (List.range (e + 1)).flatMap (fun j => gen t (f * p ^ j))

def PP : List (Nat × Nat) → Nat
  | [] => 1
  | (p, e) :: t => p ^ e * PP t

theorem gen_mem (L : List (Nat × Nat)) : ∀ f x, x ∈ gen L f → ∃ y, x = f * y ∧ y ∣ PP L := by
  induction L with
  | nil => intro f x h; simp [gen] at h; exact ⟨1, by simp [h], by simp [PP]⟩
  | cons q t ih =>
    obtain ⟨p, e⟩ := q
    intro f x h
    simp only [gen, List.mem_flatMap, List.mem_range] at h
    obtain ⟨j, hj, hx⟩ := h
    obtain ⟨y, rfl, hy⟩ := ih _ _ hx
    refine ⟨p ^ j * y, by ring, ?_⟩
    simp only [PP]
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (by omega)) hy

theorem gen_length (L : List (Nat × Nat)) : ∀ f, (gen L f).length = (L.map (fun q => q.2 + 1)).prod := by
  induction L with
  | nil => intro f; simp [gen]
  | cons q t ih =>
    obtain ⟨p, e⟩ := q
    intro f
    simp only [gen, List.length_flatMap, ih, List.map_cons, List.prod_cons]
    simp [List.sum_const_nat]

/-- `d ∣ p^e m` with a prime `p ∤ m` splits as `p^j d'` with `d' ∣ m`. -/
theorem split_dvd (p : Nat) (hp : IsPrime p) (m : Nat) (hpm : ¬ p ∣ m) :
    ∀ e d, d ∣ p ^ e * m → ∃ j, j ≤ e ∧ ∃ d', d = p ^ j * d' ∧ d' ∣ m := by
  intro e
  induction e with
  | zero => intro d hd; exact ⟨0, le_refl _, d, by simp, by simpa using hd⟩
  | succ e ih =>
    intro d hd
    by_cases hpd : p ∣ d
    · obtain ⟨d1, rfl⟩ := hpd
      have hp0 : 0 < p := by have := hp.1; omega
      have : d1 ∣ p ^ e * m := by
        rw [Nat.pow_succ, Nat.mul_comm (p ^ e) p, Nat.mul_assoc] at hd
        exact Nat.dvd_of_mul_dvd_mul_left hp0 hd
      obtain ⟨j, hj, d', rfl, hd'⟩ := ih d1 this
      exact ⟨j + 1, by omega, d', by rw [Nat.pow_succ]; ring, hd'⟩
    · have hc : Nat.Coprime d p := by
        have h1 : Nat.gcd d p ∣ p := Nat.gcd_dvd_right d p
        rcases hp.2 _ h1 with h | h
        · exact h
        · exact absurd (h ▸ Nat.gcd_dvd_left d p) hpd
      have hc' : Nat.Coprime d (p ^ (e + 1)) := Nat.Coprime.pow_right _ hc
      exact ⟨0, by omega, d, by simp, hc'.dvd_of_dvd_mul_left hd⟩

/-- Distinct primes. -/
def PrimesOK (L : List (Nat × Nat)) : Prop := (∀ q ∈ L, IsPrime q.1) ∧ (L.map Prod.fst).Nodup

theorem prime_dvd_pow (p q e : Nat) (hp : IsPrime p) (hq : IsPrime q) (h : p ∣ q ^ e) : p = q := by
  induction e with
  | zero => simp at h; have := hp.1; subst h; omega
  | succ e ih =>
    rw [Nat.pow_succ] at h
    by_cases hd : p ∣ q ^ e
    · exact ih hd
    · have hc : Nat.Coprime p (q ^ e) := by
        have h1 : Nat.gcd p (q ^ e) ∣ p := Nat.gcd_dvd_left _ _
        rcases hp.2 _ h1 with h | h
        · exact h
        · exact absurd (h ▸ Nat.gcd_dvd_right p (q ^ e)) hd
      have := hc.dvd_of_dvd_mul_left h
      rcases hq.2 _ this with h | h
      · have := hp.1; omega
      · exact h

theorem not_dvd_PP (p : Nat) (hp : IsPrime p) : ∀ (L : List (Nat × Nat)), (∀ q ∈ L, IsPrime q.1) →
    p ∉ L.map Prod.fst → ¬ p ∣ PP L := by
  intro L
  induction L with
  | nil => intro _ _ h; simp [PP] at h; have := hp.1; subst h; omega
  | cons q t ih =>
    obtain ⟨q, e⟩ := q
    intro hL hn h
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    simp only [PP] at h
    by_cases hd : p ∣ q ^ e
    · exact hn.1 (prime_dvd_pow p q e hp (hL (q, e) (by simp)) hd)
    · have hc : Nat.Coprime p (q ^ e) := by
        have h1 : Nat.gcd p (q ^ e) ∣ p := Nat.gcd_dvd_left _ _
        rcases hp.2 _ h1 with h | h
        · exact h
        · exact absurd (h ▸ Nat.gcd_dvd_right p (q ^ e)) hd
      exact ih (fun x hx => hL x (by simp [hx])) hn.2 (hc.dvd_of_dvd_mul_left h)

theorem gen_complete (L : List (Nat × Nat)) (hL : PrimesOK L) : ∀ f d, d ∣ PP L → f * d ∈ gen L f := by
  induction L with
  | nil => intro f d hd; simp [PP] at hd; simp [gen, hd]
  | cons q t ih =>
    obtain ⟨p, e⟩ := q
    intro f d hd
    obtain ⟨hpr, hnd⟩ := hL
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hp : IsPrime p := hpr (p, e) (by simp)
    have hpt : ¬ p ∣ PP t := not_dvd_PP p hp t (fun q hq => hpr q (by simp [hq])) hnd.1
    obtain ⟨j, hj, d', rfl, hd'⟩ := split_dvd p hp (PP t) hpt e d (by simpa [PP] using hd)
    simp only [gen, List.mem_flatMap, List.mem_range]
    refine ⟨j, by omega, ?_⟩
    have := ih ⟨fun q hq => hpr q (by simp [hq]), hnd.2⟩ (f * p ^ j) d' hd'
    rwa [← Nat.mul_assoc]

theorem gen_nodup (L : List (Nat × Nat)) (hL : PrimesOK L) : ∀ f, 0 < f → (gen L f).Nodup := by
  induction L with
  | nil => intro f _; simp [gen]
  | cons q t ih =>
    obtain ⟨p, e⟩ := q
    intro f hf
    obtain ⟨hpr, hnd⟩ := hL
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hp : IsPrime p := hpr (p, e) (by simp)
    have hp0 : 0 < p := by have := hp.1; omega
    have hpt : ¬ p ∣ PP t := not_dvd_PP p hp t (fun q hq => hpr q (by simp [hq])) hnd.1
    have ht : PrimesOK t := ⟨fun q hq => hpr q (by simp [hq]), hnd.2⟩
    simp only [gen]
    rw [List.nodup_flatMap]
    refine ⟨fun j _ => ih ht _ (Nat.mul_pos hf (Nat.pow_pos hp0)), ?_⟩
    apply (List.nodup_range).pairwise_of_forall_ne
    intro a ha b hb hab x hxa hxb
    obtain ⟨ya, rfl, hya⟩ := gen_mem t _ _ hxa
    obtain ⟨yb, hyb', hyb⟩ := gen_mem t _ _ hxb
    -- f p^a ya = f p^b yb with p ∤ ya, yb
    have hpa : ¬ p ∣ ya := fun h => hpt (Nat.dvd_trans h hya)
    have hpb : ¬ p ∣ yb := fun h => hpt (Nat.dvd_trans h hyb)
    have e1 : p ^ a * ya = p ^ b * yb := by
      rw [Nat.mul_assoc, Nat.mul_assoc] at hyb'
      exact Nat.eq_of_mul_eq_mul_left hf hyb'
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have : ya = p ^ (b - a) * yb := by
        rw [show b = a + (b - a) by omega, Nat.pow_add, Nat.mul_assoc] at e1
        exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp0) e1
      exact hpa (by rw [this]; exact Nat.dvd_trans (by simpa using (Nat.pow_dvd_pow p (show 1 ≤ b - a by omega))) (Nat.dvd_mul_right _ _))
    · have : yb = p ^ (a - b) * ya := by
        rw [show a = b + (a - b) by omega, Nat.pow_add, Nat.mul_assoc] at e1
        exact (Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp0) e1).symm
      exact hpb (by rw [this]; exact Nat.dvd_trans (by simpa using (Nat.pow_dvd_pow p (show 1 ≤ a - b by omega))) (Nat.dvd_mul_right _ _))


def Lf (factor : Array (UInt64 × Int)) : List (Nat × Nat) := factor.toList.map (fun q => (q.1.toNat, q.2.toNat))

def costG : List (Nat × Nat) → Nat
  | [] => 0
  | [(_, e)] => 1 + 2 * (e + 1)
  | (_, e) :: t => 2 + (e + 1) * (1 + costG t)

theorem costG_cons (p e : Nat) (t : List (Nat × Nat)) (ht : t ≠ []) : costG ((p, e) :: t) = 2 + (e + 1) * (1 + costG t) := by
  cases t with
  | nil => exact absurd rfl ht
  | cons a t => rfl

def DPre (factor : Array (UInt64 × Int)) (f : UInt64) (i : Int) : Prop :=
  0 ≤ i ∧ i < factor.size ∧ (∀ q ∈ factor.toList, 0 < q.2 ∧ q.2 < 64) ∧ (∀ q ∈ factor.toList, 1 ≤ q.1.toNat) ∧
    1 ≤ f.toNat ∧ f.toNat * PP ((Lf factor).drop i.toNat) < 2 ^ 64

theorem PP_pos (L : List (Nat × Nat)) (h : ∀ q ∈ L, 1 ≤ q.1) : 1 ≤ PP L := by
  induction L with
  | nil => simp [PP]
  | cons q t ih =>
    obtain ⟨p, e⟩ := q
    simp only [PP]
    have hp : 1 ≤ p := h (p, e) (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)

theorem Lf_drop (factor : Array (UInt64 × Int)) (i : Int) (h0 : 0 ≤ i) (hi : i < factor.size) :
    (Lf factor).drop i.toNat = ((get factor i).1.toNat, (get factor i).2.toNat) :: (Lf factor).drop (i + 1).toNat := by
  have hlt : i.toNat < (Lf factor).length := by simp [Lf]; omega
  rw [List.drop_eq_getElem_cons hlt]
  simp only [Lf, List.getElem_map, get, Array.getElem!_eq_getD, Array.getD]
  rw [show (i + 1).toNat = i.toNat + 1 by omega]
  have : i.toNat < factor.size := by omega
  simp [this]

theorem Lf_mem (factor : Array (UInt64 × Int)) (h1 : ∀ q ∈ factor.toList, 1 ≤ q.1.toNat) (k : Nat) :
    ∀ q ∈ (Lf factor).drop k, 1 ≤ q.1 := by
  intro q hq
  have := List.mem_of_mem_drop hq
  simp only [Lf, List.mem_map] at this
  obtain ⟨x, hx, rfl⟩ := this
  exact h1 x hx

theorem get_mem (factor : Array (UInt64 × Int)) (i : Int) (h0 : 0 ≤ i) (hi : i < factor.size) :
    get factor i ∈ factor.toList := by
  simp only [get, Array.getElem!_eq_getD, Array.getD]
  have : i.toNat < factor.size := by omega
  simp [this]

theorem mul_val (f p : UInt64) (P j : Nat) (hp : p.toNat = P ^ j % 2 ^ 64) (hf : 1 ≤ f.toNat)
    (hb : f.toNat * P ^ j < 2 ^ 64) : (f * p).toNat = f.toNat * P ^ j := by
  have : P ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hf) hb
  rw [UInt64.toNat_mul, hp, Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt hb]

theorem pow_step (p q : UInt64) (P j : Nat) (hp : p.toNat = P ^ j % 2 ^ 64) (hq : q.toNat = P) :
    (p * q).toNat = P ^ (j + 1) % 2 ^ 64 := by
  rw [UInt64.toNat_mul, hp, hq, Nat.mod_mul_mod, ← Nat.pow_succ]

theorem bound_j (f P E j : Nat) (R : List (Nat × Nat)) (hj : j ≤ E) (hP : 1 ≤ P) (hR : 1 ≤ PP R) (h : f * PP ((P, E) :: R) < 2 ^ 64) :
    f * P ^ j * PP R < 2 ^ 64 := by
  simp only [PP] at h
  have : P ^ j ≤ P ^ E := Nat.pow_le_pow_right hP hj
  have := Nat.mul_le_mul_left f (Nat.mul_le_mul_right (PP R) this)
  rw [Nat.mul_assoc]; omega

theorem bound_j' (f P E j : Nat) (R : List (Nat × Nat)) (hj : j ≤ E) (hP : 1 ≤ P) (hR : 1 ≤ PP R) (h : f * PP ((P, E) :: R) < 2 ^ 64) :
    f * P ^ j < 2 ^ 64 := by
  have := bound_j f P E j R hj hP hR h
  exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hR) this

theorem range_cur_lt {e : Int} {pref suff : List Int} {cur : Int} (h : range 0 (e + 1) = pref ++ cur :: suff) :
    pref.length < (e + 1).toNat := by
  have := congrArg List.length h
  rw [range_length] at this; simp at this; omega

/-- The invariant of the loop of the last level. -/
def LI (div : Array UInt64) (f : UInt64) (P : Nat) (s : Nat) (len : Nat) (st : Array UInt64 × UInt64) (t : Nat) : Prop :=
  st.1.toList.map UInt64.toNat = div.toList.map UInt64.toNat ++ (List.range len).map (fun j => f.toNat * P ^ j) ∧
    st.2.toNat = P ^ len % 2 ^ 64 ∧ t = s + 2 * len

theorem li_step (div : Array UInt64) (f : UInt64) (q : UInt64) (s len : Nat) (st : Array UInt64 × UInt64) (t : Nat)
    (h : LI div f q.toNat s len st t) (hf : 1 ≤ f.toNat) (hb : f.toNat * q.toNat ^ len < 2 ^ 64) :
    LI div f q.toNat s (len + 1) (st.1.push (f * st.2), st.2 * q) (t + 1 + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, pow_step _ _ _ _ h2 rfl, by omega⟩
  simp only [Array.toList_push, List.map_append, h1, List.range_succ, List.map_cons, List.map_nil, List.append_assoc]
  rw [mul_val f st.2 q.toNat len h2 hf hb]

/-- The invariant of the loop of an inner level. -/
def NI (div : Array UInt64) (f : UInt64) (P E : Nat) (R : List (Nat × Nat)) (s : Nat) (st : Array UInt64 × UInt64 × Int)
    (t : Nat) : Prop :=
  ∃ j : Nat, st.2.2 = (j : Int) ∧ j ≤ E + 1 ∧
    st.1.toList.map UInt64.toNat = div.toList.map UInt64.toNat ++ (List.range j).flatMap (fun j => gen R (f.toNat * P ^ j)) ∧
    st.2.1.toNat = P ^ j % 2 ^ 64 ∧ t ≤ s + j * (1 + costG R)

theorem flatMap_single (l : List Nat) (g : Nat → Nat) : l.flatMap (fun j => [g j]) = l.map g := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem gen_single (P E f : Nat) : gen [(P, E)] f = (List.range (E + 1)).map (fun j => f * P ^ j) := by
  simp only [gen]; exact flatMap_single _ _


def DPost (factor : Array (UInt64 × Int)) (div : Array UInt64) (f : UInt64) (i : Int) (t0 : Nat) (r : Array UInt64) (t : Nat) : Prop :=
  r.toList.map UInt64.toNat = div.toList.map UInt64.toNat ++ gen ((Lf factor).drop i.toNat) f.toNat ∧
    t ≤ t0 + costG ((Lf factor).drop i.toNat)

section
variable (factor : Array (UInt64 × Int)) (div : Array UInt64) (f : UInt64) (i : Int) (t0 : Nat)

theorem dpre_facts (hP : DPre factor f i) :
    0 < (get factor i).2 ∧ (get factor i).2 < 64 ∧ 1 ≤ (get factor i).1.toNat ∧ 1 ≤ f.toNat ∧
    1 ≤ PP ((Lf factor).drop (i + 1).toNat) ∧
    f.toNat * PP (((get factor i).1.toNat, (get factor i).2.toNat) :: (Lf factor).drop (i + 1).toNat) < 2 ^ 64 := by
  obtain ⟨h0, hi, he, h1, hf, hb⟩ := hP
  have hm := get_mem factor i h0 hi
  rw [Lf_drop factor i h0 hi] at hb
  exact ⟨(he _ hm).1, (he _ hm).2, h1 _ hm, hf, PP_pos _ (Lf_mem factor h1 _), hb⟩

theorem vc_last_step (hP : DPre factor f i) (pref : List Int) (cur : Int) (suff : List Int)
    (h : range 0 ((get factor i).2 + 1) = pref ++ cur :: suff) (b : Array UInt64 × UInt64) (t : Nat)
    (hb : LI div f (get factor i).1.toNat (t0 + 1) pref.length b t) :
    LI div f (get factor i).1.toNat (t0 + 1) (pref ++ [cur]).length (b.1.push (f * b.2), b.2 * (get factor i).1) (t + 1 + 1) := by
  obtain ⟨he0, he1, hp1, hf, hR, hb'⟩ := dpre_facts factor f i hP
  have hl := range_cur_lt h
  simp only [List.length_append, List.length_singleton]
  exact li_step div f _ _ _ b t hb hf (bound_j' _ _ _ _ _ (by omega) hp1 hR hb')

theorem vc_last_pre (s : Nat) (hs : s = t0) : LI div f (get factor i).1.toNat (t0 + 1) 0 (div, 1) (s + 1) := by
  refine ⟨by simp, by simp, by omega⟩

theorem vc_last_post (hP : DPre factor f i) (hlast : i = (factor.size : Int) - 1) (r : Array UInt64 × UInt64) (s : Nat)
    (h : LI div f (get factor i).1.toNat (t0 + 1) (range 0 ((get factor i).2 + 1)).length r s) :
    DPost factor div f i t0 r.1 s := by
  obtain ⟨he0, he1, hp1, hf, hR, hb'⟩ := dpre_facts factor f i hP
  obtain ⟨h0, hi, -⟩ := hP
  obtain ⟨h1, h2, h3⟩ := h
  rw [range_length] at h1 h3
  have hE : ((get factor i).2 + 1 - 0).toNat = (get factor i).2.toNat + 1 := by omega
  rw [hE] at h1 h3
  have hR0 : (Lf factor).drop (i + 1).toNat = [] := by
    apply List.drop_eq_nil_of_le; simp [Lf]; omega
  unfold DPost
  rw [Lf_drop factor i h0 hi, hR0, gen_single]
  refine ⟨h1, ?_⟩
  simp only [costG]; omega

theorem vc_inner_exit (hP : DPre factor f i) (hnl : ¬ i = (factor.size : Int) - 1) (b : Array UInt64 × UInt64 × Int) (s : Nat)
    (h : NI div f (get factor i).1.toNat (get factor i).2.toNat ((Lf factor).drop (i + 1).toNat) (t0 + 1) b s)
    (hc : ¬ b.2.2 ≤ (get factor i).2) : DPost factor div f i t0 b.1 (s + 1) := by
  obtain ⟨he0, he1, hp1, hf, hR, hb'⟩ := dpre_facts factor f i hP
  obtain ⟨h0, hi, -⟩ := hP
  obtain ⟨j, hj, hjE, h1, h2, h3⟩ := h
  have hjv : j = (get factor i).2.toNat + 1 := by omega
  subst hjv
  have hne : (Lf factor).drop (i + 1).toNat ≠ [] := by
    intro hn; have := List.drop_eq_nil_iff.mp hn; simp [Lf] at this; omega
  unfold DPost
  rw [Lf_drop factor i h0 hi, costG_cons _ _ _ hne]
  refine ⟨h1, by omega⟩

theorem vc_inner_pre (hP : DPre factor f i) (hnl : ¬ i = (factor.size : Int) - 1) (b : Array UInt64 × UInt64 × Int) (s : Nat)
    (h : NI div f (get factor i).1.toNat (get factor i).2.toNat ((Lf factor).drop (i + 1).toNat) (t0 + 1) b s)
    (hc : b.2.2 ≤ (get factor i).2) : DPre factor (f * b.2.1) (i + 1) ∧ (f * b.2.1).toNat = f.toNat * (get factor i).1.toNat ^ b.2.2.toNat := by
  obtain ⟨he0, he1, hp1, hf, hR, hb'⟩ := dpre_facts factor f i hP
  obtain ⟨h0, hi, hes, h1s, -⟩ := hP
  obtain ⟨j, hj, hjE, h1, h2, h3⟩ := h
  have hjl : j ≤ (get factor i).2.toNat := by omega
  have hmv := mul_val f b.2.1 _ j h2 hf (bound_j' _ _ _ _ _ hjl hp1 hR hb')
  have hpos : 1 ≤ f.toNat * (get factor i).1.toNat ^ j := Nat.mul_pos hf (Nat.pow_pos (by omega))
  refine ⟨⟨by omega, by omega, hes, h1s, by rw [hmv]; exact hpos, ?_⟩, by rw [hmv, hj]; simp⟩
  rw [hmv]; exact bound_j _ _ _ _ _ hjl hp1 hR hb'

theorem vc_inner_step (hP : DPre factor f i) (hnl : ¬ i = (factor.size : Int) - 1) (b : Array UInt64 × UInt64 × Int) (s : Nat)
    (h : NI div f (get factor i).1.toNat (get factor i).2.toNat ((Lf factor).drop (i + 1).toNat) (t0 + 1) b s)
    (hc : b.2.2 ≤ (get factor i).2) (r : Array UInt64) (s' : Nat) (hr : DPost factor b.1 (f * b.2.1) (i + 1) (s + 1) r s') :
    NI div f (get factor i).1.toNat (get factor i).2.toNat ((Lf factor).drop (i + 1).toNat) (t0 + 1)
      (r, b.2.1 * (get factor i).1, b.2.2 + 1) s' ∧
    ((get factor i).2 + 1 - (b.2.2 + 1)).toNat < ((get factor i).2 + 1 - b.2.2).toNat := by
  have hmv := (vc_inner_pre factor div f i t0 hP hnl b s h hc).2
  obtain ⟨j, hj, hjE, h1, h2, h3⟩ := h
  obtain ⟨hr1, hr2⟩ := hr
  rw [hmv, hj] at hr1
  simp only [Int.toNat_natCast] at hr1
  refine ⟨⟨j + 1, by rw [hj]; push_cast; ring, by omega, ?_, pow_step _ _ _ _ h2 rfl, ?_⟩, by omega⟩
  · rw [hr1, h1, List.range_succ, List.flatMap_append, List.append_assoc]; simp
  · rw [Nat.add_mul]; omega

end

theorem dfs_spec (fu : Nat) : ∀ (factor : Array (UInt64 × Int)) (div : Array UInt64) (f : UInt64) (i : Int) (t0 : Nat),
    DPre factor f i → factor.size ≤ i.toNat + fu →
    ⦃fun t => ⌜t = t0⌝⦄ cp.divisors_dfs_rec fu factor div f i ⦃⇓ r t => ⌜DPost factor div f i t0 r t⌝⦄ := by
  induction fu with
  | zero => intro factor div f i t0 hP hs; obtain ⟨h0, hi, -⟩ := hP; omega
  | succ fu ih =>
  intro factor div f i t0 hP hs
  mvcgen [cp.divisors_dfs_rec, ih]
  case inv1 =>
    exact ⇓⟨xs, st⟩ t => ⌜LI div f (get factor i).1.toNat (t0 + 1) xs.prefix.length st t⌝
  case vc5.inv =>
    exact ⟨fun st t => ⌜NI div f (get factor i).1.toNat (get factor i).2.toNat ((Lf factor).drop (i + 1).toNat) (t0 + 1) st t⌝,
      fun st t => ⌜DPost factor div f i t0 st.1 t⌝, fun st => ((get factor i).2 + 1 - st.2.2).toNat⟩
  case vc1.step =>
    rename_i hl pref cur suff hr b dv p s hb dv' p'
    exact vc_last_step factor div f i t0 hP pref cur suff hr b s hb
  case vc2.succ.isTrue.pre => rename_i s hs nf jp hl; exact vc_last_pre factor div f i t0 s hs
  case vc3.succ.isTrue.post.success =>
    rename_i s1 hs1 nf jp hl r dv p s h
    exact vc_last_post factor div f i t0 hP (of_dec_true hl) r s h
  case vc6.step.isTrue =>
    rename_i s1 hs1 nf jp hl b dv bs p j s h hc
    exact vc_inner_exit factor div f i t0 hP (of_dec_false hl) b s h (of_ndec_true hc)
  case vc7.a =>
    rename_i s1 hs1 nf jp hl b dv bs p j s h hc
    exact (vc_inner_pre factor div f i t0 hP (of_dec_false hl) b s h (of_ndec_false hc)).1
  case vc8.a => have := hP.1; omega
  case vc9.step.isFalse.post.success =>
    rename_i s1 hs1 nf jp hl b dv bs p j s h hc r p2 j2 s' hr
    have := vc_inner_step factor div f i t0 hP (of_dec_false hl) b s h (of_ndec_false hc) r s' hr
    exact ⟨this.1, this.2⟩
  case vc10.succ.isFalse.pre =>
    rename_i s hs nf jp hl
    obtain ⟨he0, he1, -⟩ := dpre_facts factor f i hP
    refine ⟨⟨0, rfl, by omega, by simp, by simp, by simp; omega⟩, ?_⟩
    simp only [fuel]; omega
  all_goals first | exact ExceptConds.entails_false | (rename_i h; exact h)


def conv (q : UInt64 × Int) : Nat × Nat := (q.1.toNat, q.2.toNat)

theorem PP_runs (r : List (UInt64 × Int)) : PP (r.map conv) = ((unrle r).map UInt64.toNat).prod := by
  induction r with
  | nil => simp [PP, unrle]
  | cons q r ih =>
    simp only [List.map_cons, conv, PP]
    rw [show unrle (q :: r) = List.replicate q.2.toNat q.1 ++ unrle r by simp [unrle]]
    rw [List.map_append, List.prod_append, ← ih]
    simp [conv]

theorem mem_runs (r : List (UInt64 × Int)) (q : UInt64 × Int) (hq : q ∈ r) (hpos : 0 < q.2) :
    q.1 ∈ unrle r ∧ q.2.toNat ≤ (unrle r).length := by
  induction r with
  | nil => simp at hq
  | cons a r ih =>
    rw [show unrle (a :: r) = List.replicate a.2.toNat a.1 ++ unrle r by simp [unrle]]
    rcases List.mem_cons.mp hq with rfl | h
    · refine ⟨List.mem_append_left _ (List.mem_replicate.mpr ⟨by omega, rfl⟩), by simp⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_append_right _ h1, by simp; omega⟩

/-- Runs of a sorted list have strictly increasing values. -/
theorem runs_strict (r : List (UInt64 × Int)) (hok : RunsOk r)
    (hs : (unrle r).Pairwise (fun a b => a.toNat ≤ b.toNat)) : (r.map (fun q => q.1.toNat)).Pairwise (· < ·) := by
  induction r with
  | nil => simp
  | cons a r ih =>
    obtain ⟨hpos, hadj⟩ := hok
    rw [show unrle (a :: r) = List.replicate a.2.toNat a.1 ++ unrle r by simp [unrle]] at hs
    rw [List.pairwise_append] at hs
    obtain ⟨-, hs2, hs3⟩ := hs
    have hok' : RunsOk r := ⟨fun p hp => hpos p (by simp [hp]), fun i h => by
      have := hadj (i + 1) (by simp; omega); simpa using this⟩
    have ha : a.1 ∈ List.replicate a.2.toNat a.1 := List.mem_replicate.mpr ⟨by have := hpos a (by simp); omega, rfl⟩
    simp only [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih hok' hs2⟩
    intro y hy
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    have hle : a.1.toNat ≤ b.1.toNat := hs3 _ ha _ (mem_runs r b hb (hpos b (by simp [hb]))).1
    -- strict: the first later run differs from `a`, every later run value is at least that one
    cases r with
    | nil => simp at hb
    | cons c r' =>
      have hac : a.1 ≠ c.1 := by have := hadj 0 (by simp); simpa using this
      have hac' : a.1.toNat < c.1.toNat := by
        have := hs3 _ ha _ (mem_runs (c :: r') c (by simp) (hpos c (by simp))).1
        have : a.1.toNat ≠ c.1.toNat := fun h => hac (UInt64.toNat_inj.mp h)
        omega
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hac'
      · have := ih hok' hs2
        simp only [List.map_cons, List.pairwise_cons] at this
        have := this.1 _ (List.mem_map.mpr ⟨b, hb', rfl⟩)
        omega

theorem prodE_le (L : List (Nat × Nat)) (h : ∀ q ∈ L, 2 ≤ q.1) : (L.map (fun q => q.2 + 1)).prod ≤ PP L := by
  induction L with
  | nil => simp [PP]
  | cons q t ih =>
    obtain ⟨p, e⟩ := q
    simp only [List.map_cons, List.prod_cons, PP]
    have hp : 2 ≤ p := h (p, e) (by simp)
    have h1 : e + 1 ≤ p ^ e := Nat.le_trans (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hp e)
    exact Nat.mul_le_mul h1 (ih (fun x hx => h x (by simp [hx])))

theorem prodE_pos (t : List (Nat × Nat)) : 1 ≤ (t.map (fun q => q.2 + 1)).prod := by
  induction t with
  | nil => simp
  | cons q t ih => simp only [List.map_cons, List.prod_cons]; exact Nat.mul_pos (by omega) ih

theorem costG_le (L : List (Nat × Nat)) (hL : L ≠ []) : costG L ≤ 4 * L.length * (L.map (fun q => q.2 + 1)).prod := by
  induction L with
  | nil => exact absurd rfl hL
  | cons q t ih =>
    obtain ⟨p, e⟩ := q
    by_cases ht : t = []
    · subst ht; simp [costG]; omega
    · rw [costG_cons _ _ _ ht]
      have := ih ht
      have hD := prodE_pos t
      simp only [List.length_cons, List.map_cons, List.prod_cons]
      have := Nat.mul_le_mul_left (e + 1) this
      nlinarith

def DivOK (n : Nat) (r : Array UInt64) : Prop :=
  (∀ x ∈ r.toList, x.toNat ∣ n) ∧ r.toList.Pairwise (fun a b => a.toNat ≤ b.toNat) ∧
    (W → (∀ d, d ∣ n → ∃ x ∈ r.toList, x.toNat = d) ∧ (r.toList.map UInt64.toNat).Nodup)

theorem dfs_top_spec (factor : Array (UInt64 × Int)) (div : Array UInt64) (f : UInt64) (i : Int) (t0 : Nat)
    (hP : DPre factor f i) (hs : factor.size < 64) :
    ⦃fun t => ⌜t = t0⌝⦄ cp.divisors_dfs factor div f i ⦃⇓ r t => ⌜DPost factor div f i t0 r t⌝⦄ := by
  unfold cp.divisors_dfs
  exact dfs_spec _ factor div f i t0 hP (by have := fuel_ge; omega)

theorem count_facts (n : UInt64) (hn1 : n ≠ 1) (factor : Array (UInt64 × Int)) (f : Array UInt64)
    (hp : prodL f = n.toNat) (hg : Good f) (hs : f.toList.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (hr : factor.toList = rle f.toList) :
    DPre factor 1 0 ∧ factor.size < 64 ∧ PP (Lf factor) = n.toNat ∧ (W → PrimesOK (Lf factor)) ∧
      (∀ q ∈ Lf factor, 2 ≤ q.1) := by
  have hL : Lf factor = (rle f.toList).map conv := by simp only [Lf, hr]; rfl
  have hz := size_lt f hg 1 n.toNat (le_refl _) (by rw [Nat.mul_one]; exact hp) n.toNat_lt
  have hlen : factor.size ≤ f.size := by
    have := rle_len_le f.toList; rw [← hr] at this; simpa using this
  have hPP : PP (Lf factor) = n.toNat := by rw [hL, PP_runs, unrle_rle]; exact hp
  have hmem : ∀ q ∈ factor.toList, (0 < q.2 ∧ q.2 < 64) ∧ q.1 ∈ f.toList := by
    intro q hq
    rw [hr] at hq
    have hpos := (rle_ok f.toList).1 q hq
    obtain ⟨h1, h2⟩ := mem_runs _ q hq hpos
    rw [unrle_rle] at h1 h2
    simp at h2
    exact ⟨⟨hpos, by omega⟩, h1⟩
  have hne : 0 < factor.size := by
    by_contra h0
    have : factor.toList = [] := List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
    rw [hr, rle_nil_iff] at this
    have : prodL f = 1 := by simp [prodL, this]
    exact hn1 (UInt64.toNat_inj.mp (by rw [← hp, this]; rfl))
  have h2 : ∀ q ∈ Lf factor, 2 ≤ q.1 := by
    intro q hq
    simp only [Lf, List.mem_map] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact (hg x.1 (hmem x hx).2).1
  refine ⟨⟨le_refl _, by omega, fun q hq => (hmem q hq).1, fun q hq => by
      have := (hg q.1 (hmem q hq).2).1; omega, by simp, by simp [hPP]; exact n.toNat_lt⟩,
    by omega, hPP, fun hW => ⟨?_, ?_⟩, h2⟩
  · intro q hq
    simp only [Lf, List.mem_map] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact (hg x.1 (hmem x hx).2).2 hW
  · have hst := runs_strict (rle f.toList) (rle_ok _) (by rw [unrle_rle]; exact hs)
    rw [hL, List.map_map]
    exact hst.imp (fun h => Nat.ne_of_lt h)

theorem log2_le63 (D : Nat) (h : D < 2 ^ 64) : Nat.log2 D ≤ 63 := by
  by_cases hD : D = 0
  · subst hD; simp
  · have := (Nat.log2_lt hD).mpr h; omega

theorem final_div (n : UInt64) (hn1 : n ≠ 1) (factor : Array (UInt64 × Int)) (t0 s1 : Nat)
    (hc : (∃ f : Array UInt64, prodL f = n.toNat ∧ Good f ∧ f.toList.Pairwise (fun a b => a.toNat ≤ b.toNat) ∧
      factor.toList = rle f.toList) ∧ s1 ≤ t0 + 1 + Kc * n.toNat + 800)
    (r : Array UInt64) (s : Nat) (hd : DPost factor ([] : List UInt64).toArray 1 0 s1 r s) :
    DivOK n.toNat (Cpp.sort r) ∧ s + sortCost r.size + (Cpp.sort r).size ≤ t0 + (Kc + 330) * n.toNat + 1000 := by
  obtain ⟨⟨f, hp, hg, hs, hr⟩, hs1⟩ := hc
  obtain ⟨hpre, hz, hPP, hW, h2⟩ := count_facts n hn1 factor f hp hg hs hr
  obtain ⟨hd1, hd2⟩ := hd
  simp only [Array.toList_empty, List.map_nil, List.nil_append, Int.toNat_zero, List.drop_zero] at hd1 hd2
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1] at hd1
  have hperm := sort64_perm r
  have hsz : r.size = (gen (Lf factor) 1).length := by rw [← hd1]; simp
  have hD := prodE_le (Lf factor) h2
  rw [← gen_length (Lf factor) 1, hPP, ← hsz] at hD
  have hne : Lf factor ≠ [] := by
    intro h; have := hpre.2.1
    have hl : (Lf factor).length = factor.size := by simp [Lf]
    rw [h] at hl; simp at hl; omega
  have hcg := costG_le (Lf factor) hne
  rw [← gen_length (Lf factor) 1, ← hsz] at hcg
  have hlen : (Lf factor).length < 64 := by simp [Lf]; exact hz
  have hc1 : costG (Lf factor) ≤ 252 * n.toNat := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 4 (show (Lf factor).length ≤ 63 by omega)) hD
    omega
  have hsc : sortCost r.size ≤ 64 * n.toNat := by
    unfold sortCost
    have := log2_le63 r.size (by have := n.toNat_lt; omega)
    have := Nat.mul_le_mul hD (show Nat.log2 r.size + 1 ≤ 64 by omega)
    omega
  refine ⟨⟨?_, sort64_sorted r, fun w => ⟨?_, ?_⟩⟩, ?_⟩
  · intro x hx
    have hx' : x.toNat ∈ gen (Lf factor) 1 := by rw [← hd1]; exact List.mem_map_of_mem (hperm.mem_iff.mp hx)
    obtain ⟨y, hy, hyd⟩ := gen_mem _ _ _ hx'
    rw [hy, Nat.one_mul, ← hPP]; exact hyd
  · intro d hdv
    have := gen_complete (Lf factor) (hW w) 1 d (by rw [hPP]; exact hdv)
    rw [Nat.one_mul, ← hd1] at this
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp this
    exact ⟨x, hperm.mem_iff.mpr hx, rfl⟩
  · have := gen_nodup (Lf factor) (hW w) 1 (by omega)
    rw [← hd1] at this
    exact (hperm.map _).nodup_iff.mpr this
  · rw [sort64_size]
    unfold Kc at *
    omega

theorem div_one (t0 s : Nat) (hs : s = t0) :
    DivOK (1 : UInt64).toNat (replicate 1 1) ∧ s + 1 + Int.toNat 1 ≤ t0 + (Kc + 330) * (1 : UInt64).toNat + 1000 := by
  have e1 : (1 : UInt64).toNat = 1 := rfl
  have e2 : replicate 1 (1 : UInt64) = Array.replicate 1 1 := rfl
  have e3 : Int.toNat 1 = 1 := rfl
  rw [e1, e2, e3]
  refine ⟨⟨?_, ?_, fun _ => ⟨?_, ?_⟩⟩, ?_⟩
  · intro x hx; simp at hx; subst hx; exact Nat.dvd_refl _
  · simp
  · intro d hd
    have : d = 1 := Nat.dvd_one.mp hd
    exact ⟨1, by simp, by rw [this]; rfl⟩
  · simp
  · subst hs; have : 0 ≤ Kc := Nat.zero_le _; omega

/-- `divisors(n)`: the divisors of `n` in increasing order (`n ≥ 1`). Every element divides `n` and the result is
sorted; under `MRWitnessSet` (the hypothesis of `is_prime`) every divisor occurs exactly once. -/
theorem divisors_spec (n : UInt64) (h1 : 1 ≤ n.toNat) (t0 : Nat) :
    ⦃fun t => ⌜t = t0⌝⦄ cp.divisors n
    ⦃⇓ r t => ⌜DivOK n.toNat r ∧ t ≤ t0 + (Kc + 330) * n.toNat + 1000⌝⦄ := by
  mvcgen [cp.divisors, factorize_count_spec, dfs_top_spec]
  case vc3.hP =>
    rename_i hn r d s h
    obtain ⟨⟨f, hp, hg, hs, hr⟩, -⟩ := h
    exact (count_facts n (of_dec_false hn) r f hp hg hs hr).1
  case vc4.hs =>
    rename_i hn r d s h
    obtain ⟨⟨f, hp, hg, hs, hr⟩, -⟩ := h
    exact (count_facts n (of_dec_false hn) r f hp hg hs hr).2.1
  case vc5.isFalse.post.success.post.success =>
    rename_i s2 hs2 hn fac d s1 hc r s hd dv
    subst hs2
    exact final_div n (of_dec_false hn) fac s2 s1 hc r s hd
  case vc1.isTrue =>
    rename_i s hs hn
    have e := of_dec_true hn
    rw [e]
    exact div_one t0 s hs
  all_goals first | exact ExceptConds.entails_false | simp

end Proofs.Cpp.Factorize
