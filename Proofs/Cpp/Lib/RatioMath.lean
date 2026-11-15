import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

/-! A pure signed-integer model for the original Ratio normalization.
The C++ boundary requires inputs and intermediates, including absolute values
and common denominators, to fit their types. -/

namespace Proofs.Cpp.RatioMath

def normalize (n d : Int) : Int × Int :=
  if n = 0 then (0, 1) else
    let g : Int := Nat.gcd n.natAbs d.natAbs
    if d < 0 then (-n / g, -d / g) else (n / g, d / g)

/-- The normalized fields are the canonical numerator and positive denominator. -/
theorem normalize_eq_canonical (n d : Int) (hd : d ≠ 0) :
    normalize n d = ((Rat.divInt n d).num, ((Rat.divInt n d).den : Int)) := by
  by_cases hn : n = 0
  · simp [normalize, hn]
  by_cases hneg : d < 0
  · have habs : (d.natAbs : Int) = -d := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
    simp [normalize, hn, hneg, Rat.num_divInt, Rat.den_divInt, hd,
      Int.sign_eq_neg_one_of_neg hneg, Int.gcd, Nat.gcd_comm, Int.natCast_ediv, habs]
  · have hpos : 0 < d := by omega
    have habs : (d.natAbs : Int) = d := Int.natAbs_of_nonneg (Int.le_of_lt hpos)
    simp [normalize, hn, hneg, Rat.num_divInt, Rat.den_divInt, hd,
      Int.sign_eq_one_of_pos hpos, Int.gcd, Nat.gcd_comm, Int.natCast_ediv, habs]

theorem normalize_den_pos (n d : Int) (hd : d ≠ 0) :
    0 < (normalize n d).2 := by
  rw [normalize_eq_canonical n d hd]
  have h := (Rat.divInt n d).den_nz
  dsimp
  omega

theorem normalize_coprime (n d : Int) (hd : d ≠ 0) :
    Nat.Coprime (normalize n d).1.natAbs (normalize n d).2.natAbs := by
  rw [normalize_eq_canonical n d hd]
  simpa using (Rat.divInt n d).reduced

theorem normalize_value (n d : Int) (hd : d ≠ 0) :
    Rat.divInt (normalize n d).1 (normalize n d).2 = Rat.divInt n d := by
  rw [normalize_eq_canonical n d hd]
  exact Rat.num_divInt_den _

theorem increment_value (n d : Int) (hd : d ≠ 0) :
    Rat.divInt (n + d) d = Rat.divInt n d + 1 := by
  have hone : Rat.divInt 1 1 = 1 := rfl
  simpa only [Int.mul_one, Int.one_mul, hone] using
    (Rat.divInt_add_divInt n 1 hd (by decide : (1 : Int) ≠ 0)).symm

theorem decrement_value (n d : Int) (hd : d ≠ 0) :
    Rat.divInt (n - d) d = Rat.divInt n d - 1 := by
  have hone : Rat.divInt 1 1 = 1 := rfl
  simpa only [Int.mul_one, Int.one_mul, hone] using
    (Rat.divInt_sub_divInt n 1 hd (by decide : (1 : Int) ≠ 0)).symm

theorem negate_value (n d : Int) (hd : d ≠ 0) :
    Rat.divInt (normalize (-n) d).1 (normalize (-n) d).2 = -Rat.divInt n d := by
  rw [normalize_value (-n) d hd]
  exact (Rat.neg_divInt n d).symm

def add (n d m e : Int) : Int × Int :=
  let l : Int := Int.lcm d e
  normalize (l / d * n + l / e * m) l

def sub (n d m e : Int) : Int × Int :=
  let l : Int := Int.lcm d e
  normalize (l / d * n - l / e * m) l

theorem add_value (n d m e : Int) (hd : d ≠ 0) (he : e ≠ 0) :
    Rat.divInt (add n d m e).1 (add n d m e).2 = Rat.divInt n d + Rat.divInt m e := by
  have hl : (Int.lcm d e : Int) ≠ 0 := by
    exact_mod_cast Int.lcm_ne_zero hd he
  dsimp only [add]
  rw [normalize_value _ _ hl, Rat.divInt_add_divInt n m hd he]
  apply (Rat.divInt_eq_divInt_iff hl (Int.mul_ne_zero hd he)).mpr
  calc
    _ = ((Int.lcm d e : Int) / d * d) * n * e + ((Int.lcm d e : Int) / e * e) * m * d := by ring
    _ = (Int.lcm d e : Int) * n * e + (Int.lcm d e : Int) * m * d := by
      rw [Int.ediv_mul_cancel (Int.dvd_lcm_left d e), Int.ediv_mul_cancel (Int.dvd_lcm_right d e)]
    _ = _ := by ring

theorem sub_value (n d m e : Int) (hd : d ≠ 0) (he : e ≠ 0) :
    Rat.divInt (sub n d m e).1 (sub n d m e).2 = Rat.divInt n d - Rat.divInt m e := by
  have hl : (Int.lcm d e : Int) ≠ 0 := by
    exact_mod_cast Int.lcm_ne_zero hd he
  dsimp only [sub]
  rw [normalize_value _ _ hl, Rat.divInt_sub_divInt n m hd he]
  apply (Rat.divInt_eq_divInt_iff hl (Int.mul_ne_zero hd he)).mpr
  calc
    _ = ((Int.lcm d e : Int) / d * d) * n * e - ((Int.lcm d e : Int) / e * e) * m * d := by ring
    _ = (Int.lcm d e : Int) * n * e - (Int.lcm d e : Int) * m * d := by
      rw [Int.ediv_mul_cancel (Int.dvd_lcm_left d e), Int.ediv_mul_cancel (Int.dvd_lcm_right d e)]
    _ = _ := by ring

/-- The divisions by the gcd are exact, so C++'s truncating division agrees with
mathematical integer division even for a negative numerator. -/
theorem gcd_tdiv_left (n d : Int) :
    n.tdiv (Nat.gcd n.natAbs d.natAbs : Int) = n / (Nat.gcd n.natAbs d.natAbs : Int) := by
  exact Int.tdiv_eq_ediv_of_dvd (Int.gcd_dvd_left n d)

theorem gcd_tdiv_right (n d : Int) :
    d.tdiv (Nat.gcd n.natAbs d.natAbs : Int) = d / (Nat.gcd n.natAbs d.natAbs : Int) := by
  exact Int.tdiv_eq_ediv_of_dvd (Int.gcd_dvd_right n d)

/-- Exact cancellation preserves a nonzero denominator. -/
theorem quotient_ne_zero (d g : Int) (hd : d ≠ 0) (hg : g ∣ d) :
    d / g ≠ 0 := by
  intro h
  have hc := Int.ediv_mul_cancel hg
  rw [h, Int.zero_mul] at hc
  exact hd hc.symm

theorem cancel_value (n d g : Int) (hd : d ≠ 0)
    (hn : g ∣ n) (hgd : g ∣ d) :
    Rat.divInt (n / g) (d / g) = Rat.divInt n d := by
  apply (Rat.divInt_eq_divInt_iff (quotient_ne_zero d g hd hgd) hd).mpr
  calc
    n / g * d = n / g * (d / g * g) := by rw [Int.ediv_mul_cancel hgd]
    _ = (n / g * g) * (d / g) := by ring
    _ = n * (d / g) := by rw [Int.ediv_mul_cancel hn]

def mul (n d m e : Int) : Int × Int :=
  let g : Int := Int.gcd n e
  let h : Int := Int.gcd m d
  (n / g * (m / h), d / h * (e / g))

theorem mul_den_ne_zero (n d m e : Int) (hd : d ≠ 0) (he : e ≠ 0) :
    (mul n d m e).2 ≠ 0 := by
  exact mul_ne_zero
    (quotient_ne_zero d _ hd (Int.gcd_dvd_right m d))
    (quotient_ne_zero e _ he (Int.gcd_dvd_right n e))

theorem mul_value (n d m e : Int) (hd : d ≠ 0) (he : e ≠ 0) :
    Rat.divInt (mul n d m e).1 (mul n d m e).2 =
      Rat.divInt n d * Rat.divInt m e := by
  have h₁ := cancel_value n e (Int.gcd n e) he
    (Int.gcd_dvd_left n e) (Int.gcd_dvd_right n e)
  have h₂ := cancel_value m d (Int.gcd m d) hd
    (Int.gcd_dvd_left m d) (Int.gcd_dvd_right m d)
  calc
    _ = Rat.divInt (n / (Int.gcd n e : Int)) (e / (Int.gcd n e : Int)) *
        Rat.divInt (m / (Int.gcd m d : Int)) (d / (Int.gcd m d : Int)) := by
      rw [Rat.divInt_mul_divInt]
      simp only [mul]
      congr 1
      ring
    _ = Rat.divInt n e * Rat.divInt m d := by rw [h₁, h₂]
    _ = _ := by
      simp only [Rat.divInt_mul_divInt]
      congr 1
      ring

def div (n d m e : Int) : Int × Int :=
  let g : Int := Int.gcd n m
  let h : Int := Int.gcd d e
  normalize (n / g * (e / h)) (d / h * (m / g))

theorem div_eq_canonical (n d m e : Int) (hd : d ≠ 0) (hm : m ≠ 0) :
    div n d m e = ((Rat.divInt n d / Rat.divInt m e).num,
      ((Rat.divInt n d / Rat.divInt m e).den : Int)) := by
  have hden := mul_den_ne_zero n d e m hd hm
  have hg : Int.gcd e d = Int.gcd d e := Int.gcd_comm e d
  dsimp only [div]
  rw [normalize_eq_canonical _ _ (by simpa only [mul, hg] using hden)]
  have hval := mul_value n d e m hd hm
  have hv : Rat.divInt (n / (Int.gcd n m : Int) * (e / (Int.gcd d e : Int)))
      (d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))) =
        Rat.divInt n d / Rat.divInt m e := by
    simpa only [mul, hg, Rat.divInt_mul_divInt, Rat.divInt_div_divInt] using hval
  rw [hv]

theorem div_value (n d m e : Int) (hd : d ≠ 0) (hm : m ≠ 0) :
    Rat.divInt (div n d m e).1 (div n d m e).2 =
      Rat.divInt n d / Rat.divInt m e := by
  have hden := mul_den_ne_zero n d e m hd hm
  have hval := mul_value n d e m hd hm
  have hg : Int.gcd e d = Int.gcd d e := Int.gcd_comm e d
  dsimp only [div]
  rw [normalize_value _ _ (by simpa only [mul, hg] using hden)]
  rw [Rat.divInt_div_divInt]
  simpa only [mul, hg, Rat.divInt_mul_divInt] using hval

/-- Comparison cancels only a positive common denominator factor. -/
theorem compare_le (n d m e : Int) (hd : 0 < d) (he : 0 < e) :
    e / (Int.gcd d e : Int) * n ≤ d / (Int.gcd d e : Int) * m ↔
      Rat.divInt n d ≤ Rat.divInt m e := by
  have hg : (0 : Int) < (Int.gcd d e : Int) := by
    exact_mod_cast Int.gcd_pos_of_ne_zero_right d (Int.ne_of_gt he)
  rw [← Int.mul_le_mul_right hg, Rat.divInt_le_divInt hd he]
  have h₁ : e / (Int.gcd d e : Int) * n * (Int.gcd d e : Int) = n * e := by
    calc
      _ = n * (e / (Int.gcd d e : Int) * (Int.gcd d e : Int)) := by ring
      _ = _ := by rw [Int.ediv_mul_cancel (Int.gcd_dvd_right d e)]
  have h₂ : d / (Int.gcd d e : Int) * m * (Int.gcd d e : Int) = m * d := by
    calc
      _ = m * (d / (Int.gcd d e : Int) * (Int.gcd d e : Int)) := by ring
      _ = _ := by rw [Int.ediv_mul_cancel (Int.gcd_dvd_left d e)]
  rw [h₁, h₂]

theorem compare_lt (n d m e : Int) (hd : 0 < d) (he : 0 < e) :
    e / (Int.gcd d e : Int) * n < d / (Int.gcd d e : Int) * m ↔
      Rat.divInt n d < Rat.divInt m e := by
  rw [← not_le, ← not_le, ← compare_le m e n d he hd]
  rw [Int.gcd_comm e d]

theorem normalize_eq_iff (n d m e : Int) (hd : d ≠ 0) (he : e ≠ 0) :
    normalize n d = normalize m e ↔ Rat.divInt n d = Rat.divInt m e := by
  constructor
  · intro h
    have hv := congrArg (fun p : Int × Int => Rat.divInt p.1 p.2) h
    simpa only [normalize_value n d hd, normalize_value m e he] using hv
  · intro h
    rw [normalize_eq_canonical n d hd, normalize_eq_canonical m e he, h]

/-- Positive denominator and reduced numerator/denominator. Raw stream input
need not satisfy this predicate. -/
def Canonical (n d : Int) : Prop := 0 < d ∧ Int.gcd n d = 1

theorem normalize_canonical (n d : Int) (hd : d ≠ 0) :
    Canonical (normalize n d).1 (normalize n d).2 := by
  refine ⟨normalize_den_pos n d hd, ?_⟩
  exact normalize_coprime n d hd

theorem canonical_fields (n d : Int) (h : Canonical n d) :
    ((Rat.divInt n d).num, ((Rat.divInt n d).den : Int)) = (n, d) := by
  have hg : Int.gcd d n = 1 := by rw [Int.gcd_comm]; exact h.2
  have hd : d ≠ 0 := Int.ne_of_gt h.1
  simp [Rat.num_divInt, Rat.den_divInt, hg, hd, Int.sign_eq_one_of_pos h.1,
    Int.natAbs_of_nonneg (Int.le_of_lt h.1)]

theorem normalize_fixed (n d : Int) (h : Canonical n d) :
    normalize n d = (n, d) := by
  rw [normalize_eq_canonical n d (Int.ne_of_gt h.1)]
  exact canonical_fields n d h

theorem increment_canonical (n d : Int) (h : Canonical n d) :
    Canonical (n + d) d := by
  exact ⟨h.1, by rw [Int.gcd_add_self_left]; exact h.2⟩

theorem decrement_canonical (n d : Int) (h : Canonical n d) :
    Canonical (n - d) d := by
  exact ⟨h.1, by rw [Int.gcd_sub_self_left]; exact h.2⟩

theorem add_canonical (n d m e : Int) (hd : d ≠ 0) (he : e ≠ 0) :
    Canonical (add n d m e).1 (add n d m e).2 := by
  apply normalize_canonical
  exact_mod_cast Int.lcm_ne_zero hd he

theorem sub_canonical (n d m e : Int) (hd : d ≠ 0) (he : e ≠ 0) :
    Canonical (sub n d m e).1 (sub n d m e).2 := by
  apply normalize_canonical
  exact_mod_cast Int.lcm_ne_zero hd he

theorem div_canonical (n d m e : Int) (hd : d ≠ 0) (hm : m ≠ 0) :
    Canonical (div n d m e).1 (div n d m e).2 := by
  apply normalize_canonical
  have hden := mul_den_ne_zero n d e m hd hm
  simpa only [mul, Int.gcd_comm e d] using hden

theorem mul_rat_fields (q r : Rat) :
    mul q.num (q.den : Int) r.num (r.den : Int) = ((q * r).num, ((q * r).den : Int)) := by
  change mul q.num (q.den : Int) r.num (r.den : Int) =
    ((Rat.mul q r).num, ((Rat.mul q r).den : Int))
  unfold Rat.mul
  simp only [mul, Int.gcd, Int.natAbs_natCast, Int.divExact_eq_tdiv,
    Nat.divExact_eq_div, Int.natCast_mul, Int.natCast_ediv]
  have hq := gcd_tdiv_left q.num (r.den : Int)
  have hr := gcd_tdiv_left r.num (q.den : Int)
  simp only [Int.natAbs_natCast] at hq hr
  rw [hq, hr]

theorem mul_eq_canonical (n d m e : Int) (ha : Canonical n d) (hb : Canonical m e) :
    mul n d m e = ((Rat.divInt n d * Rat.divInt m e).num,
      ((Rat.divInt n d * Rat.divInt m e).den : Int)) := by
  have hna := congrArg Prod.fst (canonical_fields n d ha)
  have hda := congrArg Prod.snd (canonical_fields n d ha)
  have hnb := congrArg Prod.fst (canonical_fields m e hb)
  have hdb := congrArg Prod.snd (canonical_fields m e hb)
  dsimp only at hna hda hnb hdb
  have h := mul_rat_fields (Rat.divInt n d) (Rat.divInt m e)
  simpa only [hna, hda, hnb, hdb] using h

theorem mul_canonical (n d m e : Int) (ha : Canonical n d) (hb : Canonical m e) :
    Canonical (mul n d m e).1 (mul n d m e).2 := by
  rw [mul_eq_canonical n d m e ha hb]
  refine ⟨?_, ?_⟩
  · change (0 : Int) < ((Rat.divInt n d * Rat.divInt m e).den : Int)
    exact_mod_cast (Rat.divInt n d * Rat.divInt m e).den_pos
  · exact (Rat.divInt n d * Rat.divInt m e).reduced

/-- LCM-based common denominator scaling is exact with either division convention. -/
theorem lcm_tdiv_left (d e : Int) :
    (Int.lcm d e : Int).tdiv d = (Int.lcm d e : Int) / d := by
  exact Int.tdiv_eq_ediv_of_dvd (Int.dvd_lcm_left d e)

theorem lcm_tdiv_right (d e : Int) :
    (Int.lcm d e : Int).tdiv e = (Int.lcm d e : Int) / e := by
  exact Int.tdiv_eq_ediv_of_dvd (Int.dvd_lcm_right d e)

theorem lcm_magnitude_formula (a b : Int) :
    (a.natAbs : Int) / (Int.gcd a b : Int) * (b.natAbs : Int) = (Int.lcm a b : Int) := by
  rw [Int.gcd, Int.lcm_def, ← Int.natCast_ediv, ← Int.natCast_mul]
  congr 1
  exact Nat.div_mul_right_comm (Nat.gcd_dvd_left a.natAbs b.natAbs) b.natAbs

/-- Unsigned normalization embedded into the signed mathematical model. -/
theorem normalize_nat_pair (n d : Nat) :
    normalize (n : Int) (d : Int) =
      let p : Nat × Nat := if n = 0 then (0, 1) else
        (n / Nat.gcd n d, d / Nat.gcd n d)
      ((p.1 : Int), (p.2 : Int)) := by
  by_cases hn : n = 0
  · simp [normalize, hn]
  · simp [normalize, hn, Int.natCast_ediv]

theorem lcm_nat_formula (a b : Nat) :
    a / Nat.gcd a b * b = Nat.lcm a b := by
  exact Nat.div_mul_right_comm (Nat.gcd_dvd_left a b) b

theorem mul_nat_pair (n d m e : Nat) :
    mul (n : Int) (d : Int) (m : Int) (e : Int) =
      (((n / Nat.gcd n e * (m / Nat.gcd m d) : Nat) : Int),
       ((d / Nat.gcd m d * (e / Nat.gcd n e) : Nat) : Int)) := by
  simp only [mul, Int.gcd, Int.natAbs_natCast, Int.natCast_mul, Int.natCast_ediv]

theorem div_nat_pair (n d m e : Nat) :
    div (n : Int) (d : Int) (m : Int) (e : Int) =
      normalize ((n / Nat.gcd n m * (e / Nat.gcd d e) : Nat) : Int)
        ((d / Nat.gcd d e * (m / Nat.gcd n m) : Nat) : Int) := by
  simp only [div, Int.gcd, Int.natAbs_natCast, Int.natCast_mul, Int.natCast_ediv]

theorem add_nat_pair (n d m e : Nat) :
    add (n : Int) (d : Int) (m : Int) (e : Int) =
      normalize ((Nat.lcm d e / d * n + Nat.lcm d e / e * m : Nat) : Int) (Nat.lcm d e : Int) := by
  simp only [add, Int.lcm_def, Int.natAbs_natCast, Int.natCast_add, Int.natCast_mul, Int.natCast_ediv]

theorem sub_nat_pair (n d m e : Nat)
    (h : Nat.lcm d e / e * m ≤ Nat.lcm d e / d * n) :
    sub (n : Int) (d : Int) (m : Int) (e : Int) =
      normalize ((Nat.lcm d e / d * n - Nat.lcm d e / e * m : Nat) : Int) (Nat.lcm d e : Int) := by
  simp only [sub, Int.lcm_def, Int.natAbs_natCast, Int.natCast_sub h,
    Int.natCast_mul, Int.natCast_ediv]

theorem compare_nat_lt (n d m e : Nat) (hd : 0 < d) (he : 0 < e) :
    e / Nat.gcd d e * n < d / Nat.gcd d e * m ↔
      Rat.divInt (n : Int) (d : Int) < Rat.divInt (m : Int) (e : Int) := by
  have h := compare_lt (n : Int) (d : Int) (m : Int) (e : Int) (by omega) (by omega)
  simpa only [Int.gcd, Int.natAbs_natCast, ← Int.natCast_ediv, ← Int.natCast_mul,
    Int.ofNat_lt] using h

end Proofs.Cpp.RatioMath
