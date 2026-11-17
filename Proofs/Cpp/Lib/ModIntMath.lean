import Proofs.Cpp.Prelude
import Proofs.Fermat
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring

namespace Proofs.Cpp.ModIntMath

/-- Signed powers over a prime residue ring: negative exponents use the
Fermat inverse of the positive absolute power. -/
def signedPowerResidue (m x : Nat) (n : Int) : Nat :=
  if n < 0 then (x ^ n.natAbs % m) ^ (m - 2) % m else x ^ n.toNat % m

theorem inverse_residue_unit (m x : Nat) (hp : Proofs.Fermat.IsPrime m)
    (hx0 : 0 < x) (hx : x < m) : x * (x ^ (m - 2) % m) % m = 1 :=
  Proofs.Fermat.inv_mul_eq_one m x hp hx0 hx

theorem quotient_residue_unit (m x y : Nat) (hp : Proofs.Fermat.IsPrime m)
    (hx : x < m) (hy0 : 0 < y) (hy : y < m) :
    (x * (y ^ (m - 2) % m) % m) * y % m = x := by
  have h := inverse_residue_unit m y hp hy0 hy
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  have e : x * (y ^ (m - 2) % m) * y = x * (y * (y ^ (m - 2) % m)) := by
    rw [Nat.mul_assoc, Nat.mul_comm (y ^ (m - 2) % m) y]
  rw [e, Nat.mul_mod, h]
  simp [Nat.mod_eq_of_lt hx]

theorem power_residue_nonzero (m x exponent : Nat) (hp : Proofs.Fermat.IsPrime m)
    (hx0 : 0 < x) (hx : x < m) : x ^ exponent % m ≠ 0 := by
  have hc := Nat.Coprime.pow_left exponent (Proofs.Fermat.coprime_of_lt m x hp hx0 hx)
  intro hz
  have hg := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hz)
  change Nat.gcd (x ^ exponent) m = 1 at hc
  rw [hg] at hc
  have hm := hp.1
  omega

theorem bool_remainder (tag : String) (x : Bool) (m : UInt32) :
    (ModToUInt32.apply (tag := tag) x m).toNat = (if x then 1 else 0) % m.toNat := by
  cases x <;> simp [ModToUInt32.apply, UInt32.toNat_mod]

theorem u32_remainder (tag : String) (x m : UInt32) :
    (ModToUInt32.apply (tag := tag) x m).toNat = x.toNat % m.toNat := by
  exact UInt32.toNat_mod x m

theorem u64_remainder (tag : String) (x : UInt64) (m : UInt32) (hm : 0 < m.toNat) :
    (ModToUInt32.apply (tag := tag) x m).toNat = x.toNat % m.toNat := by
  change ((x % m.toUInt64).toUInt32).toNat = _
  rw [UInt64.toNat_toUInt32, UInt64.toNat_mod, UInt32.toNat_toUInt64]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ hm) (UInt32.toNat_lt m))

theorem u32_ofInt_toNat (x : Int) (h0 : 0 ≤ x) (h1 : x < 4294967296) :
    (UInt32.ofInt x).toNat = x.toNat := by
  simp only [UInt32.ofInt, UInt32.toNat_ofNat']
  rw [Int.emod_eq_of_lt h0 (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Wide unsigned bindings include the entire unsigned 128-bit input range;
the residue alone, rather than the original input, must fit UInt32. -/
theorem wide_integer_remainder (tag : String) (x : Int) (m : UInt32)
    (hx : 0 ≤ x) (hm : 0 < m.toNat) :
    ((intModToUInt32 tag false).apply x m).toNat = x.toNat % m.toNat := by
  change (UInt32.ofInt (x.tmod m.toNat)).toNat = _
  rw [Int.tmod_eq_emod_of_nonneg hx]
  have h0 := Int.emod_nonneg x (by omega : (m.toNat : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos x (by omega : (0 : Int) < m.toNat)
  rw [u32_ofInt_toNat _ h0 (by have := UInt32.toNat_lt m; omega),
      Int.toNat_emod hx (by omega)]
  simp only [Int.toNat_natCast]

theorem narrow_unsigned_remainder (tag : String) (x : Int) (m : UInt32)
    (hx : 0 ≤ x) (hx32 : x < 4294967296) (hm : 0 < m.toNat) :
    ((intModToUInt32 tag true).apply x m).toNat = x.toNat % m.toNat := by
  change (UInt32.ofInt ((((UInt32.ofInt x).toNat : Int)).tmod m.toNat)).toNat = _
  rw [u32_ofInt_toNat x hx hx32, Int.toNat_of_nonneg hx]
  exact wide_integer_remainder tag x m hx hm

def signedNormalize (x m : Int) : Int := Int.tmod (Int.tmod x m + m) m

theorem signed_intermediate (x m : Int) (hm : 0 < m) :
    0 ≤ Int.tmod x m + m ∧ Int.tmod x m + m < 2 * m := by
  have h0 := Int.emod_nonneg x (by omega : m ≠ 0)
  have h1 := Int.emod_lt_of_pos x hm
  have habs : (m.natAbs : Int) = m := by omega
  rw [Int.tmod_eq_emod]
  by_cases h : 0 ≤ x ∨ m ∣ x <;> simp only [h, ite_true, ite_false, habs] <;> omega

theorem signed_normalize_eq (x m : Int) (hm : 0 < m) :
    signedNormalize x m = x % m := by
  have h0 := (signed_intermediate x m hm).1
  have habs : (m.natAbs : Int) = m := by omega
  unfold signedNormalize
  rw [Int.tmod_eq_emod_of_nonneg h0, Int.tmod_eq_emod]
  by_cases h : 0 ≤ x ∨ m ∣ x <;> simp [h, habs]

def reduceOnce (m n : Nat) : Nat := if m ≤ n then n - m else n

theorem reduce_once_eq_mod (m n : Nat) (hn : n < 2 * m) :
    reduceOnce m n = n % m := by
  unfold reduceOnce
  split
  · rename_i h
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

def addWide (m x y : Nat) : Nat := reduceOnce m (x + y)
def subWide (m x y : Nat) : Nat := reduceOnce m (x + m - y)

theorem add_correct (m x y : Nat) (hx : x < m) (hy : y < m) :
    addWide m x y = (x + y) % m := by
  exact reduce_once_eq_mod m (x + y) (by omega)

theorem sub_correct (m x y : Nat) (hx : x < m) (hy : y < m) :
    subWide m x y = (x + m - y) % m := by
  exact reduce_once_eq_mod m (x + m - y) (by omega)

theorem add_bounds (m x y : Nat) (hx : x < m) (hy : y < m) :
    addWide m x y < m := by
  unfold addWide reduceOnce
  split <;> omega

theorem sub_bounds (m x y : Nat) (hx : x < m) (_hy : y < m) :
    subWide m x y < m := by
  unfold subWide reduceOnce
  split <;> omega

theorem sub_residue_relation (m x y : Nat) (hx : x < m) (hy : y < m) :
    subWide m x y + y = x ∨ subWide m x y + y = x + m := by
  unfold subWide reduceOnce
  split <;> omega

theorem wide_values_fit (m x y : Nat) (hm : m < 4294967296)
    (hx : x < m) (hy : y < m) :
    x + y < 18446744073709551616 ∧ x + m < 18446744073709551616 ∧ y ≤ x + m := by
  omega

def reduceWord32 (m : UInt32) (z : UInt64) : UInt32 :=
  (if decide (z ≥ m.toUInt64) then z - m.toUInt64 else z).toUInt32

def addWord32 (m x y : UInt32) : UInt32 :=
  reduceWord32 m (x.toUInt64 + y.toUInt64)

def subWord32 (m x y : UInt32) : UInt32 :=
  reduceWord32 m (x.toUInt64 + m.toUInt64 - y.toUInt64)

def mulWord32 (m x y : UInt32) : UInt32 :=
  ((x.toUInt64 * y.toUInt64) % m.toUInt64).toUInt32

def incrementWord32 (m x : UInt32) : UInt32 :=
  if decide (x = m - 1) then 0 else x + 1

def decrementWord32 (m x : UInt32) : UInt32 :=
  if decide (x = 0) then m - 1 else x - 1

def negateWord32 (m x : UInt32) : UInt32 := (m - x) % m

theorem reduceWord32_toNat (m : UInt32) (z : UInt64) (hz : z.toNat < 2 * m.toNat) :
    (reduceWord32 m z).toNat = reduceOnce m.toNat z.toNat := by
  have hm := UInt32.toNat_lt m
  by_cases h : m.toUInt64 ≤ z
  · have hn : m.toNat ≤ z.toNat := by simpa using UInt64.le_iff_toNat_le.mp h
    simp only [reduceWord32, h, decide_true, ↓reduceIte, reduceOnce, hn]
    rw [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le _ _ h, UInt32.toNat_toUInt64]
    exact Nat.mod_eq_of_lt (by omega)
  · have hn : ¬m.toNat ≤ z.toNat := by simpa using (not_congr UInt64.le_iff_toNat_le).mp h
    simp only [reduceWord32, h, decide_false, Bool.false_eq_true, ↓reduceIte, reduceOnce, hn]
    rw [UInt64.toNat_toUInt32]
    exact Nat.mod_eq_of_lt (by omega)

theorem addWord32_toNat (m x y : UInt32) (hx : x.toNat < m.toNat) (hy : y.toNat < m.toNat) :
    (addWord32 m x y).toNat = (x.toNat + y.toNat) % m.toNat := by
  have hm := UInt32.toNat_lt m
  have hz : (x.toUInt64 + y.toUInt64).toNat = x.toNat + y.toNat := by
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
        Nat.mod_eq_of_lt (by omega)]
  unfold addWord32
  rw [reduceWord32_toNat m _ (by rw [hz]; omega), hz]
  exact add_correct m.toNat x.toNat y.toNat hx hy

theorem subWord32_toNat (m x y : UInt32) (hx : x.toNat < m.toNat) (hy : y.toNat < m.toNat) :
    (subWord32 m x y).toNat = (x.toNat + m.toNat - y.toNat) % m.toNat := by
  have hm := UInt32.toNat_lt m
  have hs : (x.toUInt64 + m.toUInt64).toNat = x.toNat + m.toNat := by
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
        Nat.mod_eq_of_lt (by omega)]
  have hle : y.toUInt64 ≤ x.toUInt64 + m.toUInt64 := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [UInt32.toNat_toUInt64, hs]
    omega
  have hz : (x.toUInt64 + m.toUInt64 - y.toUInt64).toNat = x.toNat + m.toNat - y.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hle, hs, UInt32.toNat_toUInt64]
  unfold subWord32
  rw [reduceWord32_toNat m _ (by rw [hz]; omega), hz]
  exact sub_correct m.toNat x.toNat y.toNat hx hy

theorem mulWord32_toNat (m x y : UInt32) (hm : 0 < m.toNat) :
    (mulWord32 m x y).toNat = x.toNat * y.toNat % m.toNat := by
  have hx := UInt32.toNat_lt x
  have hy := UInt32.toNat_lt y
  have hp : x.toNat * y.toNat < 2 ^ 64 := by
    have h := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by decide : 0 < 2 ^ 32)
    exact h
  unfold mulWord32
  rw [UInt64.toNat_toUInt32, UInt64.toNat_mod, UInt64.toNat_mul,
      UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
      Nat.mod_eq_of_lt hp]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ hm) (UInt32.toNat_lt m))

theorem incrementWord32_toNat (m x : UInt32) (hx : x.toNat < m.toNat) :
    (incrementWord32 m x).toNat = (x.toNat + 1) % m.toNat := by
  have hm := UInt32.toNat_lt m
  have hm1 : (m - 1).toNat = m.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]
  unfold incrementWord32
  split
  · rename_i h
    have he : x = m - 1 := of_decide_eq_true h
    have hs : x.toNat + 1 = m.toNat := by rw [he, hm1]; omega
    simp only [UInt32.toNat_zero, hs, Nat.mod_self]
  · rename_i h
    have he : x ≠ m - 1 := by simpa using h
    have hn : x.toNat ≠ m.toNat - 1 := by
      intro hn
      apply he
      apply UInt32.toNat_inj.mp
      rw [hm1]
      exact hn
    rw [UInt32.toNat_add, UInt32.toNat_one,
        Nat.mod_eq_of_lt (by omega : x.toNat + 1 < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : x.toNat + 1 < m.toNat)]

theorem decrementWord32_toNat (m x : UInt32) (hx : x.toNat < m.toNat) :
    (decrementWord32 m x).toNat = (x.toNat + m.toNat - 1) % m.toNat := by
  have hm1 : (m - 1).toNat = m.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]
  unfold decrementWord32
  split
  · rename_i h
    have he : x = 0 := of_decide_eq_true h
    rw [hm1, he, UInt32.toNat_zero, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  · rename_i h
    have he : x ≠ 0 := by simpa using h
    have hn : 0 < x.toNat := by
      by_contra hn
      apply he
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_zero]
      omega
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]
    rw [show x.toNat + m.toNat - 1 = (x.toNat - 1) + m.toNat by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem negateWord32_toNat (m x : UInt32) (hx : x.toNat < m.toNat) :
    (negateWord32 m x).toNat = (m.toNat - x.toNat) % m.toNat := by
  unfold negateWord32
  rw [UInt32.toNat_mod, UInt32.toNat_sub_of_le _ _
    (UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt hx))]

theorem negateWord32_add (m x : UInt32) (hx : x.toNat < m.toNat) :
    (negateWord32 m x).toNat + x.toNat = 0 ∨
    (negateWord32 m x).toNat + x.toNat = m.toNat := by
  rw [negateWord32_toNat m x hx]
  by_cases h0 : x.toNat = 0
  · left
    simp only [h0, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
  · right
    rw [Nat.mod_eq_of_lt (by omega : m.toNat - x.toNat < m.toNat)]
    omega

/-- A fixed envelope for scalar arithmetic: modulus, two operands, one wide
intermediate and the returned/updated result. These are model data cells;
object lifetime, heap allocation and Lean's execution stack are not measured. -/
structure ArithmeticFrame where
  modulus : UInt32
  left : UInt32
  right : UInt32
  intermediate : UInt64
  result : UInt32

def ArithmeticFrame.word32s (frame : ArithmeticFrame) : List UInt32 :=
  [frame.modulus, frame.left, frame.right, frame.result, frame.result]

def ArithmeticFrame.bits (frame : ArithmeticFrame) : Nat :=
  32 * frame.word32s.length + 64

theorem arithmetic_frame_bits (frame : ArithmeticFrame) : frame.bits = 224 := by
  rfl

theorem arithmetic_peak_bits (frame : ArithmeticFrame) (calleeBits : Nat) (hc : calleeBits ≤ 224) :
    frame.bits + calleeBits ≤ 448 := by
  rw [arithmetic_frame_bits]
  omega

theorem negative_exponent_magnitude (n : Int) (hn : n < 0) :
    (-(n + 1)).toNat + 1 = n.natAbs := by
  omega

theorem negative_exponent_step_fits (n : Int)
    (hn : -9223372036854775808 ≤ n) (hneg : n < 0) :
    0 ≤ -(n + 1) ∧ -(n + 1) ≤ 9223372036854775807 := by
  omega

theorem signed_values_fit (x m : Int) (hm : 0 < m) (hwidth : m < 4294967296) :
    0 ≤ Int.tmod x m + m ∧ Int.tmod x m + m < 9223372036854775808 := by
  have h := signed_intermediate x m hm
  omega

theorem negative_power_algebra {T : Type} [DivisionMonoid T] (a : T) (k : Nat) :
    (a ^ k * a)⁻¹ = (a⁻¹) ^ (k + 1) := by
  rw [← pow_succ, inv_pow]

theorem negative_power_inverse_valid {T : Type} [GroupWithZero T]
    (a : T) (ha : a ≠ 0) (k : Nat) : a ^ k * a ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero k ha) ha

theorem negative_magnitude_word (n : Int) (hmin : -9223372036854775808 ≤ n) (hneg : n < 0) :
    (UInt64.ofInt (-(n + 1)) + 1).toNat = n.natAbs := by
  have hk0 : 0 ≤ -(n + 1) := by omega
  have hk1 : -(n + 1) < (2 : Int)^64 := by omega
  have hcast : (UInt64.ofInt (-(n + 1))).toNat = (-(n + 1)).toNat := by
    simp only [UInt64.ofInt, UInt64.toNat_ofNat']
    rw [Int.emod_eq_of_lt hk0 hk1, Nat.mod_eq_of_lt (by omega)]
  rw [UInt64.toNat_add, hcast]
  change ((-(n + 1)).toNat + 1) % 18446744073709551616 = n.natAbs
  rw [Nat.mod_eq_of_lt (by omega)]
  exact negative_exponent_magnitude n hneg

theorem negative_residue_successor (base exponent modulus : Nat) :
    (base ^ exponent % modulus * base) % modulus = base ^ (exponent + 1) % modulus := by
  rw [Nat.mod_mul_mod, pow_succ]


end Proofs.Cpp.ModIntMath
