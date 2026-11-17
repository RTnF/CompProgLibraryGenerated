import Proofs.Cpp.Gen.Modint
import Proofs.Cpp.PowMod
import Proofs.Cpp.Lib.ModIntFactorial

-- Appended to a fresh translation of the canonical original class.
open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ModIntConstructorModel

variable (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]

section Unsigned
variable {U : Type} [TypeTraits "U" U] [ModToUInt32 "U" U]
  [TemplateConstraint ((TypeTraits.isSigned (tag := "U") (α := U) ||
    TypeTraits.isCvInt128 (tag := "U") (α := U)) = false)]

theorem unsigned_ctor_run (x : U) (start : Nat) :
    (cp.ModInt.init_U (m := m) x).run start =
      some ((⟨ModToUInt32.apply (tag := "U") x m⟩ : cp.ModInt m), start + 1) := by
  rfl

theorem unsigned_set_run (previous : cp.ModInt m) (x : U) (start : Nat) :
    (cp.ModInt.set__U previous x).run start =
      some ((⟨ModToUInt32.apply (tag := "U") x m⟩ : cp.ModInt m), start + 1) := by
  rfl

theorem unsigned_ctor_correct (x : U) (value start : Nat) (hm : 0 < m.toNat)
    (hvalue : (ModToUInt32.apply (tag := "U") x m).toNat = value % m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.init_U (m := m) x).run start = some (result, start + 1) ∧
      result.x.toNat = value % m.toNat ∧ result.x.toNat < m.toNat := by
  exact ⟨⟨ModToUInt32.apply (tag := "U") x m⟩, unsigned_ctor_run m x start,
    hvalue, hvalue ▸ Nat.mod_lt value hm⟩

theorem unsigned_set_correct (previous : cp.ModInt m) (x : U) (value start : Nat)
    (hm : 0 < m.toNat)
    (hvalue : (ModToUInt32.apply (tag := "U") x m).toNat = value % m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.set__U previous x).run start = some (result, start + 1) ∧
      result.x.toNat = value % m.toNat ∧ result.x.toNat < m.toNat := by
  exact ⟨⟨ModToUInt32.apply (tag := "U") x m⟩, unsigned_set_run m previous x start,
    hvalue, hvalue ▸ Nat.mod_lt value hm⟩
end Unsigned

section Signed
local instance : Mod Int := ⟨Int.tmod⟩
variable [TypeTraits "T" Int]
  [TemplateConstraint ((TypeTraits.isSigned (tag := "T") (α := Int) ||
    TypeTraits.isCvInt128 (tag := "T") (α := Int)) = true)]

theorem signed_ctor_run (x : Int) (start : Nat) :
    (cp.ModInt.init_T (m := m) x).run start = some
      ((⟨UInt32.ofInt (ModIntMath.signedNormalize x m.toNat)⟩ : cp.ModInt m), start + 1) := by
  rfl

theorem signed_set_run (previous : cp.ModInt m) (x : Int) (start : Nat) :
    (cp.ModInt.set__T previous x).run start = some
      ((⟨UInt32.ofInt (ModIntMath.signedNormalize x m.toNat)⟩ : cp.ModInt m), start + 1) := by
  rfl

theorem signed_value (x : Int) (hm : 0 < m.toNat) :
    (UInt32.ofInt (ModIntMath.signedNormalize x m.toNat)).toNat =
      (Int.emod x m.toNat).toNat ∧
    (UInt32.ofInt (ModIntMath.signedNormalize x m.toNat)).toNat < m.toNat := by
  rw [ModIntMath.signed_normalize_eq x m.toNat (by omega)]
  have h0 := Int.emod_nonneg x (by omega : (m.toNat : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos x (by omega : (0 : Int) < m.toNat)
  rw [ModIntMath.u32_ofInt_toNat _ h0 (by have := UInt32.toNat_lt m; omega)]
  exact ⟨rfl, by omega⟩

theorem signed_ctor_correct (x : Int) (start : Nat) (hm : 0 < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.init_T (m := m) x).run start = some (result, start + 1) ∧
      result.x.toNat = (Int.emod x m.toNat).toNat ∧ result.x.toNat < m.toNat := by
  exact ⟨⟨UInt32.ofInt (ModIntMath.signedNormalize x m.toNat)⟩,
    signed_ctor_run m x start, signed_value m x hm⟩

theorem signed_set_correct (previous : cp.ModInt m) (x : Int) (start : Nat) (hm : 0 < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.set__T previous x).run start = some (result, start + 1) ∧
      result.x.toNat = (Int.emod x m.toNat).toNat ∧ result.x.toNat < m.toNat := by
  exact ⟨⟨UInt32.ofInt (ModIntMath.signedNormalize x m.toNat)⟩,
    signed_set_run m previous x start, signed_value m x hm⟩
end Signed

theorem result_word_bound (result : cp.ModInt m) : result.x.toNat < 2 ^ 32 := by
  exact UInt32.toNat_lt result.x

theorem default_ctor_run (start : Nat) :
    (cp.ModInt.init_0 (m := m)).run start =
      some ((⟨0⟩ : cp.ModInt m), start + 1) := by
  rfl

theorem get_run (value : cp.ModInt m) (start : Nat) :
    (cp.ModInt.get_ value).run start = some (value.x, start + 1) := by
  rfl

theorem modulus_run (start : Nat) :
    (cp.ModInt.mod (m := m)).run start = some (m, start + 1) := by
  rfl

theorem unary_plus_run (value : cp.ModInt m) (start : Nat) :
    (cp.ModInt.op_add value).run start = some (value, start + 1) := by
  rfl

end Proofs.Cpp.ModIntConstructorModel
-- Checked against a fresh translation of the canonical original class.
open Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.ModIntMath

namespace Proofs.Cpp.ModIntArithmeticModel

variable (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]

theorem add_assign_run (a b : cp.ModInt m) (start : Nat) :
    (cp.ModInt.op_add_assign a b).run start = some
      (((⟨addWord32 m a.x b.x⟩ : cp.ModInt m), ⟨addWord32 m a.x b.x⟩), start + 1) := by
  rfl

theorem sub_assign_run (a b : cp.ModInt m) (start : Nat) :
    (cp.ModInt.op_sub_assign a b).run start = some
      (((⟨subWord32 m a.x b.x⟩ : cp.ModInt m), ⟨subWord32 m a.x b.x⟩), start + 1) := by
  rfl

theorem mul_assign_run (a b : cp.ModInt m) (start : Nat) :
    (cp.ModInt.op_mul_assign a b).run start = some
      (((⟨mulWord32 m a.x b.x⟩ : cp.ModInt m), ⟨mulWord32 m a.x b.x⟩), start + 1) := by
  rfl

theorem add_assign_correct (a b : cp.ModInt m) (start : Nat)
    (ha : a.x.toNat < m.toNat) (hb : b.x.toNat < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_add_assign a b).run start = some ((result, result), start + 1) ∧
      result.x.toNat = (a.x.toNat + b.x.toNat) % m.toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨addWord32 m a.x b.x⟩, add_assign_run m a b start, addWord32_toNat m a.x b.x ha hb, ?_⟩
  rw [addWord32_toNat m a.x b.x ha hb]
  exact Nat.mod_lt _ (by omega)

theorem sub_assign_correct (a b : cp.ModInt m) (start : Nat)
    (ha : a.x.toNat < m.toNat) (hb : b.x.toNat < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_sub_assign a b).run start = some ((result, result), start + 1) ∧
      result.x.toNat = (a.x.toNat + m.toNat - b.x.toNat) % m.toNat ∧
      result.x.toNat < m.toNat := by
  refine ⟨⟨subWord32 m a.x b.x⟩, sub_assign_run m a b start, subWord32_toNat m a.x b.x ha hb, ?_⟩
  rw [subWord32_toNat m a.x b.x ha hb]
  exact Nat.mod_lt _ (by omega)

theorem mul_assign_correct (a b : cp.ModInt m) (start : Nat)
    (hm : 0 < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_mul_assign a b).run start = some ((result, result), start + 1) ∧
      result.x.toNat = a.x.toNat * b.x.toNat % m.toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨mulWord32 m a.x b.x⟩, mul_assign_run m a b start, mulWord32_toNat m a.x b.x hm, ?_⟩
  rw [mulWord32_toNat m a.x b.x hm]
  exact Nat.mod_lt _ hm

theorem add_run (a b : cp.ModInt m) (start : Nat) :
    (cp.op_add_ModInt_ModInt a b).run start =
      some ((⟨addWord32 m a.x b.x⟩ : cp.ModInt m), start + 2) := by
  rfl

theorem sub_run (a b : cp.ModInt m) (start : Nat) :
    (cp.op_sub_ModInt_ModInt a b).run start =
      some ((⟨subWord32 m a.x b.x⟩ : cp.ModInt m), start + 2) := by
  rfl

theorem mul_run (a b : cp.ModInt m) (start : Nat) :
    (cp.op_mul_ModInt_ModInt a b).run start =
      some ((⟨mulWord32 m a.x b.x⟩ : cp.ModInt m), start + 2) := by
  rfl

theorem add_correct (a b : cp.ModInt m) (start : Nat)
    (ha : a.x.toNat < m.toNat) (hb : b.x.toNat < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.op_add_ModInt_ModInt a b).run start = some (result, start + 2) ∧
      result.x.toNat = (a.x.toNat + b.x.toNat) % m.toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨addWord32 m a.x b.x⟩, add_run m a b start, addWord32_toNat m a.x b.x ha hb, ?_⟩
  rw [addWord32_toNat m a.x b.x ha hb]
  exact Nat.mod_lt _ (by omega)

theorem sub_correct (a b : cp.ModInt m) (start : Nat)
    (ha : a.x.toNat < m.toNat) (hb : b.x.toNat < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.op_sub_ModInt_ModInt a b).run start = some (result, start + 2) ∧
      result.x.toNat = (a.x.toNat + m.toNat - b.x.toNat) % m.toNat ∧
      result.x.toNat < m.toNat := by
  refine ⟨⟨subWord32 m a.x b.x⟩, sub_run m a b start, subWord32_toNat m a.x b.x ha hb, ?_⟩
  rw [subWord32_toNat m a.x b.x ha hb]
  exact Nat.mod_lt _ (by omega)

theorem mul_correct (a b : cp.ModInt m) (start : Nat) (hm : 0 < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.op_mul_ModInt_ModInt a b).run start = some (result, start + 2) ∧
      result.x.toNat = a.x.toNat * b.x.toNat % m.toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨mulWord32 m a.x b.x⟩, mul_run m a b start, mulWord32_toNat m a.x b.x hm, ?_⟩
  rw [mulWord32_toNat m a.x b.x hm]
  exact Nat.mod_lt _ hm

theorem increment_run (a : cp.ModInt m) (start : Nat) :
    (cp.ModInt.op_inc_0 a).run start = some
      (((⟨incrementWord32 m a.x⟩ : cp.ModInt m), ⟨incrementWord32 m a.x⟩), start + 1) := by
  rfl

theorem decrement_run (a : cp.ModInt m) (start : Nat) :
    (cp.ModInt.op_dec_0 a).run start = some
      (((⟨decrementWord32 m a.x⟩ : cp.ModInt m), ⟨decrementWord32 m a.x⟩), start + 1) := by
  rfl

theorem increment_post_run (a : cp.ModInt m) (dummy : Int) (start : Nat) :
    (cp.ModInt.op_inc_int a dummy).run start = some
      ((a, (⟨incrementWord32 m a.x⟩ : cp.ModInt m)), start + 2) := by
  rfl

theorem decrement_post_run (a : cp.ModInt m) (dummy : Int) (start : Nat) :
    (cp.ModInt.op_dec_int a dummy).run start = some
      ((a, (⟨decrementWord32 m a.x⟩ : cp.ModInt m)), start + 2) := by
  rfl

theorem increment_correct (a : cp.ModInt m) (start : Nat) (ha : a.x.toNat < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_inc_0 a).run start = some ((result, result), start + 1) ∧
      result.x.toNat = (a.x.toNat + 1) % m.toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨incrementWord32 m a.x⟩, increment_run m a start, incrementWord32_toNat m a.x ha, ?_⟩
  rw [incrementWord32_toNat m a.x ha]
  exact Nat.mod_lt _ (by omega)

theorem decrement_correct (a : cp.ModInt m) (start : Nat) (ha : a.x.toNat < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_dec_0 a).run start = some ((result, result), start + 1) ∧
      result.x.toNat = (a.x.toNat + m.toNat - 1) % m.toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨decrementWord32 m a.x⟩, decrement_run m a start, decrementWord32_toNat m a.x ha, ?_⟩
  rw [decrementWord32_toNat m a.x ha]
  exact Nat.mod_lt _ (by omega)

theorem increment_post_correct (a : cp.ModInt m) (dummy : Int) (start : Nat)
    (ha : a.x.toNat < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_inc_int a dummy).run start = some ((a, result), start + 2) ∧
      result.x.toNat = (a.x.toNat + 1) % m.toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨incrementWord32 m a.x⟩, increment_post_run m a dummy start, incrementWord32_toNat m a.x ha, ?_⟩
  rw [incrementWord32_toNat m a.x ha]
  exact Nat.mod_lt _ (by omega)

theorem decrement_post_correct (a : cp.ModInt m) (dummy : Int) (start : Nat)
    (ha : a.x.toNat < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_dec_int a dummy).run start = some ((a, result), start + 2) ∧
      result.x.toNat = (a.x.toNat + m.toNat - 1) % m.toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨decrementWord32 m a.x⟩, decrement_post_run m a dummy start, decrementWord32_toNat m a.x ha, ?_⟩
  rw [decrementWord32_toNat m a.x ha]
  exact Nat.mod_lt _ (by omega)

theorem equal_run (a b : cp.ModInt m) (start : Nat) :
    (cp.op_eq_ModInt_ModInt a b).run start = some (decide (a.x = b.x), start + 1) := by
  rfl

theorem unequal_run (a b : cp.ModInt m) (start : Nat) :
    (cp.op_ne_ModInt_ModInt a b).run start = some (decide (a.x ≠ b.x), start + 1) := by
  rfl

theorem equal_value (a b : cp.ModInt m) :
    decide (a.x = b.x) = decide (a.x.toNat = b.x.toNat) := by
  simp only [UInt32.toNat_inj]

theorem unequal_value (a b : cp.ModInt m) :
    decide (a.x ≠ b.x) = decide (a.x.toNat ≠ b.x.toNat) := by
  by_cases h : a.x = b.x
  · simp [h]
  · have hn : a.x.toNat ≠ b.x.toNat := (not_congr UInt32.toNat_inj).mpr h
    simp [h, hn]

theorem negate_run (a : cp.ModInt m) (start : Nat) :
    (cp.ModInt.op_sub a).run start =
      some ((⟨negateWord32 m a.x⟩ : cp.ModInt m), start + 2) := by
  rfl

theorem negate_correct (a : cp.ModInt m) (start : Nat) (ha : a.x.toNat < m.toNat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_sub a).run start = some (result, start + 2) ∧
      result.x.toNat = (m.toNat - a.x.toNat) % m.toNat ∧ result.x.toNat < m.toNat ∧
      (result.x.toNat + a.x.toNat = 0 ∨ result.x.toNat + a.x.toNat = m.toNat) := by
  refine ⟨⟨negateWord32 m a.x⟩, negate_run m a start, negateWord32_toNat m a.x ha, ?_,
    negateWord32_add m a.x ha⟩
  rw [negateWord32_toNat m a.x ha]
  exact Nat.mod_lt _ (by omega)

end Proofs.Cpp.ModIntArithmeticModel
open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ModIntPowerModel

/-- The binary-power model carries only result, squared base and remaining
exponent. This counts its data, not the Lean evaluator's or C++ object's heap. -/
def loopStateBits (state : UInt64 × UInt64 × UInt64) : Nat :=
  bitWidth state.1.toNat + bitWidth state.2.1.toNat + bitWidth state.2.2.toNat

theorem loop_state_bits_bounded (state : UInt64 × UInt64 × UInt64) :
    loopStateBits state ≤ 192 := by
  have h₁ := bitWidth_lt_pow state.1.toNat 64 (UInt64.toNat_lt state.1)
  have h₂ := bitWidth_lt_pow state.2.1.toNat 64 (UInt64.toNat_lt state.2.1)
  have h₃ := bitWidth_lt_pow state.2.2.toNat 64 (UInt64.toNat_lt state.2.2)
  unfold loopStateBits
  omega

/-- A fixed caller envelope. The signed source exponent is encoded in its
64-bit source width; input range premises appear on the public power spec. -/
structure CallerFrame where
  modulus : UInt32
  base : UInt32
  exponentWord : UInt64
  magnitude : UInt64
  powered : UInt32
  normalized : UInt32
  result : UInt32

def CallerFrame.bits (_ : CallerFrame) : Nat := 5 * 32 + 2 * 64

theorem caller_frame_bits (frame : CallerFrame) : frame.bits = 288 := rfl

/-- Two fixed caller envelopes cover the public power-to-inverse nesting;
the binary loop has its own three-word state. This is model working data,
excluding the evaluator stack, C++ heap/lifetimes and atomic primitive internals. -/
theorem power_working_bits (power inverse : CallerFrame) (state : UInt64 × UInt64 × UInt64) :
    power.bits + inverse.bits + loopStateBits state ≤ 768 := by
  rw [caller_frame_bits, caller_frame_bits]
  have h := loop_state_bits_bounded state
  omega

theorem helper_eq (m base : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)] (exponent : UInt64) :
    cp.ModInt.pow_nonnegative (m := m) base exponent = (do
      let result ← cp.pow_mod base.toUInt64 exponent m.toUInt64
      pure result.toUInt32) := by
  simp only [cp.ModInt.pow_nonnegative, cp.pow_mod, bind_assoc, pure_bind]

theorem helper_run (m base : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (exponent : UInt64) (hm : 2 ≤ m.toNat) (start : Nat) :
    ∃ result : UInt32,
      (cp.ModInt.pow_nonnegative (m := m) base exponent).run start =
        some (result, start + 2 + bitWidth exponent.toNat) ∧
      result.toNat = base.toNat ^ exponent.toNat % m.toNat ∧ result.toNat < m.toNat := by
  have hbound := UInt32.toNat_lt m
  have h := PowMod.pow_mod_spec base.toUInt64 exponent m.toUInt64
    (by simpa using (show 1 ≤ m.toNat by omega)) (by simp; omega) start
  obtain ⟨result, ticks, hrun, hvalue, hticks⟩ := run_of_triple h
  have hrange : result.toNat < m.toNat := by
    simpa only [UInt32.toNat_toUInt64] using hvalue ▸ Nat.mod_lt
      (base.toUInt64.toNat ^ exponent.toNat) (show 0 < m.toUInt64.toNat by simpa using (show 0 < m.toNat by omega))
  have hcast : result.toUInt32.toNat = result.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  refine ⟨result.toUInt32, ?_, ?_, ?_⟩
  · rw [helper_eq]
    change Option.bind ((cp.pow_mod base.toUInt64 exponent m.toUInt64).run start)
      (fun r => some (r.1.toUInt32, r.2)) = _
    rw [hrun]
    simpa using congrArg (fun c => some (result.toUInt32, c)) hticks
  · simpa only [hcast, UInt32.toNat_toUInt64] using hvalue
  · simpa only [hcast] using hrange

theorem reduced_word_mod (x m : UInt32) (hx : x.toNat < m.toNat) : x % m = x := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mod, Nat.mod_eq_of_lt hx]

theorem inverse_exponent (m : UInt32) (hm : 2 ≤ m.toNat) :
    (m - 2).toUInt64.toNat = m.toNat - 2 := by
  rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _
    (UInt32.le_iff_toNat_le.mpr (by simpa using hm))]
  rfl

theorem inverse_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (hm : 2 ≤ m.toNat) (hx : value.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.inv value).run start =
        some (result, start + 4 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat = value.x.toNat ^ (m.toNat - 2) % m.toNat ∧
      result.x.toNat < m.toNat := by
  obtain ⟨r, hr, hv, hb⟩ := helper_run m value.x (m - 2).toUInt64 hm (start + 1)
  simp only [inverse_exponent m hm] at hr hv
  refine ⟨⟨r⟩, ?_, hv, hb⟩
  dsimp only [cp.ModInt.inv]
  simp only [check]
  rw [show decide (value.x ≠ 0) = true from decide_eq_true hx]
  simp only [↓reduceIte, pure_bind]
  change Option.bind ((cp.ModInt.pow_nonnegative (m := m) value.x (m - 2).toUInt64).run (start + 1))
    (fun p => some ((⟨p.1 % m⟩ : cp.ModInt m), p.2 + 1)) = _
  rw [hr, Option.bind_some, reduced_word_mod r m hb]
  congr 2
  omega

theorem inverse_zero_fails (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)] (start : Nat) :
    (cp.ModInt.inv (⟨0⟩ : cp.ModInt m)).run start = none := by
  rfl

theorem inverse_correct (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (hp : Proofs.Fermat.IsPrime m.toNat)
    (hx : value.x.toNat < m.toNat) (hx0 : value.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.inv value).run start = some (result, start + 4 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat < m.toNat ∧ (value.x.toNat * result.x.toNat) % m.toNat = 1 := by
  obtain ⟨r, hr, hv, hb⟩ := inverse_run m value hp.1 hx0 start
  refine ⟨r, hr, hb, ?_⟩
  rw [hv]
  apply ModIntMath.inverse_residue_unit m.toNat value.x.toNat hp _ hx
  have hn : value.x.toNat ≠ 0 := by
    intro h
    apply hx0
    exact UInt32.toNat_inj.mp (by simpa using h)
  omega

theorem nonnegative_exponent_word (n : Int) (hn : 0 ≤ n) (hmax : n ≤ 9223372036854775807) :
    (UInt64.ofInt n).toNat = n.toNat := by
  simp only [UInt64.ofInt, UInt64.toNat_ofNat']
  rw [Int.emod_eq_of_lt hn (by omega), Nat.mod_eq_of_lt (by omega)]

theorem power_nonnegative_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (n : Int) (hm : 2 ≤ m.toNat)
    (hn : 0 ≤ n) (hmax : n ≤ 9223372036854775807) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.pow value n).run start = some (result, start + 4 + bitWidth n.toNat) ∧
      result.x.toNat = value.x.toNat ^ n.toNat % m.toNat ∧ result.x.toNat < m.toNat := by
  obtain ⟨r, hr, hv, hb⟩ := helper_run m value.x (UInt64.ofInt n) hm (start + 1)
  simp only [nonnegative_exponent_word n hn hmax] at hr hv
  refine ⟨⟨r⟩, ?_, hv, hb⟩
  simp only [cp.ModInt.pow, show ¬n < 0 by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
  change Option.bind ((cp.ModInt.pow_nonnegative (m := m) value.x (UInt64.ofInt n)).run (start + 1))
    (fun p => some ((⟨p.1 % m⟩ : cp.ModInt m), p.2 + 1)) = _
  rw [hr, Option.bind_some, reduced_word_mod r m hb]
  congr 2
  omega

theorem power_negative_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (n : Int) (hp : Proofs.Fermat.IsPrime m.toNat)
    (hx : value.x.toNat < m.toNat) (hx0 : value.x ≠ 0)
    (hn : n < 0) (hmin : -9223372036854775808 ≤ n) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.pow value n).run start = some
        (result, start + 8 + bitWidth n.natAbs + bitWidth (m.toNat - 2)) ∧
      result.x.toNat = (value.x.toNat ^ n.natAbs % m.toNat) ^ (m.toNat - 2) % m.toNat ∧
      result.x.toNat < m.toNat := by
  let magnitude : UInt64 := UInt64.ofInt (-(n + 1)) + 1
  have hmag : magnitude.toNat = n.natAbs := ModIntMath.negative_magnitude_word n hmin hn
  obtain ⟨r, hr, hv, hb⟩ := helper_run m value.x magnitude hp.1 (start + 1)
  rw [hmag] at hr hv
  have hxNat : 0 < value.x.toNat := by
    have : value.x.toNat ≠ 0 := fun h => hx0 (UInt32.toNat_inj.mp (by simpa using h))
    omega
  have hrNat : r.toNat ≠ 0 := by
    rw [hv]
    exact ModIntMath.power_residue_nonzero m.toNat value.x.toNat n.natAbs hp hxNat hx
  have hr0 : r ≠ 0 := fun h => hrNat (by rw [h]; rfl)
  obtain ⟨i, hi, hvi, hbi⟩ := inverse_run m (⟨r⟩ : cp.ModInt m) hp.1 hr0
    (start + 4 + bitWidth n.natAbs)
  refine ⟨i, ?_, ?_, hbi⟩
  · simp only [cp.ModInt.pow, hn, decide_true, ↓reduceIte]
    change Option.bind ((cp.ModInt.pow_nonnegative (m := m) value.x magnitude).run (start + 1))
      (fun p => (cp.ModInt.inv (⟨p.1 % m⟩ : cp.ModInt m)).run (p.2 + 1)) = _
    rw [hr, Option.bind_some, reduced_word_mod r m hb]
    rw [show (start + 1 + 2 + bitWidth n.natAbs) + 1 = start + 4 + bitWidth n.natAbs by omega]
    rw [show (start + 4 + bitWidth n.natAbs) + 4 + bitWidth (m.toNat - 2) =
      start + 8 + bitWidth n.natAbs + bitWidth (m.toNat - 2) by omega] at hi
    exact hi
  · simpa only [hv] using hvi

theorem power_negative_correct (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (n : Int) (hp : Proofs.Fermat.IsPrime m.toNat)
    (hx : value.x.toNat < m.toNat) (hx0 : value.x ≠ 0)
    (hn : n < 0) (hmin : -9223372036854775808 ≤ n) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.pow value n).run start = some
        (result, start + 8 + bitWidth n.natAbs + bitWidth (m.toNat - 2)) ∧
      result.x.toNat < m.toNat ∧ result.x.toNat * value.x.toNat ^ n.natAbs % m.toNat = 1 := by
  obtain ⟨r, hr, hv, hb⟩ := power_negative_run m value n hp hx hx0 hn hmin start
  have hxNat : 0 < value.x.toNat := by
    have : value.x.toNat ≠ 0 := fun h => hx0 (UInt32.toNat_inj.mp (by simpa using h))
    omega
  have hp0 := ModIntMath.power_residue_nonzero m.toNat value.x.toNat n.natAbs hp hxNat hx
  have hunit := ModIntMath.inverse_residue_unit m.toNat (value.x.toNat ^ n.natAbs % m.toNat)
    hp (by omega) (Nat.mod_lt _ (by have := hp.1; omega))
  refine ⟨r, hr, hb, ?_⟩
  rw [← Nat.mul_mod_mod, hv, Nat.mul_comm]
  exact hunit

theorem power_negative_zero_fails (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (n : Int) (hm : 2 ≤ m.toNat) (hn : n < 0) (hmin : -9223372036854775808 ≤ n) (start : Nat) :
    (cp.ModInt.pow (⟨0⟩ : cp.ModInt m) n).run start = none := by
  let magnitude : UInt64 := UInt64.ofInt (-(n + 1)) + 1
  have hmag : magnitude.toNat = n.natAbs := ModIntMath.negative_magnitude_word n hmin hn
  obtain ⟨r, hr, hv, hb⟩ := helper_run m 0 magnitude hm (start + 1)
  rw [hmag] at hr hv
  have habs : 0 < n.natAbs := by omega
  simp only [UInt32.toNat_zero, Nat.zero_pow habs, Nat.zero_mod] at hv
  have hz : r = 0 := UInt32.toNat_inj.mp (by simpa using hv)
  simp only [cp.ModInt.pow, hn, decide_true, ↓reduceIte]
  change Option.bind ((cp.ModInt.pow_nonnegative (m := m) 0 magnitude).run (start + 1))
    (fun p => (cp.ModInt.inv (⟨p.1 % m⟩ : cp.ModInt m)).run (p.2 + 1)) = _
  rw [hr, Option.bind_some, hz, reduced_word_mod 0 m (by simp; omega)]
  exact inverse_zero_fails m _

theorem division_assign_step (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b inverse : cp.ModInt m) (start finish : Nat)
    (hi : (cp.ModInt.inv b).run (start + 1) = some (inverse, finish)) :
    (cp.ModInt.op_div_assign a b).run start = some
      (((⟨ModIntMath.mulWord32 m a.x inverse.x⟩ : cp.ModInt m),
        ⟨ModIntMath.mulWord32 m a.x inverse.x⟩), finish + 1) := by
  change Option.bind ((cp.ModInt.inv b).run (start + 1)) (fun p => some
    (((⟨ModIntMath.mulWord32 m a.x p.1.x⟩ : cp.ModInt m),
      (⟨ModIntMath.mulWord32 m a.x p.1.x⟩ : cp.ModInt m)), p.2 + 1)) = _
  rw [hi]
  rfl

theorem division_assign_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hm : 2 ≤ m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_div_assign a b).run start =
        some ((result, result), start + 6 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat = a.x.toNat * (b.x.toNat ^ (m.toNat - 2) % m.toNat) % m.toNat ∧
      result.x.toNat < m.toNat := by
  obtain ⟨i, hi, hv, hb⟩ := inverse_run m b hm hb0 (start + 1)
  refine ⟨⟨ModIntMath.mulWord32 m a.x i.x⟩, ?_, ?_, ?_⟩
  · have step := division_assign_step m a b i _ _ hi
    rw [show (start + 1 + 4 + bitWidth (m.toNat - 2)) + 1 =
      start + 6 + bitWidth (m.toNat - 2) by omega] at step
    exact step
  · rw [ModIntMath.mulWord32_toNat m a.x i.x (by omega), hv]
  · rw [ModIntMath.mulWord32_toNat m a.x i.x (by omega)]
    exact Nat.mod_lt _ (by omega)

theorem division_assign_correct (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hp : Proofs.Fermat.IsPrime m.toNat)
    (ha : a.x.toNat < m.toNat) (hb : b.x.toNat < m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.ModInt.op_div_assign a b).run start =
        some ((result, result), start + 6 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat < m.toNat ∧ result.x.toNat * b.x.toNat % m.toNat = a.x.toNat := by
  obtain ⟨r, hr, hv, hbnd⟩ := division_assign_run m a b hp.1 hb0 start
  refine ⟨r, hr, hbnd, ?_⟩
  rw [hv]
  apply ModIntMath.quotient_residue_unit m.toNat a.x.toNat b.x.toNat hp ha _ hb
  have hn : b.x.toNat ≠ 0 := by
    intro h
    exact hb0 (UInt32.toNat_inj.mp (by simpa using h))
  omega

theorem division_run (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hm : 2 ≤ m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.op_div_ModInt_ModInt a b).run start = some (result, start + 7 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat = a.x.toNat * (b.x.toNat ^ (m.toNat - 2) % m.toNat) % m.toNat ∧
      result.x.toNat < m.toNat := by
  obtain ⟨r, hr, hv, hb⟩ := division_assign_run m a b hm hb0 (start + 1)
  refine ⟨r, ?_, hv, hb⟩
  change Option.bind ((cp.ModInt.op_div_assign a b).run (start + 1))
    (fun p => some (p.1.1, p.2)) = _
  rw [hr]
  rfl

theorem division_correct (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hp : Proofs.Fermat.IsPrime m.toNat)
    (ha : a.x.toNat < m.toNat) (hb : b.x.toNat < m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m,
      (cp.op_div_ModInt_ModInt a b).run start = some (result, start + 7 + bitWidth (m.toNat - 2)) ∧
      result.x.toNat < m.toNat ∧ result.x.toNat * b.x.toNat % m.toNat = a.x.toNat := by
  obtain ⟨r, hr, hv, hbnd⟩ := division_run m a b hp.1 hb0 start
  refine ⟨r, hr, hbnd, ?_⟩
  rw [hv]
  apply ModIntMath.quotient_residue_unit m.toNat a.x.toNat b.x.toNat hp ha _ hb
  have hn : b.x.toNat ≠ 0 := by
    intro h
    exact hb0 (UInt32.toNat_inj.mp (by simpa using h))
  omega

theorem bitwidth_log_succ (n : Nat) : bitWidth n ≤ Nat.log2 (n + 1) + 1 := by
  calc
    bitWidth n ≤ bitWidth (n + 1) := bitWidth_mono (Nat.le_succ n)
    _ = Nat.log2 (n + 1) + 1 := by simp [bitWidth]

theorem inverse_bitwidth_log (m : Nat) (hm : 2 ≤ m) : bitWidth (m - 2) ≤ Nat.log2 m + 1 := by
  calc
    bitWidth (m - 2) ≤ bitWidth m := bitWidth_mono (Nat.sub_le m 2)
    _ = Nat.log2 m + 1 := by simp [bitWidth, show m ≠ 0 by omega]

theorem power_correct_and_log_work (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (n : Int) (hp : Proofs.Fermat.IsPrime m.toNat)
    (hx : value.x.toNat < m.toNat) (hx0 : n < 0 → value.x ≠ 0)
    (hmin : -9223372036854775808 ≤ n) (hmax : n ≤ 9223372036854775807) (start : Nat) :
    ∃ result : cp.ModInt m, ∃ finish : Nat,
      (cp.ModInt.pow value n).run start = some (result, finish) ∧
      result.x.toNat = ModIntMath.signedPowerResidue m.toNat value.x.toNat n ∧
      result.x.toNat < m.toNat ∧
      finish ≤ start + 10 * (1 + Nat.log2 (n.natAbs + 1) + Nat.log2 m.toNat) := by
  by_cases hn : n < 0
  · obtain ⟨r, hr, hv, hb⟩ := power_negative_run m value n hp hx (hx0 hn) hn hmin start
    refine ⟨r, _, hr, ?_, hb, ?_⟩
    · simpa only [ModIntMath.signedPowerResidue, hn, ↓reduceIte] using hv
    · have h₁ := bitwidth_log_succ n.natAbs
      have h₂ := inverse_bitwidth_log m.toNat hp.1
      omega
  · obtain ⟨r, hr, hv, hb⟩ := power_nonnegative_run m value n hp.1 (by omega) hmax start
    refine ⟨r, _, hr, ?_, hb, ?_⟩
    · simpa only [ModIntMath.signedPowerResidue, hn, ↓reduceIte] using hv
    · have h₁ := bitwidth_log_succ n.toNat
      have hn' := Int.natAbs_of_nonneg (show 0 ≤ n by omega)
      have h₂ : n.natAbs = n.toNat := by omega
      rw [h₂]
      omega

theorem inverse_log_work (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (value : cp.ModInt m) (hm : 2 ≤ m.toNat) (hx : value.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m, ∃ finish : Nat,
      (cp.ModInt.inv value).run start = some (result, finish) ∧
      finish ≤ start + 5 + Nat.log2 m.toNat := by
  obtain ⟨r, hr, _, _⟩ := inverse_run m value hm hx start
  refine ⟨r, _, hr, ?_⟩
  have h := inverse_bitwidth_log m.toNat hm
  omega

theorem division_log_work (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)]
    (a b : cp.ModInt m) (hm : 2 ≤ m.toNat) (hb0 : b.x ≠ 0) (start : Nat) :
    ∃ result : cp.ModInt m, ∃ finish : Nat,
      (cp.op_div_ModInt_ModInt a b).run start = some (result, finish) ∧
      finish ≤ start + 8 + Nat.log2 m.toNat := by
  obtain ⟨r, hr, _, _⟩ := division_run m a b hm hb0 start
  refine ⟨r, _, hr, ?_⟩
  have h := inverse_bitwidth_log m.toNat hm
  omega

end Proofs.Cpp.ModIntPowerModel
-- Appended to a fresh canonical class model. Source stream operations retain
-- their own formatting, failure, exception and cost contracts.
open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ModIntStreamModel

variable (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)] [Streams]

section Input
local instance : Mod Int := ⟨Int.tmod⟩
variable [SourceStreamRead "long" Int]

theorem extract_eq (input : IStream) (value : cp.ModInt m) :
    cp.op_shr_istream_ModInt input value = (do
      tick
      let (raw, input) ← SourceStreamRead.read (source := "long") input (0 : Int)
      tick
      pure (input, input,
        (⟨UInt32.ofInt (ModIntMath.signedNormalize raw m.toNat)⟩ : cp.ModInt m))) := by
  rfl

theorem extract_run (input after : IStream) (previous : cp.ModInt m)
    (raw : Int) (start finish : Nat)
    (hr : (SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1) =
      some ((raw, after), finish)) :
    (cp.op_shr_istream_ModInt input previous).run start = some
      ((after, after, (⟨UInt32.ofInt (ModIntMath.signedNormalize raw m.toNat)⟩ : cp.ModInt m)),
        finish + 1) := by
  rw [extract_eq]
  change Option.bind ((SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1))
    (fun p => some ((p.1.2, p.1.2,
      (⟨UInt32.ofInt (ModIntMath.signedNormalize p.1.1 m.toNat)⟩ : cp.ModInt m)), p.2 + 1)) = _
  rw [hr]
  rfl

theorem extract_correct (input after : IStream) (previous : cp.ModInt m)
    (raw : Int) (start finish : Nat) (hm : 0 < m.toNat)
    (hr : (SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1) =
      some ((raw, after), finish)) :
    ∃ result : cp.ModInt m,
      (cp.op_shr_istream_ModInt input previous).run start = some ((after, after, result), finish + 1) ∧
      result.x.toNat = (Int.emod raw m.toNat).toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨UInt32.ofInt (ModIntMath.signedNormalize raw m.toNat)⟩,
    extract_run m input after previous raw start finish hr, ?_, ?_⟩
  all_goals rw [ModIntMath.signed_normalize_eq raw m.toNat (by omega)]
  all_goals
    have h0 := Int.emod_nonneg raw (by omega : (m.toNat : Int) ≠ 0)
    have h1 := Int.emod_lt_of_pos raw (by omega : (0 : Int) < m.toNat)
    rw [ModIntMath.u32_ofInt_toNat _ h0 (by have := UInt32.toNat_lt m; omega)]
  · rfl
  · omega

theorem extract_nonreturn (input : IStream) (previous : cp.ModInt m) (start : Nat)
    (hr : (SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1) = none) :
    (cp.op_shr_istream_ModInt input previous).run start = none := by
  rw [extract_eq]
  change Option.bind ((SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1)) _ = _
  rw [hr]
  rfl
end Input

section Output
variable [SourceStreamWrite "unsigned_int" UInt32]

theorem insert_eq (output : OStream) (value : cp.ModInt m) :
    cp.op_shl_ostream_ModInt output value = (do
      tick
      let output ← SourceStreamWrite.write (source := "unsigned_int") output value.x
      pure (output, output)) := by
  rfl

theorem insert_run (output after : OStream) (value : cp.ModInt m) (start finish : Nat)
    (hr : (SourceStreamWrite.write (source := "unsigned_int") output value.x).run (start + 1) =
      some (after, finish)) :
    (cp.op_shl_ostream_ModInt output value).run start = some ((after, after), finish) := by
  rw [insert_eq]
  change Option.bind ((SourceStreamWrite.write (source := "unsigned_int") output value.x).run (start + 1))
    (fun p => some ((p.1, p.1), p.2)) = _
  rw [hr]
  rfl

theorem insert_nonreturn (output : OStream) (value : cp.ModInt m) (start : Nat)
    (hr : (SourceStreamWrite.write (source := "unsigned_int") output value.x).run (start + 1) = none) :
    (cp.op_shl_ostream_ModInt output value).run start = none := by
  rw [insert_eq]
  change Option.bind ((SourceStreamWrite.write (source := "unsigned_int") output value.x).run (start + 1)) _ = _
  rw [hr]
  rfl
end Output

end Proofs.Cpp.ModIntStreamModel
-- Appended to the freshly generated entire original ModInt file.
-- Arithmetic correctness of the modular operators is a separate obligation.
open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ModIntGlobalsModel

variable [TemplateConstraint ((2 : UInt32) ≤ (998244353 : UInt32))]

local instance : Mod Int := ⟨Int.tmod⟩

def indexWord (i : Int) : UInt32 := UInt32.ofInt (ModIntMath.signedNormalize i 998244353)

theorem indexWord_toNat (i : Int) (hi : 0 ≤ i) (hiN : i < 20000003) :
    (indexWord i).toNat = i.toNat := by
  unfold indexWord
  rw [ModIntMath.signed_normalize_eq i 998244353 (by decide),
      Int.emod_eq_of_lt hi (by omega), ModIntMath.u32_ofInt_toNat i hi (by omega)]

theorem init_step (fac : Array cp.mint) (L : Nat) (hL : L < 20000002)
    (hsz : fac.size = 20000003)
    (hp : ∀ k, k ≤ L → fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k) :
    ∀ k, k ≤ L + 1 →
      (set fac (1 + (L : Int))
        (⟨ModIntMath.mulWord32 998244353 (get fac (1 + (L : Int) - 1)).x
          (indexWord (1 + (L : Int)))⟩ : cp.mint))[k]!.x.toNat =
        ModIntFactorial.factorialResidue 998244353 k := by
  intro k hk
  have e1 : (1 + (L : Int)).toNat = L + 1 := by omega
  have e2 : 1 + (L : Int) - 1 = (L : Int) := by omega
  rw [getElemBang_set _ _ _ k (by omega), e1]
  by_cases he : k = L + 1
  · subst k
    simp only [ite_true]
    rw [ModIntMath.mulWord32_toNat _ _ _ (by decide), e2, get_natCast, hp L (Nat.le_refl _),
        indexWord_toNat _ (by omega) (by omega), e1]
    exact ModIntFactorial.factorial_step 998244353 L
  · simp only [he, ite_false]
    exact hp k (by omega)

/-- Functional array update model with a symbolic loop endpoint. Each loop
body accounts for its loop, constructor, binary wrapper and multiplication. -/
def initModel (limit : Int) (state : cp.GlobalState) : M cp.GlobalState := do
  tick
  check (decide (state.fac.size = 20000003))
  tick
  let mut fac := set state.fac 0 (⟨indexWord 1⟩ : cp.mint)
  for i in range 1 limit do
    tick
    tick
    tick
    tick
    fac := set fac i
      (⟨ModIntMath.mulWord32 998244353 (get fac (i - 1)).x (indexWord i)⟩ : cp.mint)
  return { fac }

theorem init_model_eq (state : cp.GlobalState) : cp.init state = initModel cp.MAX_FAC state := by
  rfl

theorem init_model_spec (limit : Int) (hl : limit = 20000003)
    (state : cp.GlobalState) (hs : state.fac.size = 20000003) (start : Nat) :
    ⦃fun c => ⌜c = start⌝⦄ initModel limit state
    ⦃⇓ result c => ⌜result.fac.size = 20000003 ∧
      (∀ k, k < 20000003 → result.fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k) ∧
      c = start + 2 + 4 * 20000002⌝⦄ := by
  mvcgen [initModel]
  case inv1 =>
    exact ⇓⟨xs, fac⟩ c => ⌜fac.size = 20000003 ∧
      (∀ k, k ≤ xs.prefix.length → fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k) ∧
      c = start + 2 + 4 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  all_goals try contradiction
  · have hlr := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    have he := range_cursor ‹range _ _ = _ ++ _ :: _›
    subst he
    obtain ⟨hsz, hp, hc⟩ := ‹_ ∧ _ ∧ _›
    exact ⟨hsz, init_step _ _ (by omega) hsz hp, by omega⟩
  · refine ⟨hs, ?_, ‹_›⟩
    rw [getElemBang_set _ _ _ _ (by omega)]
    rfl
  · obtain ⟨hsz, hp, hc⟩ := ‹_ ∧ _ ∧ _›
    have hlen : (range 1 limit).length = 20000002 := by
      unfold range
      rw [List.length_map, List.length_range]
      omega
    rw [hlen] at hp hc
    exact ⟨hsz, fun k hk => hp k (by omega), by omega⟩

def initialModel (count : Nat) : M cp.GlobalState := do
  tick
  let mut fac : Array cp.mint := Array.empty
  for _ in [:count] do
    tick
    tick
    fac := fac.push (⟨0⟩ : cp.mint)
  return { fac }

theorem initial_model_eq : cp.initializeGlobals = initialModel 20000003 := by rfl

theorem initial_spec (count start : Nat) :
    ⦃fun c => ⌜c = start⌝⦄ initialModel count
    ⦃⇓ result c => ⌜result.fac = Array.replicate count (⟨0⟩ : cp.mint) ∧
      c = start + 1 + 2 * count⌝⦄ := by
  mvcgen [initialModel]
  case inv1 =>
    exact ⇓⟨xs, fac⟩ c => ⌜fac = Array.replicate xs.prefix.length (⟨0⟩ : cp.mint) ∧
      c = start + 1 + 2 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨ha, hc⟩ := ‹_ ∧ _›
    rw [ha, ← Array.replicate_succ]
    exact ⟨rfl, by omega⟩
  · exact ⟨rfl, ‹_ = start›⟩
  · assumption

theorem initial_model_run (count start : Nat) :
    ∃ state : cp.GlobalState,
      (initialModel count).run start = some (state, start + 1 + 2 * count) ∧
      state.fac = Array.replicate count (⟨0⟩ : cp.mint) := by
  obtain ⟨state, finish, hr, ha, hc⟩ := run_of_triple (initial_spec count start)
  exact ⟨state, hc ▸ hr, ha⟩

theorem initial_run (start : Nat) :
    ∃ state : cp.GlobalState,
      cp.initializeGlobals.run start = some (state, start + 1 + 2 * 20000003) ∧
      state.fac = Array.replicate 20000003 (⟨0⟩ : cp.mint) := by
  rw [initial_model_eq]
  exact initial_model_run 20000003 start

/-- Evaluate the quotient using a read-only factorial table. -/
def tableQuotient (fac : Array cp.mint) (n k : Int) : M cp.mint := do
  tick
  check (decide (fac.size = 20000003))
  let denominator ← cp.op_mul_ModInt_ModInt (m := (998244353 : UInt32))
    (Cpp.get fac k) (Cpp.get fac (n - k))
  cp.op_div_ModInt_ModInt (m := (998244353 : UInt32)) (Cpp.get fac n) denominator

theorem combination_eq (state : cp.GlobalState) (n k : Int) :
    cp.C n k state = (do
      let result ← tableQuotient state.fac n k
      pure (result, state)) := by
  cases state
  simp only [cp.C, tableQuotient, bind_assoc, pure_bind]

theorem combination_run (state : cp.GlobalState) (n k : Int)
    (result : cp.mint) (start finish : Nat)
    (h : (tableQuotient state.fac n k).run start = some (result, finish)) :
    (cp.C n k state).run start = some ((result, state), finish) := by
  rw [combination_eq]
  change Option.bind ((tableQuotient state.fac n k).run start)
    (fun r => some ((r.1, state), r.2)) = _
  rw [h]
  rfl

theorem combination_preserves_state (state after : cp.GlobalState) (n k : Int)
    (result : cp.mint) (start finish : Nat)
    (h : (cp.C n k state).run start = some ((result, after), finish)) : after = state := by
  rw [combination_eq] at h
  change Option.bind ((tableQuotient state.fac n k).run start)
    (fun r => some ((r.1, state), r.2)) = _ at h
  cases hr : (tableQuotient state.fac n k).run start with
  | none => simp only [hr, Option.bind_none, reduceCtorEq] at h
  | some value =>
    simp only [hr, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.2.symm

def TableRep (fac : Array cp.mint) : Prop :=
  fac.size = 20000003 ∧
    ∀ k, k < 20000003 → fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k

theorem table_run_of_spec (action : M cp.GlobalState) (start : Nat)
    (h : ⦃fun c => ⌜c = start⌝⦄ action
      ⦃⇓ result c => ⌜result.fac.size = 20000003 ∧
        (∀ k, k < 20000003 → result.fac[k]!.x.toNat = ModIntFactorial.factorialResidue 998244353 k) ∧
        c = start + 2 + 4 * 20000002⌝⦄) :
    ∃ result : cp.GlobalState,
      action.run start = some (result, start + 2 + 4 * 20000002) ∧ TableRep result.fac := by
  obtain ⟨r, finish, hr, hsz, hv, hc⟩ := run_of_triple h
  exact ⟨r, hc ▸ hr, hsz, hv⟩

theorem init_model_run (limit : Int) (hl : limit = 20000003)
    (state : cp.GlobalState) (hs : state.fac.size = 20000003) (start : Nat) :
    ∃ result : cp.GlobalState,
      (initModel limit state).run start = some (result, start + 2 + 4 * 20000002) ∧ TableRep result.fac := by
  exact table_run_of_spec _ start (init_model_spec limit hl state hs start)

theorem init_run (state : cp.GlobalState) (hs : state.fac.size = 20000003) (start : Nat) :
    ∃ result : cp.GlobalState,
      (cp.init state).run start = some (result, start + 2 + 4 * 20000002) ∧ TableRep result.fac := by
  rw [init_model_eq]
  exact init_model_run cp.MAX_FAC rfl state hs start

theorem combination_correct (state : cp.GlobalState) (n k : Nat) (hrep : TableRep state.fac)
    (hn : n < 20000003) (hk : k ≤ n) (start : Nat) :
    ∃ result : cp.mint,
      (cp.C (n : Int) (k : Int) state).run start = some ((result, state), start + 40) ∧
      result.x.toNat = n.choose k % 998244353 ∧ result.x.toNat < 998244353 := by
  let a : cp.mint := get state.fac (n : Int)
  let b : cp.mint := get state.fac (k : Int)
  let c : cp.mint := get state.fac ((n : Int) - (k : Int))
  have ha : a.x.toNat = ModIntFactorial.factorialResidue 998244353 n := by
    exact hrep.2 n hn
  have hb : b.x.toNat = ModIntFactorial.factorialResidue 998244353 k := by
    exact hrep.2 k (by omega)
  have hc : c.x.toNat = ModIntFactorial.factorialResidue 998244353 (n - k) := by
    dsimp [c]
    rw [show (n : Int) - (k : Int) = ((n - k : Nat) : Int) by omega, get_natCast]
    exact hrep.2 _ (by omega)
  let d : cp.mint := ⟨ModIntMath.mulWord32 998244353 b.x c.x⟩
  have hd : d.x.toNat = ModIntFactorial.denominator 998244353 n k := by
    dsimp [d]
    rw [ModIntMath.mulWord32_toNat _ _ _ (by decide), hb, hc]
    exact (Nat.mul_mod _ _ _).symm
  have hp := ModIntFactorial.fixed_modulus_prime
  have hd0 : d.x ≠ 0 := by
    intro hz
    have hv := congrArg UInt32.toNat hz
    rw [hd] at hv
    exact ModIntFactorial.denominator_nonzero 998244353 n k hp (by omega) hk hv
  obtain ⟨r, hr, hv, hrange⟩ := ModIntPowerModel.division_run 998244353 a d (by decide) hd0 (start + 3)
  have hbw : bitWidth (998244353 - 2) = 30 := by decide
  refine ⟨r, ?_, ?_, hrange⟩
  · rw [combination_eq]
    unfold tableQuotient
    rw [show state.fac.size = 20000003 from hrep.1]
    simp only [decide_true, check, ↓reduceIte, pure_bind]
    change Option.bind ((cp.op_mul_ModInt_ModInt b c).run (start + 1)) (fun p =>
      Option.bind ((cp.op_div_ModInt_ModInt a p.1).run p.2)
        (fun q => some ((q.1, state), q.2))) = _
    rw [ModIntArithmeticModel.mul_run 998244353 b c (start + 1), Option.bind_some]
    change Option.bind ((cp.op_div_ModInt_ModInt a d).run (start + 3))
      (fun q => some ((q.1, state), q.2)) = _
    rw [hr, Option.bind_some]
    change some ((r, state), start + 3 + 7 + bitWidth (998244353 - 2)) = _
    rw [hbw]
  · rw [hv, ha, hd]
    exact ModIntFactorial.binomial_correct 998244353 n k hp (by omega) hk

/-- The full source initialization followed by a query. The returned table
is retained, allowing subsequent queries without rebuilding it. -/
theorem init_combination_run (state : cp.GlobalState) (hs : state.fac.size = 20000003)
    (n k : Nat) (hn : n < 20000003) (hk : k ≤ n) (start : Nat) :
    ∃ result : cp.mint, ∃ after : cp.GlobalState,
      ((do
        let ready ← cp.init state
        cp.C (n : Int) (k : Int) ready) : M (cp.mint × cp.GlobalState)).run start =
        some ((result, after), (start + 2 + 4 * 20000002) + 40) ∧
      TableRep after.fac ∧ result.x.toNat = n.choose k % 998244353 := by
  obtain ⟨after, hi, ht⟩ := init_run state hs start
  obtain ⟨result, hc, hv, _⟩ := combination_correct after n k ht hn hk _
  refine ⟨result, after, ?_, ht, hv⟩
  change Option.bind ((cp.init state).run start) _ = _
  rw [hi, Option.bind_some]
  exact hc

/-- Startup, initialization, and a query are all connected to the original
entry points. No concrete table is evaluated while checking this theorem. -/
theorem startup_combination_run (n k : Nat) (hn : n < 20000003) (hk : k ≤ n)
    (start : Nat) :
    ∃ result : cp.mint, ∃ after : cp.GlobalState,
      ((do
        let zero ← cp.initializeGlobals
        let ready ← cp.init zero
        cp.C (n : Int) (k : Int) ready) : M (cp.mint × cp.GlobalState)).run start =
        some ((result, after), ((start + 1 + 2 * 20000003) + 2 + 4 * 20000002) + 40) ∧
      TableRep after.fac ∧ result.x.toNat = n.choose k % 998244353 := by
  obtain ⟨zero, hz, ha⟩ := initial_run start
  have hs : zero.fac.size = 20000003 := by rw [ha, Array.size_replicate]
  obtain ⟨result, after, hc, ht, hv⟩ := init_combination_run zero hs n k hn hk _
  refine ⟨result, after, ?_, ht, hv⟩
  change Option.bind (cp.initializeGlobals.run start) _ = _
  rw [hz, Option.bind_some]
  exact hc

/-- Array data in the model consists of one 32-bit word per table entry.
This excludes C++ heap/lifetime and the evaluator's own storage. -/
def tableDataBits (state : cp.GlobalState) : Nat := 32 * state.fac.size

theorem table_data_bound (state : cp.GlobalState) (h : TableRep state.fac) :
    tableDataBits state = 32 * 20000003 := by
  exact congrArg (32 * ·) h.1

theorem initialization_linear_work (count : Nat) :
    1 + 2 * count ≤ 3 * (count + 1) := by omega

theorem factorial_linear_work (count : Nat) :
    2 + 4 * count ≤ 4 * (count + 1) := by omega

end Proofs.Cpp.ModIntGlobalsModel
