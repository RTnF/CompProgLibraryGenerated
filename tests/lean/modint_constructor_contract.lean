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
