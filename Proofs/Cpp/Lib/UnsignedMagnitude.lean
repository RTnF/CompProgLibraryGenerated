import Proofs.Cpp.Lib.Basic

namespace Proofs.Cpp

/-- Natural-number interpretation sufficient for unsigned Euclid. The laws are
proved for concrete bindings, not supplied as unverified axioms. -/
class UnsignedMagnitude (T : Type) [Zero T] [Mod T] [LT T] where
  magnitude : T → Nat
  zero_iff : ∀ x, magnitude x = 0 ↔ x = 0
  mod_eq : ∀ x y, magnitude (x % y) = magnitude x % magnitude y
  bound : ∀ x, magnitude x < fuel
  not_lt_zero : ∀ x : T, ¬x < 0

namespace UnsignedMagnitude
variable {T : Type} [Zero T] [Mod T] [LT T] [UnsignedMagnitude T]

@[simp] theorem magnitude_zero : magnitude (0 : T) = 0 := (zero_iff 0).mpr rfl

@[simp] theorem magnitude_mod (x y : T) :
    magnitude (x % y) = magnitude x % magnitude y := mod_eq x y

instance : UnsignedMagnitude UInt8 where
  magnitude := UInt8.toNat
  zero_iff x := by
    constructor
    · intro h
      exact UInt8.toNat_inj.mp (by simpa using h)
    · intro h
      subst x
      rfl
  mod_eq := UInt8.toNat_mod
  bound x := by
    have h := UInt8.toNat_lt x
    change x.toNat < 2 ^ 8 at h
    change x.toNat < 2 ^ 64
    omega
  not_lt_zero x := by
    change ¬x.toNat < 0
    omega

instance : UnsignedMagnitude UInt16 where
  magnitude := UInt16.toNat
  zero_iff x := by
    constructor
    · intro h
      exact UInt16.toNat_inj.mp (by simpa using h)
    · intro h
      subst x
      rfl
  mod_eq := UInt16.toNat_mod
  bound x := by
    have h := UInt16.toNat_lt x
    change x.toNat < 2 ^ 16 at h
    change x.toNat < 2 ^ 64
    omega
  not_lt_zero x := by
    change ¬x.toNat < 0
    omega

instance : UnsignedMagnitude UInt32 where
  magnitude := UInt32.toNat
  zero_iff x := by
    constructor
    · intro h
      exact UInt32.toNat_inj.mp (by simpa using h)
    · intro h
      subst x
      rfl
  mod_eq := UInt32.toNat_mod
  bound x := by
    have h := UInt32.toNat_lt x
    change x.toNat < 2 ^ 32 at h
    change x.toNat < 2 ^ 64
    omega
  not_lt_zero x := by
    change ¬x.toNat < 0
    omega

instance : UnsignedMagnitude UInt64 where
  magnitude := UInt64.toNat
  zero_iff x := by
    constructor
    · intro h
      exact UInt64.toNat_inj.mp (by simpa using h)
    · intro h
      subst x
      rfl
  mod_eq := UInt64.toNat_mod
  bound x := UInt64.toNat_lt x
  not_lt_zero x := by
    change ¬x.toNat < 0
    omega

end UnsignedMagnitude

/-- Exact division and unit for the non-overflowing normalization algorithm. -/
class UnsignedDivision (T : Type) [Zero T] [One T] [Div T] [Mod T] [LT T]
    [UnsignedMagnitude T] where
  one_eq : UnsignedMagnitude.magnitude (1 : T) = 1
  div_eq : ∀ x y : T, UnsignedMagnitude.magnitude (x / y) =
    UnsignedMagnitude.magnitude x / UnsignedMagnitude.magnitude y

namespace UnsignedDivision

instance : UnsignedDivision UInt8 where
  one_eq := rfl
  div_eq := UInt8.toNat_div

instance : UnsignedDivision UInt16 where
  one_eq := rfl
  div_eq := UInt16.toNat_div

instance : UnsignedDivision UInt32 where
  one_eq := rfl
  div_eq := UInt32.toNat_div

instance : UnsignedDivision UInt64 where
  one_eq := rfl
  div_eq := UInt64.toNat_div

end UnsignedDivision

/-- Stored unsigned products agree with natural multiplication when the result
fits the representation. LCM has this same representability precondition. -/
class UnsignedProduct (T : Type) [Zero T] [Mod T] [LT T] [Mul T]
    [UnsignedMagnitude T] where
  capacity : Nat
  magnitude_lt : ∀ x : T, UnsignedMagnitude.magnitude x < capacity
  mul_exact : ∀ x y : T,
    UnsignedMagnitude.magnitude x * UnsignedMagnitude.magnitude y < capacity →
    UnsignedMagnitude.magnitude (x * y) =
      UnsignedMagnitude.magnitude x * UnsignedMagnitude.magnitude y

namespace UnsignedProduct

instance : UnsignedProduct UInt8 where
  capacity := 2 ^ 8
  magnitude_lt := UInt8.toNat_lt
  mul_exact x y h := by
    change x.toNat * y.toNat < _ at h
    change (x * y).toNat = x.toNat * y.toNat
    rw [UInt8.toNat_mul, Nat.mod_eq_of_lt h]

instance : UnsignedProduct UInt16 where
  capacity := 2 ^ 16
  magnitude_lt := UInt16.toNat_lt
  mul_exact x y h := by
    change x.toNat * y.toNat < _ at h
    change (x * y).toNat = x.toNat * y.toNat
    rw [UInt16.toNat_mul, Nat.mod_eq_of_lt h]

instance : UnsignedProduct UInt32 where
  capacity := 2 ^ 32
  magnitude_lt := UInt32.toNat_lt
  mul_exact x y h := by
    change x.toNat * y.toNat < _ at h
    change (x * y).toNat = x.toNat * y.toNat
    rw [UInt32.toNat_mul, Nat.mod_eq_of_lt h]

instance : UnsignedProduct UInt64 where
  capacity := 2 ^ 64
  magnitude_lt := UInt64.toNat_lt
  mul_exact x y h := by
    change x.toNat * y.toNat < _ at h
    change (x * y).toNat = x.toNat * y.toNat
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h]

end UnsignedProduct

class UnsignedAddSub (T : Type) [Zero T] [Mod T] [LT T] [Mul T] [Add T] [Sub T]
    [UnsignedMagnitude T] [UnsignedProduct T] where
  add_exact : ∀ x y : T,
    UnsignedMagnitude.magnitude x + UnsignedMagnitude.magnitude y < UnsignedProduct.capacity (T := T) →
    UnsignedMagnitude.magnitude (x + y) = UnsignedMagnitude.magnitude x + UnsignedMagnitude.magnitude y
  sub_exact : ∀ x y : T, UnsignedMagnitude.magnitude y ≤ UnsignedMagnitude.magnitude x →
    UnsignedMagnitude.magnitude (x - y) = UnsignedMagnitude.magnitude x - UnsignedMagnitude.magnitude y

namespace UnsignedAddSub

instance : UnsignedAddSub UInt8 where
  add_exact x y h := by
    change x.toNat + y.toNat < 2 ^ 8 at h
    change (x + y).toNat = x.toNat + y.toNat
    rw [UInt8.toNat_add, Nat.mod_eq_of_lt h]
  sub_exact x y h := by
    change y.toNat ≤ x.toNat at h
    exact UInt8.toNat_sub_of_le x y (UInt8.le_iff_toNat_le.mpr h)

instance : UnsignedAddSub UInt16 where
  add_exact x y h := by
    change x.toNat + y.toNat < 2 ^ 16 at h
    change (x + y).toNat = x.toNat + y.toNat
    rw [UInt16.toNat_add, Nat.mod_eq_of_lt h]
  sub_exact x y h := by
    change y.toNat ≤ x.toNat at h
    exact UInt16.toNat_sub_of_le x y (UInt16.le_iff_toNat_le.mpr h)

instance : UnsignedAddSub UInt32 where
  add_exact x y h := by
    change x.toNat + y.toNat < 2 ^ 32 at h
    change (x + y).toNat = x.toNat + y.toNat
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt h]
  sub_exact x y h := by
    change y.toNat ≤ x.toNat at h
    exact UInt32.toNat_sub_of_le x y (UInt32.le_iff_toNat_le.mpr h)

instance : UnsignedAddSub UInt64 where
  add_exact x y h := by
    change x.toNat + y.toNat < 2 ^ 64 at h
    change (x + y).toNat = x.toNat + y.toNat
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]
  sub_exact x y h := by
    change y.toNat ≤ x.toNat at h
    exact UInt64.toNat_sub_of_le x y (UInt64.le_iff_toNat_le.mpr h)

end UnsignedAddSub
/-- The source comparison order agrees with the natural interpretation. -/
class UnsignedOrder (T : Type) [Zero T] [Mod T] [LT T] [UnsignedMagnitude T] where
  lt_iff : ∀ x y : T, x < y ↔ UnsignedMagnitude.magnitude x < UnsignedMagnitude.magnitude y

namespace UnsignedOrder

instance : UnsignedOrder UInt8 where
  lt_iff _ _ := UInt8.lt_iff_toNat_lt

instance : UnsignedOrder UInt16 where
  lt_iff _ _ := UInt16.lt_iff_toNat_lt

instance : UnsignedOrder UInt32 where
  lt_iff _ _ := UInt32.lt_iff_toNat_lt

instance : UnsignedOrder UInt64 where
  lt_iff _ _ := UInt64.lt_iff_toNat_lt

end UnsignedOrder

end Proofs.Cpp
