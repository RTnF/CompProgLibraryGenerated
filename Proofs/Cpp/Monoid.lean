import Proofs.Cpp.Gen.Monoid
import Proofs.Cpp.Lib.MonoidMath

namespace Proofs.Cpp.Monoid
open Proofs.Cpp.Gen MonoidMath
theorem mul_construct {T : Type} (x : T) (t : Nat) :
  (cp.MonoidMul.init_T x).run t = some ((⟨x⟩ : cp.MonoidMul T), t + 1) := by rfl

theorem mul_e {T : Type} [One T] (t : Nat) :
  (cp.MonoidMul.e (T := T)).run t = some ((⟨(1 : T)⟩ : cp.MonoidMul T), t + 2) := by
  rfl

theorem mul_init_0 {T : Type} [One T] (t : Nat) :
  (cp.MonoidMul.init_0 (T := T)).run t = some ((⟨(1 : T)⟩ : cp.MonoidMul T), t + 3) := by
  rfl

theorem mul_hidden {T : Type} [Mul T] (x y : T) (t : Nat) :
  (cp.op_MonoidMul_MonoidMul_hidden (⟨x⟩ : cp.MonoidMul T) ⟨y⟩).run t =
    some ((⟨mulOp x y⟩ : cp.MonoidMul T), t + 2) := by rfl

theorem mul_qualified {T : Type} [Mul T] (x y : T) (t : Nat) :
  (cp.op_MonoidMul_MonoidMul_qualified (⟨x⟩ : cp.MonoidMul T) ⟨y⟩).run t =
    some ((⟨mulOp x y⟩ : cp.MonoidMul T), t + 2) := by rfl

theorem max_construct {T : Type} (x : T) (t : Nat) :
  (cp.MonoidMax.init_T x).run t = some ((⟨x⟩ : cp.MonoidMax T), t + 1) := by rfl

theorem max_e {T : Type} [NumericTraits "T" T] (t : Nat) :
  (cp.MonoidMax.e (T := T)).run t = some ((⟨(maxIdentity (T := T))⟩ : cp.MonoidMax T), t + 2) := by
  cases hf : NumericTraits.isFloatingPoint (tag := "T") (α := T) <;>
    simp [cp.MonoidMax.e, cp.MonoidMax.init_T, Cpp.tick,
      StateT.run, modify, maxIdentity, hf] <;> rfl

theorem max_init_0 {T : Type} [NumericTraits "T" T] (t : Nat) :
  (cp.MonoidMax.init_0 (T := T)).run t = some ((⟨(maxIdentity (T := T))⟩ : cp.MonoidMax T), t + 3) := by
  cases hf : NumericTraits.isFloatingPoint (tag := "T") (α := T) <;>
    simp [cp.MonoidMax.init_0, cp.MonoidMax.e, cp.MonoidMax.init_T, Cpp.tick,
      StateT.run, modify, maxIdentity, hf] <;> rfl

theorem max_hidden {T : Type} [Max T] (x y : T) (t : Nat) :
  (cp.op_MonoidMax_MonoidMax_hidden (⟨x⟩ : cp.MonoidMax T) ⟨y⟩).run t =
    some ((⟨maxOp x y⟩ : cp.MonoidMax T), t + 2) := by rfl

theorem max_qualified {T : Type} [Max T] (x y : T) (t : Nat) :
  (cp.op_MonoidMax_MonoidMax_qualified (⟨x⟩ : cp.MonoidMax T) ⟨y⟩).run t =
    some ((⟨maxOp x y⟩ : cp.MonoidMax T), t + 2) := by rfl

theorem min_construct {T : Type} (x : T) (t : Nat) :
  (cp.MonoidMin.init_T x).run t = some ((⟨x⟩ : cp.MonoidMin T), t + 1) := by rfl

theorem min_e {T : Type} [NumericTraits "T" T] (t : Nat) :
  (cp.MonoidMin.e (T := T)).run t = some ((⟨(minIdentity (T := T))⟩ : cp.MonoidMin T), t + 2) := by
  cases hf : NumericTraits.isFloatingPoint (tag := "T") (α := T) <;>
    simp [cp.MonoidMin.e, cp.MonoidMin.init_T, Cpp.tick,
      StateT.run, modify, minIdentity, hf] <;> rfl

theorem min_init_0 {T : Type} [NumericTraits "T" T] (t : Nat) :
  (cp.MonoidMin.init_0 (T := T)).run t = some ((⟨(minIdentity (T := T))⟩ : cp.MonoidMin T), t + 3) := by
  cases hf : NumericTraits.isFloatingPoint (tag := "T") (α := T) <;>
    simp [cp.MonoidMin.init_0, cp.MonoidMin.e, cp.MonoidMin.init_T, Cpp.tick,
      StateT.run, modify, minIdentity, hf] <;> rfl

theorem min_hidden {T : Type} [Min T] (x y : T) (t : Nat) :
  (cp.op_MonoidMin_MonoidMin_hidden (⟨x⟩ : cp.MonoidMin T) ⟨y⟩).run t =
    some ((⟨minOp x y⟩ : cp.MonoidMin T), t + 2) := by rfl

theorem min_qualified {T : Type} [Min T] (x y : T) (t : Nat) :
  (cp.op_MonoidMin_MonoidMin_qualified (⟨x⟩ : cp.MonoidMin T) ⟨y⟩).run t =
    some ((⟨minOp x y⟩ : cp.MonoidMin T), t + 2) := by rfl

theorem model_mul_associative {T : Type} [Semigroup T] (x y z : T) :
    mulOp (mulOp x y) z = mulOp x (mulOp y z) := by
  exact MonoidMath.mul_associative x y z

theorem model_mul_identity {T : Type} [MulOneClass T] (x : T) :
    mulOp 1 x = x ∧ mulOp x 1 = x := by
  exact MonoidMath.mul_identity x

theorem model_max_associative {T : Type} [LinearOrder T] (x y z : T) :
    maxOp (maxOp x y) z = maxOp x (maxOp y z) := by
  exact MonoidMath.max_associative x y z

theorem model_min_associative {T : Type} [LinearOrder T] (x y z : T) :
    minOp (minOp x y) z = minOp x (minOp y z) := by
  exact MonoidMath.min_associative x y z

theorem model_max_identity {T : Type} [LinearOrder T] [NumericTraits "T" T]
    (x : T) (hx : maxIdentity ≤ x) :
    maxOp maxIdentity x = x ∧ maxOp x maxIdentity = x := by
  exact MonoidMath.max_identity x hx

theorem model_min_identity {T : Type} [LinearOrder T] [NumericTraits "T" T]
    (x : T) (hx : x ≤ minIdentity) :
    minOp minIdentity x = x ∧ minOp x minIdentity = x := by
  exact MonoidMath.min_identity x hx

theorem model_max_value {T : Type} [LinearOrder T] (x y : T) :
    (maxOp x y = x ∨ maxOp x y = y) ∧ x ≤ maxOp x y ∧ y ≤ maxOp x y := by
  exact MonoidMath.max_value x y

theorem model_min_value {T : Type} [LinearOrder T] (x y : T) :
    (minOp x y = x ∨ minOp x y = y) ∧ minOp x y ≤ x ∧ minOp x y ≤ y := by
  exact MonoidMath.min_value x y

theorem model_max_bounds {T : Type} [LinearOrder T] (lo hi x y : T)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) :
    lo ≤ maxOp x y ∧ maxOp x y ≤ hi := by
  exact MonoidMath.max_bounds lo hi x y hx hy

theorem model_min_bounds {T : Type} [LinearOrder T] (lo hi x y : T)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) :
    lo ≤ minOp x y ∧ minOp x y ≤ hi := by
  exact MonoidMath.min_bounds lo hi x y hx hy

theorem model_frame_cells {T : Type} (frame : Frame T) : frame.values.length ≤ 4 := by
  exact MonoidMath.frame_cells frame

theorem model_all_operations_space {T : Type} (frame : Frame T) (calleeCells : Nat)
    (hc : calleeCells ≤ 4) : peakCells frame calleeCells ≤ 8 := by
  exact MonoidMath.all_operations_space frame calleeCells hc

end Proofs.Cpp.Monoid
