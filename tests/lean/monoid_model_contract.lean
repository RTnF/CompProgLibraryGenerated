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

end Proofs.Cpp.Monoid
