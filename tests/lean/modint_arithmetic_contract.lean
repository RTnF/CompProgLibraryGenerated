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
