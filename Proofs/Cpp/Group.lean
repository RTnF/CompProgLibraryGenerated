import Proofs.Cpp.Gen.Group
import Proofs.Cpp.Lib.GroupMath

namespace Proofs.Cpp.Group
open Proofs.Cpp.Gen
open GroupMath

theorem sum_construct {T : Type} (x : T) (t : Nat) :
    (cp.GroupSum.init_T x).run t = some ((⟨x⟩ : cp.GroupSum T), t + 1) := by
  rfl

theorem sum_identity {T : Type} [Zero T] (t : Nat) :
    (cp.GroupSum.e (T := T)).run t = some ((⟨0⟩ : cp.GroupSum T), t + 2) := by
  rfl

theorem sum_default {T : Type} [Zero T] (t : Nat) :
    (cp.GroupSum.init_0 (T := T)).run t = some ((⟨0⟩ : cp.GroupSum T), t + 3) := by
  rfl

theorem sum_value {T : Type} (x : T) (t : Nat) :
    (cp.GroupSum.x (⟨x⟩ : cp.GroupSum T)).run t = some (x, t + 1) := by
  rfl

theorem sum_inverse {T : Type} [Neg T] (x : T) (t : Nat) :
    (cp.GroupSum.inv (⟨x⟩ : cp.GroupSum T)).run t = some ((⟨GroupMath.sumInv x⟩ : cp.GroupSum T), t + 2) := by
  rfl

theorem sum_op_hidden {T : Type} [Add T] (x y : T) (t : Nat) :
    (cp.op_GroupSum_GroupSum_hidden (⟨x⟩ : cp.GroupSum T) ⟨y⟩).run t = some ((⟨GroupMath.sumOp x y⟩ : cp.GroupSum T), t + 2) := by
  rfl

theorem sum_op_qualified {T : Type} [Add T] (x y : T) (t : Nat) :
    (cp.op_GroupSum_GroupSum_qualified (⟨x⟩ : cp.GroupSum T) ⟨y⟩).run t = some ((⟨GroupMath.sumOp x y⟩ : cp.GroupSum T), t + 2) := by
  rfl

theorem mul_construct {T : Type} [Zero T] [DecidableEq T] (x : T) (hx : x ≠ 0) (t : Nat) :
    (cp.GroupMul.init_T x).run t = some ((⟨x⟩ : cp.GroupMul T), t + 1) := by
  simp [cp.GroupMul.init_T, Proofs.Cpp.tick, Proofs.Cpp.check, hx, StateT.run, modify]
  rfl

theorem mul_identity {T : Type} [Zero T] [One T] [DecidableEq T] (h : (1 : T) ≠ 0) (t : Nat) :
    (cp.GroupMul.e (T := T)).run t = some ((⟨1⟩ : cp.GroupMul T), t + 2) := by
  simp [cp.GroupMul.e, cp.GroupMul.init_T, Proofs.Cpp.tick, Proofs.Cpp.check, h, StateT.run, modify]
  rfl

theorem mul_default {T : Type} [Zero T] [One T] [DecidableEq T] (h : (1 : T) ≠ 0) (t : Nat) :
    (cp.GroupMul.init_0 (T := T)).run t = some ((⟨1⟩ : cp.GroupMul T), t + 3) := by
  simp [cp.GroupMul.init_0, cp.GroupMul.e, cp.GroupMul.init_T, Proofs.Cpp.tick, Proofs.Cpp.check, h, StateT.run, modify]
  rfl

theorem mul_inverse {T : Type} [Zero T] [One T] [Div T] [DecidableEq T] (x : T) (h : 1 / x ≠ 0) (t : Nat) :
    (cp.GroupMul.inv (⟨x⟩ : cp.GroupMul T)).run t = some ((⟨GroupMath.mulInv x⟩ : cp.GroupMul T), t + 2) := by
  simp [cp.GroupMul.inv, cp.GroupMul.init_T, GroupMath.mulInv, Proofs.Cpp.tick, Proofs.Cpp.check, h, StateT.run, modify]
  rfl

theorem mul_value {T : Type} (x : T) (t : Nat) :
    (cp.GroupMul.x (⟨x⟩ : cp.GroupMul T)).run t = some (x, t + 1) := by
  rfl

theorem mul_op_hidden {T : Type} [Zero T] [Mul T] [DecidableEq T] (x y : T) (h : x * y ≠ 0) (t : Nat) :
    (cp.op_GroupMul_GroupMul_hidden (⟨x⟩ : cp.GroupMul T) ⟨y⟩).run t = some ((⟨GroupMath.mulOp x y⟩ : cp.GroupMul T), t + 2) := by
  simp [cp.op_GroupMul_GroupMul_hidden, cp.GroupMul.init_T, GroupMath.mulOp, Proofs.Cpp.tick, Proofs.Cpp.check, h, StateT.run, modify]
  rfl

theorem mul_op_qualified {T : Type} [Zero T] [Mul T] [DecidableEq T] (x y : T) (h : x * y ≠ 0) (t : Nat) :
    (cp.op_GroupMul_GroupMul_qualified (⟨x⟩ : cp.GroupMul T) ⟨y⟩).run t = some ((⟨GroupMath.mulOp x y⟩ : cp.GroupMul T), t + 2) := by
  simp [cp.op_GroupMul_GroupMul_qualified, cp.GroupMul.init_T, GroupMath.mulOp, Proofs.Cpp.tick, Proofs.Cpp.check, h, StateT.run, modify]
  rfl

theorem affine_construct {T : Type} (a b : T) (t : Nat) :
    (cp.GroupAffine.init_T_T a b).run t = some ((⟨a, b⟩ : cp.GroupAffine T), t + 1) := by
  rfl

theorem affine_identity {T : Type} [Zero T] [One T] (t : Nat) :
    (cp.GroupAffine.e (T := T)).run t = some ((⟨(GroupMath.affineIdentity (T := T)).1, (GroupMath.affineIdentity (T := T)).2⟩ : cp.GroupAffine T), t + 2) := by
  rfl

theorem affine_default {T : Type} [Zero T] [One T] (t : Nat) :
    (cp.GroupAffine.init_0 (T := T)).run t = some ((⟨(GroupMath.affineIdentity (T := T)).1, (GroupMath.affineIdentity (T := T)).2⟩ : cp.GroupAffine T), t + 3) := by
  rfl

theorem affine_a {T : Type} (a b : T) (t : Nat) :
    (cp.GroupAffine.a (⟨a, b⟩ : cp.GroupAffine T)).run t = some (a, t + 1) := by
  rfl

theorem affine_b {T : Type} (a b : T) (t : Nat) :
    (cp.GroupAffine.b (⟨a, b⟩ : cp.GroupAffine T)).run t = some (b, t + 1) := by
  rfl

theorem affine_apply {T : Type} [Mul T] [Add T] (a b x : T) (t : Nat) :
    (cp.GroupAffine.apply (⟨a, b⟩ : cp.GroupAffine T) x).run t = some (GroupMath.affineApply (a, b) x, t + 1) := by
  rfl

theorem affine_inverse {T : Type} [One T] [Div T] [Neg T] (a b : T) (t : Nat) :
    (cp.GroupAffine.inv (⟨a, b⟩ : cp.GroupAffine T)).run t = some ((⟨(GroupMath.affineInv (a, b)).1, (GroupMath.affineInv (a, b)).2⟩ : cp.GroupAffine T), t + 2) := by
  rfl

theorem affine_op_hidden {T : Type} [Mul T] [Add T] (a b c d : T) (t : Nat) :
    (cp.op_GroupAffine_GroupAffine_hidden (⟨a, b⟩ : cp.GroupAffine T) ⟨c, d⟩).run t = some ((⟨(GroupMath.affineOp (a, b) (c, d)).1, (GroupMath.affineOp (a, b) (c, d)).2⟩ : cp.GroupAffine T), t + 2) := by
  rfl

theorem affine_op_qualified {T : Type} [Mul T] [Add T] (a b c d : T) (t : Nat) :
    (cp.op_GroupAffine_GroupAffine_qualified (⟨a, b⟩ : cp.GroupAffine T) ⟨c, d⟩).run t = some ((⟨(GroupMath.affineOp (a, b) (c, d)).1, (GroupMath.affineOp (a, b) (c, d)).2⟩ : cp.GroupAffine T), t + 2) := by
  rfl

theorem affine_integer_inverse (a b : Int) (t : Nat) :
    (@cp.GroupAffine.inv Int inferInstance inferInstance (⟨Int.tdiv⟩ : Div Int)
      (⟨a, b⟩ : cp.GroupAffine Int)).run t =
      some ((⟨(GroupMath.affineIntInv (a, b)).1,
        (GroupMath.affineIntInv (a, b)).2⟩ : cp.GroupAffine Int), t + 2) := by
  rfl

theorem model_sum_associative {T : Type} [AddSemigroup T] (x y z : T) :
    sumOp (sumOp x y) z = sumOp x (sumOp y z) := by
  exact GroupMath.sum_associative x y z

theorem model_sum_identity {T : Type} [AddZeroClass T] (x : T) :
    sumOp 0 x = x ∧ sumOp x 0 = x := by
  exact GroupMath.sum_identity x

theorem model_sum_inverse {T : Type} [AddGroup T] (x : T) :
    sumOp (sumInv x) x = 0 ∧ sumOp x (sumInv x) = 0 := by
  exact GroupMath.sum_inverse x

theorem model_mul_associative {T : Type} [Semigroup T] (x y z : T) :
    mulOp (mulOp x y) z = mulOp x (mulOp y z) := by
  exact GroupMath.mul_associative x y z

theorem model_mul_identity {T : Type} [MulOneClass T] (x : T) :
    mulOp 1 x = x ∧ mulOp x 1 = x := by
  exact GroupMath.mul_identity x

theorem model_mul_inverse {T : Type} [DivisionRing T] (x : T) (hx : x ≠ 0) :
    mulOp (mulInv x) x = 1 ∧ mulOp x (mulInv x) = 1 := by
  exact GroupMath.mul_inverse x hx

theorem model_affine_composition {T : Type} [CommSemiring T] (p q : Affine T) (x : T) :
    affineApply (affineOp p q) x = affineApply q (affineApply p x) := by
  exact GroupMath.affine_composition p q x

theorem model_affine_associative {T : Type} [Semiring T] (p q r : Affine T) :
    affineOp (affineOp p q) r = affineOp p (affineOp q r) := by
  exact GroupMath.affine_associative p q r

theorem model_affine_identity {T : Type} [Semiring T] (p : Affine T) :
    affineOp affineIdentity p = p ∧ affineOp p affineIdentity = p := by
  exact GroupMath.affine_identity p

theorem model_affine_inverse {T : Type} [Field T] (p : Affine T) (ha : p.1 ≠ 0) :
    affineOp (affineInv p) p = affineIdentity ∧
    affineOp p (affineInv p) = affineIdentity := by
  exact GroupMath.affine_inverse p ha

theorem model_affine_integer_inverse_unit (a b : Int) (ha : a = 1 ∨ a = -1) :
    affineOp (affineIntInv (a, b)) (a, b) = affineIdentity ∧
    affineOp (a, b) (affineIntInv (a, b)) = affineIdentity := by
  exact GroupMath.affine_integer_inverse_unit a b ha

theorem model_all_operations_space {T : Type} (frame : Frame T) (calleeCells : Nat)
    (hc : calleeCells ≤ 8) : peakCells frame calleeCells ≤ 18 := by
  exact GroupMath.all_operations_space frame calleeCells hc

end Proofs.Cpp.Group
