import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring

/-! Pure values for the three classes in the original group.hpp.
The algebraic laws are conditional on the stated algebraic structure. In
particular, integer division does not make arbitrary nonzero integers a group.
C++ arithmetic and its intermediates must fit their types. -/
namespace Proofs.Cpp.GroupMath

def sumOp {T : Type} [Add T] (x y : T) : T := x + y
def sumInv {T : Type} [Neg T] (x : T) : T := -x
def mulOp {T : Type} [Mul T] (x y : T) : T := x * y
def mulInv {T : Type} [One T] [Div T] (x : T) : T := 1 / x

theorem sum_associative {T : Type} [AddSemigroup T] (x y z : T) :
    sumOp (sumOp x y) z = sumOp x (sumOp y z) := by
  exact add_assoc x y z

theorem sum_identity {T : Type} [AddZeroClass T] (x : T) :
    sumOp 0 x = x ∧ sumOp x 0 = x := by
  exact ⟨zero_add x, add_zero x⟩

theorem sum_inverse {T : Type} [AddGroup T] (x : T) :
    sumOp (sumInv x) x = 0 ∧ sumOp x (sumInv x) = 0 := by
  exact ⟨neg_add_cancel x, add_neg_cancel x⟩

theorem mul_associative {T : Type} [Semigroup T] (x y z : T) :
    mulOp (mulOp x y) z = mulOp x (mulOp y z) := by
  exact mul_assoc x y z

theorem mul_identity {T : Type} [MulOneClass T] (x : T) :
    mulOp 1 x = x ∧ mulOp x 1 = x := by
  exact ⟨one_mul x, mul_one x⟩

theorem mul_inverse {T : Type} [DivisionRing T] (x : T) (hx : x ≠ 0) :
    mulOp (mulInv x) x = 1 ∧ mulOp x (mulInv x) = 1 := by
  simp [mulOp, mulInv, hx]

abbrev Affine (T : Type) := T × T

def affineIdentity {T : Type} [Zero T] [One T] : Affine T := (1, 0)
def affineApply {T : Type} [Mul T] [Add T] (p : Affine T) (x : T) : T :=
  p.1 * x + p.2

/-- p is applied before q, as in the original C++ hidden friend. -/
def affineOp {T : Type} [Mul T] [Add T] (p q : Affine T) : Affine T :=
  (p.1 * q.1, p.2 * q.1 + q.2)

def affineInv {T : Type} [One T] [Div T] [Neg T] (p : Affine T) : Affine T :=
  (1 / p.1, -p.2 / p.1)

theorem affine_composition {T : Type} [CommSemiring T] (p q : Affine T) (x : T) :
    affineApply (affineOp p q) x = affineApply q (affineApply p x) := by
  dsimp [affineApply, affineOp]
  ring

theorem affine_associative {T : Type} [Semiring T] (p q r : Affine T) :
    affineOp (affineOp p q) r = affineOp p (affineOp q r) := by
  apply Prod.ext
  · exact mul_assoc _ _ _
  · simp [affineOp, add_mul, mul_assoc, add_assoc]

theorem affine_identity {T : Type} [Semiring T] (p : Affine T) :
    affineOp affineIdentity p = p ∧ affineOp p affineIdentity = p := by
  simp [affineOp, affineIdentity]

theorem affine_inverse {T : Type} [Field T] (p : Affine T) (ha : p.1 ≠ 0) :
    affineOp (affineInv p) p = affineIdentity ∧
    affineOp p (affineInv p) = affineIdentity := by
  constructor <;> apply Prod.ext <;>
    simp [affineOp, affineInv, affineIdentity, div_eq_mul_inv, ha]

/-- Integer C++ uses truncating division, including when the result is not an
inverse. The affine constructor deliberately allows a returned slope of zero. -/
def affineIntInv (p : Affine Int) : Affine Int :=
  (Int.tdiv 1 p.1, Int.tdiv (-p.2) p.1)

theorem affine_integer_inverse_unit (a b : Int) (ha : a = 1 ∨ a = -1) :
    affineOp (affineIntInv (a, b)) (a, b) = affineIdentity ∧
    affineOp (a, b) (affineIntInv (a, b)) = affineIdentity := by
  rcases ha with ha | ha <;> subst a <;>
    simp [affineOp, affineIntInv, affineIdentity]

/-- A conservative scalar-cell envelope, including future intermediate values.
No loop history, heap allocation or object-lifetime trace is retained. -/
def affineEnvelope {T : Type} [Mul T] [Add T] (p q : Affine T) : List T :=
  [p.1, p.2, q.1, q.2, p.1 * q.1, p.2 * q.1,
   p.2 * q.1 + q.2, (affineOp p q).1, (affineOp p q).2]

theorem affine_envelope_cells {T : Type} [Mul T] [Add T] (p q : Affine T) :
    (affineEnvelope p q).length = 9 := by
  rfl

/-- Envelopes of the pure operations. Computed values are explicit so no
algebraic laws or element-size assumptions are needed to count scalar cells. -/
inductive Frame (T : Type) where
  | copy (x : T)
  | unary (x result : T)
  | binary (x y result : T)
  | affineCopy (p : Affine T)
  | apply (p : Affine T) (x product result : T)
  | inverse (p : Affine T) (negative inverseA inverseB : T)
  | compose (p q : Affine T) (productA productB : T) (result : Affine T)

def Frame.values {T : Type} : Frame T → List T
  | .copy x => [x, x]
  | .unary x r => [x, r, r]
  | .binary x y r => [x, y, r, r]
  | .affineCopy p => [p.1, p.2, p.1, p.2]
  | .apply p x product r => [p.1, p.2, x, product, r]
  | .inverse p negative a b => [p.1, p.2, negative, a, b, a, b]
  | .compose p q a b r => [p.1, p.2, q.1, q.2, a, b, r.1, r.2, r.1, r.2]

theorem frame_cells {T : Type} (frame : Frame T) : frame.values.length ≤ 10 := by
  cases frame <;> simp [Frame.values]

/-- A default constructor has at most two nested calls (factory and value
constructor), with at most four scalar input/result fields in each. Keeping
both frames simultaneously also bounds the shallower wrappers. -/
def peakCells {T : Type} (frame : Frame T) (calleeCells : Nat) : Nat :=
  frame.values.length + calleeCells

theorem all_operations_space {T : Type} (frame : Frame T) (calleeCells : Nat)
    (hc : calleeCells ≤ 8) : peakCells frame calleeCells ≤ 18 := by
  have h := frame_cells frame
  unfold peakCells
  omega

end Proofs.Cpp.GroupMath
