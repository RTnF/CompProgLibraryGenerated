import Proofs.Cpp.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic

/-! Pure models for all three classes of the original monoid.hpp.
Element operations have their own contracts. In particular, floating-point
multiplication is not assumed associative, and an opaque type's default
numeric_limits value need not be a least or greatest element. -/
namespace Proofs.Cpp.MonoidMath

def mulOp {T : Type} [Mul T] (x y : T) : T := x * y
def maxOp {T : Type} [Max T] (x y : T) : T := max x y
def minOp {T : Type} [Min T] (x y : T) : T := min x y

def maxIdentity {T : Type} [NumericTraits "T" T] : T :=
  if NumericTraits.isFloatingPoint (tag := "T") (α := T) then
    if NumericTraits.hasInfinity (tag := "T") (α := T) then
      NumericTraits.negativeInfinity (tag := "T") (α := T)
    else NumericTraits.lowest (tag := "T") (α := T)
  else NumericTraits.minimum (tag := "T") (α := T)

def minIdentity {T : Type} [NumericTraits "T" T] : T :=
  if NumericTraits.isFloatingPoint (tag := "T") (α := T) then
    if NumericTraits.hasInfinity (tag := "T") (α := T) then
      NumericTraits.infinity (tag := "T") (α := T)
    else NumericTraits.maximum (tag := "T") (α := T)
  else NumericTraits.maximum (tag := "T") (α := T)

theorem mul_associative {T : Type} [Semigroup T] (x y z : T) :
    mulOp (mulOp x y) z = mulOp x (mulOp y z) := mul_assoc x y z

theorem mul_identity {T : Type} [MulOneClass T] (x : T) :
    mulOp 1 x = x ∧ mulOp x 1 = x := ⟨one_mul x, mul_one x⟩

theorem max_associative {T : Type} [LinearOrder T] (x y z : T) :
    maxOp (maxOp x y) z = maxOp x (maxOp y z) := max_assoc x y z

theorem min_associative {T : Type} [LinearOrder T] (x y z : T) :
    minOp (minOp x y) z = minOp x (minOp y z) := min_assoc x y z

theorem max_identity {T : Type} [LinearOrder T] [NumericTraits "T" T]
    (x : T) (hx : maxIdentity ≤ x) :
    maxOp maxIdentity x = x ∧ maxOp x maxIdentity = x :=
  ⟨max_eq_right hx, max_eq_left hx⟩

theorem min_identity {T : Type} [LinearOrder T] [NumericTraits "T" T]
    (x : T) (hx : x ≤ minIdentity) :
    minOp minIdentity x = x ∧ minOp x minIdentity = x :=
  ⟨min_eq_right hx, min_eq_left hx⟩

theorem max_value {T : Type} [LinearOrder T] (x y : T) :
    (maxOp x y = x ∨ maxOp x y = y) ∧ x ≤ maxOp x y ∧ y ≤ maxOp x y := by
  refine ⟨?_, le_max_left x y, le_max_right x y⟩
  rcases le_total x y with h | h
  · exact Or.inr (max_eq_right h)
  · exact Or.inl (max_eq_left h)

theorem min_value {T : Type} [LinearOrder T] (x y : T) :
    (minOp x y = x ∨ minOp x y = y) ∧ minOp x y ≤ x ∧ minOp x y ≤ y := by
  refine ⟨?_, min_le_left x y, min_le_right x y⟩
  rcases le_total x y with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

theorem max_bounds {T : Type} [LinearOrder T] (lo hi x y : T)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) :
    lo ≤ maxOp x y ∧ maxOp x y ≤ hi :=
  ⟨le_trans hx.1 (le_max_left x y), max_le hx.2 hy.2⟩

theorem min_bounds {T : Type} [LinearOrder T] (lo hi x y : T)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) :
    lo ≤ minOp x y ∧ minOp x y ≤ hi :=
  ⟨le_min hx.1 hy.1, le_trans (min_le_left x y) hx.2⟩

/-- Fixed envelopes of values computed or copied by these scalar operations.
They count model scalar cells; the representation and cost of T, heap allocation,
object lifetime and Lean's execution stack are outside this measure. -/
inductive Frame (T : Type) where
  | copy (value : T)
  | identity (value : T)
  | binary (left right result : T)

def Frame.values {T : Type} : Frame T → List T
  | .copy value => [value, value]
  | .identity value => [value, value]
  | .binary left right result => [left, right, result, result]

theorem frame_cells {T : Type} (frame : Frame T) : frame.values.length ≤ 4 := by
  cases frame <;> simp [Frame.values]

/-- A default constructor nests a factory and a value constructor. Retaining
both two-cell result frames also bounds every shallower entry point. -/
def peakCells {T : Type} (frame : Frame T) (calleeCells : Nat) : Nat :=
  frame.values.length + calleeCells

theorem all_operations_space {T : Type} (frame : Frame T) (calleeCells : Nat)
    (hc : calleeCells ≤ 4) : peakCells frame calleeCells ≤ 8 := by
  have h := frame_cells frame
  unfold peakCells
  omega

end Proofs.Cpp.MonoidMath
