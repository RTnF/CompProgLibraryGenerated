import Proofs.Cpp.Gen.MonoidLazy
import Proofs.Cpp.Lib.Basic
import Proofs.Cpp.Lib.MonoidMath



open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.MonoidLazy

theorem add_extrema_apply_run {T M : Type}
    [ReadField "x" M] [AddResult (ReadField.Value "x" M) T]
    [Conv (AddResult.Value (ReadField.Value "x" M) T) M]
    (update : cp.RangeAddRangeMaxMin_RangeAdd T) (x : M) (clock : Nat) :
    (cp.RangeAddRangeMaxMin_RangeAdd.apply update x).run clock =
      some ((Conv.conv (AddResult.add (ReadField.read (member := "x") x) update.v), update), clock + 1) := by
  cases update
  rfl

theorem set_extrema_apply_run {T M : Type} [ConditionalResult M T]
    [Conv (ConditionalResult.Value M T) M]
    (update : cp.RangeSetRangeMaxMin_RangeSet T) (x : M) (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeSet.apply update x).run clock =
      some ((Conv.conv (if update.noop then ConditionalResult.left (Right := T) x
                       else ConditionalResult.right (Left := M) update.v), update), clock + 1) := by
  cases update
  rfl

theorem add_sum_apply_run {T : Type} [MulResult Int T]
    [AddResult T (MulResult.Value Int T)] [Conv (AddResult.Value T (MulResult.Value Int T)) T]
    (update : cp.RangeAddRangeSum_RangeAdd T) (x : cp.RangeAddRangeSum_RangeSum T)
    (clock : Nat) :
    (cp.RangeAddRangeSum_RangeAdd.apply update x).run clock =
      some ((⟨Conv.conv (AddResult.add x.x (MulResult.mul x.size_ update.v)), x.size_⟩, update), clock + 2) := by
  cases update
  rfl

theorem set_sum_apply_run {T : Type} [MulResult T Int] [AssignResult T (MulResult.Value T Int)]
    (update : cp.RangeSetRangeSum_RangeSet T) (x : cp.RangeSetRangeSum_RangeSum T)
    (clock : Nat) :
    (cp.RangeSetRangeSum_RangeSet.apply update x).run clock =
      some (((if update.noop then x else
          ⟨AssignResult.assign x.x (MulResult.mul update.v x.size_), x.size_⟩), update), clock + 1) := by
  obtain ⟨v, noop⟩ := update
  cases noop <;> cases x <;> rfl

theorem set_compose_run {T : Type} (f g : cp.RangeSetRangeMaxMin_RangeSet T) (clock : Nat) :
    (cp.compose_RangeSetRangeMaxMin_RangeSet_RangeSetRangeMaxMin_RangeSet f g).run clock =
      some ((if f.noop then g else f), clock + 1) := rfl

theorem add_compose_run {T : Type} [Add T] (f g : cp.RangeAddRangeMaxMin_RangeAdd T) (clock : Nat) :
    (cp.compose_RangeAddRangeMaxMin_RangeAdd_RangeAddRangeMaxMin_RangeAdd f g).run clock =
      some (⟨f.v + g.v⟩, clock + 2) := rfl

end Proofs.Cpp.MonoidLazy


open Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.MonoidMath

namespace Proofs.Cpp.MonoidLazy

theorem add_max_identity_run {T : Type} [NumericTraits "T" T] (clock : Nat) :
    (cp.RangeAddRangeMaxMin_RangeMax.e (T := T)).run clock =
      some ((⟨maxIdentity (T := T)⟩ : cp.RangeAddRangeMaxMin_RangeMax T), clock + 2) := by
  cases hf : NumericTraits.isFloatingPoint (tag := "T") (α := T) <;>
    simp [cp.RangeAddRangeMaxMin_RangeMax.e, cp.RangeAddRangeMaxMin_RangeMax.init_T, tick, StateT.run, modify,
      maxIdentity, hf] <;> rfl

theorem add_max_op_run {T : Type} [Max T] (a b : cp.RangeAddRangeMaxMin_RangeMax T) (clock : Nat) :
    (cp.op_RangeAddRangeMaxMin_RangeMax_RangeAddRangeMaxMin_RangeMax a b).run clock =
      some (⟨maxOp a.x b.x⟩, clock + 2) := rfl

theorem add_min_identity_run {T : Type} [NumericTraits "T" T] (clock : Nat) :
    (cp.RangeAddRangeMaxMin_RangeMin.e (T := T)).run clock =
      some ((⟨minIdentity (T := T)⟩ : cp.RangeAddRangeMaxMin_RangeMin T), clock + 2) := by
  cases hf : NumericTraits.isFloatingPoint (tag := "T") (α := T) <;>
    simp [cp.RangeAddRangeMaxMin_RangeMin.e, cp.RangeAddRangeMaxMin_RangeMin.init_T, tick, StateT.run, modify,
      minIdentity, hf] <;> rfl

theorem add_min_op_run {T : Type} [Min T] (a b : cp.RangeAddRangeMaxMin_RangeMin T) (clock : Nat) :
    (cp.op_RangeAddRangeMaxMin_RangeMin_RangeAddRangeMaxMin_RangeMin a b).run clock =
      some (⟨minOp a.x b.x⟩, clock + 2) := rfl

theorem set_max_identity_run {T : Type} [NumericTraits "T" T] (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeMax.e (T := T)).run clock =
      some ((⟨maxIdentity (T := T)⟩ : cp.RangeSetRangeMaxMin_RangeMax T), clock + 2) := by
  cases hf : NumericTraits.isFloatingPoint (tag := "T") (α := T) <;>
    simp [cp.RangeSetRangeMaxMin_RangeMax.e, cp.RangeSetRangeMaxMin_RangeMax.init_T, tick, StateT.run, modify,
      maxIdentity, hf] <;> rfl

theorem set_max_op_run {T : Type} [Max T] (a b : cp.RangeSetRangeMaxMin_RangeMax T) (clock : Nat) :
    (cp.op_RangeSetRangeMaxMin_RangeMax_RangeSetRangeMaxMin_RangeMax a b).run clock =
      some (⟨maxOp a.x b.x⟩, clock + 2) := rfl

theorem set_min_identity_run {T : Type} [NumericTraits "T" T] (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeMin.e (T := T)).run clock =
      some ((⟨minIdentity (T := T)⟩ : cp.RangeSetRangeMaxMin_RangeMin T), clock + 2) := by
  cases hf : NumericTraits.isFloatingPoint (tag := "T") (α := T) <;>
    simp [cp.RangeSetRangeMaxMin_RangeMin.e, cp.RangeSetRangeMaxMin_RangeMin.init_T, tick, StateT.run, modify,
      minIdentity, hf] <;> rfl

theorem set_min_op_run {T : Type} [Min T] (a b : cp.RangeSetRangeMaxMin_RangeMin T) (clock : Nat) :
    (cp.op_RangeSetRangeMaxMin_RangeMin_RangeSetRangeMaxMin_RangeMin a b).run clock =
      some (⟨minOp a.x b.x⟩, clock + 2) := rfl

end Proofs.Cpp.MonoidLazy

namespace Proofs.Cpp.MonoidLazy

def combineSum {T : Type} [Add T] (left right : T × Int) : T × Int :=
  (left.1 + right.1, left.2 + right.2)

def addToSum {T : Type} [IntCast T] [Add T] [Mul T] (increment : T) (x : T × Int) : T × Int :=
  (x.1 + (x.2 : T) * increment, x.2)

def setSum {T : Type} [IntCast T] [Mul T] (value : Option T) (x : T × Int) : T × Int :=
  match value with
  | none => x
  | some v => (v * (x.2 : T), x.2)

theorem combine_sum_assoc {T : Type} [AddSemigroup T] (a b c : T × Int) :
    combineSum (combineSum a b) c = combineSum a (combineSum b c) := by
  simp [combineSum, add_assoc]

theorem add_sum_combine {T : Type} [Ring T] (v : T) (x y : T × Int) :
    addToSum v (combineSum x y) = combineSum (addToSum v x) (addToSum v y) := by
  simp only [addToSum, combineSum, Int.cast_add]
  congr 1
  rw [add_mul]
  ac_rfl

theorem add_sum_compose {T : Type} [Ring T] (f g : T) (x : T × Int) :
    addToSum (f + g) x = addToSum f (addToSum g x) := by
  simp only [addToSum]
  congr 1
  rw [mul_add]
  ac_rfl

theorem set_sum_combine {T : Type} [Ring T] (v : Option T) (x y : T × Int) :
    setSum v (combineSum x y) = combineSum (setSum v x) (setSum v y) := by
  cases v <;> simp [setSum, combineSum, Int.cast_add, mul_add]

theorem set_sum_compose {T : Type} [IntCast T] [Mul T] (f g : Option T) (x : T × Int) :
    setSum (f.or g) x = setSum f (setSum g x) := by
  cases f <;> cases g <;> rfl

end Proofs.Cpp.MonoidLazy

open Proofs.Cpp Proofs.Cpp.Gen



open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.MonoidLazy

theorem legacy_sum_ctor {T : Type} (x : T) (n : Int) (clock : Nat) :
    (cp.RangeSum.init_T_int x n).run clock = some (⟨x, n⟩, clock + 1) := rfl

theorem legacy_sum_zero {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeSum.init_0 (T := T)).run clock = some (⟨0, 0⟩, clock + 1) := rfl

theorem legacy_sum_op {T : Type} [Add T] (a b : cp.RangeSum T) (clock : Nat) :
    (cp.op_RangeSum_RangeSum a b).run clock =
      some (⟨a.x + b.x, a.size_ + b.size_⟩, clock + 2) := rfl

theorem legacy_add_ctor {T : Type} (v : T) (clock : Nat) :
    (cp.RangeAdd.init_T v).run clock = some (⟨v⟩, clock + 1) := rfl

theorem legacy_add_zero {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeAdd.init_0 (T := T)).run clock = some (⟨0⟩, clock + 1) := rfl

theorem legacy_add_compose {T : Type} [Add T] (f g : cp.RangeAdd T) (clock : Nat) :
    (cp.compose_RangeAdd_RangeAdd f g).run clock = some (⟨f.v + g.v⟩, clock + 2) := rfl

theorem legacy_add_extremum {T : Type} [Add T] (f : cp.RangeAdd T) (x : T) (clock : Nat) :
    (cp.RangeAdd.applyExtremum f x).run clock = some (x + f.v, clock + 1) := rfl

theorem legacy_add_sum {T : Type} [Add T] [Mul T] [IntCast T]
    (f : cp.RangeAdd T) (x : T) (count : Int) (clock : Nat) :
    (cp.RangeAdd.applySumX f x count).run clock = some (x + (count : T) * f.v, clock + 1) := rfl

theorem legacy_set_ctor {T : Type} (v : T) (clock : Nat) :
    (cp.RangeSet.init_T v).run clock = some (⟨v, false⟩, clock + 1) := rfl

theorem legacy_set_flag {T : Type} (v : T) (noop : Bool) (clock : Nat) :
    (cp.RangeSet.init_T_bool v noop).run clock = some (⟨v, noop⟩, clock + 1) := rfl

theorem legacy_set_id {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeSet.init_0 (T := T)).run clock = some (⟨0, true⟩, clock + 1) := rfl

theorem legacy_set_compose {T : Type} (f g : cp.RangeSet T) (clock : Nat) :
    (cp.compose_RangeSet_RangeSet f g).run clock =
      some ((if f.noop then g else f), clock + 2) := by
  obtain ⟨v, noop⟩ := f
  cases noop <;> cases g <;> rfl

theorem legacy_set_extremum {T : Type} (f : cp.RangeSet T) (x : T) (clock : Nat) :
    (cp.RangeSet.applyExtremum f x).run clock =
      some ((if f.noop then x else f.v), clock + 1) := by
  obtain ⟨v, noop⟩ := f
  cases noop <;> rfl

theorem legacy_set_sum {T : Type} [Mul T] [IntCast T]
    (f : cp.RangeSet T) (x : T) (count : Int) (clock : Nat) :
    (cp.RangeSet.applySumX f x count).run clock =
      some ((if f.noop then x else f.v * (count : T)), clock + 1) := by
  obtain ⟨v, noop⟩ := f
  cases noop <;> rfl

end Proofs.Cpp.MonoidLazy

open Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.MonoidMath

namespace Proofs.Cpp.MonoidLazy

theorem add_max_ctor {T : Type} (x : T) (clock : Nat) :
    (cp.RangeAddRangeMaxMin_RangeMax.init_T x).run clock = some (⟨x⟩, clock + 1) := rfl

theorem add_max_default {T : Type} [NumericTraits "T" T] (clock : Nat) :
    (cp.RangeAddRangeMaxMin_RangeMax.init_0 (T := T)).run clock =
      some (⟨maxIdentity (T := T)⟩, clock + 3) := by
  simp [cp.RangeAddRangeMaxMin_RangeMax.init_0, tick, StateT.run_bind, add_max_identity_run]

theorem add_min_ctor {T : Type} (x : T) (clock : Nat) :
    (cp.RangeAddRangeMaxMin_RangeMin.init_T x).run clock = some (⟨x⟩, clock + 1) := rfl

theorem add_min_default {T : Type} [NumericTraits "T" T] (clock : Nat) :
    (cp.RangeAddRangeMaxMin_RangeMin.init_0 (T := T)).run clock =
      some (⟨minIdentity (T := T)⟩, clock + 3) := by
  simp [cp.RangeAddRangeMaxMin_RangeMin.init_0, tick, StateT.run_bind, add_min_identity_run]

theorem set_max_ctor {T : Type} (x : T) (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeMax.init_T x).run clock = some (⟨x⟩, clock + 1) := rfl

theorem set_max_default {T : Type} [NumericTraits "T" T] (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeMax.init_0 (T := T)).run clock =
      some (⟨maxIdentity (T := T)⟩, clock + 3) := by
  simp [cp.RangeSetRangeMaxMin_RangeMax.init_0, tick, StateT.run_bind, set_max_identity_run]

theorem set_min_ctor {T : Type} (x : T) (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeMin.init_T x).run clock = some (⟨x⟩, clock + 1) := rfl

theorem set_min_default {T : Type} [NumericTraits "T" T] (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeMin.init_0 (T := T)).run clock =
      some (⟨minIdentity (T := T)⟩, clock + 3) := by
  simp [cp.RangeSetRangeMaxMin_RangeMin.init_0, tick, StateT.run_bind, set_min_identity_run]

theorem add_sum_ctor {T : Type} (x : T) (count : Int) (clock : Nat) :
    (cp.RangeAddRangeSum_RangeSum.init_T_int x count).run clock = some (⟨x, count⟩, clock + 1) := rfl

theorem add_sum_default {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeAddRangeSum_RangeSum.init_0 (T := T)).run clock = some (⟨0, 0⟩, clock + 3) := rfl

theorem add_sum_identity {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeAddRangeSum_RangeSum.e (T := T)).run clock = some (⟨0, 0⟩, clock + 2) := rfl

theorem add_sum_op {T : Type} [Add T] (a b : cp.RangeAddRangeSum_RangeSum T) (clock : Nat) :
    (cp.op_RangeAddRangeSum_RangeSum_RangeAddRangeSum_RangeSum a b).run clock =
      some (⟨a.x + b.x, a.size_ + b.size_⟩, clock + 2) := rfl

theorem set_sum_ctor {T : Type} (x : T) (count : Int) (clock : Nat) :
    (cp.RangeSetRangeSum_RangeSum.init_T_int x count).run clock = some (⟨x, count⟩, clock + 1) := rfl

theorem set_sum_default {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeSetRangeSum_RangeSum.init_0 (T := T)).run clock = some (⟨0, 0⟩, clock + 3) := rfl

theorem set_sum_identity {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeSetRangeSum_RangeSum.e (T := T)).run clock = some (⟨0, 0⟩, clock + 2) := rfl

theorem set_sum_op {T : Type} [Add T] (a b : cp.RangeSetRangeSum_RangeSum T) (clock : Nat) :
    (cp.op_RangeSetRangeSum_RangeSum_RangeSetRangeSum_RangeSum a b).run clock =
      some (⟨a.x + b.x, a.size_ + b.size_⟩, clock + 2) := rfl

theorem add_maxmin_ctor {T : Type} (v : T) (clock : Nat) :
    (cp.RangeAddRangeMaxMin_RangeAdd.init v).run clock = some (⟨v⟩, clock + 1) := rfl

theorem add_maxmin_action_identity {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeAddRangeMaxMin_RangeAdd.id_ (T := T)).run clock = some (⟨0⟩, clock + 2) := rfl

theorem set_maxmin_ctor {T : Type} (v : T) (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeSet.init_T v).run clock = some (⟨v, false⟩, clock + 1) := rfl

theorem set_maxmin_default {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeSet.init_0 (T := T)).run clock = some (⟨0, true⟩, clock + 1) := rfl

theorem set_maxmin_action_identity {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeSetRangeMaxMin_RangeSet.id_ (T := T)).run clock = some (⟨0, true⟩, clock + 2) := rfl

theorem add_sum_action_ctor {T : Type} (v : T) (clock : Nat) :
    (cp.RangeAddRangeSum_RangeAdd.init v).run clock = some (⟨v⟩, clock + 1) := rfl

theorem add_sum_action_identity {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeAddRangeSum_RangeAdd.id_ (T := T)).run clock = some (⟨0⟩, clock + 2) := rfl

theorem set_sum_action_ctor {T : Type} (v : T) (clock : Nat) :
    (cp.RangeSetRangeSum_RangeSet.init_T v).run clock = some (⟨v, false⟩, clock + 1) := rfl

theorem set_sum_action_default {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeSetRangeSum_RangeSet.init_0 (T := T)).run clock = some (⟨0, true⟩, clock + 1) := rfl

theorem set_sum_action_identity {T : Type} [Zero T] (clock : Nat) :
    (cp.RangeSetRangeSum_RangeSet.id_ (T := T)).run clock = some (⟨0, true⟩, clock + 2) := rfl

theorem add_sum_compose_run {T : Type} [Add T] (f g : cp.RangeAddRangeSum_RangeAdd T) (clock : Nat) :
    (cp.compose_RangeAddRangeSum_RangeAdd_RangeAddRangeSum_RangeAdd f g).run clock =
      some (⟨f.v + g.v⟩, clock + 2) := rfl

theorem set_sum_compose_run {T : Type} (f g : cp.RangeSetRangeSum_RangeSet T) (clock : Nat) :
    (cp.compose_RangeSetRangeSum_RangeSet_RangeSetRangeSum_RangeSet f g).run clock =
      some ((if f.noop then g else f), clock + 1) := rfl

end Proofs.Cpp.MonoidLazy

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.MonoidLazy

theorem monotone_max {T : Type} [LinearOrder T] (f : T → T)
    (hf : Monotone f) (x y : T) : f (max x y) = max (f x) (f y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (hf h)]
  · rw [max_eq_left h, max_eq_left (hf h)]

theorem monotone_min {T : Type} [LinearOrder T] (f : T → T)
    (hf : Monotone f) (x y : T) : f (min x y) = min (f x) (f y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (hf h)]
  · rw [min_eq_right h, min_eq_right (hf h)]

theorem numeric_add_composition {T : Type} [AddCommSemigroup T] (x f g : T) :
    x + (f + g) = (x + g) + f := by ac_rfl

@[instance_reducible] def ringLeftMul (T : Type) [Ring T] : MulResult Int T where
  Value := T
  mul n v := (n : T) * v

@[instance_reducible] def ringRightMul (T : Type) [Ring T] : MulResult T Int where
  Value := T
  mul v n := v * (n : T)

@[instance_reducible] def ringSumAdd (T : Type) [Ring T] :
    AddResult T (@MulResult.Value Int T (ringLeftMul T)) where
  Value := T
  add := (· + ·)

@[instance_reducible] def ringSumAssign (T : Type) [Ring T] :
    AssignResult T (@MulResult.Value T Int (ringRightMul T)) where
  assign _ value := value

theorem numeric_add_sum_run {T : Type} [Ring T] (v x : T) (size : Int) (clock : Nat) :
    (@cp.RangeAddRangeSum_RangeAdd.apply T (ringLeftMul T) (ringSumAdd T) ⟨id⟩
      ⟨v⟩ ⟨x, size⟩).run clock =
      some ((⟨(addToSum v (x, size)).1, size⟩, ⟨v⟩), clock + 2) := rfl

theorem numeric_set_sum_run {T : Type} [Ring T] (v x : T) (size : Int)
    (noop : Bool) (clock : Nat) :
    (@cp.RangeSetRangeSum_RangeSet.apply T (ringRightMul T) (ringSumAssign T)
      ⟨v, noop⟩ ⟨x, size⟩).run clock =
      some ((⟨(setSum (if noop then none else some v) (x, size)).1, size⟩, ⟨v, noop⟩), clock + 1) := by
  cases noop <;> rfl

end Proofs.Cpp.MonoidLazy
