import Proofs.Cpp.Prelude

namespace Proofs.Cpp

/-- Reading the named member of a dependent C++ record argument. -/
class ReadField (member : String) (Record : Type) where
  Value : Type
  read : Record → Value

/-- A dependent C++ addition, including its actual result type after promotions. -/
class AddResult (Left Right : Type) where
  Value : Type
  add : Left → Right → Value

/-- A dependent C++ multiplication and its promoted result type. -/
class MulResult (Left Right : Type) where
  Value : Type
  mul : Left → Right → Value

/-- Assignment to a dependent target, including overloaded assignment. -/
class AssignResult (Target Value : Type) where
  assign : Target → Value → Target

/-- The two conversions to the common type of a dependent C++ conditional. -/
class ConditionalResult (Left Right : Type) where
  Value : Type
  left : Left → Value
  right : Right → Value

/-- `T::name()`: a static member function of a class template parameter `T`, called without arguments. The
instance is the translated static member of the actual argument (docs/translation.md). -/
class StaticCall (name : String) (T R : Type) where
  call : Cpp.M R

/-- An unqualified call `name(a, b)` whose arguments depend on a template parameter: the function is found by
argument-dependent lookup on the actual argument types, so the instance is that function's translation. -/
class AdlCall2 (name : String) (A B R : Type) where
  call : A → B → Cpp.M R

/-- `f(x)` for a value `f` of a template parameter type `F` (a function object): the translation of its call
operator on the argument type `A`. -/
class Invoke1 (F A R : Type) where
  call : F → A → Cpp.M R

/-- `f.name(x)` for a value `f` of a class template parameter type `F`: the translation of the member `name` of the
actual argument on the argument type `A`. -/
class Method1 (name : String) (F A R : Type) where
  call : F → A → Cpp.M R

/-- `a << b` / `a >> b` for a value `a` of a template parameter type and an `int` shift count `b`. The instance for
the mathematical integer carrier of the signed integer types is the prelude's `Cpp.shl` / `Cpp.shr`. -/
class ShiftInt (T : Type) where
  shl : T → Int → T
  shr : T → Int → T

instance : ShiftInt Int where
  shl := Cpp.shl
  shr := Cpp.shr

/-- `x.member` for a value `x` of a class type parameter whose default argument is a known class: the member's type
`Value` is the one in that class (docs/translation.md). -/
class Field (member : String) (Record : Type) (Value : Type) where
  get : Record → Value

/-- The state that the constructors of `E` share (e.g. the id counter of `Edge<T>`; `Unit` for a class without
static data). -/
class ConstructState (E : Type) where
  State : Type
  /-- the state at program start (the static initialization) -/
  start : M State

/-- The constructor of `E` on the argument tuple `Args` (`(from, to, args...)`), with its effect on the state. -/
class Construct (E Args : Type) [ConstructState E] where
  make : Args → ConstructState.State E → M (E × ConstructState.State E)

end Proofs.Cpp
