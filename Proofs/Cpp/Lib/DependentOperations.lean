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

end Proofs.Cpp
