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

end Proofs.Cpp
