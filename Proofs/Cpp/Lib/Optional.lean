import Proofs.Cpp.Prelude

namespace Proofs.Cpp

def optionalValue {T : Type} (value : Option T) : M T :=
  match value with
  | some item => pure item
  | none => fun _ => none

end Proofs.Cpp
