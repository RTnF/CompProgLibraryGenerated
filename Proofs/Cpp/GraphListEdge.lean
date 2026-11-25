import Proofs.Cpp.Gen.Edge
import Proofs.Cpp.Lib.DependentOperations

/-! # `Edge<T>` as the edge type of `ListGraph<Cost, E>` (library/graph/graph_list.hpp)

The instances of the dependent operations of `ListGraph` for `E = Edge<T>` (the default argument): the fields
`from`, `to`, `cost`, the shared constructor state (the id counter of `Edge<T>`, starting at 0) and the two
constructors `Edge(from, to)` and `Edge(from, to, cost)` on the argument tuples `(from, to, ())` and
`(from, to, cost)`. -/

namespace Proofs.Cpp
open Proofs.Cpp.Gen

instance {T : Type} : Field "from" (cp.Edge T) Int := ⟨fun e => e.from_⟩
instance {T : Type} : Field "to" (cp.Edge T) Int := ⟨fun e => e.to_⟩
instance {T : Type} : Field "id" (cp.Edge T) Int := ⟨fun e => e.id_⟩
instance {T : Type} : Field "cost" (cp.Edge T) T := ⟨fun e => e.cost⟩

instance {T : Type} : ConstructState (cp.Edge T) where
  State := cp.GlobalState_0b9f55bc762329ec T "Edge"
  start := cp.initializeGlobals_0b9f55bc762329ec

instance {T : Type} [One T] : Construct (cp.Edge T) (Int × Int × Unit) where
  make a st := cp.Edge.init_int_int a.1 a.2.1 st

instance {T : Type} : Construct (cp.Edge T) (Int × Int × T) where
  make a st := cp.Edge.init_int_int_T a.1 a.2.1 a.2.2 st

end Proofs.Cpp
