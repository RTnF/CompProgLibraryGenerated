import Proofs.Cpp.Gen.GraphFlow

open Proofs.Cpp.Gen

namespace Proofs.Cpp

instance {T : Type} : Field "from" (cp.FlowEdge T) Int := ⟨fun e => e.from_⟩
instance {T : Type} : Field "to" (cp.FlowEdge T) Int := ⟨fun e => e.to_⟩
instance {T : Type} : Field "rev" (cp.FlowEdge T) Int := ⟨fun e => e.rev⟩
instance {T : Type} : Field "cap" (cp.FlowEdge T) T := ⟨fun e => e.cap⟩
instance {T : Type} : Field "cost" (cp.FlowEdge T) T := ⟨fun e => e.cost⟩
instance {T : Type} : WriteField "cap" (cp.FlowEdge T) T := ⟨fun e cap => { e with cap }⟩

instance {T : Type} : ConstructState (cp.FlowEdge T) where
  State := cp.GlobalState_5be60fe7c0622cd9 T "FlowEdge"
  start := cp.initializeGlobals_5be60fe7c0622cd9

instance {T : Type} [Zero T] [Max T] : Construct (cp.FlowEdge T) (Int × Int × Int × T × Unit) where
  make a st := cp.FlowEdge.init_int_int_int_T a.1 a.2.1 a.2.2.1 a.2.2.2.1 st

instance {T : Type} [Zero T] [Max T] [IntCast T] : Construct (cp.FlowEdge T) (Int × Int × Int × Int × Unit) where
  make a st := cp.FlowEdge.init_int_int_int_T a.1 a.2.1 a.2.2.1 (Int.cast a.2.2.2.1) st

instance {T : Type} [Zero T] [Max T] : Construct (cp.FlowEdge T) (Int × Int × Int × T × T × Unit) where
  make a st := cp.FlowEdge.init_int_int_int_T_T a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 st

instance {T : Type} [Zero T] [Max T] [IntCast T] : Construct (cp.FlowEdge T) (Int × Int × Int × Int × T × Unit) where
  make a st := cp.FlowEdge.init_int_int_int_T_T a.1 a.2.1 a.2.2.1 (Int.cast a.2.2.2.1) a.2.2.2.2.1 st

end Proofs.Cpp
