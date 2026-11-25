import Proofs.Cpp.Gen.EdgeFlow

/-! # `FlowEdge<T>` (library/graph/edge_flow.hpp)

An edge `from -> to` of a flow network with the index `rev` of its reverse edge, a capacity, a cost and an id.
Every specialization `FlowEdge<T>` has its own counter `next_id` (the model state `cp.GlobalState_… T tag`, the
tag being the C++ spelling of `T`). The counter starts at 0; each construction takes its value as the id and
increments it. The capacity is `max cap 0` (0 when not given); the cost is 0 when not given. One step each.
`operator<<` is outside the model (docs/translation.md). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.EdgeFlow

abbrev Counter (T : Type) (tag : String) := cp.GlobalState_5be60fe7c0622cd9 T tag

/-- The counter starts at 0. -/
theorem init_globals_spec {T : Type} {tag : String} (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.initializeGlobals_5be60fe7c0622cd9 (T := T) (cppStaticSpecialization := tag))
    ⦃⇓ g c => ⌜g.FlowEdge_next_id = 0 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.initializeGlobals_5be60fe7c0622cd9]
  all_goals simp_all +zetaDelta

/-- `FlowEdge(from, to, rev, cap, cost)`. -/
theorem init_cap_cost_spec {T : Type} [Zero T] [Max T] {tag : String} (u v r : Int) (cap cost : T)
    (g : Counter T tag) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.FlowEdge.init_int_int_int_T_T u v r cap cost g
    ⦃⇓ x c => ⌜x.1 = ⟨u, v, r, g.FlowEdge_next_id, max cap 0, cost⟩ ∧
      x.2.FlowEdge_next_id = g.FlowEdge_next_id + 1 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.FlowEdge.init_int_int_int_T_T]
  all_goals simp_all +zetaDelta

/-- `FlowEdge(from, to, rev, cap)`: the cost is 0. -/
theorem init_cap_spec {T : Type} [Zero T] [Max T] {tag : String} (u v r : Int) (cap : T)
    (g : Counter T tag) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.FlowEdge.init_int_int_int_T u v r cap g
    ⦃⇓ x c => ⌜x.1 = ⟨u, v, r, g.FlowEdge_next_id, max cap 0, 0⟩ ∧
      x.2.FlowEdge_next_id = g.FlowEdge_next_id + 1 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.FlowEdge.init_int_int_int_T]
  all_goals simp_all +zetaDelta

/-- `FlowEdge(from, to, rev)`: the capacity and the cost are 0. -/
theorem init_spec {T : Type} [Zero T] {tag : String} (u v r : Int) (g : Counter T tag) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.FlowEdge.init_int_int_int (T := T) u v r g
    ⦃⇓ x c => ⌜x.1 = ⟨u, v, r, g.FlowEdge_next_id, 0, 0⟩ ∧
      x.2.FlowEdge_next_id = g.FlowEdge_next_id + 1 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.FlowEdge.init_int_int_int]
  all_goals simp_all +zetaDelta

end Proofs.Cpp.EdgeFlow
