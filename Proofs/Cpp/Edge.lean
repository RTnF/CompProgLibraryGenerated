import Proofs.Cpp.Gen.Edge

/-! # `Edge<T>` (library/graph/edge.hpp)

An edge `from -> to` with a cost and an id. Every specialization `Edge<T>` has its own counter `next_id`
(the model state `cp.GlobalState_… T tag`, where the tag is the C++ spelling of `T`, so `Edge<int>` and
`Edge<long long>` keep separate counters although both costs are `Int` in the model). The counter starts at 0
and each construction takes its current value as the id and increments it. One step each.
`operator<<` is outside the model (docs/translation.md). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.Edge

abbrev Counter (T : Type) (tag : String) := cp.GlobalState_0b9f55bc762329ec T tag

/-- The counter starts at 0. -/
theorem init_globals_spec {T : Type} {tag : String} (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.initializeGlobals_0b9f55bc762329ec (T := T) (cppStaticSpecialization := tag))
    ⦃⇓ g c => ⌜g.Edge_next_id = 0 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.initializeGlobals_0b9f55bc762329ec]
  all_goals simp_all +zetaDelta

/-- `Edge(from, to, cost)`: the fields are the arguments, the id is the counter, which is incremented. -/
theorem init_cost_spec {T : Type} {tag : String} (u v : Int) (cost : T) (g : Counter T tag) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Edge.init_int_int_T u v cost g
    ⦃⇓ r c => ⌜r.1 = ⟨u, v, g.Edge_next_id, cost⟩ ∧ r.2.Edge_next_id = g.Edge_next_id + 1 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Edge.init_int_int_T]
  all_goals simp_all +zetaDelta

/-- `Edge(from, to)`: the cost is `1`. -/
theorem init_unit_spec {T : Type} [One T] {tag : String} (u v : Int) (g : Counter T tag) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.Edge.init_int_int (T := T) u v g
    ⦃⇓ r c => ⌜r.1 = ⟨u, v, g.Edge_next_id, (1 : T)⟩ ∧ r.2.Edge_next_id = g.Edge_next_id + 1 ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.Edge.init_int_int]
  all_goals simp_all +zetaDelta

end Proofs.Cpp.Edge
