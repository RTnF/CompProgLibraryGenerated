import Proofs.Cpp.Gen.TreeDistance
import Proofs.Cpp.Lib.Basic

/-! # `tree_distance` (library/tree/tree_distance.hpp)

The distance of two vertices from the costs from the root and their lowest common ancestor; one step. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeDistance

/-- `tree_distance(cost_depth, u, v, lca) = cost_depth[u] + cost_depth[v] - 2 cost_depth[lca]` in one step. With
`lca` the lowest common ancestor of `u` and `v` and `cost_depth` the cost of the path from the root, this is the cost
of the path between `u` and `v`. -/
theorem tree_distance_spec {Cost : Type} [Inhabited Cost] [IntCast Cost] [Add Cost] [Sub Cost] [Mul Cost]
    (cd : Array Cost) (u v lca : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_distance cd u v lca
    ⦃⇓ r c => ⌜r = cd[u.toNat]! + cd[v.toNat]! - cd[lca.toNat]! * ((2 : Int) : Cost) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.tree_distance]
  simp_all +zetaDelta [get]

end Proofs.Cpp.TreeDistance
