import Proofs.Math.FlowResidualMath

namespace Proofs.FlowResidual

variable {Arc Vertex : Type}

theorem Path.snoc {n : Network Arc Vertex} {s t : Vertex} {path : List Arc}
    (walk : Path n s t path) (a : Arc) (src : n.tail a = t) : Path n s (n.head a) (path ++ [a]) := by
  induction walk with
  | nil => rw [← src]; exact .cons a (.nil _)
  | cons e _ ih => exact .cons e (ih src)

/-- Final labels certify the stored predecessor edge, including its order of last relaxation. -/
structure ValidParents (n : Network Arc Vertex) (cap : Capacity Arc) (source : Vertex)
    (dist : Vertex → Option Int) (pred : Vertex → Option Arc) (last : Vertex → Nat) : Prop where
  source_distance : dist source = some 0
  predecessor : ∀ v d, v ≠ source → dist v = some d →
    ∃ a c, pred v = some a ∧ n.head a = v ∧ 0 < cap a ∧
      dist (n.tail a) = some c ∧ d = c + n.cost a ∧ last (n.tail a) < last v

def routeVertices (n : Network Arc Vertex) (sink : Vertex) (path : List Arc) : List Vertex :=
  path.map n.tail ++ [sink]

def FollowsParents (n : Network Arc Vertex) (pred : Vertex → Option Arc) (path : List Arc) : Prop :=
  ∀ a ∈ path, pred (n.head a) = some a

/-- A tight predecessor chain is a simple positive-capacity path with the recorded distance. -/
theorem predecessor_route [DecidableEq Vertex] (n : Network Arc Vertex) (cap : Capacity Arc)
    (s : Vertex) (dist : Vertex → Option Int) (pred : Vertex → Option Arc) (last : Vertex → Nat)
    (tree : ValidParents n cap s dist pred last) (v : Vertex) (d : Int) (finite : dist v = some d) :
    ∃ path, Path n s v path ∧ FollowsParents n pred path ∧ (∀ a ∈ path, 0 < cap a) ∧
      (path.map n.cost).sum = d ∧ (routeVertices n v path).Nodup ∧
      (∀ x ∈ routeVertices n v path, last x ≤ last v) := by
  induction h : last v using Nat.strong_induction_on generalizing v d with
  | h k ih =>
    by_cases base : v = s
    · subst v
      rw [tree.source_distance, Option.some.injEq] at finite
      exact ⟨[], .nil _, by simp [FollowsParents], by simp, finite, by simp [routeVertices], by simp [routeVertices, h]⟩
    obtain ⟨a, c, hp, hv, hpos, hc, hcost, earlier⟩ := tree.predecessor v d base finite
    obtain ⟨path, pathOk, follows, positive, cost, unique, rank⟩ := ih (last (n.tail a))
      (by omega) (n.tail a) c hc rfl
    have extend : routeVertices n v (path ++ [a]) = routeVertices n (n.tail a) path ++ [v] := by
      simp [routeVertices, List.append_assoc]
    refine ⟨path ++ [a], hv ▸ pathOk.snoc a rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact follows b hb
      · obtain rfl : b = a := by simpa using hb
        rwa [hv]
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact positive b hb
      · obtain rfl : b = a := by simpa using hb
        exact hpos
    · simpa [List.map_append, List.sum_append, cost] using hcost.symm
    · rw [extend, List.nodup_append]
      refine ⟨unique, by simp, ?_⟩
      intro x hx y hy equal
      have eq : y = v := by simpa using hy
      have bound := rank x hx
      have hv : last x = last v := congrArg last (equal.trans eq)
      omega
    · intro x hx
      rw [extend, List.mem_append] at hx
      rcases hx with hx | hx
      · have bound := rank x hx
        omega
      · obtain rfl : x = v := by simpa using hx
        omega

end Proofs.FlowResidual
