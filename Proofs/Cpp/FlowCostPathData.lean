import Proofs.Cpp.FlowCostEntry

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]

theorem parent_indices (n : Network Arc Nat) (g : cp.FlowGraph Int E) (cap : Capacity Arc)
    (atSlot : Int → Int → Option Arc) (layout : Layout n g cap atSlot) (b : Pass Int) (s : Nat) (a : Arc)
    (parent : savedParent atSlot s b (n.head a) = some a) :
    get b.2.1 (n.head a : Int) = (n.tail a : Int) ∧ get b.2.2.1 (n.head a : Int) = (layout.position a : Int) := by
  unfold savedParent at parent
  split at parent
  · cases parent
  · exact layout.lookup_sound _ _ _ parent

/-- The stored indices recover the exact simple shortest path and its capacity slots. -/
theorem predecessor_path (n : Network Arc Nat) (g : cp.FlowGraph Int E) (cap : Capacity Arc)
    (atSlot : Int → Int → Option Arc) (layout : Layout n g cap atSlot) (b : Pass Int) (s t : Nat)
    (ht : t < g.adj.size) (seen : known b t = true) (last : Nat → Nat)
    (pred : ValidParents n cap s (fun v => if known b v then some (label b v) else none)
      (savedParent atSlot s b) last) :
    ∃ path, Path n s t path ∧ (∀ a ∈ path, 0 < cap a) ∧ DistinctPairs n path ∧ path.length < g.adj.size ∧
      (path.map n.cost).sum = label b t ∧
      ∀ a ∈ path, n.head a ≠ s ∧ get b.2.1 (n.head a : Int) = (n.tail a : Int) ∧
        get b.2.2.1 (n.head a : Int) = (layout.position a : Int) := by
  obtain ⟨path, route, fromParents, positive, hc, simple, _⟩ := predecessor_route n cap s
    (fun v => if known b v then some (label b v) else none) (savedParent atSlot s b) last pred t (label b t) (by simp [seen])
  have bounded : routeVertices n t path ⊆ List.range g.adj.size := by
    intro v h
    apply List.mem_range.mpr
    rw [routeVertices, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
      exact layout.tailBound a
    · obtain rfl : v = t := by simpa using h
      exact ht
  have hlen := simple.length_le_of_subset bounded
  simp only [routeVertices, List.length_append, List.length_map, List.length_cons, List.length_nil, List.length_range] at hlen
  refine ⟨path, route, positive, route.distinct_pairs simple, by omega, hc, ?_⟩
  intro a ha
  have parent := fromParents a ha
  have unequal : n.head a ≠ s := by
    intro eq
    simp [savedParent, eq] at parent
  exact ⟨unequal, parent_indices n g cap atSlot layout b s a parent⟩

end Proofs.Cpp.FlowCostSearch
