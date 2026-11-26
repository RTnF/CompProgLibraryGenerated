import Proofs.Math.FlowCostParents

namespace Proofs.FlowResidual

variable {Arc Vertex : Type}

theorem Path.split_at_vertex {n : Network Arc Vertex} {u t : Vertex} {path : List Arc}
    (walk : Path n u t path) {v : Vertex} (mem : v ∈ routeVertices n t path) :
    ∃ front back, path = front ++ back ∧ Path n u v front ∧ Path n v t back := by
  induction walk with
  | nil w =>
    have hv : v = w := by simpa [routeVertices] using mem
    subst v
    exact ⟨[], [], rfl, .nil _, .nil _⟩
  | cons a walk ih =>
    rw [show routeVertices n _ (a :: _) = n.tail a :: routeVertices n _ _ from rfl, List.mem_cons] at mem
    rcases mem with h | h
    · subst v
      exact ⟨[], _ :: _, rfl, .nil _, .cons a walk⟩
    · obtain ⟨front, back, eq, first, second⟩ := ih h
      exact ⟨a :: front, back, congrArg (List.cons a) eq, .cons a first, second⟩

theorem Path.eq_of_empty {n : Network Arc Vertex} {u t : Vertex} {path : List Arc}
    (walk : Path n u t path) (empty : path = []) : u = t := by
  cases walk with
  | nil => rfl
  | cons => cases empty

theorem Path.split_last {n : Network Arc Vertex} {u t : Vertex} {path : List Arc}
    (walk : Path n u t path) (nonempty : path ≠ []) :
    ∃ front a, path = front ++ [a] ∧ Path n u (n.tail a) front ∧ n.head a = t := by
  induction walk with
  | nil => exact False.elim (nonempty rfl)
  | @cons a v rest tail ih =>
    by_cases empty : rest = []
    · exact ⟨[], a, by simp [empty], .nil _, tail.eq_of_empty empty⟩
    · obtain ⟨front, last, eq, first, head⟩ := ih empty
      exact ⟨a :: front, last, congrArg (List.cons a) eq, .cons a first, head⟩

theorem Path.origin_mem {n : Network Arc Vertex} {u t : Vertex} {path : List Arc}
    (walk : Path n u t path) : u ∈ routeVertices n t path := by
  cases walk <;> simp [routeVertices]

theorem Path.head_mem {n : Network Arc Vertex} {u t : Vertex} {path : List Arc}
    (walk : Path n u t path) {a : Arc} (ha : a ∈ path) : n.head a ∈ routeVertices n t path := by
  induction walk with
  | nil => cases ha
  | cons b rest ih =>
    change n.head a ∈ n.tail b :: routeVertices n _ _
    apply List.mem_cons_of_mem
    rcases List.mem_cons.mp ha with rfl | later
    · exact rest.origin_mem
    · exact ih later

theorem Path.distinct_pairs {n : Network Arc Vertex} {u t : Vertex} {path : List Arc}
    (walk : Path n u t path) (simple : (routeVertices n t path).Nodup) : DistinctPairs n path := by
  induction walk with
  | nil => exact .nil
  | @cons a v tail rest ih =>
    change (n.tail a :: routeVertices n v tail).Nodup at simple
    obtain ⟨absent, sub⟩ := List.nodup_cons.mp simple
    refine .cons (fun h => absent ?_) (fun h => absent ?_) (ih sub)
    · unfold routeVertices
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a, h, rfl⟩))
    · rw [← n.reverse_head]
      exact rest.head_mem h

theorem DistinctPairs.snoc {n : Network Arc Vertex} {path : List Arc} (distinct : DistinctPairs n path)
    (a : Arc) (fresh : a ∉ path) (reverseFresh : n.reverse a ∉ path) : DistinctPairs n (path ++ [a]) := by
  induction distinct with
  | nil => exact .cons (by simp) (by simp) .nil
  | @cons b rest bFresh brFresh tail ih =>
    have hab : a ≠ b := fun h => fresh (h ▸ List.mem_cons_self ..)
    have har : n.reverse a ≠ b := fun h => reverseFresh (h ▸ List.mem_cons_self ..)
    have hbr : n.reverse b ≠ a := by
      intro h
      apply har
      rw [← h, n.reverse_reverse]
    refine .cons ?_ ?_ (ih (fun h => fresh (List.mem_cons_of_mem _ h))
      (fun h => reverseFresh (List.mem_cons_of_mem _ h)))
    · simp [bFresh, Ne.symm hab]
    · simp [brFresh, hbr]

theorem DistinctPairs.reverse {n : Network Arc Vertex} {path : List Arc} (distinct : DistinctPairs n path) :
    DistinctPairs n path.reverse := by
  induction distinct with
  | nil => exact .nil
  | @cons a rest fresh rev _ ih =>
    rw [List.reverse_cons]
    exact ih.snoc a (by simpa using fresh) (by simpa using rev)

variable [DecidableEq Arc] [DecidableEq Vertex]

/-- Deleting a repeated-vertex segment keeps positive capacities and never raises the cost. -/
theorem Path.simple_cheaper {n : Network Arc Vertex} {cap : Capacity Arc} {p : Vertex → Int}
    (feasible : FeasiblePotential n cap p) {s t : Vertex} {path : List Arc}
    (walk : Path n s t path) (positive : ∀ a ∈ path, 0 < cap a) :
    ∃ q, Path n s t q ∧ (∀ a ∈ q, 0 < cap a) ∧ (routeVertices n t q).Nodup ∧
      q.length ≤ path.length ∧ (q.map n.cost).sum ≤ (path.map n.cost).sum := by
  induction walk with
  | nil => exact ⟨[], .nil _, by simp, by simp [routeVertices], by simp, by simp⟩
  | @cons a v rest tail ih =>
    have aPos := positive a (List.mem_cons_self ..)
    obtain ⟨q, qPath, qPos, qSimple, qLen, qCost⟩ := ih (fun a ha => positive a (List.mem_cons_of_mem _ ha))
    by_cases h : n.tail a ∈ routeVertices n v q
    · obtain ⟨front, back, eq, first, second⟩ := qPath.split_at_vertex h
      have sub : ∀ b ∈ front, 0 < cap b := by
        intro b hb
        exact qPos b (eq ▸ List.mem_append.mpr (Or.inl hb))
      have cycleCost := path_cost_lower n cap p feasible (.cons a first) (by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact aPos
        · exact sub b hb)
      refine ⟨back, second, ?_, ?_, ?_, ?_⟩
      · intro b hb
        exact qPos b (eq ▸ List.mem_append.mpr (Or.inr hb))
      · rw [eq] at qSimple
        unfold routeVertices at qSimple ⊢
        rw [List.map_append, List.append_assoc, List.nodup_append] at qSimple
        exact qSimple.2.1
      · rw [eq, List.length_append] at qLen
        simp only [List.length_cons]
        omega
      · rw [eq, List.map_append, List.sum_append] at qCost
        simp only [List.map_cons, List.sum_cons] at cycleCost ⊢
        omega
    · refine ⟨a :: q, .cons a qPath, ?_, ?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact aPos
        · exact qPos b hb
      · change (n.tail a :: routeVertices n v q).Nodup
        exact List.nodup_cons.mpr ⟨h, qSimple⟩
      · simp only [List.length_cons]
        omega
      · simp only [List.map_cons, List.sum_cons]
        omega

def HasWalkCost (n : Network Arc Vertex) (cap : Capacity Arc) (s t : Vertex) (cost : Int) : Prop :=
  ∃ path, Path n s t path ∧ (∀ a ∈ path, 0 < cap a) ∧ (path.map n.cost).sum = cost

omit [DecidableEq Vertex] in
private theorem least_walk_cost (n : Network Arc Vertex) (cap : Capacity Arc) (p : Vertex → Int)
    (feasible : FeasiblePotential n cap p) (s t : Vertex) (d : Int) (witness : HasWalkCost n cap s t d) :
    ∃ optimum, HasWalkCost n cap s t optimum ∧ ∀ c, HasWalkCost n cap s t c → optimum ≤ c := by
  classical
  induction hi : (d - (p t - p s)).toNat using Nat.strong_induction_on generalizing d with
  | h k ih =>
    by_cases shorter : ∃ c, HasWalkCost n cap s t c ∧ c < d
    · obtain ⟨c, hc, hlt⟩ := shorter
      obtain ⟨path, route, positive, cost⟩ := hc
      have lo := path_cost_lower n cap p feasible route positive
      rw [cost] at lo
      have decrease : (c - (p t - p s)).toNat < k := by omega
      exact ih _ decrease c ⟨path, route, positive, cost⟩ rfl
    · refine ⟨d, witness, ?_⟩
      intro c hc
      by_contra h
      exact shorter ⟨c, hc, by omega⟩

/-- If the sink is reachable, an optimum is attained by a simple path in the finite vertex range. -/
theorem shortest_simple (n : Network Arc Vertex) (cap : Capacity Arc) (p : Vertex → Int)
    (feasible : FeasiblePotential n cap p) (vertices : List Vertex) (s t : Vertex) (sink : t ∈ vertices)
    (bounded : ∀ a, n.tail a ∈ vertices) (d : Int) (witness : HasWalkCost n cap s t d) :
    ∃ q, Path n s t q ∧ (∀ a ∈ q, 0 < cap a) ∧ q.length < vertices.length ∧
      ∀ c, HasWalkCost n cap s t c → (q.map n.cost).sum ≤ c := by
  obtain ⟨opt, ⟨path, route, positive, cost⟩, min⟩ := least_walk_cost n cap p feasible s t d witness
  obtain ⟨q, qr, qp, nodup, _, cheaper⟩ := route.simple_cheaper feasible positive
  have cover : routeVertices n t q ⊆ vertices := by
    intro v hv
    rw [routeVertices, List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
      exact bounded a
    · obtain rfl : v = t := by simpa using hv
      exact sink
  have len := nodup.length_le_of_subset cover
  simp only [routeVertices, List.length_append, List.length_map, List.length_cons, List.length_nil] at len
  refine ⟨q, qr, qp, by omega, ?_⟩
  intro c hc
  have h := min c hc
  omega

end Proofs.FlowResidual
