import Proofs.Math.FlowResidualOptimality
import Proofs.Math.FlowResidualPaths

namespace Proofs.FlowResidual

variable {Arc Vertex : Type} [DecidableEq Vertex]

structure FlowCert (n : Network Arc Vertex) (arcs : List Arc) (base cap : Capacity Arc)
    (s t : Vertex) (amount cost : Int) : Prop where
  nonnegative : ∀ a, 0 ≤ cap a
  signed : SignedFeasible n arcs base s t amount (fun a => base a - cap a)
  chargedCost : charged arcs base cap n.cost = 2 * cost
  priced : ∃ p, FeasiblePotential n cap p

def OptimalCost (n : Network Arc Vertex) (arcs : List Arc) (base : Capacity Arc)
    (s t : Vertex) (amount cost : Int) : Prop :=
  (∃ f, SignedFeasible n arcs base s t amount f ∧ transportCost n arcs f = 2 * cost) ∧
  ∀ f, SignedFeasible n arcs base s t amount f → 2 * cost ≤ transportCost n arcs f

theorem FlowCert.initial (n : Network Arc Vertex) (arcs : List Arc) (base : Capacity Arc) (s t : Vertex)
    (nonneg : ∀ a, 0 ≤ base a) (price : ∃ p, FeasiblePotential n base p) : FlowCert n arcs base base s t 0 0 := by
  have zeros : (fun a => base a - base a) = fun _ => 0 := by funext a; omega
  refine ⟨nonneg, ?_, ?_, price⟩
  · rw [zeros]
    refine ⟨by simp, nonneg, ?_⟩
    intro v
    simp [divergence]
    change (arcs.map fun _ => (0 : Int)).sum = 0
    simp
  · unfold charged
    simp
    change (arcs.map fun _ => (0 : Int)).sum = 0
    simp

theorem FlowCert.optimal (n : Network Arc Vertex) (arcs : List Arc) (vertices : List Vertex)
    (uniq : vertices.Nodup) (inRange : ∀ a ∈ arcs, n.tail a ∈ vertices ∧ n.head a ∈ vertices)
    (base cap : Capacity Arc) (s t : Vertex) (amount cost : Int) (cert : FlowCert n arcs base cap s t amount cost) :
    OptimalCost n arcs base s t amount cost := by
  refine ⟨⟨fun a => base a - cap a, cert.signed, cert.chargedCost⟩, ?_⟩
  intro f hx
  obtain ⟨p, hp⟩ := cert.priced
  rw [← cert.chargedCost]
  exact signed_optimal n arcs vertices uniq inRange base cap p hp s t amount f cert.signed hx

variable [DecidableEq Arc]

/-- Updating any fraction of a tight, admissible route preserves the optimal-flow certificate. -/
theorem FlowCert.augment (n : Network Arc Vertex) (arcs : List Arc) (unique : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (base cap : Capacity Arc) (s t : Vertex) (amount cost : Int) (cert : FlowCert n arcs base cap s t amount cost)
    (p : Vertex → Int) (hp : FeasiblePotential n cap p) (path : List Arc) (route : Path n s t path)
    (distinct : DistinctPairs n path) (tight : ∀ a ∈ path, Tight n p a)
    (d : Int) (nonnegative : 0 ≤ d) (supply : ∀ a ∈ path, d ≤ cap a) :
    FlowCert n arcs base (FlowResidual.augment n d cap path.reverse) s t (amount + d)
      (cost + d * (path.map n.cost).sum) := by
  have capacity := nonneg_after_augment n cap path.reverse d nonnegative cert.nonnegative distinct.reverse (by
    intro a ha
    exact supply a (by simpa using ha))
  refine ⟨capacity, signed_augmentation n arcs unique all base cap s t amount path route cert.signed d capacity, ?_, ?_⟩
  · rw [charged_add arcs base cap, cert.chargedCost, charged_cost n arcs unique all, Int.mul_add]
  · refine ⟨p, potential_after_augment n cap p path.reverse d hp nonnegative ?_⟩
    intro a ha
    exact tight a (by simpa using ha)

end Proofs.FlowResidual
