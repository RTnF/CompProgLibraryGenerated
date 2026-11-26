import Proofs.Cpp.FlowCostSlopeState

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [NumericTraits "Cost" Int] [ShiftInt Int] [DecidableEq Arc]

def roundCharge (g : cp.FlowGraph Int E) : Nat :=
  7 + 8 * g.adj.size + g.adj.size * (1 + g.adj.size + arcCount g)

inductive SlopeTransition (n : Network Arc Nat) (arcs : List Arc) (base : Capacity Arc)
    (g : cp.FlowGraph Int E) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc) (s t : Nat)
    (result : Slope) (amount cost cutoff : Int) : ForInStep (SlopeState E) → Prop where
  | exhausted : (∀ f q, SignedFeasible n arcs base s t f q → f ≤ amount) →
      SlopeTransition n arcs base g slot atSlot s t result amount cost cutoff (finishSlope g result amount cost)
  | pushed (out : Array (Array E)) (d price : Int) :
      0 < d →
      CapacityLayout n {g with adj := out} slot atSlot →
      (out.size = g.adj.size ∧ ∀ v : Nat, out[v]!.size = g.adj[v]!.size) →
      FlowCert n arcs base (capacity out slot) s t (amount + d) (cost + d * price) →
      (∀ delta : Int, 0 ≤ delta → delta ≤ d → OptimalCost n arcs base s t (amount + delta) (cost + delta * price)) →
      SlopeTransition n arcs base g slot atSlot s t result amount cost cutoff
        (nextSlope {g with adj := out} (result.push (amount + d, cost + d * price)) (amount + d) (cost + d * price) cutoff)

/-- One produced segment remains optimal throughout its interval and preserves the paired residual graph. -/
theorem slope_step_spec (n : Network Arc Nat) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (base : Capacity Arc) (g : cp.FlowGraph Int E) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc)
    (layout : CapacityLayout n g slot atSlot) (laws : CapLaws (E := E)) (s t : Nat)
    (hs : s < g.adj.size) (ht : t < g.adj.size) (fuelBound : g.adj.size ≤ fuel)
    (limPos : 0 < flowLimit) (slope : Slope) (amount cost cutoff : Int)
    (cert : FlowCert n arcs base (capacity g.adj slot) s t amount cost) (clock : Nat) :
    ∃ out finish, (slopeStep (s : Int) (t : Int) cutoff () (packSlope none g slope amount cost)).run clock =
      some (out, finish) ∧ SlopeTransition n arcs base g slot atSlot s t slope amount cost cutoff out ∧
      finish ≤ clock + roundCharge g := by
  let cap := capacity g.adj slot
  let vertices := List.range g.adj.size
  have order (a : Arc) (_ : a ∈ arcs) : n.tail a ∈ vertices ∧ n.head a ∈ vertices :=
    ⟨List.mem_range.mpr (layout.order.tailBound a), List.mem_range.mpr (layout.order.headBound a)⟩
  have unique : vertices.Nodup := List.nodup_range
  obtain ⟨p, pf⟩ := cert.priced
  obtain ⟨b, afterSearch, search, sizes, sound, close, _, ⟨last, good⟩, work⟩ :=
    bellman_ford_spec n g cap atSlot layout.order p pf s hs fuelBound (clock + 1)
  by_cases absent : get b.2.1 (t : Int) = -1
  · refine ⟨_, afterSearch, slope_unreachable_step g s t cutoff slope amount cost b clock afterSearch search absent, ?_, ?_⟩
    · apply SlopeTransition.exhausted
      intro f q feasible
      have sinkAbsent : known b t = false := by simp [known, absent, get_natCast]
      have cut (a : Arc) (u : known b (n.tail a) = true) (v : known b (n.head a) = false) : cap a ≤ 0 := by
        by_contra pos
        have h := (close a (by omega) u).1
        rw [v] at h
        contradiction
      exact signed_cut_maximal n arcs vertices unique order base cap (known b) s t (List.mem_range.mpr hs)
        (List.mem_range.mpr ht) sound.root.1 sinkAbsent cut amount f q cert.signed feasible
    · unfold roundCharge
      omega
  · have seen : known b t = true := (known_iff b t).mpr ⟨by rwa [sizes.parent], absent⟩
    obtain ⟨path, route, positive, distinct, hlen, exactCost, parents⟩ :=
      predecessor_path n g cap atSlot layout.order b s t ht seen last good
    obtain ⟨d, out, run, dpos, _, supply, _, ro, dims, rev, residual⟩ :=
      slope_path_step n g slot layout.represents laws atSlot layout.order layout.slotEq layout.reverseIndices
        s t cutoff slope amount cost b clock afterSearch search seen path route (by omega) positive parents limPos
    obtain ⟨newP, feasible, reached⟩ := reachable_potential n cap arcs all (known b) (label b) p pf close
    have tight : ∀ a ∈ path, Tight n newP a := by
      apply path_tight_of_cost n cap newP feasible route positive
      rw [reached s sound.root.1, reached t seen, sound.root.2, Int.sub_zero]
      exact exactCost
    have altered : FlowCert n arcs base (capacity out slot) s t (amount + d) (cost + d * label b t) := by
      rw [residual, ← exactCost]
      exact cert.augment n arcs nd all base cap s t amount cost newP feasible path route distinct tight d (by omega) supply
    refine ⟨_, _, run, .pushed out d (label b t) dpos (layout.withRows out ro dims rev) dims altered ?_, ?_⟩
    · intro e enonneg ebound
      rw [← exactCost]
      have between := cert.augment n arcs nd all base cap s t amount cost newP feasible path route distinct tight e enonneg
        (fun a ha => le_trans ebound (supply a ha))
      exact between.optimal n arcs vertices unique order base _ s t _ _
    · unfold roundCharge
      omega

end Proofs.Cpp.FlowCostSearch
