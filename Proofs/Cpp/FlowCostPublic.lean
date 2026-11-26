import Proofs.Cpp.FlowCostSlopeLoop

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [NumericTraits "Cost" Int] [ShiftInt Int] [DecidableEq Arc]

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem tickN_run (k t : Nat) : (tickN k).run t = some ((), t + k) := rfl
private theorem some_bind {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl
private theorem integral_cast (a : Int) : (Int.cast a : Int) = a := rfl

/-- The generated slope ends at a maximum flow or at the first breakpoint covering the cutoff. -/
theorem slope_spec (n : Network Arc Nat) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (g : cp.FlowGraph Int E) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc) (laws : CapLaws (E := E))
    (layout : CapacityLayout n g slot atSlot) (s t : Nat) (hs : s < g.adj.size) (ht : t < g.adj.size)
    (fuelBound : g.adj.size ≤ fuel) (limPos : 0 < flowLimit) (cutoff : Int) (pos : 0 < cutoff)
    (cutoffBound : cutoff.toNat ≤ fuel) (capNonneg : ∀ a, 0 ≤ capacity g.adj slot a)
    (potential : ∃ p, FeasiblePotential n (capacity g.adj slot) p) (clock : Nat) :
    ∃ (out : cp.FlowGraph Int E) (points : Slope) (amount cost : Int) (finish : Nat),
      (cp.FlowGraph.min_cost_flow_slope g (s : Int) (t : Int) cutoff).run clock = some ((points, out), finish) ∧
      FlowCert n arcs (capacity g.adj slot) (capacity out.adj slot) s t amount cost ∧
      CostCurve n arcs (capacity g.adj slot) s t points amount cost ∧
      StopReason n arcs (capacity g.adj slot) s t cutoff points amount cost ∧
      points.size ≤ cutoff.toNat + 1 ∧ finish ≤ clock + 2 + cutoff.toNat * roundCharge g := by
  let verts := List.range g.adj.size
  have capCert := FlowCert.initial n arcs (capacity g.adj slot) s t capNonneg potential
  have initial := capCert.optimal n arcs verts List.nodup_range
    (fun a _ => ⟨List.mem_range.mpr (layout.order.tailBound a), List.mem_range.mpr (layout.order.headBound a)⟩)
    (capacity g.adj slot) (capacity g.adj slot) s t 0 0
  have curve := CostCurve.start initial
  have hm : (cutoff - 0).toNat ≤ fuel := by simpa using cutoffBound
  obtain ⟨out, result, amount, cost, finish, ran, valid, breaks, why, _, memory, work⟩ :=
    slope_loop n arcs nd all (capacity g.adj slot) slot atSlot laws s t cutoff limPos fuel g layout hs ht fuelBound
      origin 0 0 capCert curve pos hm (clock + 2)
  refine ⟨out, result, amount, cost, finish, ?_, valid, breaks, why, ?_, ?_⟩
  · rw [slope_program]
    unfold slopeProgram
    simp only [Int.toNat_one, show ¬ cutoff = 0 by omega, decide_false, Bool.false_eq_true, ite_false,
      StateT.run_bind, tick_run, tickN_run, some_bind]
    change ((loopFuel fuel (packSlope none g origin 0 0) (slopeStep (s : Int) (t : Int) cutoff)).run (clock + 2) >>= _) = _
    rw [ran]
    rfl
  · simp [origin, replicate] at memory
    omega
  · simpa using work

omit [DecidableEq Arc] in
theorem curve_last (n : Network Arc Nat) (arcs : List Arc) (base : Capacity Arc) (s t : Nat) (points : Slope)
    (amount cost : Int) (curve : CostCurve n arcs base s t points amount cost) :
    0 < points.size ∧ get points (size points - 1) = (amount, cost) := by
  cases curve with
  | start => exact ⟨by decide, rfl⟩
  | @push prior before fee d price curve hd optimal =>
    have h : (size (prior.push (before + d, fee + d * price)) - 1).toNat = prior.size := by
      simp [size]
    refine ⟨by simp, ?_⟩
    rw [get_eq, h]
    have bound : prior.size < (prior.push (before + d, fee + d * price)).size := by simp
    simp only [getElem!_pos, bound, Array.getElem_push_eq]

private theorem previous_point (prior : Slope) (len : 0 < prior.size) (point : Int × Int) :
    get (prior.push point) (size (prior.push point) - 2) = get prior (size prior - 1) := by
  have h : (size (prior.push point) - 2).toNat = prior.size - 1 := by simp [size]; omega
  have old : (size prior - 1).toNat = prior.size - 1 := by simp [size, Int.toNat_sub]
  rw [get_eq, get_eq, h, old]
  have bound : prior.size - 1 < prior.size := by omega
  have bpush : prior.size - 1 < (prior.push point).size := by simp; omega
  simp only [getElem!_pos, bound, bpush, Array.getElem_push_lt]

omit [DecidableEq Arc] in
private theorem fixed_positive_exhausted (g out : cp.FlowGraph Int E) (s t need : Int) (points : Slope)
    (clock finish : Nat) (positive : 0 < need)
    (run : (cp.FlowGraph.min_cost_flow_slope g s t need).run (clock + 1) = some ((points, out), finish))
    (low : (get points (size points - 1)).1 < need) :
    (cp.FlowGraph.min_cost_flow g s t need).run clock = some ((-1, out), finish) := by
  unfold cp.FlowGraph.min_cost_flow
  dsimp only
  have h : ¬ need = 0 := by omega
  simp only [h, decide_false, Bool.false_eq_true, ite_false, StateT.run_bind, tick_run, some_bind, integral_cast]
  change ((cp.FlowGraph.min_cost_flow_slope g s t need).run (clock + 1) >>= _) = _
  rw [run]
  simp only [some_bind, low, decide_true, ite_true]
  rfl

omit [DecidableEq Arc] in
private theorem fixed_positive_cover (g out : cp.FlowGraph Int E) (s t need : Int) (points : Slope)
    (clock finish : Nat) (positive : 0 < need)
    (run : (cp.FlowGraph.min_cost_flow_slope g s t need).run (clock + 1) = some ((points, out), finish))
    (a c d p : Int) (hd : 0 < d) (enough : need ≤ a + d)
    (one : get points (size points - 2) = (a, c)) (two : get points (size points - 1) = (a + d, c + d * p)) :
    (cp.FlowGraph.min_cost_flow g s t need).run clock = some ((c + (need - a) * p, out), finish) := by
  unfold cp.FlowGraph.min_cost_flow
  dsimp only
  have h : ¬ need = 0 := by omega
  simp only [h, decide_false, Bool.false_eq_true, ite_false, StateT.run_bind, tick_run, some_bind, integral_cast]
  change ((cp.FlowGraph.min_cost_flow_slope g s t need).run (clock + 1) >>= _) = _
  rw [run]
  simp only [some_bind, one, two, show ¬ a + d < need by omega, decide_false, Bool.false_eq_true, ite_false]
  have diff : c + d * p - c = d * p := by omega
  have dx : a + d - a = d := by omega
  rw [diff, dx, Int.mul_ediv_cancel_left _ (by omega)]
  congr 3
  rw [Int.mul_comm p, Int.add_comm]
  rfl

/-- A positive requested value is returned at its exact optimal cost, or feasibility fails. -/
theorem min_cost_flow_spec (n : Network Arc Nat) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (g : cp.FlowGraph Int E) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc) (laws : CapLaws (E := E))
    (layout : CapacityLayout n g slot atSlot) (s t : Nat) (hs : s < g.adj.size) (ht : t < g.adj.size)
    (fuelBound : g.adj.size ≤ fuel) (limPos : 0 < flowLimit) (need : Int) (pos : 0 < need)
    (cutoffBound : need.toNat ≤ fuel) (capNonneg : ∀ a, 0 ≤ capacity g.adj slot a)
    (potential : ∃ p, FeasiblePotential n (capacity g.adj slot) p) (clock : Nat) :
    ∃ (answer : Int) (out : cp.FlowGraph Int E) (finish : Nat),
      (cp.FlowGraph.min_cost_flow g (s : Int) (t : Int) need).run clock = some ((answer, out), finish) ∧
      (OptimalCost n arcs (capacity g.adj slot) s t need answer ∨
        (answer = -1 ∧ ¬ ∃ f, SignedFeasible n arcs (capacity g.adj slot) s t need f)) ∧
      finish ≤ clock + 3 + need.toNat * roundCharge g := by
  obtain ⟨out, points, amount, cost, finish, ran, _, curve, why, _, spent⟩ :=
    slope_spec n arcs nd all g slot atSlot laws layout s t hs ht fuelBound limPos need pos cutoffBound capNonneg potential (clock + 1)
  obtain ⟨_, last⟩ := curve_last n arcs (capacity g.adj slot) s t points amount cost curve
  cases why with
  | exhausted remains maxAmount =>
    refine ⟨-1, out, finish, ?_, Or.inr ⟨rfl, ?_⟩, by omega⟩
    · exact fixed_positive_exhausted g out (s : Int) (t : Int) need points clock finish pos ran (by rwa [last])
    · rintro ⟨f, feasible⟩
      have bound := maxAmount need f feasible
      omega
  | @covered prior amount cost delta price oldCurve remains enough opt =>
    have positive : 0 < delta := by omega
    have first := curve_last n arcs (capacity g.adj slot) s t prior amount cost oldCurve
    have one := (previous_point prior first.1 (amount + delta, cost + delta * price)).trans first.2
    refine ⟨cost + (need - amount) * price, out, finish, ?_, Or.inl ?_, by omega⟩
    · exact fixed_positive_cover g out (s : Int) (t : Int) need _ clock finish pos ran amount cost delta price positive enough one last
    · have h := opt (need - amount) (by omega) (by omega)
      rwa [show amount + (need - amount) = need by omega] at h

end Proofs.Cpp.FlowCostSearch
