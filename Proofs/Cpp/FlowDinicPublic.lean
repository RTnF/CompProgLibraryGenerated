import Proofs.Cpp.FlowDinicPhase

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [NumericTraits "Cost" Int] [ShiftInt Int] [DecidableEq Arc]

private theorem signed_zero (n : Network Arc Nat) (arcs : List Arc) (base : Capacity Arc) (s t : Nat)
    (valid : ∀ a, 0 ≤ base a) : SignedFeasible n arcs base s t 0 (fun a => base a - base a) := by
  refine ⟨by simp, by simpa using valid, ?_⟩
  intro v
  change (arcs.map (fun a => (base a - base a) * (indicator (n.tail a) v - indicator (n.head a) v))).sum = _
  simp

def LowerDistance (n : Network Arc Nat) (cap : Capacity Arc) (s t lower : Nat) : Prop :=
  ∀ path, Path n s t path → (∀ a ∈ path, 0 < cap a) → lower ≤ path.length

private theorem equal_charge (g out : cp.FlowGraph Int E) (arcs : List Arc)
    (dims : out.adj.size = g.adj.size ∧ ∀ v : Nat, out.adj[v]!.size = g.adj[v]!.size) :
    phaseCharge out arcs = phaseCharge g arcs := by
  have ha : FlowCostSearch.arcCount out = FlowCostSearch.arcCount g := arcCount_withRows g out.adj dims
  simp only [phaseCharge, dims.1, ha]

/-- Every continuing BFS phase strictly increases the least admissible residual distance. -/
theorem max_loop (n : Network Arc Nat) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (base : Capacity Arc) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc) (laws : CapLaws (E := E))
    (s t : Nat) (different : s ≠ t) (fuelArcs : 8 * arcs.length + 1 ≤ fuel) (limPos : 0 < flowLimit)
    (edgeBound : ∀ a, base a ≤ 7 * flowLimit) (lim : Nat) (g : cp.FlowGraph Int E)
    (layout : CapacityLayout n g slot atSlot) (nonnegative : ∀ a, 0 ≤ capacity g.adj slot a)
    (hs : s < g.adj.size) (ht : t < g.adj.size) (fuelSize : g.adj.size + 2 ≤ fuel)
    (flow : Int) (flowNonnegative : 0 ≤ flow)
    (feasible : SignedFeasible n arcs base s t flow (fun a => base a - capacity g.adj slot a))
    (lower : Nat) (below : lower ≤ g.adj.size) (progress : LowerDistance n (capacity g.adj slot) s t lower)
    (bound : g.adj.size + 1 - lower ≤ lim) (clock : Nat) :
    ∃ (out : cp.FlowGraph Int E) (amount : Int) (finish : Nat),
      (loopFuel lim (packMax none g flow) (maxStep (s : Int) (t : Int))).run clock =
        some (packMax (some (amount, out)) out amount, finish) ∧
      SignedFeasible n arcs base s t amount (fun a => base a - capacity out.adj slot a) ∧
      (∀ f q, SignedFeasible n arcs base s t f q → f ≤ amount) ∧
      flow ≤ amount ∧ finish ≤ clock + (g.adj.size + 1 - lower) * phaseCharge g arcs := by
  induction lim generalizing g flow lower clock with
  | zero => omega
  | succ left ih =>
    obtain ⟨step, after, one, transition, cost⟩ := max_step_spec n arcs nd all base g slot atSlot layout laws nonnegative
      s t hs ht different fuelSize fuelArcs limPos edgeBound flow flowNonnegative feasible clock
    have posRank : 1 ≤ g.adj.size + 1 - lower := by omega
    have pay := Nat.mul_le_mul_right (phaseCharge g arcs) posRank
    rw [Nat.one_mul] at pay
    cases transition with
    | halt lv optimal =>
      refine ⟨{g with level := lv}, flow, after, ?_, feasible, optimal, le_rfl, by omega⟩
      rw [loopFuel, StateT.run_bind, one]
      rfl
    | progress next amount d updated counters dims capValid net greater small before afterBound =>
      obtain ⟨p, route, len, forward⟩ := before
      have lowerOld : lower ≤ d := by rw [← len]; exact progress p route forward
      have up : LowerDistance n (capacity next.adj slot) s t (d + 1) := by
        intro path route positive
        have h := afterBound path route positive
        omega
      have delta : (next.adj.size + 1 - (d + 1)) + 1 ≤ g.adj.size + 1 - lower := by rw [dims.1]; omega
      obtain ⟨out, last, finish, runTail, valid, opt, monotone, tailCost⟩ := ih next updated capValid
        (by rwa [dims.1]) (by rwa [dims.1]) (by rwa [dims.1]) amount (by omega) net (d + 1)
        (by rw [dims.1]; omega) up (by omega) after
      have pay := Nat.mul_le_mul_right (phaseCharge g arcs) delta
      rw [Nat.add_mul, Nat.one_mul] at pay
      rw [equal_charge g next arcs dims] at tailCost
      refine ⟨out, last, finish, ?_, valid, opt, le_trans greater monotone, by omega⟩
      rw [loopFuel, StateT.run_bind, one]
      exact runTail

/-- The generated maximum-flow entry terminates and returns a feasible maximum. -/
theorem max_flow_spec (n : Network Arc Nat) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (g : cp.FlowGraph Int E) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc)
    (layout : CapacityLayout n g slot atSlot) (laws : CapLaws (E := E))
    (s t : Nat) (hs : s < g.adj.size) (ht : t < g.adj.size) (different : s ≠ t)
    (fuelSize : g.adj.size + 2 ≤ fuel) (fuelArcs : 8 * arcs.length + 1 ≤ fuel) (limPos : 0 < flowLimit)
    (valid : ∀ a, 0 ≤ capacity g.adj slot a ∧ capacity g.adj slot a ≤ 7 * flowLimit) (clock : Nat) :
    ∃ (out : cp.FlowGraph Int E) (amount : Int) (finish : Nat),
      (cp.FlowGraph.max_flow g (s : Int) (t : Int)).run clock = some ((amount, out), finish) ∧
      SignedFeasible n arcs (capacity g.adj slot) s t amount (fun a => capacity g.adj slot a - capacity out.adj slot a) ∧
      (∀ f q, SignedFeasible n arcs (capacity g.adj slot) s t f q → f ≤ amount) ∧
      0 ≤ amount ∧ finish ≤ clock + 1 + (g.adj.size + 1) * phaseCharge g arcs := by
  have nonnegative (a : Arc) := (valid a).1
  have initial := signed_zero n arcs (capacity g.adj slot) s t nonnegative
  obtain ⟨out, amount, finish, ran, feasible, maximal, greater, spent⟩ := max_loop n arcs nd all (capacity g.adj slot) slot
    atSlot laws s t different fuelArcs limPos (fun a => (valid a).2) fuel g layout nonnegative hs ht fuelSize 0 (by decide)
    initial 0 (by omega) (fun _ _ _ => Nat.zero_le _) (by omega) (clock + 1)
  refine ⟨out, amount, finish, ?_, feasible, maximal, greater, by simpa using spent⟩
  rw [max_flow_program]
  unfold maxProgram
  simp only [StateT.run_bind]
  have ht : tick.run clock = some ((), clock + 1) := rfl
  rw [ht]
  change ((loopFuel fuel (packMax none g 0) (maxStep (s : Int) (t : Int))).run (clock + 1) >>= _) = _
  rw [ran]
  rfl

end Proofs.Cpp.FlowDinic
