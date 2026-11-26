import Proofs.Cpp.FlowCostSlopeRound

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [NumericTraits "Cost" Int] [ShiftInt Int] [DecidableEq Arc]

def origin : Slope := replicate 1 (0, 0)

inductive CostCurve (n : Network Arc Nat) (arcs : List Arc) (base : Capacity Arc) (s t : Nat) : Slope → Int → Int → Prop where
  | start : OptimalCost n arcs base s t 0 0 → CostCurve n arcs base s t origin 0 0
  | push {prior : Slope} {amount cost : Int} (d price : Int) : CostCurve n arcs base s t prior amount cost → 0 < d →
      (∀ delta : Int, 0 ≤ delta → delta ≤ d → OptimalCost n arcs base s t (amount + delta) (cost + delta * price)) →
      CostCurve n arcs base s t (prior.push (amount + d, cost + d * price)) (amount + d) (cost + d * price)

inductive StopReason (n : Network Arc Nat) (arcs : List Arc) (base : Capacity Arc) (s t : Nat) (cutoff : Int) :
    Slope → Int → Int → Prop where
  | exhausted {result amount cost} : amount < cutoff →
      (∀ f q, SignedFeasible n arcs base s t f q → f ≤ amount) → StopReason n arcs base s t cutoff result amount cost
  | covered {prior : Slope} {amount cost : Int} (d price : Int) : CostCurve n arcs base s t prior amount cost →
      amount < cutoff → cutoff ≤ amount + d →
      (∀ delta : Int, 0 ≤ delta → delta ≤ d → OptimalCost n arcs base s t (amount + delta) (cost + delta * price)) →
      StopReason n arcs base s t cutoff (prior.push (amount + d, cost + d * price)) (amount + d) (cost + d * price)

private theorem roundCharge_eq (g : cp.FlowGraph Int E) (out : Array (Array E))
    (dims : out.size = g.adj.size ∧ ∀ v : Nat, out[v]!.size = g.adj[v]!.size) :
    roundCharge {g with adj := out} = roundCharge g := by
  unfold roundCharge
  rw [arcCount_withRows g out dims]
  simp only [dims.1]

/-- Every continuing iteration sends a positive integral amount. The remaining cutoff bounds all work. -/
theorem slope_loop (n : Network Arc Nat) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (base : Capacity Arc) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc) (laws : CapLaws (E := E))
    (s t : Nat) (cutoff : Int) (limPos : 0 < flowLimit) (lim : Nat) (g : cp.FlowGraph Int E)
    (layout : CapacityLayout n g slot atSlot) (hs : s < g.adj.size) (ht : t < g.adj.size)
    (fuelBound : g.adj.size ≤ fuel) (result : Slope) (amount cost : Int)
    (cert : FlowCert n arcs base (capacity g.adj slot) s t amount cost)
    (curve : CostCurve n arcs base s t result amount cost)
    (remains : amount < cutoff) (budget : (cutoff - amount).toNat ≤ lim) (clock : Nat) :
    ∃ (final : cp.FlowGraph Int E) (points : Slope) (flow price : Int) (finish : Nat),
      (loopFuel lim (packSlope none g result amount cost) (slopeStep (s : Int) (t : Int) cutoff)).run clock =
        some (packSlope (some (points, final)) final points flow price, finish) ∧
      FlowCert n arcs base (capacity final.adj slot) s t flow price ∧
      CostCurve n arcs base s t points flow price ∧ StopReason n arcs base s t cutoff points flow price ∧
      flow ≥ amount ∧ points.size ≤ result.size + (cutoff - amount).toNat ∧
      finish ≤ clock + (cutoff - amount).toNat * roundCharge g := by
  induction lim generalizing g result amount cost clock with
  | zero => omega
  | succ left ih =>
    obtain ⟨step, after, run, next, spent⟩ := slope_step_spec n arcs nd all base g slot atSlot layout laws s t
      hs ht fuelBound limPos result amount cost cutoff cert clock
    have remPositive : 0 < (cutoff - amount).toNat := by omega
    have costOne := Nat.mul_le_mul_right (roundCharge g) (show 1 ≤ (cutoff - amount).toNat by omega)
    rw [Nat.one_mul] at costOne
    cases next with
    | exhausted maximal =>
      refine ⟨g, result, amount, cost, after, ?_, cert, curve, .exhausted remains maximal, le_rfl, by omega, by omega⟩
      rw [loopFuel, StateT.run_bind, run]
      rfl
    | pushed adj d unitCost positive nextLayout dims nextCert segment =>
      let nextGraph : cp.FlowGraph Int E := {g with adj := adj}
      let flow := amount + d
      let price := cost + d * unitCost
      let points := result.push (flow, price)
      have newCurve : CostCurve n arcs base s t points flow price := .push d unitCost curve positive segment
      have count : points.size = result.size + 1 := by simp [points]
      by_cases stop : cutoff ≤ flow
      · refine ⟨nextGraph, points, flow, price, after, ?_, nextCert, newCurve, .covered d unitCost curve remains stop segment,
          by dsimp [flow]; omega, by omega, by omega⟩
        rw [loopFuel, StateT.run_bind, run]
        have tested : decide (flow ≥ cutoff) = true := decide_eq_true stop
        have he : nextSlope nextGraph points flow price cutoff = finishSlope nextGraph points flow price := by
          unfold nextSlope
          rw [ite_eq_left tested]
        change (some (nextSlope nextGraph points flow price cutoff, after) >>= _) = _
        rw [he]
        rfl
      · have smaller : (cutoff - flow).toNat + 1 ≤ (cutoff - amount).toNat := by dsimp [flow]; omega
        have go : flow < cutoff := by omega
        obtain ⟨g', p', f', c', last, tailRun, fcert, fcurve, why, raised, used, tailCost⟩ :=
          ih nextGraph nextLayout (by simpa [nextGraph, dims.1] using hs) (by simpa [nextGraph, dims.1] using ht)
            (by simpa [nextGraph, dims.1] using fuelBound) points flow price nextCert newCurve go (by omega) after
        have fee : roundCharge nextGraph = roundCharge g := roundCharge_eq g adj dims
        have ticket := Nat.mul_le_mul_right (roundCharge g) smaller
        rw [Nat.add_mul, Nat.one_mul] at ticket
        rw [fee] at tailCost
        refine ⟨g', p', f', c', last, ?_, fcert, fcurve, why, ?_, by omega, by omega⟩
        · rw [loopFuel, StateT.run_bind, run]
          have tested : ¬ decide (flow ≥ cutoff) = true := by
            rw [decide_eq_false stop]
            decide
          have he : nextSlope nextGraph points flow price cutoff = .yield (packSlope none nextGraph points flow price) := by
            unfold nextSlope
            rw [ite_eq_right tested]
          change (some (nextSlope nextGraph points flow price cutoff, after) >>= _) = _
          rw [he]
          exact tailRun
        · dsimp [flow] at raised
          omega

end Proofs.Cpp.FlowCostSearch
