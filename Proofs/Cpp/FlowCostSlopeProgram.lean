import Proofs.Cpp.FlowCostAugment

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowDinic Proofs.Cpp.FlowResidualView

namespace Proofs.Cpp.FlowCostSearch

variable {E : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [NumericTraits "Cost" Int] [ShiftInt Int]

abbrev Slope := Array (Int × Int)
abbrev SlopeState (E : Type) := Option (Slope × cp.FlowGraph Int E) × Int × Int × Array (Array E) ×
  Array Int × Array Int × Slope × Int × Int

def packSlope (ret : Option (Slope × cp.FlowGraph Int E)) (g : cp.FlowGraph Int E)
    (result : Slope) (amount cost : Int) : SlopeState E :=
  (ret, g.n_, g.m_, g.adj, g.level, g.iter, result, amount, cost)

def slopeGraph (b : SlopeState E) : cp.FlowGraph Int E :=
  ⟨b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2.1⟩

def slopeResult (b : SlopeState E) : Slope := b.2.2.2.2.2.2.1
def slopeAmount (b : SlopeState E) : Int := b.2.2.2.2.2.2.2.1
def slopeCost (b : SlopeState E) : Int := b.2.2.2.2.2.2.2.2

def slopeStep (s t cutoff : Int) (_ : Unit) (b : SlopeState E) : M (ForInStep (SlopeState E)) := do
  tick
  let search ← cp.FlowGraph.bellman_ford (slopeGraph b) s
  let g := search.2
  let dist := search.1.1
  let pv := search.1.2.1
  let pe := search.1.2.2
  if decide (get pv t = -1) then
    return .done (packSlope (some (slopeResult b, g)) g (slopeResult b) (slopeAmount b) (slopeCost b))
  else
    let bound ← cp.FlowGraph.F_MAX (Cost := Int) (E := E)
    let minimum ← forIn forever (bound, t) (bottleneckStep g.adj s pv pe)
    let amount := slopeAmount b + minimum.1
    let cost := slopeCost b + minimum.1 * get dist t
    tick
    let result := (slopeResult b).push (amount, cost)
    let pushed ← forIn forever (g.adj, t) (pushParentStep s pv pe minimum.1)
    let next := { g with adj := pushed.1 }
    if decide (amount ≥ cutoff) then
      return .done (packSlope (some (result, next)) next result amount cost)
    else
      return .yield (packSlope none next result amount cost)

def slopeProgram (g : cp.FlowGraph Int E) (s t cutoff : Int) : M (Slope × cp.FlowGraph Int E) := do
  tick
  tickN 1
  let result := replicate 1 (0, 0)
  if decide (cutoff = 0) then
    return (result, g)
  else
    let out ← forIn forever (packSlope none g result 0 0) (slopeStep s t cutoff)
    match out.1 with
    | some r => return r
    | none => failure

theorem slope_program (g : cp.FlowGraph Int E) (s t cutoff : Int) :
    cp.FlowGraph.min_cost_flow_slope g s t cutoff = slopeProgram g s t cutoff := by
  unfold cp.FlowGraph.min_cost_flow_slope slopeProgram slopeStep packSlope slopeGraph slopeResult slopeAmount slopeCost
    bottleneckStep pushParentStep pushPairTo atEdge revIdx withCap cap
  dsimp only
  apply congrArg (fun f : Unit → M (Slope × cp.FlowGraph Int E) => tick >>= f)
  funext _
  apply congrArg (fun f : Unit → M (Slope × cp.FlowGraph Int E) => tickN 1 >>= f)
  funext _
  by_cases h : cutoff = 0
  · simp only [h, decide_true, ite_true]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    congr 1
    funext st
    cases st.1 <;> rfl

end Proofs.Cpp.FlowCostSearch
