import Proofs.Cpp.FlowDinicDfs

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.Cpp.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

variable {Cost E : Type} [Inhabited E] [Zero Cost] [Add Cost] [Sub Cost] [LT Cost] [DecidableLT Cost]
  [DecidableEq Cost] [Min Cost] [Field "cap" E Cost] [Field "to" E Int] [Field "rev" E Int]
  [WriteField "cap" E Cost] [NumericTraits "Cost" Cost] [ShiftInt Cost]

abbrev BlockFrame (Cost E : Type) := Int × Int × Array (Array E) × Array Int × Array Int × Cost × Cost
abbrev MaxFrame (Cost E : Type) := Option (Cost × cp.FlowGraph Cost E) × Int × Int × Array (Array E) × Array Int × Array Int × Cost

def packBlock (g : cp.FlowGraph Cost E) (flow pending : Cost) : BlockFrame Cost E :=
  (g.n_, g.m_, g.adj, g.level, g.iter, flow, pending)

def blockGraph (b : BlockFrame Cost E) : cp.FlowGraph Cost E := ⟨b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1⟩
def blockFlow (b : BlockFrame Cost E) : Cost := b.2.2.2.2.2.1
def blockPending (b : BlockFrame Cost E) : Cost := b.2.2.2.2.2.2

def packMax (ret : Option (Cost × cp.FlowGraph Cost E)) (g : cp.FlowGraph Cost E) (flow : Cost) : MaxFrame Cost E :=
  (ret, g.n_, g.m_, g.adj, g.level, g.iter, flow)

def maxGraph (b : MaxFrame Cost E) : cp.FlowGraph Cost E := ⟨b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2.1⟩
def maxAmount (b : MaxFrame Cost E) : Cost := b.2.2.2.2.2.2

def blockStep (s t : Int) (_ : Unit) (b : BlockFrame Cost E) : M (ForInStep (BlockFrame Cost E)) := do
  tick
  if !(decide (blockPending b > 0)) then
    return .done b
  else
    let amount := blockFlow b + blockPending b
    let bound ← cp.FlowGraph.F_MAX (E := E)
    let out ← cp.FlowGraph.dfs (blockGraph b) s t bound
    return .yield (packBlock out.2 amount out.1)

def initializeCursors (g : cp.FlowGraph Cost E) : cp.FlowGraph Cost E :=
  { g with iter := replicate g.n_ 0 }

def maxStep (s t : Int) (_ : Unit) (b : MaxFrame Cost E) : M (ForInStep (MaxFrame Cost E)) := do
  tick
  let g ← cp.FlowGraph.bfs (maxGraph b) s
  if decide (get g.level t = -1) then
    return .done (packMax (some (maxAmount b, g)) g (maxAmount b))
  else
    tickN g.n_.toNat
    let bound ← cp.FlowGraph.F_MAX (E := E)
    let c ← cp.FlowGraph.dfs (initializeCursors g) s t bound
    let out ← forIn forever (packBlock c.2 (maxAmount b) c.1) (blockStep s t)
    return .yield (packMax none (blockGraph out) (blockFlow out))

def maxProgram (g : cp.FlowGraph Cost E) (s t : Int) : M (Cost × cp.FlowGraph Cost E) := do
  tick
  let out ← forIn forever (packMax none g 0) (maxStep s t)
  match out.1 with
  | some r => return r
  | none => failure

theorem max_flow_program (g : cp.FlowGraph Cost E) (s t : Int) : cp.FlowGraph.max_flow g s t = maxProgram g s t := by
  unfold cp.FlowGraph.max_flow maxProgram maxStep blockStep packBlock blockGraph blockFlow blockPending packMax maxGraph
    maxAmount initializeCursors
  dsimp only
  apply congrArg (fun body : Unit → M (Cost × cp.FlowGraph Cost E) => tick >>= body)
  funext _
  congr 1
  funext st
  cases st.1 <;> rfl

end Proofs.Cpp.FlowDinic
