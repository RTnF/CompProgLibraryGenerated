import Proofs.Cpp.Gen.GraphFlow
import Proofs.Cpp.Lib.Basic

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.FlowCostSearch

variable {Cost E : Type} [Inhabited Cost] [Inhabited E] [Zero Cost] [Add Cost] [LT Cost] [DecidableLT Cost]
  [DecidableEq Cost] [Field "cap" E Cost] [Field "cost" E Cost] [Field "to" E Int]
  [NumericTraits "Cost" Cost] [ShiftInt Cost]

abbrev Labels (Cost : Type) := Array Cost × Array Int × Array Int
abbrev Pass (Cost : Type) := Array Cost × Array Int × Array Int × Bool

def target (e : E) : Int := Field.get (member := "to") e

def relaxes (e : E) (v : Int) (s : Pass Cost) : Bool :=
  let w := target e
  let d := get s.1 v + Field.get (member := "cost") e
  decide ((0 : Cost) < Field.get (member := "cap") e) &&
    (decide (get s.2.1 w = -1) || decide (d < get s.1 w))

def relaxEdge (e : E) (v i : Int) (s : Pass Cost) : Pass Cost :=
  let w := target e
  let d := get s.1 v + Field.get (member := "cost") e
  (set s.1 w d, set s.2.1 w v, set s.2.2.1 w i, true)

def edgeStep (row : Array E) (v : Int) (i : Int) (s : Pass Cost) : M (ForInStep (Pass Cost)) := do
  tick
  let e := get row i
  if relaxes e v s then
    return .yield (relaxEdge e v i s)
  else
    return .yield s

def rowStep (adj : Array (Array E)) (v : Int) (s : Pass Cost) : M (ForInStep (Pass Cost)) := do
  tick
  if decide (get s.2.1 v = -1) then
    return .yield s
  let row := get adj v
  let out ← forIn (range 0 (size row)) s (edgeStep row v)
  return .yield out

def passStep (g : cp.FlowGraph Cost E) (_ : Unit) (s : Labels Cost) : M (ForInStep (Labels Cost)) := do
  tick
  let out ← forIn (range 0 g.n_) (s.1, s.2.1, s.2.2, false) (rowStep g.adj)
  let targets := (out.1, out.2.1, out.2.2.1)
  if !out.2.2.2 then
    return .done targets
  return .yield targets

def search (g : cp.FlowGraph Cost E) (source : Int) : M (Labels Cost × cp.FlowGraph Cost E) := do
  tick
  let inf ← cp.FlowGraph.F_MAX (Cost := Cost) (E := E)
  tickN g.n_.toNat
  let dist := replicate g.n_ inf
  tickN g.n_.toNat
  let pv := set (replicate g.n_ (-1)) source source
  tickN g.n_.toNat
  let pe := replicate g.n_ 0
  let out ← forIn forever (set dist source 0, pv, pe) (passStep g)
  tickN out.1.size
  tickN out.2.1.size
  tickN out.2.2.size
  return (out, g)

omit [DecidableEq Cost] in
theorem search_program (g : cp.FlowGraph Cost E) (source : Int) :
    cp.FlowGraph.bellman_ford g source = search g source := by
  unfold cp.FlowGraph.bellman_ford search passStep rowStep edgeStep relaxes target relaxEdge
  dsimp only
  rfl

end Proofs.Cpp.FlowCostSearch
