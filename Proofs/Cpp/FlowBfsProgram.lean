import Proofs.Cpp.Gen.GraphFlow
import Proofs.Math.FlowBfsMath
import Proofs.Cpp.Lib.Basic

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.FlowBfs

variable {Cost E : Type} [Inhabited E] [Zero Cost] [LT Cost] [DecidableLT Cost]
  [Field "cap" E Cost] [Field "to" E Int]

abbrev BfsState := Array Int × List Int

def target (e : E) : Int := Field.get (member := "to") e

def positive (e : E) : Prop := (0 : Cost) < Field.get (member := "cap") e

instance (e : E) : Decidable (positive (Cost := Cost) e) := inferInstanceAs (Decidable ((0 : Cost) < _))

def edgeStep (v : Int) (e : E) (b : BfsState) : M (ForInStep BfsState) := do
  tick
  if decide (positive (Cost := Cost) e) && decide (get b.1 (target e) = -1) then
    let level := set b.1 (target e) (get b.1 v + 1)
    let q ← queuePush b.2 (target e)
    return .yield (level, q)
  else
    return .yield (b.1, b.2)

def vertexStep (adj : Array (Array E)) (_ : Unit) (b : BfsState) : M (ForInStep BfsState) := do
  tick
  if !(decide ((UInt64.ofNat b.2.length) ≠ 0)) then
    return .done (b.1, b.2)
  else
    let v ← queueFront b.2
    let q ← queuePop b.2
    let out ← forIn (get adj v) (b.1, q) (edgeStep (Cost := Cost) v)
    return .yield (out.1, out.2)

def bfsProgram (g : cp.FlowGraph Cost E) (s : Int) : M (cp.FlowGraph Cost E) := do
  tick
  tickN g.n_.toNat
  let level := set (replicate g.n_ (-1)) s 0
  let q ← queuePush ([] : List Int) s
  let out ← forIn forever (level, q) (vertexStep (Cost := Cost) g.adj)
  return { g with level := out.1 }

theorem bfs_program (g : cp.FlowGraph Cost E) (s : Int) : cp.FlowGraph.bfs g s = bfsProgram g s := by
  rw [cp.FlowGraph.bfs]
  unfold bfsProgram vertexStep edgeStep positive target
  dsimp only
  rfl

omit [Inhabited E] in
theorem edge_discovered (u : Int) (e : E) (b : BfsState) (t : Nat)
    (hp : positive (Cost := Cost) e) (h : get b.1 (target e) = -1) :
    (edgeStep (Cost := Cost) u e b).run t =
      some (.yield (set b.1 (target e) (get b.1 u + 1), b.2 ++ [target e]), t + 2) := by
  unfold edgeStep
  rw [ite_eq_left (by simp [hp, h])]
  rfl

omit [Inhabited E] in
theorem edge_ignored (u : Int) (e : E) (b : BfsState) (t : Nat)
    (h : ¬ (positive (Cost := Cost) e ∧ get b.1 (target e) = -1)) :
    (edgeStep (Cost := Cost) u e b).run t = some (.yield b, t + 1) := by
  unfold edgeStep
  have hskip : ¬ (decide (positive (Cost := Cost) e) && decide (get b.1 (target e) = -1)) = true := by
    simp [h]
  rw [ite_eq_right hskip]
  rfl

end Proofs.Cpp.FlowBfs
