import Proofs.Cpp.FlowCostSlopeProgram
import Proofs.Math.FlowResidualOptimality

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [NumericTraits "Cost" Int] [ShiftInt Int] [DecidableEq Arc]

abbrev flowLimit : Int := ShiftInt.shr (NumericTraits.maximum (tag := "Cost") (α := Int)) 2

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem limit_run (t : Nat) : (cp.FlowGraph.F_MAX (Cost := Int) (E := E)).run t = some (flowLimit, t + 1) := rfl
private theorem some_bind {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

private theorem run_choice {α : Type} (test : Prop) [Decidable test] (yes no : α) (clock : Nat) :
    (if test then (pure yes : M α) else pure no).run clock = some ((if test then yes else no), clock) := by
  split <;> rfl

def finishSlope (g : cp.FlowGraph Int E) (result : Slope) (amount cost : Int) : ForInStep (SlopeState E) :=
  .done (packSlope (some (result, g)) g result amount cost)

def nextSlope (g : cp.FlowGraph Int E) (result : Slope) (amount cost cutoff : Int) : ForInStep (SlopeState E) :=
  if decide (amount ≥ cutoff) then finishSlope g result amount cost else .yield (packSlope none g result amount cost)

theorem slope_unreachable_step (g : cp.FlowGraph Int E) (s t cutoff : Int) (result : Slope) (amount cost : Int)
    (b : Pass Int) (clock afterSearch : Nat)
    (search : (cp.FlowGraph.bellman_ford g s).run (clock + 1) = some ((labelPart b, g), afterSearch))
    (absent : get b.2.1 t = -1) :
    (slopeStep s t cutoff () (packSlope none g result amount cost)).run clock =
      some (finishSlope g result amount cost, afterSearch) := by
  unfold slopeStep finishSlope
  simp only [packSlope, slopeGraph, slopeResult, slopeAmount, slopeCost, StateT.run_bind, tick_run, some_bind]
  rw [search]
  simp only [some_bind, labelPart, absent, decide_true, ite_true]
  rfl

theorem slope_path_step (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (rep : Represents n g.adj slot) (laws : CapLaws (E := E)) (atSlot : Int → Int → Option Arc)
    (layout : Layout n g (capacity g.adj slot) atSlot) (slotEq : ∀ a, slot a = (n.tail a, layout.position a))
    (validRev : ∀ a, 0 ≤ revIdx (readSlot g.adj (slot a))) (s t : Nat) (cutoff : Int)
    (slope : Slope) (amount cost : Int) (b : Pass Int) (clock afterSearch : Nat)
    (search : (cp.FlowGraph.bellman_ford g (s : Int)).run (clock + 1) = some ((labelPart b, g), afterSearch))
    (seen : known b t = true) (path : List Arc) (route : Path n s t path) (enough : path.length < fuel)
    (positive : ∀ a ∈ path, 0 < capacity g.adj slot a)
    (parents : ∀ a ∈ path, n.head a ≠ s ∧ get b.2.1 (n.head a : Int) = (n.tail a : Int) ∧
      get b.2.2.1 (n.head a : Int) = (layout.position a : Int)) (limPos : 0 < flowLimit) :
    ∃ (d : Int) (out : Array (Array E)),
      (slopeStep (s : Int) (t : Int) cutoff () (packSlope none g slope amount cost)).run clock =
        some (nextSlope {g with adj := out} (slope.push (amount + d, cost + d * label b t))
          (amount + d) (cost + d * label b t) cutoff, afterSearch + 4 + 2 * path.length) ∧
      0 < d ∧ d ≤ flowLimit ∧ (∀ a ∈ path, d ≤ capacity g.adj slot a) ∧
      (∀ a ≤ flowLimit, (∀ e ∈ path, a ≤ capacity g.adj slot e) → a ≤ d) ∧
      Represents n out slot ∧ (out.size = g.adj.size ∧ ∀ v : Nat, out[v]!.size = g.adj[v]!.size) ∧
      (∀ a, 0 ≤ revIdx (readSlot out (slot a))) ∧ capacity out slot = augment n d (capacity g.adj slot) path.reverse := by
  obtain ⟨d, hMin, hPos, hBound, supply, maxValue⟩ := bottleneck_loop n g (capacity g.adj slot) atSlot layout b s t
    path route fuel enough positive parents flowLimit limPos (afterSearch + 1)
  have atIndex (a : Arc) (ha : a ∈ path) : n.head a ≠ s ∧ get b.2.1 (n.head a : Int) = ((slot a).1 : Int) ∧
      get b.2.2.1 (n.head a : Int) = ((slot a).2 : Int) := by
    rw [slotEq]
    exact parents a ha
  obtain ⟨out, hPush, outRep, dims, revOk, capEq⟩ := push_parent_loop n slot laws b s t path route fuel enough atIndex
    g.adj rep validRev d (afterSearch + 1 + path.length + 1 + 1)
  refine ⟨d, out, ?_, hPos, hBound, supply, maxValue, outRep, dims, revOk, capEq⟩
  have parentPresent : get b.2.1 (t : Int) ≠ -1 := ((known_iff b t).mp seen).2
  unfold slopeStep nextSlope finishSlope
  simp only [packSlope, slopeGraph, slopeResult, slopeAmount, slopeCost, StateT.run_bind, tick_run, some_bind]
  rw [search]
  simp only [some_bind, labelPart, parentPresent, decide_false, Bool.false_eq_true, ite_false, limit_run, label]
  change ((loopFuel fuel (flowLimit, (t : Int)) (bottleneckStep g.adj (s : Int) b.2.1 b.2.2.1)).run (afterSearch + 1) >>= _) = _
  rw [hMin]
  simp only [some_bind, StateT.run_bind, tick_run]
  change ((loopFuel fuel (g.adj, (t : Int)) (pushParentStep (s : Int) b.2.1 b.2.2.1 d)).run
    (afterSearch + 1 + path.length + 1 + 1) >>= _) = _
  rw [hPush]
  have eq : afterSearch + 1 + path.length + 1 + 1 + path.length + 1 = afterSearch + 4 + 2 * path.length := by omega
  rw [eq]
  simp only [some_bind]
  exact run_choice (decide (cutoff ≤ amount + d) = true) _ _ _

end Proofs.Cpp.FlowCostSearch
