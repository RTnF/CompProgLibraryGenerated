import Proofs.Cpp.FlowDinicBound

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.Cpp.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [NumericTraits "Cost" Int] [ShiftInt Int] [DecidableEq Arc]

abbrev DfsCall (E : Type) := cp.FlowGraph Int E → Int → Int → Int → M (Int × cp.FlowGraph Int E)

private def blockStepWith (call : DfsCall E) (s t : Int) (_ : Unit) (b : BlockFrame Int E) : M (ForInStep (BlockFrame Int E)) := do
  tick
  if !(decide (blockPending b > 0)) then
    return .done b
  else
    let amount := blockFlow b + blockPending b
    let bound ← cp.FlowGraph.F_MAX (Cost := Int) (E := E)
    let out ← call (blockGraph b) s t bound
    return .yield (packBlock out.2 amount out.1)

private def blockingStartWith (call : DfsCall E) (lim : Nat) (g : cp.FlowGraph Int E) (s t flow : Int) : M (BlockFrame Int E) := do
  let bound ← cp.FlowGraph.F_MAX (Cost := Int) (E := E)
  let first ← call g s t bound
  loopFuel lim (packBlock first.2 flow first.1) (blockStepWith call s t)

def blockingStart (lim : Nat) (g : cp.FlowGraph Int E) (s t flow : Int) : M (BlockFrame Int E) :=
  blockingStartWith cp.FlowGraph.dfs lim g s t flow

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem limit_run (t : Nat) : (cp.FlowGraph.F_MAX (Cost := Int) (E := E)).run t = some (flowLimit, t + 1) := rfl
private theorem some_bind {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

omit [DecidableEq Arc] in
private theorem loop_pending_zero (lim : Nat) (g : cp.FlowGraph Int E) (s t flow : Int) (clock : Nat) :
    (loopFuel (lim + 1) (packBlock g flow 0) (blockStep s t)).run clock = some (packBlock g flow 0, clock + 1) := by
  rw [loopFuel]
  unfold blockStep blockPending packBlock
  dsimp only
  simp only [show ¬ (0 : Int) > 0 by omega, decide_false, Bool.not_false, ite_true]
  rfl

omit [DecidableEq Arc] in
private theorem loop_pending_pos_with (call : DfsCall E) (lim : Nat) (g : cp.FlowGraph Int E) (s t flow d : Int)
    (pos : 0 < d) (clock : Nat) :
    (loopFuel (lim + 1) (packBlock g flow d) (blockStepWith call s t)).run clock =
      (blockingStartWith call lim g s t (flow + d)).run (clock + 1) := by
  rw [loopFuel]
  unfold blockStepWith blockPending blockFlow blockGraph packBlock blockingStartWith
  dsimp only
  have skip : ¬ (!decide (d > 0)) = true := by rw [decide_eq_true pos]; decide
  rw [ite_eq_right skip]
  simp only [StateT.run_bind, tick_run, limit_run, some_bind]
  rw [bind_assoc]
  rfl

omit [DecidableEq Arc] in
private theorem blocking_first_with (call : DfsCall E) (lim : Nat) (g out : cp.FlowGraph Int E) (s t flow d : Int) (clock finish : Nat)
    (ran : (call g s t flowLimit).run (clock + 1) = some ((d, out), finish)) :
    (blockingStartWith call lim g s t flow).run clock = (loopFuel lim (packBlock out flow d) (blockStepWith call s t)).run finish := by
  unfold blockingStartWith
  simp only [StateT.run_bind, limit_run, some_bind, ran]

/-- The blocking phase spends cursor credits and one bounded path traversal per augmentation. -/
theorem blocking_spec (n : Network Arc Nat) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (base : Capacity Arc) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc) (laws : CapLaws (E := E))
    (s t : Nat) (unique : s ≠ t) (upper : Int)
    (feasibleBound : ∀ amount f, SignedFeasible n arcs base s t amount f → amount ≤ upper)
    (limPos : 0 < flowLimit) (lim : Nat) (g : cp.FlowGraph Int E) (state : LayerState n g slot atSlot t)
    (hs : s < g.adj.size) (ht : t < g.adj.size) (head : levelsView g.level s = some 0)
    (fuelBound : g.adj.size ≤ fuel) (flow : Int) (flowNonneg : 0 ≤ flow)
    (valid : SignedFeasible n arcs base s t flow (fun a => base a - capacity g.adj slot a))
    (budget : phaseEnergy n (levelsView g.level) (capacity g.adj slot) arcs upper flow flowLimit + 1 ≤ lim)
    (clock : Nat) :
    ∃ (out : cp.FlowGraph Int E) (amount : Int) (finish : Nat),
      (blockingStart lim g (s : Int) (t : Int) flow).run clock = some (packBlock out amount 0, finish) ∧
      Nonempty (LayerState n out slot atSlot t) ∧ PhaseSame g out 0 ∧
      SignedFeasible n arcs base s t amount (fun a => base a - capacity out.adj slot a) ∧ flow ≤ amount ∧
      ¬ LayerPath n (capacity out.adj slot) (levelsView g.level) s t ∧
      finish + 2 * cursorCharge g ≤ clock + 3 + 2 * cursorCharge out +
        phaseEnergy n (levelsView g.level) (capacity g.adj slot) arcs upper flow flowLimit * (3 + 2 * g.adj.size) := by
  induction lim generalizing g state flow clock with
  | zero => omega
  | succ left ih =>
    have rankBound : rank (List.range g.adj.size) (levelsView g.level) 0 ≤ fuel := by
      have b := rank_le (List.range g.adj.size) (levelsView g.level) 0
      simp only [List.length_range] at b
      omega
    obtain ⟨next, pending, after, used, dfs, ⟨nextState⟩, kept, exit, spent⟩ :=
      dfs_spec n slot atSlot laws t fuel g state s 0 hs head rankBound flowLimit limPos (clock + 1)
    have ran : (cp.FlowGraph.dfs g (s : Int) (t : Int) flowLimit).run (clock + 1) = some ((pending, next), after) := by
      rw [cp.FlowGraph.dfs]
      exact dfs
    have unfoldBlock : (blockingStart (left + 1) g (s : Int) (t : Int) flow).run clock =
        (loopFuel (left + 1) (packBlock next flow pending) (blockStep (s : Int) (t : Int))).run after :=
      blocking_first_with cp.FlowGraph.dfs _ _ _ _ _ _ _ _ _ ran
    cases exit with
    | blocked val count intact noPath =>
      have hn : ¬ LayerPath n (capacity next.adj slot) (levelsView g.level) s t := by rwa [intact]
      have signed : SignedFeasible n arcs base s t flow (fun a => base a - capacity next.adj slot a) := by rwa [intact]
      refine ⟨next, flow, after + 1, ?_, ⟨nextState⟩, kept, signed, le_rfl, hn, ?_⟩
      · rw [unfoldBlock, val, loop_pending_zero]
      · rw [count] at spent
        omega
    | found path uses move =>
      have hs' : s < next.adj.size := by rwa [kept.vertices]
      have ht' : t < next.adj.size := by rwa [kept.vertices]
      have level' : levelsView next.level s = some 0 := by rwa [kept.level]
      have fuel' : next.adj.size ≤ fuel := by rwa [kept.vertices]
      have dpos := move.positive
      have amountNonneg : 0 ≤ flow + pending := by omega
      have pf := nextState.nonnegative
      rw [move.after] at pf
      have signed := signed_augmentation n arcs nd all base (capacity g.adj slot) s t flow path move.route valid pending pf
      rw [← move.after] at signed
      have decrease := energy_drops n g next slot arcs nd all s t flowLimit pending upper flow limPos
        (feasibleBound (flow + pending) _ signed) path move
      have cut : phaseEnergy n (levelsView next.level) (capacity next.adj slot) arcs upper (flow + pending) flowLimit + 1 ≤ left := by
        rw [kept.level]
        omega
      obtain ⟨out, amount, finish, tail, stateOut, phase, net, monotone, blocked, tailWork⟩ :=
        ih next nextState hs' ht' level' fuel' (flow + pending) amountNonneg signed cut (after + 1)
      have len := unit_length n (levelsView g.level) (List.range g.adj.size) move.route (fun a ha => (move.usable a ha).2)
        (List.mem_range.mpr ht) (fun a => List.mem_range.mpr (state.layout.order.tailBound a))
      simp only [List.length_range] at len
      have timeTokens := Nat.mul_le_mul_right (3 + 2 * g.adj.size)
        (show phaseEnergy n (levelsView g.level) (capacity next.adj slot) arcs upper (flow + pending) flowLimit + 1 ≤
          phaseEnergy n (levelsView g.level) (capacity g.adj slot) arcs upper flow flowLimit by omega)
      rw [Nat.add_mul, Nat.one_mul] at timeTokens
      rw [kept.vertices, kept.level] at tailWork
      refine ⟨out, amount, finish, ?_, stateOut, kept.trans phase, net, by omega, ?_, ?_⟩
      · have step : (loopFuel (left + 1) (packBlock next flow pending) (blockStep (s : Int) (t : Int))).run after =
            (blockingStart left next (s : Int) (t : Int) (flow + pending)).run (after + 1) :=
          loop_pending_pos_with cp.FlowGraph.dfs left next _ _ flow pending dpos after
        rw [unfoldBlock, step, tail]
      · rwa [kept.level] at blocked
      · rw [uses] at spent
        omega

end Proofs.Cpp.FlowDinic
