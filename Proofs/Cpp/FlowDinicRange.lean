import Proofs.Cpp.FlowDinicState

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.Cpp.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

private theorem range_as_nat (i stop : Nat) : range (i : Int) (stop : Int) =
    (List.range' i (stop - i)).map (fun k : Nat => (k : Int)) := by
  have hn : ((stop : Int) - (i : Int)).toNat = stop - i := by omega
  rw [range, hn, List.range'_eq_map_range, List.map_map]
  simp [Function.comp_def]

theorem range_next (i stop : Nat) (has : i < stop) : range (i : Int) (stop : Int) =
    (i : Int) :: range ((i + 1 : Nat) : Int) (stop : Int) := by
  rw [range_as_nat, range_as_nat]
  have h : stop - i = (stop - (i + 1)) + 1 := by omega
  conv => lhs; rw [h]
  rw [List.range'_succ]
  rfl

theorem range_finished (i : Nat) : range (i : Int) (i : Int) = [] := by simp [range]

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [DecidableEq Arc]

inductive SearchExit (n : Network Arc Nat) (before after : cp.FlowGraph Int E) (slot : Arc → Slot)
    (v sink : Nat) (limit amount : Int) (used : Nat) : Prop where
  | blocked : amount = 0 → used = 0 → after.adj = before.adj →
      ¬ LayerPath n (capacity before.adj slot) (levelsView before.level) v sink → SearchExit n before after slot v sink limit amount used
  | found (path : List Arc) : used = path.length → PathPush n before after slot v sink limit amount path →
      SearchExit n before after slot v sink limit amount used

inductive ProbeExit (n : Network Arc Nat) (before : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (v sink i depth : Nat) (limit : Int) (clock finish : Nat) :
    ForInStep (Frame Int E) → Prop where
  | skip (after : cp.FlowGraph Int E) : LayerState n after slot atSlot sink → PhaseSame before after depth →
      after.adj = before.adj → cursor after v = ((i + 1 : Nat) : Int) →
      finish + 2 * cursorCharge before ≤ clock + 2 * cursorCharge after →
      ProbeExit n before slot atSlot v sink i depth limit clock finish (.yield (pack none after))
  | found (after : cp.FlowGraph Int E) (amount : Int) (path : List Arc) :
      LayerState n after slot atSlot sink → PhaseSame before after depth →
      PathPush n before after slot v sink limit amount path →
      finish + 2 * cursorCharge before ≤ clock + 2 * cursorCharge after + 2 * path.length →
      ProbeExit n before slot atSlot v sink i depth limit clock finish (.done (pack (some (amount, after)) after))

def answer (st : Frame Int E) : Int × cp.FlowGraph Int E := st.1.getD (0, frameGraph st)

/-- A finite row advances past every failed slot and stops immediately after a successful route. -/
theorem scan_certified_row (n : Network Arc Nat) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc)
    (lim : Nat) (v sink depth : Nat) (limit : Int) (different : v ≠ sink) (root : cp.FlowGraph Int E)
    (probe : ∀ (g : cp.FlowGraph Int E) (i clock : Nat), LayerState n g slot atSlot sink →
      v < g.adj.size → i < (get g.adj (v : Int)).size → cursor g v = (i : Int) → levelsView g.level v = some depth →
      PhaseSame root g depth →
      ∃ state finish, (tryEdge lim (v : Int) (sink : Int) limit (i : Int) (pack none g)).run clock = some (state, finish) ∧
        ProbeExit n g slot atSlot v sink i depth limit clock finish state)
    (g : cp.FlowGraph Int E) (good : LayerState n g slot atSlot sink) (fromRoot : PhaseSame root g depth) (i stop : Nat)
    (before : i ≤ stop) (sizeRow : (get g.adj (v : Int)).size = stop) (hv : v < g.adj.size)
    (atPos : cursor g v = (i : Int)) (here : levelsView g.level v = some depth) (clock : Nat) :
    ∃ (state : Frame Int E) (finish used : Nat),
      (forIn (range (i : Int) (stop : Int)) (pack none g) (tryEdge lim (v : Int) (sink : Int) limit)).run clock =
        some (state, finish) ∧ Nonempty (LayerState n (answer state).2 slot atSlot sink) ∧ PhaseSame g (answer state).2 depth ∧
      SearchExit n g (answer state).2 slot v sink limit (answer state).1 used ∧
      finish + 2 * cursorCharge g ≤ clock + 2 * cursorCharge (answer state).2 + 2 * used := by
  induction countEq : stop - i using Nat.strong_induction_on generalizing g i clock with
  | h remaining ih =>
    by_cases finished : i = stop
    · subst i
      have noRoute : ¬ LayerPath n (capacity g.adj slot) (levelsView g.level) v sink := by
        intro route
        obtain ⟨a, va, viable, tail⟩ := layer_path_first n _ _ v sink different route
        have bound := good.layout.order.positionBound a
        rw [va, sizeRow] at bound
        have skipped : ((slot a).2 : Int) < cursor g (n.tail a) := by
          rw [good.layout.slotEq, va, atPos]
          simp only
          omega
        exact good.cursors.prefix_dead a skipped viable tail
      refine ⟨pack none g, clock, 0, ?_, ⟨good⟩, .refl g depth, .blocked rfl rfl rfl noRoute, by simp [answer, pack, frameGraph]⟩
      rw [range_finished]
      rfl
    · have has : i < stop := by omega
      have edgeRange : i < (get g.adj (v : Int)).size := by rwa [sizeRow]
      obtain ⟨state, after, run, effect⟩ := probe g i clock good hv edgeRange atPos here fromRoot
      cases effect with
      | skip next nextGood same untouched advanced charge =>
        have hc : stop - (i + 1) < remaining := by omega
        obtain ⟨out, finish, used, tailRun, st, kept, exit, time⟩ := ih (stop - (i + 1)) hc next nextGood (fromRoot.trans same) (i + 1) (by omega)
          ((same.row_size v).trans sizeRow) (by rwa [same.vertices]) advanced (by rwa [same.level]) after rfl
        refine ⟨out, finish, used, ?_, st, same.trans kept, ?_, by omega⟩
        · rw [range_next i stop has, List.forIn_cons, StateT.run_bind, run]
          exact tailRun
        · cases exit with
          | blocked zero empty eq noPath =>
            refine .blocked zero empty (eq.trans untouched) ?_
            simpa only [untouched, same.level] using noPath
          | found path used route =>
            refine .found path used ⟨route.route, ?_, route.positive, route.within_limit, ?_, ?_, ?_⟩
            · simpa only [untouched, same.level] using route.usable
            · simpa only [untouched] using route.supply
            · simpa only [untouched] using route.maximal
            · simpa only [untouched] using route.after
      | found afterGraph val path valid same route cost =>
        refine ⟨pack (some (val, afterGraph)) afterGraph, after, path.length, ?_, ⟨valid⟩, same, .found path rfl route, cost⟩
        rw [range_next i stop has, List.forIn_cons, StateT.run_bind, run]
        rfl

end Proofs.Cpp.FlowDinic
