import Proofs.Cpp.FlowDinicRange

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.Cpp.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [DecidableEq Arc]

/-- The generated depth-first search either proves that the remaining layer paths are blocked or pushes an exact bottleneck. -/
theorem dfs_spec (n : Network Arc Nat) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc)
    (laws : CapLaws (E := E)) (sink lim : Nat) (g : cp.FlowGraph Int E) (st : LayerState n g slot atSlot sink)
    (v depth : Nat) (hv : v < g.adj.size) (here : levelsView g.level v = some depth)
    (fuelEnough : rank (List.range g.adj.size) (levelsView g.level) depth ≤ lim)
    (limit : Int) (positive : 0 < limit) (clock : Nat) :
    ∃ (out : cp.FlowGraph Int E) (amount : Int) (finish used : Nat),
      (cp.FlowGraph.dfs_rec lim g (v : Int) (sink : Int) limit).run clock = some ((amount, out), finish) ∧
      Nonempty (LayerState n out slot atSlot sink) ∧ PhaseSame g out depth ∧
      SearchExit n g out slot v sink limit amount used ∧
      finish + 2 * cursorCharge g ≤ clock + 1 + 2 * cursorCharge out + 2 * used := by
  induction lim generalizing g st v depth limit clock with
  | zero =>
    have h := rank_step (List.range g.adj.size) (levelsView g.level) List.nodup_range v (List.mem_range.mpr hv) depth here
    omega
  | succ lim ih =>
    by_cases terminal : v = sink
    · subst v
      have route : PathPush n g g slot sink sink limit limit [] := ⟨.nil _, by simp, positive, le_rfl, by simp,
        fun _ h _ => h, rfl⟩
      refine ⟨g, limit, clock + 1, 0, ?_, ⟨st⟩, .refl g depth, .found [] rfl route, by omega⟩
      rw [dfs_frame]
      unfold frame
      simp only [decide_true, ite_true]
      rfl
    · have probe (curr : cp.FlowGraph Int E) (idx start : Nat) (state : LayerState n curr slot atSlot sink)
          (inside : v < curr.adj.size) (within : idx < (get curr.adj (v : Int)).size)
          (cursorAt : cursor curr v = (idx : Int)) (reached : levelsView curr.level v = some depth)
          (measure : rank (List.range curr.adj.size) (levelsView curr.level) depth ≤ lim + 1) :
          ∃ res finish, (tryEdge lim (v : Int) (sink : Int) limit (idx : Int) (pack none curr)).run start = some (res, finish) ∧
            ProbeExit n curr slot atSlot v sink idx depth limit start finish res := by
        obtain ⟨a, atTail, atIndex⟩ := state.layout.order.covers v inside idx within
        have identified : slot a = (v, idx) := by simp [state.layout.slotEq a, atTail, atIndex]
        have equivalence : eligible curr (v : Int) (idx : Int) = true ↔
            Usable n (capacity curr.adj slot) (levelsView curr.level) a := by
          simpa only [atTail, identified] using eligible_usable n curr slot state.layout.represents state.distance a
            (state.nonnegative a) depth (by rwa [atTail])
        have unique (b : Arc) (eq : slot b = (v, idx)) : b = a :=
          state.layout.represents.injective (eq.trans identified.symm)
        by_cases go : eligible curr (v : Int) (idx : Int) = true
        · have allow := equivalence.mp go
          have destination : levelsView curr.level (n.head a) = some (depth + 1) := by
            obtain ⟨j, hj, w⟩ := allow.2
            rw [atTail, reached, Option.some.injEq] at hj
            rwa [hj]
          have hsize : n.head a < curr.adj.size := state.layout.order.headBound a
          have smaller := rank_step (List.range curr.adj.size) (levelsView curr.level) List.nodup_range v
            (List.mem_range.mpr inside) depth reached
          obtain ⟨child, flow, after, used, childRun, ⟨childState⟩, childSame, exit, childCost⟩ :=
            ih curr state (n.head a) (depth + 1) hsize destination (by omega) (min limit (capacity curr.adj slot a))
              (lt_min positive allow.1) (start + 1)
          have destinationCpp : destOf (atEdge curr.adj (v : Int) (idx : Int)) = (n.head a : Int) := by
            have h := state.layout.represents.head_eq a
            rw [identified] at h
            exact h
          have capacityCpp : capOf (atEdge curr.adj (v : Int) (idx : Int)) = capacity curr.adj slot a := by
            unfold capacity
            rw [identified]
            rfl
          have eq := tryEdge_recursive lim curr child (v : Int) (sink : Int) (idx : Int) limit flow start after go
            (by rwa [destinationCpp, capacityCpp])
          cases exit with
          | blocked zero noTime intact blocked =>
            have hi : idx < (get child.adj (v : Int)).size := by rw [childSame.row_size]; exact within
            have childV : v < child.adj.size := by rwa [childSame.vertices]
            have childLv : levelsView child.level v = some depth := by rwa [childSame.level]
            have cursorStill : cursor child v = (idx : Int) := (childSame.earlier v depth reached (by omega)).trans cursorAt
            have childDead (b : Arc) (hb : slot b = (v, idx)) :
                Dead n (capacity child.adj slot) (levelsView child.level) sink b := by
              obtain rfl : b = a := unique b hb
              intro _
              simpa only [intact, childSame.level] using blocked
            let next := advanceCursor child (v : Int) (idx : Int)
            have nextState := childState.nextCursor v idx childV hi cursorStill childDead
            have hc := cursor_advance_charge child v idx (by rw [childState.cursors.size]; exact childV) cursorStill
            have nextSame := (childSame.earlier_than (by omega : depth ≤ depth + 1)).trans
              (advance_same childState.cursors v idx depth childV childLv)
            refine ⟨_, after, ?_, .skip next nextState nextSame intact ?_ ?_⟩
            · simpa only [zero, ite_true] using eq
            · have h := cursor_advanced child v (idx : Int) (by rwa [childState.cursors.size]) v
              rw [ite_eq_left rfl] at h
              simpa [next] using h
            · rw [noTime] at childCost
              change after + 2 * cursorCharge curr ≤ start + 2 * cursorCharge (advanceCursor child (v : Int) (idx : Int))
              rw [hc]
              omega
          | found path len flowPath =>
            obtain ⟨afterState, hsame, augmented⟩ := parent_push childState laws (childSame.earlier_than (by omega : depth ≤ depth + 1))
              a flow limit path allow flowPath
            have hflow : flow ≠ 0 := by have h := flowPath.positive; omega
            rw [len] at childCost
            rw [atTail, identified] at afterState hsame augmented
            refine ⟨_, after, ?_, .found _ flow (a :: path) afterState hsame augmented ?_⟩
            · simpa only [hflow, ite_false] using eq
            · simp only [List.length_cons, cursorCharge]
              unfold cursorCharge at childCost
              omega
        · have skip : eligible curr (v : Int) (idx : Int) = false := by
            cases guard : eligible curr (v : Int) (idx : Int) <;> simp_all
          have dead (b : Arc) (hb : slot b = (v, idx)) :
              Dead n (capacity curr.adj slot) (levelsView curr.level) sink b := by
            obtain rfl : b = a := unique b hb
            intro allowed
            exact False.elim (go (equivalence.mpr allowed))
          let next := advanceCursor curr (v : Int) (idx : Int)
          have charge := cursor_advance_charge curr v idx (by rwa [state.cursors.size]) cursorAt
          refine ⟨_, _, tryEdge_ineligible lim curr (v : Int) (sink : Int) (idx : Int) limit start skip,
            .skip next (state.nextCursor v idx inside within cursorAt dead) (advance_same state.cursors v idx depth inside reached) rfl ?_ ?_⟩
          · have h := cursor_advanced curr v (idx : Int) (by rwa [state.cursors.size]) v
            rw [ite_eq_left rfl] at h
            simpa [next] using h
          · change start + 1 + 2 * cursorCharge curr ≤ start + 2 * cursorCharge (advanceCursor curr (v : Int) (idx : Int))
            rw [charge]
            omega
      let initial := (cursor g v).toNat
      have ⟨nonneg, upper⟩ := st.cursors.within v hv
      have actual : cursor g v = (initial : Int) := (Int.toNat_of_nonneg nonneg).symm
      let stop := (get g.adj (v : Int)).size
      have inRow : initial ≤ stop := by change cursor g v ≤ (stop : Int) at upper; omega
      obtain ⟨state, finish, used, scan, finishState, same, exit, cost⟩ := scan_certified_row n slot atSlot lim v sink depth limit terminal g
        (fun curr i time stable vm ix cp lv unchanged => probe curr i time stable vm ix cp lv (by
          rw [unchanged.vertices, unchanged.level]
          exact fuelEnough))
        g st (.refl g depth) initial stop inRow rfl hv actual here (clock + 1)
      refine ⟨(answer state).2, (answer state).1, finish, used, ?_, finishState, same, exit, by omega⟩
      rw [dfs_frame]
      unfold frame
      have ne : ¬ (v : Int) = (sink : Int) := by omega
      have skip : ¬ decide ((v : Int) = (sink : Int)) = true := by rw [decide_eq_false ne]; decide
      rw [ite_eq_right skip]
      simp only [StateT.run_bind]
      have ht : tick.run clock = some ((), clock + 1) := rfl
      rw [ht]
      change ((forIn (range (cursor g v) (stop : Int)) (pack none g) (tryEdge lim (v : Int) (sink : Int) limit)).run
        (clock + 1) >>= _) = _
      rw [actual, scan]
      cases h : state.1 <;> simp [answer, h] <;> rfl

end Proofs.Cpp.FlowDinic
