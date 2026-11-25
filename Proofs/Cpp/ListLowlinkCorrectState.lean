import Proofs.Cpp.ListLowlinkFrame

namespace Proofs.Cpp.ListLowlink

open Proofs.Cpp Proofs.LowlinkInv Proofs.LowlinkRoot Proofs.LowlinkPush Proofs.LowlinkPop Proofs.LowlinkScan
open Proofs.LowlinkMultigraph

namespace DfsState

abbrev seen (r : DfsState) := r.1
abbrev order (r : DfsState) := r.2.1
abbrev low (r : DfsState) := r.2.2.1
abbrev points (r : DfsState) := r.2.2.2.1
abbrev bridges (r : DfsState) := r.2.2.2.2.1
abbrev counter (r : DfsState) := r.2.2.2.2.2

def mark (r : DfsState) (v : Nat) : DfsState :=
  (set r.seen v true, set r.order v r.counter, set r.low v (get (set r.order v r.counter) v),
    r.points, r.bridges, r.counter + 1)

def withLow (r : DfsState) (arr : Array Int) : DfsState :=
  (r.seen, r.order, arr, r.points, r.bridges, r.counter)

def withPoints (r : DfsState) (points : Array Int) : DfsState :=
  (r.seen, r.order, r.low, points, r.bridges, r.counter)

def withBridges (r : DfsState) (bridges : Array (Int × Int)) : DfsState :=
  (r.seen, r.order, r.low, r.points, bridges, r.counter)

end DfsState

abbrev LoopState.core (r : LoopState) : DfsState :=
  (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1)

abbrev LoopState.art (r : LoopState) := r.2.2.2.2.2.2.1
abbrev LoopState.skipped (r : LoopState) := r.2.2.2.2.2.2.2.1
abbrev LoopState.children (r : LoopState) := r.2.2.2.2.2.2.2.2

def LoopState.ofCore (r : DfsState) (art skipped : Bool) (children : Int) : LoopState :=
  (r.seen, r.order, r.low, r.points, r.bridges, r.counter, art, skipped, children)

def LowStable (start r : DfsState) : Prop :=
  (∀ i : Nat, start.seen[i]! = true → r.seen[i]! = true) ∧
  (∀ i : Nat, start.seen[i]! = true → r.low[i]! = start.low[i]!)

theorem LowStable.keepLow {start r : DfsState} (A : LowStable start r) (v : Nat) (value : Int)
    (hv : v < r.low.size) (hnew : start.seen[v]! = false) :
    LowStable start (r.withLow (set r.low v value)) := by
  refine ⟨A.1, fun i hi => ?_⟩
  have hne : i ≠ v := by intro h; subst i; simp [hnew] at hi
  simp only [DfsState.withLow, DfsState.low, getElemBang_set r.low (v : Int) value i (by simpa using hv), Int.toNat_natCast,
    hne, ite_false]
  exact A.2 i hi

theorem LowStable.trans {x y z : DfsState} (A : LowStable x y) (B : LowStable y z) : LowStable x z :=
  ⟨fun i hi => B.1 i (A.1 i hi), fun i hi => (B.2 i (A.1 i hi)).trans (A.2 i hi)⟩

def capAt (st : St) (v : Nat) (copies : Nat) : Option Int :=
  if 2 ≤ copies then some (st.O (st.P v).toNat) else none

structure VisitArrays (n : Nat) (st : St) (r : DfsState) : Prop where
  seenSize : r.seen.size = n
  orderSize : r.order.size = n
  lowSize : r.low.size = n
  visits : VisitProjection r.seen r.order r.counter st

structure FrameStart {E : Type} [Inhabited E] [Field "to" E Int]
    (adj : Array (Array E)) (n v : Nat) (parent : Int) (st : St) (r : DfsState) : Prop where
  valid : MInv n (rowHeads adj n) (rowEnds adj n) st
  depth : 0 < st.sp
  top : st.Sk (st.sp - 1) = v
  parentEq : st.P v = parent
  cursor : st.It v = (rowHeads adj n v : Int)
  lowEq : st.L v = r.counter
  sepZero : st.Sp v = 0
  fresh : r.seen[v]! = false
  arrays : VisitArrays n st (r.mark v)
  points : PointsMatch st none r.points
  bridges : BridgesMatch (listTargets adj) st r.bridges

structure CursorState {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E))
    (n v : Nat) (start st : St) (args : DfsState) (pref : List E) (r : LoopState) : Prop where
  valid : MInv n (rowHeads adj n) (rowEnds adj n) st
  frame : SameFrame start st v
  arrays : VisitArrays n st r.core
  cursor : st.It v = (cursorIdx adj n v pref : Int)
  cap : r.core.low[v]! = effectiveLow (st.L v) (capAt st v ((edgeTargets pref).count (st.P v)))
  skipped : r.skipped = decide (0 < (edgeTargets pref).count (st.P v))
  art : ArtFrame st v r.art r.children
  points : PointsMatch st none r.core.points
  bridges : BridgesMatch (listTargets adj) st r.core.bridges
  stable : LowStable args r.core

theorem FrameStart.mem {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n v : Nat} {p : Int} {st : St} {args : DfsState} (H : FrameStart adj n v p st args) : v ∈ st.Vis := by
  have hw := (H.valid.sk_mem (st.sp - 1) (by have := H.depth; omega)).1
  rwa [H.top] at hw

theorem CursorState.mem {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n v : Nat} {start st : St} {args : DfsState} {pref : List E} {r : LoopState}
    (H : CursorState adj n v start st args pref r) (hv : v ∈ start.Vis) : v ∈ st.Vis :=
  H.frame.grows.subset hv

theorem enter_cursor {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n v : Nat} {p : Int} {st : St} {args : DfsState}
    (H : FrameStart adj n v p st args) :
    CursorState adj n v st st args [] (LoopState.ofCore (args.mark v) false false 0) := by
  have hv := H.valid.vis_lt v H.mem
  have ho : args.order.size = n := by
    simpa [DfsState.mark, DfsState.order] using H.arrays.orderSize
  have hl : args.low.size = n := by
    simpa [DfsState.mark, DfsState.low] using H.arrays.lowSize
  have hu : args.seen.size = n := by
    simpa [DfsState.mark, DfsState.seen] using H.arrays.seenSize
  have hc := Cells.enter n v args.seen args.order args.low args.counter
    (get (set args.order v args.counter) v) hv H.fresh ho hl
  have hm := get_marked args.seen v (by omega)
  refine ⟨H.valid, SameFrame.refl _ _, H.arrays, by rw [H.cursor, cursor_nil],
    ?_, by simp [edgeTargets, LoopState.ofCore], art_frame_enter _ _ H.sepZero, H.points, H.bridges,
    ⟨hm.2, fun i hi => (hc.preserves i hi).2⟩⟩
  change (set args.low v (get (set args.order v args.counter) v))[v]! = _
  simp only [edgeTargets, List.map_nil, List.count_nil, capAt, effectiveLow]
  rw [get_eq, getElemBang_set _ _ _ _ (by simpa [hl] using hv)]
  simp only [Int.toNat_natCast, ite_true]
  rw [getElemBang_set _ _ _ _ (by simpa [ho] using hv)]
  simp [H.lowEq]


def visitedRow (r : LoopState) (v w : Nat) (parent : Int) : LoopState :=
  if decide ((w : Int) = parent) && !r.skipped then LoopState.ofCore r.core r.art true r.children
  else LoopState.ofCore
    (r.core.withLow (set r.core.low v (min r.core.low[v]! r.core.order[w]!)))
    r.art r.skipped r.children

theorem visit_cursor_step {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n v : Nat} {p : Int} {start st : St} {args : DfsState} {pref suff : List E} {e : E}
    {r : LoopState} (A : FrameStart adj n v p start args) (H : CursorState adj n v start st args pref r)
    (hrow : (Row adj v).toList = pref ++ e :: suff)
    (hNN : 0 ≤ (Field.get (member := "to") e : Int))
    (hw : r.core.seen[(Field.get (member := "to") e : Int).toNat]! = true) :
    CursorState adj n v start (advanceVisited st v (Field.get (member := "to") e : Int).toNat)
      args (pref ++ [e]) (visitedRow r v (Field.get (member := "to") e : Int).toNat p) := by
  let w := (Field.get (member := "to") e : Int).toNat
  let next := advanceVisited st v w
  have eta : (w : Int) = (Field.get (member := "to") e : Int) := Int.toNat_of_nonneg hNN
  have hvis := H.mem A.mem
  have hv := H.valid.vis_lt v hvis
  have hd : 0 < st.sp := by rw [H.frame.depth]; exact A.depth
  have ht := H.frame.top A.depth A.top
  have hp : st.P v = p := (H.frame.visited v A.mem).2.trans A.parentEq
  have hseen := (H.arrays.visits.marked v).mpr hvis
  obtain ⟨hi', hVisit⟩ := advance_visited_inv H.valid H.arrays.visits hd ht hw (fun hne => by
    obtain ⟨hbound, hed⟩ := cursor_lookup hrow hv (Ne.symm hne)
    exact ⟨cursorIdx adj n v pref, H.cursor.symm, by exact_mod_cast hbound, hed⟩)
  have hstep : SameFrame st next v := advance_same_frame _ _ _
  have hfin : next.Fi = st.Fi := by unfold next advanceVisited; split <;> rfl
  have htopFin := (H.valid.sk_mem (st.sp - 1) (by omega)).2
  rw [ht] at htopFin
  obtain ⟨hpts, hbridge⟩ := output_unchanged H.valid
    (scan_preserves_finished (w := w) htopFin) hfin (fun x hx => (hstep.visited x hx).1)
    _ _ _ H.points H.bridges
  have hit : next.It v = (cursorIdx adj n v (pref ++ [e]) : Int) := by
    rw [cursor_step]
    change next.It v = (↑(cursorIdx adj n v pref + if w = v then 0 else 1) : Int)
    by_cases h : v = w
    · rw [show next.It v = st.It v by simp only [next, advanceVisited, h, ite_true]]
      simpa only [ite_eq_left h.symm, Nat.add_zero] using H.cursor
    · simp [next, advanceVisited, h, Ne.symm h, scanS, upd_same, H.cursor]
  have hZ : next.P v = st.P v := (hstep.visited v hvis).2
  have hO : next.O = st.O := by unfold next advanceVisited; split <;> rfl
  have hout := advance_visited_low H.valid H.arrays.visits hseen hw (edgeTargets pref) r.skipped H.skipped
  simp only at hout
  rw [← (show edgeTargets (pref ++ [e]) = edgeTargets pref ++ [(w : Int)] by simp [edgeTargets, eta])] at hout
  have hold := H.cap
  unfold capAt at hold
  rw [← hold] at hout
  have hpair :
      (if decide ((w : Int) = p) && !r.skipped then (true, r.core.low[v]!)
        else (r.skipped, min r.core.low[v]! r.core.order[w]!)) =
      (decide (0 < (edgeTargets (pref ++ [e])).count (next.P v)),
        effectiveLow (next.L v) (capAt next v ((edgeTargets (pref ++ [e])).count (next.P v)))) := by
    simp only [capAt, hZ, hp, hO]
    simpa only [hp] using hout
  have hl : v < r.core.low.size := by rw [H.arrays.lowSize]; exact hv
  have hs := getElemBang_set r.core.low (v : Int) (min r.core.low[v]! r.core.order[w]!) v (by simpa using hl)
  simp only [Int.toNat_natCast, ite_true] at hs
  change CursorState adj n v start next args (pref ++ [e]) (visitedRow r v w p)
  by_cases choose : (decide ((w : Int) = p) && !r.skipped) = true
  · simp only [visitedRow, ite_eq_left choose] at hpair ⊢
    exact ⟨hi', H.frame.trans hstep, ⟨H.arrays.seenSize, H.arrays.orderSize, H.arrays.lowSize, hVisit⟩, hit,
      (congrArg Prod.snd hpair), (congrArg Prod.fst hpair), art_frame_advance _ _ _ _ _ H.art,
      hpts, hbridge, H.stable⟩
  · simp only [visitedRow, ite_eq_right choose] at hpair ⊢
    refine ⟨hi', H.frame.trans hstep,
      ⟨H.arrays.seenSize, H.arrays.orderSize, (size_set _ _ _).trans H.arrays.lowSize, hVisit⟩, hit, ?_,
      (congrArg Prod.fst hpair), art_frame_advance _ _ _ _ _ H.art, hpts, hbridge,
      H.stable.keepLow _ _ hl A.fresh⟩
    exact hs.trans (congrArg Prod.snd hpair)


theorem edge_mem_of_split {E : Type} {row pref suff : List E} {e : E} (hs : row = pref ++ e :: suff) :
    e ∈ row := by simp [hs]

theorem prefix_target_nonneg {E : Type} [Inhabited E] [Field "to" E Int]
    {adj : Array (Array E)} {n v : Nat} {pref suff : List E} {e : E}
    (valid : Valid adj n) (hv : v < n) (hrow : (Row adj v).toList = pref ++ e :: suff) :
    ∀ t ∈ edgeTargets pref, 0 ≤ t := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact (valid v hv a (by rw [hrow]; exact List.mem_append_left _ ha)).1

theorem prepare_child {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n v : Nat} {p : Int} {start st : St} {args : DfsState} {pref suff : List E} {e : E}
    {r : LoopState} (G : GH n (rowHeads adj n) (rowEnds adj n))
    (valid : Valid adj n) (A : FrameStart adj n v p start args) (H : CursorState adj n v start st args pref r)
    (hrow : (Row adj v).toList = pref ++ e :: suff)
    (hw : r.core.seen[(Field.get (member := "to") e : Int).toNat]! = false) :
    let w := (Field.get (member := "to") e : Int).toNat
    FrameStart adj n w (v : Int) (pushS (rowHeads adj n) st v w) r.core := by
  let w := (Field.get (member := "to") e : Int).toNat
  let pushed := pushS (rowHeads adj n) st v w
  have hvV := H.mem A.mem
  have hv := H.valid.vis_lt v hvV
  have hb := (valid v hv e (edge_mem_of_split hrow)).2
  have hnew : w ∉ st.Vis := by rw [← H.arrays.visits.marked w, hw]; decide
  have hne : v ≠ w := fun h => hnew (h ▸ hvV)
  have hd : 0 < st.sp := by rw [H.frame.depth]; exact A.depth
  have ht := H.frame.top A.depth A.top
  obtain ⟨hbound, hed⟩ := cursor_lookup hrow hv (Ne.symm hne)
  obtain ⟨I', visit'⟩ := enter_child G H.valid H.arrays.visits hd ht H.cursor.symm
    (by exact_mod_cast hbound) hed H.arrays.seenSize H.arrays.orderSize hw
  obtain ⟨hp', hb'⟩ := output_unchanged H.valid
    (child_preserves_finished (v := v) H.valid hnew) (after := pushed) rfl
    (fun x hx => upd_ne _ _ _ _ (fun he => hnew (he ▸ hx))) _ _ _ H.points H.bridges
  refine ⟨I', by show 0 < st.sp + 1; omega, ?_, upd_same _ _ _, upd_same _ _ _, ?_,
    H.valid.sep_unv w hnew, hw, ⟨(size_set _ _ _).trans H.arrays.seenSize, (size_set _ _ _).trans H.arrays.orderSize,
      (size_set _ _ _).trans H.arrays.lowSize, visit'⟩, hp', hb'⟩
  · show upd st.Sk st.sp w (st.sp + 1 - 1) = w
    rw [Nat.add_sub_cancel, upd_same]
  · show upd st.L w (st.Vis.length : Int) w = r.core.counter
    rw [upd_same, H.arrays.visits.counter]

structure FrameEnd {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E))
    (n v : Nat) (start done : St) (args r : DfsState) : Prop where
  valid : MInv n (rowHeads adj n) (rowEnds adj n) done
  frame : SameFrame start done v
  arrays : VisitArrays n done r
  cursor : done.It v = (rowHeads adj n (v + 1) : Int)
  cap : r.low[v]! = effectiveLow (done.L v)
    (capAt done v ((edgeTargets (Row adj v).toList).count (done.P v)))
  points : PointsMatch done (some v) r.points
  bridges : BridgesMatch (listTargets adj) done r.bridges
  stable : LowStable args r

def finishFrame (r : LoopState) (v : Nat) (parent : Int) : DfsState :=
  let emit := if decide (parent = -1) && decide (2 ≤ r.children) then true else r.art
  r.core.withPoints (if emit then r.core.points.push v else r.core.points)

theorem finish_cursor {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n v : Nat} {p : Int} {start st : St} {args : DfsState} {r : LoopState}
    (A : FrameStart adj n v p start args)
    (H : CursorState adj n v start st args (Row adj v).toList r) :
    FrameEnd adj n v start st args (finishFrame r v p) := by
  have hp := (H.frame.visited _ A.mem).2.trans A.parentEq
  have hd : 0 < st.sp := by rw [H.frame.depth]; exact A.depth
  have ht := H.frame.top A.depth A.top
  have hf := (H.valid.sk_mem (st.sp - 1) (by omega)).2
  rw [ht] at hf
  have h := art_frame_exit st v r.art r.children H.art
  rw [hp] at h
  have hp' := point_pending v r.core.points hf H.points _ h
  refine ⟨H.valid, H.frame, ⟨H.arrays.seenSize, H.arrays.orderSize, H.arrays.lowSize, H.arrays.visits⟩,
    ?_, H.cap, hp', H.bridges, H.stable⟩
  rw [H.cursor, cursor_full (H.valid.vis_lt v (H.mem A.mem))]


def joinChild (r : LoopState) (res : DfsState) (v w : Nat) (parent : Int) : LoopState :=
  let lo := res.low[w]!
  let order := res.order[v]!
  let low := set res.low v (min res.low[v]! lo)
  let art := if decide (parent ≠ -1) && decide (order ≤ lo) then true else r.art
  let bridges := if order < lo then res.bridges.push (bridgeKey v w) else res.bridges
  LoopState.ofCore ((res.withLow low).withBridges bridges) art r.skipped (r.children + 1)

theorem join_cursor_step {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n v : Nat} {parent : Int} {start st done : St} {args : DfsState} {pref suff : List E} {e : E}
    {r : LoopState} {res : DfsState} (G : GH n (rowHeads adj n) (rowEnds adj n))
    (valid : Valid adj n) (A : FrameStart adj n v parent start args)
    (H : CursorState adj n v start st args pref r)
    (hrow : (Row adj v).toList = pref ++ e :: suff)
    (hw : r.core.seen[(Field.get (member := "to") e : Int).toNat]! = false)
    (D : FrameEnd adj n (Field.get (member := "to") e : Int).toNat
      (pushS (rowHeads adj n) st v (Field.get (member := "to") e : Int).toNat) done r.core res) :
    CursorState adj n v start (popS done (Field.get (member := "to") e : Int).toNat)
      args (pref ++ [e]) (joinChild r res v (Field.get (member := "to") e : Int).toNat parent) := by
  let w := (Field.get (member := "to") e : Int).toNat
  let pushed := pushS (rowHeads adj n) st v w
  let after := popS done w
  change CursorState adj n v start after args (pref ++ [e]) (joinChild r res v w parent)
  have hvVis := H.mem A.mem
  have hv := H.valid.vis_lt v hvVis
  obtain ⟨hNN, hwn⟩ := valid v hv e (edge_mem_of_split hrow)
  have eta : (w : Int) = (Field.get (member := "to") e : Int) := Int.toNat_of_nonneg hNN
  have hnew : w ∉ st.Vis := by rw [← H.arrays.visits.marked w, hw]; decide
  have hvw : v ≠ w := fun he => hnew (he ▸ hvVis)
  have htop : pushed.Sk (pushed.sp - 1) = w := by
    show upd st.Sk st.sp w (st.sp + 1 - 1) = w
    rw [Nat.add_sub_cancel, upd_same]
  have hpushed : 0 < pushed.sp := by show 0 < st.sp + 1; omega
  have hd : 0 < done.sp := by rw [D.frame.depth]; exact hpushed
  have ht := D.frame.top hpushed htop
  have hwp : w ∈ pushed.Vis := by simp [pushed, pushS]
  have hwV : w ∈ done.Vis := D.frame.grows.subset hwp
  have hvOld : st.Vis <+: pushed.Vis := ⟨[w], rfl⟩
  have hvDone : v ∈ done.Vis := (hvOld.trans D.frame.grows).subset hvVis
  obtain ⟨hframe, hit, hP, hL, hSp⟩ := return_child_frame hvVis hnew D.frame
  have hparent : st.P v = parent := (H.frame.visited v A.mem).2.trans A.parentEq
  have hPa : after.P v = st.P v := (hframe.visited v hvVis).2
  have hPd : done.P v = st.P v := hPa
  have horder : res.order[v]! = done.O v := D.arrays.visits.numbered v hvDone
  have hNNrow : ∀ t ∈ edgeTargets (Row adj w).toList, 0 ≤ t := by
    intro t hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact (valid w hwn a ha).1
  let count := (listTargets adj w).count v
  let parallel := decide (2 ≤ count)
  have hchild : res.low[w]! = effectiveLow (done.L w) (if parallel then some (done.O v) else none) := by
    have h := D.cap
    change _ = effectiveLow _ (capAt done w ((edgeTargets (Row adj w).toList).count (done.P w))) at h
    rw [hP] at h
    have hCount : count = (edgeTargets (Row adj w).toList).count (v : Int) :=
      nonnegative_count _ _ hNNrow
    rw [← hCount] at h
    simpa [capAt, hP, parallel] using h
  have hprefixCount : (edgeTargets (pref ++ [e])).count (after.P v) =
      (edgeTargets pref).count (st.P v) := by
    have hne : (w : Int) ≠ st.P v := by
      intro he
      exact hnew (H.valid.par_ok w v he.symm).1
    simp [edgeTargets, List.count_append, hPa, ← eta, hne]
  have hcap : capAt after v ((edgeTargets (pref ++ [e])).count (after.P v)) =
      capAt st v ((edgeTargets pref).count (st.P v)) := by
    rw [hprefixCount]
    unfold capAt
    split
    · rename_i hcnt
      have hmem : st.P v ∈ edgeTargets pref := List.count_pos_iff.mp (by omega)
      have hpos := prefix_target_nonneg valid hv hrow _ hmem
      have hp' : Pr st.P (st.P v).toNat v := by unfold Pr; omega
      rw [hPa, (hframe.visited _ (H.valid.par_ok _ _ hp').1).1]
    · rfl
  obtain ⟨I', hVisit⟩ := pop_projection D.valid D.arrays.visits hd ht D.cursor
  have hpoints := point_pop D.valid hd ht _ D.points
  have hbridge0 := bridge_pop D.valid hd ht (listTargets adj) _ D.bridges
  have hArt0 : ArtFrame done v r.art r.children := by
    unfold ArtFrame
    rw [hPd, hSp]
    exact H.art
  have hArt := art_frame_return G D.valid hP r.art r.children hArt0 parallel
  rw [← hchild, ← horder, hPd, hparent] at hArt
  let oldCap := capAt st v ((edgeTargets pref).count (st.P v))
  obtain ⟨hLowOut, _, hChildStable, _, hBridgeTest⟩ := pop_child_values D.valid hP oldCap parallel
  rw [← hchild, hL] at hLowOut
  have holdLow := D.stable.2 v ((H.arrays.visits.marked v).mpr hvVis)
  rw [← H.cap, ← holdLow] at hLowOut
  have hBridge : res.order[v]! < res.low[w]! ↔
      (0 ≤ done.P w ∧ done.O (done.P w).toNat < done.L w ∧
        (listTargets adj w).count (done.P w).toNat < 2) := by
    rw [horder, hchild, hBridgeTest, hChildStable, hP, Int.toNat_natCast]
    simp only [parallel, count, decide_eq_false_iff_not, Int.natCast_nonneg, true_and]
    omega
  have hbridge : BridgesMatch (listTargets adj) after
      (if res.order[v]! < res.low[w]! then res.bridges.push (bridgeKey v w) else res.bridges) := by
    simp only [hBridge]
    change BridgesMatch (listTargets adj) after
      (if 0 ≤ done.P w ∧ done.O (done.P w).toNat < done.L w ∧
          (listTargets adj w).count (done.P w).toNat < 2
        then res.bridges.push (bridgeKey (done.P w).toNat w) else res.bridges) at hbridge0
    simpa [hP] using hbridge0
  have hvLow : v < res.low.size := by rw [D.arrays.lowSize]; exact hv
  have hupdated := getElemBang_set res.low (v : Int) (min res.low[v]! res.low[w]!) v (by simpa using hvLow)
  simp only [Int.toNat_natCast, ite_true] at hupdated
  refine ⟨I', H.frame.trans hframe,
    ⟨D.arrays.seenSize, D.arrays.orderSize, (size_set _ _ _).trans D.arrays.lowSize, hVisit⟩, ?_, ?_, ?_,
    hArt, hpoints, hbridge, (H.stable.trans D.stable).keepLow _ _ hvLow A.fresh⟩
  · rw [hit, cursor_step, H.cursor]
    change _ = (↑(cursorIdx adj n v pref + if w = v then 0 else 1) : Int)
    simp only [ite_eq_right (Ne.symm hvw), Int.natCast_add, Int.natCast_one]
  · show (set res.low v (min res.low[v]! res.low[w]!))[v]! = _
    rw [hupdated, hcap]
    exact hLowOut.symm
  · rw [hprefixCount]
    exact H.skipped

end Proofs.Cpp.ListLowlink
