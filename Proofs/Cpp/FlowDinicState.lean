import Proofs.Cpp.FlowDinicCursor
import Proofs.Math.FlowResidualPaths

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.Cpp.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [DecidableEq Arc]

structure LayerState (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (t : Nat) where
  layout : CapacityLayout n g slot atSlot
  cursors : Cursors n g slot t
  distance : ValidDistance n (capacity g.adj slot) (levelsView g.level)
  nonnegative : ∀ a, 0 ≤ capacity g.adj slot a

structure PhaseSame (before after : cp.FlowGraph Int E) (d : Nat) : Prop where
  vertexCount : after.n_ = before.n_
  arcCounter : after.m_ = before.m_
  vertices : after.adj.size = before.adj.size
  rows : ∀ v : Nat, after.adj[v]!.size = before.adj[v]!.size
  level : after.level = before.level
  earlier : ∀ u k, levelsView before.level u = some k → k < d → cursor after u = cursor before u

protected theorem PhaseSame.refl (g : cp.FlowGraph Int E) (d : Nat) : PhaseSame g g d :=
  ⟨rfl, rfl, rfl, fun _ => rfl, rfl, fun _ _ _ _ => rfl⟩

protected theorem PhaseSame.trans {a b c : cp.FlowGraph Int E} {d : Nat} (ab : PhaseSame a b d) (bc : PhaseSame b c d) :
    PhaseSame a c d := by
  refine ⟨bc.vertexCount.trans ab.vertexCount, bc.arcCounter.trans ab.arcCounter, bc.vertices.trans ab.vertices,
    fun v => (bc.rows v).trans (ab.rows v), bc.level.trans ab.level, ?_⟩
  intro u k h hk
  exact (bc.earlier u k (by rwa [ab.level]) hk).trans (ab.earlier u k h hk)

theorem PhaseSame.earlier_than {g out : cp.FlowGraph Int E} {d e : Nat} (h : PhaseSame g out d) (le : e ≤ d) :
    PhaseSame g out e := ⟨h.vertexCount, h.arcCounter, h.vertices, h.rows, h.level,
      fun u k hu hk => h.earlier u k hu (lt_of_lt_of_le hk le)⟩

theorem PhaseSame.row_size {g out : cp.FlowGraph Int E} {d : Nat} (h : PhaseSame g out d) (v : Nat) :
    (get out.adj (v : Int)).size = (get g.adj (v : Int)).size := by simpa only [get_natCast] using h.rows v

def LayerState.nextCursor {n : Network Arc Nat} {g : cp.FlowGraph Int E} {slot : Arc → Slot}
    {atSlot : Int → Int → Option Arc} {t : Nat} (st : LayerState n g slot atSlot t) (v i : Nat)
    (hv : v < g.adj.size) (hi : i < (get g.adj (v : Int)).size) (atPos : cursor g v = (i : Int))
    (dead : ∀ a, slot a = (v, i) → Dead n (capacity g.adj slot) (levelsView g.level) t a) :
    LayerState n (advanceCursor g (v : Int) (i : Int)) slot atSlot t :=
  ⟨layout_changeIter st.layout _, cursor_bump st.layout st.cursors v i hv hi atPos dead, st.distance, st.nonnegative⟩

theorem advance_same {n : Network Arc Nat} {g : cp.FlowGraph Int E} {slot : Arc → Slot}
    {t : Nat} (st : Cursors n g slot t) (v i d : Nat) (hv : v < g.adj.size) (here : levelsView g.level v = some d) :
    PhaseSame g (advanceCursor g (v : Int) (i : Int)) d := by
  refine ⟨rfl, rfl, rfl, fun _ => rfl, rfl, ?_⟩
  intro w j hj earlier
  have ne : w ≠ v := by
    intro eq
    subst w
    rw [here, Option.some.injEq] at hj
    omega
  rw [cursor_advanced g v (i : Int) (by rwa [st.size]) w, ite_eq_right ne]

private theorem layer_single_state {n : Network Arc Nat} {g : cp.FlowGraph Int E} {slot : Arc → Slot}
    {atSlot : Int → Int → Option Arc} {t : Nat} (st : LayerState n g slot atSlot t) (laws : CapLaws (E := E))
    (a : Arc) (d : Int) (h : UnitStep n (levelsView g.level) a) (nonnegative : 0 ≤ d)
    (bound : d ≤ capacity g.adj slot a) :
    let next := adjust g.adj (slot a) d
    ∃ st' : LayerState n {g with adj := next} slot atSlot t,
      (next.size = g.adj.size ∧ ∀ v : Nat, next[v]!.size = g.adj[v]!.size) ∧
      capacity next slot = update n (capacity g.adj slot) a d := by
  let next := adjust g.adj (slot a) d
  have rep := st.layout.represents
  have ha := rep.bounded a
  have hr : InBounds g.adj (reverseSlot g.adj (slot a)) := by rw [rep.reverse_eq]; exact rep.bounded _
  have ne : reverseSlot g.adj (slot a) ≠ slot a := by
    rw [rep.reverse_eq]
    exact fun eq => n.reverse_ne a (rep.injective eq)
  have dims := adjust_shape laws g.adj (slot a) d ha hr
  have capEq := rep.adjust_capacity laws a d
  have newBounds (b : Arc) : 0 ≤ revIdx (readSlot next (slot b)) := by
    rw [(adjust_metadata laws g.adj (slot a) d ha hr ne (slot b)).2.1]
    exact st.layout.reverseIndices b
  have l' := st.layout.withRows next (rep.adjust laws a d) dims newBounds
  have w : WeakensLayer n (levelsView g.level) (capacity g.adj slot) (capacity next slot) := by
    rw [capEq]
    exact layer_after_update n _ _ a d h nonnegative
  refine ⟨⟨l', cursor_with_rows st.cursors next dims w, ?_, ?_⟩, dims, capEq⟩
  · change ValidDistance n (capacity next slot) (levelsView g.level)
    rw [capEq]
    exact distances_after_update n (capacity g.adj slot) (levelsView g.level) a d nonnegative st.distance h
  · rw [capEq]
    exact update_nonneg n (capacity g.adj slot) a d st.nonnegative nonnegative bound

theorem LayerState.push {n : Network Arc Nat} {g : cp.FlowGraph Int E} {slot : Arc → Slot}
    {atSlot : Int → Int → Option Arc} {t : Nat} (st : LayerState n g slot atSlot t) (laws : CapLaws (E := E))
    (a : Arc) (d : Int) (h : UnitStep n (levelsView g.level) a) (nonnegative : 0 ≤ d)
    (bound : d ≤ capacity g.adj slot a) :
    let out := {g with adj := pushPair g.adj (n.tail a : Int) ((slot a).2 : Int) d}
    ∃ st' : LayerState n out slot atSlot t,
      (∀ k, PhaseSame g out k) ∧ capacity out.adj slot = update n (capacity g.adj slot) a d := by
  have rep := st.layout.represents
  have castNonneg : 0 ≤ dest (readSlot g.adj (slot a)) := by rw [rep.head_eq]; exact Int.natCast_nonneg _
  have eq : pushPair g.adj (n.tail a : Int) ((slot a).2 : Int) d = adjust g.adj (slot a) d := by
    rw [← rep.tail_eq a]
    exact pushPair_adjust laws g.adj (slot a).1 (slot a).2 d (rep.bounded a) castNonneg (st.layout.reverseIndices a)
  dsimp only
  rw [eq]
  obtain ⟨st', dims, he⟩ := layer_single_state st laws a d h nonnegative bound
  exact ⟨st', fun _ => ⟨rfl, rfl, dims.1, dims.2, rfl, fun _ _ _ _ => rfl⟩, he⟩

structure PathPush (n : Network Arc Nat) (start final : cp.FlowGraph Int E) (slot : Arc → Slot)
    (u t : Nat) (limit flow : Int) (path : List Arc) : Prop where
  route : Path n u t path
  usable : ∀ a ∈ path, Usable n (capacity start.adj slot) (levelsView start.level) a
  positive : 0 < flow
  within_limit : flow ≤ limit
  supply : ∀ a ∈ path, flow ≤ capacity start.adj slot a
  maximal : ∀ d ≤ limit, (∀ a ∈ path, d ≤ capacity start.adj slot a) → d ≤ flow
  after : capacity final.adj slot = augment n flow (capacity start.adj slot) path.reverse

/-- A recursive success charges the parent arc after the child has finished. -/
theorem parent_push {n : Network Arc Nat} {g child : cp.FlowGraph Int E} {slot : Arc → Slot}
    {atSlot : Int → Int → Option Arc} {t depth : Nat} (st : LayerState n child slot atSlot t) (laws : CapLaws (E := E))
    (base : PhaseSame g child depth) (a : Arc) (flow limit : Int) (path : List Arc)
    (allow : Usable n (capacity g.adj slot) (levelsView g.level) a)
    (fromChild : PathPush n g child slot (n.head a) t (min limit (capacity g.adj slot a)) flow path) :
    let next := {child with adj := pushPair child.adj (n.tail a : Int) ((slot a).2 : Int) flow}
    ∃ st' : LayerState n next slot atSlot t,
      PhaseSame g next depth ∧ PathPush n g next slot (n.tail a) t limit flow (a :: path) := by
  have unit := allow.2
  have avoided := parent_not_in_child n (levelsView g.level) a unit fromChild.route (fun b hb => (fromChild.usable b hb).2)
  have hc : capacity child.adj slot a = capacity g.adj slot a := by
    rw [fromChild.after]
    exact augment_unrelated n _ path.reverse flow a (by simpa using avoided.1) (by simpa using avoided.2)
  have step : UnitStep n (levelsView child.level) a := by rwa [base.level]
  have capLimit : flow ≤ capacity g.adj slot a := le_trans fromChild.within_limit (min_le_right ..)
  have hbound : flow ≤ capacity child.adj slot a := by rwa [hc]
  obtain ⟨stOut, same, mapped⟩ := st.push laws a flow step (Int.le_of_lt fromChild.positive) hbound
  refine ⟨stOut, base.trans (same depth), ⟨.cons a fromChild.route, ?_, fromChild.positive,
    le_trans fromChild.within_limit (min_le_left ..), ?_, ?_, ?_⟩⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact allow
    · exact fromChild.usable b hb
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact capLimit
    · exact fromChild.supply b hb
  · intro delta hl ha
    exact fromChild.maximal delta (le_min hl (ha a (List.mem_cons_self ..))) (fun b hb => ha b (List.mem_cons_of_mem _ hb))
  · rw [mapped, fromChild.after, List.reverse_cons]
    unfold augment
    rw [List.foldl_append]
    rfl

end Proofs.Cpp.FlowDinic
