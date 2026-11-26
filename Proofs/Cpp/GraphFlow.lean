import Proofs.Cpp.FlowCanonicalLayout
import Proofs.Cpp.FlowCostPublic
import Proofs.Cpp.FlowDinicPublic
import Proofs.Cpp.FlowEdgeBindings
import Proofs.Cpp.Gen.GraphFlow
import Proofs.Cpp.Lib.Basic

/-! # FlowGraph

Public contracts for the translated residual-network API. The layout contracts refer to the
same two physical slots that the C++ implementation updates. The cost curve certifies each
integral flow between consecutive breakpoints.
-/

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.GraphFlow

theorem init_empty {Cost E : Type} (t : Nat) :
    (cp.FlowGraph.init_0 (Cost := Cost) (E := E)).run t = some (⟨0, 0, Array.empty, Array.empty, Array.empty⟩, t + 1) := rfl

theorem init_vertices {Cost E : Type} (n : Int) (t : Nat) :
    (cp.FlowGraph.init_int (Cost := Cost) (E := E) n).run t =
      some (⟨n, 0, Array.replicate n.toNat (Array.empty : Array E), Array.empty, Array.empty⟩, t + 1 + n.toNat) := rfl

theorem index_row {Cost E : Type} [Inhabited E] (g : cp.FlowGraph Cost E) (i : Int) (t : Nat) :
    (cp.FlowGraph.op_index g i).run t = some ((get g.adj i, g), t + 1) := by cases g; rfl

theorem append_vertex {Cost E : Type} (g : cp.FlowGraph Cost E) (t : Nat) :
    (cp.FlowGraph.add_node g).run t =
      some ({g with n_ := g.n_ + 1, adj := g.adj.push Array.empty, level := g.level.push 0}, t + 3) := rfl

theorem flow_limit {Cost E : Type} [NumericTraits "Cost" Cost] [ShiftInt Cost] (t : Nat) :
    (cp.FlowGraph.F_MAX (Cost := Cost) (E := E)).run t =
      some (ShiftInt.shr (NumericTraits.maximum (tag := "Cost") (α := Cost)) 2, t + 1) := rfl

section Augment
variable {Cost E : Type} [Inhabited Cost] [Inhabited E] [Zero Cost] [IntCast Cost]
  [Add Cost] [Sub Cost] [Mul Cost] [Div Cost] [LT Cost] [LE Cost]
  [DecidableLT Cost] [DecidableLE Cost] [DecidableEq Cost] [Min Cost]
  [Field "cap" E Cost] [Field "cost" E Cost] [Field "rev" E Int] [Field "to" E Int]
  [NumericTraits "Cost" Cost] [ShiftInt Cost] [WriteField "cap" E Cost]

theorem minimum_zero (g : cp.FlowGraph Cost E) (source sink : Int) (t : Nat) :
    (cp.FlowGraph.min_cost_flow g source sink 0).run t = some (((0 : Cost), g), t + 1) := rfl

omit [IntCast Cost] [Div Cost] in
theorem slope_zero (g : cp.FlowGraph Cost E) (source sink : Int) (t : Nat) :
    (cp.FlowGraph.min_cost_flow_slope g source sink 0).run t =
      some ((([(0, 0)] : List (Cost × Cost)).toArray, g), t + 2) := by
  unfold cp.FlowGraph.min_cost_flow_slope
  dsimp only
  have h : decide ((0 : Cost) = 0) = true := decide_eq_true rfl
  rw [ite_eq_left h]
  rfl

end Augment

section Insert
variable {Cost E : Type} [Inhabited E] [ConstructState E]
  [Construct E (Int × Int × Int × Cost × Unit)] [Construct E (Int × Int × Int × Int × Unit)]

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem pure_run {α : Type} (a : α) (t : Nat) : (pure a : M α).run t = some (a, t) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

def appendEdge (adj : Array (Array E)) (v : Int) (e : E) : Array (Array E) :=
  set adj v ((get adj v).push e)

omit [Inhabited E] [ConstructState E] [Construct E (Int × Int × Int × Int × Unit)] in
theorem appended_row (adj : Array (Array E)) (v : Int) (e : E) (hv : v.toNat < adj.size) :
    get (appendEdge adj v e) v = (get adj v).push e := by
  unfold appendEdge
  rw [get_eq, getElemBang_set adj v _ _ hv, ite_eq_left rfl]

/-- The two constructor calls receive the actual indices of the other arcs, also when they share a row. -/
theorem add_edge_max_run (g : cp.FlowGraph Cost E) (u v : Int) (cap : Cost)
    (hu : u.toNat < g.adj.size) (state next final : ConstructState.State E) (a b : E) (t ta tb : Nat)
    (ha : (Construct.make (E := E) (u, v, size (get g.adj v) + if u = v then 1 else 0, cap, ()) state).run (t + 1) =
      some ((a, next), ta))
    (hb : (Construct.make (E := E) (v, u, size (get g.adj u), (0 : Int), ()) next).run (ta + 1) =
      some ((b, final), tb)) :
    (cp.FlowGraph.add_edge_max_flow g u v cap state).run t =
      some ((final, { g with m_ := g.m_ + 1, adj := appendEdge (appendEdge g.adj u a) v b }), tb + 1) := by
  have back : size (get (appendEdge g.adj u a) u) - 1 = size (get g.adj u) := by
    rw [appended_row _ _ _ hu]
    simp [size]
  have haa : (Construct.make (E := E) (u, v,
      size (get g.adj v) + (if decide (u = v) then 1 else 0), cap, ()) state).run (t + 1) =
      some ((a, next), ta) := by
    by_cases h : u = v
    · simp only [h, decide_true, ite_true] at ha ⊢
      exact ha
    · simp only [h, decide_false, Bool.false_eq_true, ite_false] at ha ⊢
      exact ha
  simp only [cp.FlowGraph.add_edge_max_flow, StateT.run_bind, tick_run, some_bind, pure_run, haa]
  change ((Construct.make (E := E) (v, u, size (get (appendEdge g.adj u a) u) - 1, (0 : Int), ()) next).run
    (ta + 1) >>= _) = _
  rw [back, hb]
  rfl

end Insert

section CostInsert
variable {Cost E : Type} [Inhabited E] [Neg Cost] [ConstructState E]
  [Construct E (Int × Int × Int × Cost × Cost × Unit)] [Construct E (Int × Int × Int × Int × Cost × Unit)]

theorem add_edge_cost_run (g : cp.FlowGraph Cost E) (u v : Int) (cap cost : Cost) (hu : u.toNat < g.adj.size)
    (state next final : ConstructState.State E) (a b : E) (t ta tb : Nat)
    (ha : (Construct.make (E := E) (u, v, size (get g.adj v) + if u = v then 1 else 0, cap, cost, ()) state).run (t + 1) =
      some ((a, next), ta))
    (hb : (Construct.make (E := E) (v, u, size (get g.adj u), (0 : Int), -cost, ()) next).run (ta + 1) = some ((b, final), tb)) :
    (cp.FlowGraph.add_edge_min_cost_flow g u v cap cost state).run t =
      some ((final, {g with m_ := g.m_ + 1, adj := appendEdge (appendEdge g.adj u a) v b}), tb + 1) := by
  have back : size (get (appendEdge g.adj u a) u) - 1 = size (get g.adj u) := by
    rw [appended_row _ _ _ hu]
    simp [size]
  have haa : (Construct.make (E := E) (u, v,
      size (get g.adj v) + (if decide (u = v) then 1 else 0), cap, cost, ()) state).run (t + 1) = some ((a, next), ta) := by
    by_cases h : u = v
    · simp only [h, decide_true, ite_true] at ha ⊢
      exact ha
    · simp only [h, decide_false, Bool.false_eq_true, ite_false] at ha ⊢
      exact ha
  simp only [cp.FlowGraph.add_edge_min_cost_flow, StateT.run_bind, tick_run, some_bind, pure_run, haa]
  change ((Construct.make (E := E) (v, u, size (get (appendEdge g.adj u a) u) - 1, (0 : Int), -cost, ()) next).run
    (ta + 1) >>= _) = _
  rw [back, hb]
  rfl

end CostInsert

end Proofs.Cpp.GraphFlow

open Proofs.Cpp Proofs.Cpp.Gen
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowPairLayout

namespace Proofs.Cpp.GraphFlow

variable {E : Type} [Inhabited E]

def atEnd (adj : Array (Array E)) (u : Nat) : Slot := (u, adj[u]!.size)

theorem appendEdge_size (adj : Array (Array E)) (u : Nat) (e : E) :
    (appendEdge adj (u : Int) e).size = adj.size := size_set ..

theorem appendEdge_row (adj : Array (Array E)) (u : Nat) (e : E) (hu : u < adj.size) (v : Nat) :
    (appendEdge adj (u : Int) e)[v]! = if v = u then adj[v]!.push e else adj[v]! := by
  unfold appendEdge
  rw [getElemBang_set _ _ _ _ (by simpa using hu : (u : Int).toNat < adj.size), Int.toNat_natCast]
  by_cases h : v = u <;> simp [h, get_natCast]

theorem appendEdge_keeps (adj : Array (Array E)) (u : Nat) (e : E) (hu : u < adj.size) (a : Slot)
    (old : InBounds adj a) : InBounds (appendEdge adj (u : Int) e) a ∧
      readSlot (appendEdge adj (u : Int) e) a = readSlot adj a := by
  have rows := appendEdge_row adj u e hu a.1
  have bottom : a.2 < (appendEdge adj (u : Int) e)[a.1]!.size := by
    rw [rows]
    by_cases h : a.1 = u
    · simp only [h, ite_true, Array.size_push] at old ⊢
      exact Nat.lt_succ_of_lt (h ▸ old.2)
    · rw [ite_eq_right h]
      exact old.2
  refine ⟨⟨by rw [appendEdge_size]; exact old.1, bottom⟩, ?_⟩
  unfold readSlot
  simp only [get_natCast]
  rw [rows]
  by_cases h : a.1 = u
  · have hnew : a.2 < (adj[a.1]!.push e).size := by rw [Array.size_push]; exact Nat.lt_succ_of_lt old.2
    simp only [ite_eq_left h, getElem!_pos, hnew, old.2, Array.getElem_push_lt]
  · rw [ite_eq_right h]

theorem appendEdge_last (adj : Array (Array E)) (u : Nat) (e : E) (hu : u < adj.size) :
    let out := appendEdge adj (u : Int) e
    InBounds out (atEnd adj u) ∧ readSlot out (atEnd adj u) = e := by
  have rows := appendEdge_row adj u e hu u
  rw [ite_eq_left rfl] at rows
  refine ⟨⟨by rw [appendEdge_size]; exact hu, ?_⟩, ?_⟩
  · dsimp only [atEnd]
    rw [rows, Array.size_push]
    exact Nat.lt_succ_self _
  · unfold atEnd readSlot
    simp only [get_natCast]
    rw [rows]
    have h : adj[u]!.size < (adj[u]!.push e).size := by simp
    simp only [getElem!_pos, h, Array.getElem_push_eq]

theorem appendEdge_partition (adj : Array (Array E)) (u : Nat) (e : E) (hu : u < adj.size) (a : Slot)
    (inOut : InBounds (appendEdge adj (u : Int) e) a) : InBounds adj a ∨ a = atEnd adj u := by
  have row : a.1 < adj.size := by simpa only [appendEdge_size] using inOut.1
  have i := inOut.2
  rw [appendEdge_row adj u e hu a.1] at i
  by_cases hv : a.1 = u
  · rw [ite_eq_left hv, Array.size_push] at i
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i) with h | h
    · exact Or.inl ⟨row, h⟩
    · exact Or.inr (Prod.ext hv (hv ▸ h))
  · rw [ite_eq_right hv] at i
    exact Or.inl ⟨row, i⟩

section Residual

variable [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int] [Field "rev" E Int]

/-- Appending the two edges preserves every old pair and connects the new pair by its actual indices. -/
theorem append_pair_layout (adj : Array (Array E)) (old : PairedRows adj) (u v : Nat)
    (hu : u < adj.size) (hv : v < adj.size) (forward backward : E)
    (fTo : dest forward = (v : Int)) (bTo : dest backward = (u : Int))
    (fRev : revIdx forward = ((atEnd (appendEdge adj (u : Int) forward) v).2 : Int))
    (bRev : revIdx backward = ((atEnd adj u).2 : Int)) (bCost : price backward = -price forward) :
    PairedRows (appendEdge (appendEdge adj (u : Int) forward) (v : Int) backward) := by
  let mid := appendEdge adj (u : Int) forward
  let out := appendEdge mid (v : Int) backward
  let a := atEnd adj u
  let b := atEnd mid v
  have hvm : v < mid.size := by rw [show mid.size = adj.size from appendEdge_size ..]; exact hv
  have aMid := appendEdge_last adj u forward hu
  have aOut := appendEdge_keeps mid v backward hvm a aMid.1
  have bOut := appendEdge_last mid v backward hvm
  have different : a ≠ b := by
    intro h
    have bad : InBounds mid b := by rw [← h]; exact aMid.1
    exact (Nat.lt_irrefl _) bad.2
  have unchanged (p : Slot) (hp : InBounds adj p) : InBounds out p ∧ readSlot out p = readSlot adj p := by
    obtain ⟨hm, first⟩ := appendEdge_keeps adj u forward hu p hp
    obtain ⟨hn, second⟩ := appendEdge_keeps mid v backward hvm p hm
    exact ⟨hn, second.trans first⟩
  have forwardVal : readSlot out a = forward := aOut.2.trans aMid.2
  have backVal : readSlot out b = backward := bOut.2
  have forwardIdx : reverseSlot out a = b := by
    unfold reverseSlot
    rw [forwardVal, fTo, fRev]
    simp [b, mid, atEnd]
  have backIdx : reverseSlot out b = a := by
    unfold reverseSlot
    rw [backVal, bTo, bRev]
    simp [a, atEnd]
  have oldIdx (p : Slot) (hp : InBounds adj p) : reverseSlot out p = reverseSlot adj p := by
    unfold reverseSlot
    rw [(unchanged p hp).2]
  have partition (p : Slot) (hp : InBounds out p) : InBounds adj p ∨ p = a ∨ p = b := by
    rcases appendEdge_partition mid v backward hvm p hp with before | eq
    · rcases appendEdge_partition adj u forward hu p before with before | eq
      · exact Or.inl before
      · exact Or.inr (Or.inl eq)
    · exact Or.inr (Or.inr eq)
  change PairedRows out
  constructor
  · intro p hp
    rcases partition p hp with before | rfl | rfl
    · rw [(unchanged p before).2]; exact old.to_nonnegative p before
    · rw [forwardVal, fTo]; exact Int.natCast_nonneg _
    · rw [backVal, bTo]; exact Int.natCast_nonneg _
  · intro p hp
    rcases partition p hp with before | rfl | rfl
    · rw [(unchanged p before).2]; exact old.rev_nonnegative p before
    · rw [forwardVal, fRev]; exact Int.natCast_nonneg _
    · rw [backVal, bRev]; exact Int.natCast_nonneg _
  · intro p hp
    rcases partition p hp with before | rfl | rfl
    · rw [oldIdx p before]; exact (unchanged _ (old.rev_valid p before)).1
    · rw [forwardIdx]; exact bOut.1
    · rw [backIdx]; exact aOut.1
  · intro p hp
    rcases partition p hp with before | rfl | rfl
    · rw [oldIdx p before]; exact old.rev_distinct p before
    · rw [forwardIdx]; exact different.symm
    · rw [backIdx]; exact different
  · intro p hp
    rcases partition p hp with before | rfl | rfl
    · rw [oldIdx p before, oldIdx _ (old.rev_valid p before)]
      exact old.rev_symmetric p before
    · rw [forwardIdx, backIdx]
    · rw [backIdx, forwardIdx]
  · intro p hp
    rcases partition p hp with before | rfl | rfl
    · rw [oldIdx p before, (unchanged _ (old.rev_valid p before)).2, (unchanged p before).2]
      exact old.cost_antisym p before
    · rw [forwardIdx, backVal, forwardVal]
      exact bCost
    · rw [backIdx, forwardVal, backVal, bCost, Int.neg_neg]

end Residual

theorem after_first_reverse_index (adj : Array (Array E)) (u v : Nat) (e : E) (hu : u < adj.size) :
    ((atEnd (appendEdge adj (u : Int) e) v).2 : Int) =
      size (get adj (v : Int)) + if (u : Int) = (v : Int) then 1 else 0 := by
  unfold atEnd size
  rw [appendEdge_row adj u e hu v]
  by_cases equal : u = v
  · subst v
    simp [get_natCast]
  · have ne : v ≠ u := Ne.symm equal
    have neq : (u : Int) ≠ (v : Int) := by omega
    simp [ne, neq, get_natCast]

abbrev FlowEdgeCounter := cp.GlobalState_5be60fe7c0622cd9 Int "FlowEdge"

/-- The default C++ edge constructors realize the initial pairing, including a shared row. -/
theorem default_add_cost_layout (g : cp.FlowGraph Int (cp.FlowEdge Int)) (paired : PairedRows g.adj)
    (u v : Nat) (hu : u < g.adj.size) (hv : v < g.adj.size) (cap fee : Int) (state : FlowEdgeCounter) (clock : Nat) :
    ∃ out, (cp.FlowGraph.add_edge_min_cost_flow g (u : Int) (v : Int) cap fee state).run clock =
      some ((⟨state.FlowEdge_next_id + 2⟩, out), clock + 5) ∧
      PairedRows out.adj ∧ out.adj.size = g.adj.size ∧ out.n_ = g.n_ ∧ out.m_ = g.m_ + 1 := by
  let id := state.FlowEdge_next_id
  let r := size (get g.adj (v : Int)) + if (u : Int) = (v : Int) then 1 else 0
  let back := size (get g.adj (u : Int))
  let edge : cp.FlowEdge Int := ⟨(u : Int), (v : Int), r, id, max cap 0, fee⟩
  let reverse : cp.FlowEdge Int := ⟨(v : Int), (u : Int), back, id + 1, 0, -fee⟩
  let mid := appendEdge g.adj (u : Int) edge
  let adj := appendEdge mid (v : Int) reverse
  let newState : FlowEdgeCounter := ⟨id + 1⟩
  let after : FlowEdgeCounter := ⟨(id + 1) + 1⟩
  have fRev : revIdx edge = ((atEnd mid v).2 : Int) := (after_first_reverse_index g.adj u v edge hu).symm
  have bRev : revIdx reverse = ((atEnd g.adj u).2 : Int) := rfl
  have proof := append_pair_layout g.adj paired u v hu hv edge reverse rfl rfl fRev bRev rfl
  refine ⟨{g with m_ := g.m_ + 1, adj}, ?_, proof, by rw [appendEdge_size, appendEdge_size], rfl, rfl⟩
  have r₁ : (Construct.make (E := cp.FlowEdge Int) ((u : Int), (v : Int), r, cap, fee, ()) state).run (clock + 1) =
      some ((edge, newState), clock + 2) := rfl
  have r₂ : (Construct.make (E := cp.FlowEdge Int) ((v : Int), (u : Int), back, (0 : Int), -fee, ()) newState).run
      (clock + 2 + 1) = some ((reverse, after), clock + 4) := rfl
  have run := add_edge_cost_run g (u : Int) (v : Int) cap fee (by simpa using hu) state newState after edge reverse
    clock (clock + 2) (clock + 4) r₁ r₂
  have he : (id + 1) + 1 = id + 2 := by omega
  simpa only [after, he] using run

theorem default_add_max_layout (g : cp.FlowGraph Int (cp.FlowEdge Int)) (paired : PairedRows g.adj)
    (u v : Nat) (hu : u < g.adj.size) (hv : v < g.adj.size) (cap : Int) (state : FlowEdgeCounter) (clock : Nat) :
    ∃ out, (cp.FlowGraph.add_edge_max_flow g (u : Int) (v : Int) cap state).run clock =
      some ((⟨state.FlowEdge_next_id + 2⟩, out), clock + 5) ∧
      PairedRows out.adj ∧ out.adj.size = g.adj.size ∧ out.n_ = g.n_ ∧ out.m_ = g.m_ + 1 := by
  have same : cp.FlowGraph.add_edge_max_flow g (u : Int) (v : Int) cap state =
      cp.FlowGraph.add_edge_min_cost_flow g (u : Int) (v : Int) cap 0 state := rfl
  simp only [same]
  exact default_add_cost_layout g paired u v hu hv cap 0 state clock

section Vertices

variable [Field "to" E Int] [Field "rev" E Int] [Field "cost" E Int]

theorem no_arc_pairs (adj : Array (Array E)) (no : ∀ a, ¬ InBounds adj a) : PairedRows adj := by
  constructor <;> intro a ha <;> exact False.elim (no a ha)

theorem initial_pairs (n : Nat) : PairedRows (Array.replicate n (Array.empty : Array E)) := by
  apply no_arc_pairs
  intro a h
  have hr : a.1 < n := by simpa using h.1
  have h' := h.2
  simp [getElem!_pos, hr] at h'
  change a.2 < 0 at h'
  omega

theorem append_isolated_vertex (adj : Array (Array E)) (paired : PairedRows adj) : PairedRows (adj.push Array.empty) := by
  let out := adj.push (Array.empty : Array E)
  have same_row (v : Nat) (hv : v < adj.size) : out[v]! = adj[v]! := by
    have ho : v < out.size := by simp [out]; omega
    simp only [getElem!_pos, ho, hv]
    exact Array.getElem_push_lt hv
  have domain (a : Slot) : InBounds out a ↔ InBounds adj a := by
    unfold InBounds
    constructor
    · intro ⟨v, i⟩
      have within : a.1 < adj.size := by
        by_contra h
        have eq : a.1 = adj.size := by simp [out] at v; omega
        have last : out[a.1]! = Array.empty := by rw [eq]; simp [out, getElem!_pos]
        rw [last] at i
        change a.2 < 0 at i
        omega
      refine ⟨within, ?_⟩
      rwa [same_row _ within] at i
    · intro ⟨v, i⟩
      have hv : a.1 < out.size := by simp [out]; omega
      refine ⟨hv, ?_⟩
      rwa [same_row _ v]
  have reads (a : Slot) (ha : InBounds adj a) : readSlot out a = readSlot adj a := by
    unfold readSlot
    have he : get out (a.1 : Int) = get adj (a.1 : Int) := by
      simpa only [get_natCast] using same_row a.1 ha.1
    rw [he]
  have index (a : Slot) (ha : InBounds adj a) : reverseSlot out a = reverseSlot adj a := by
    unfold reverseSlot
    rw [reads a ha]
  change PairedRows out
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have b := (domain a).mp ha
    rw [reads a b]
    exact paired.to_nonnegative a b
  · intro a ha
    have b := (domain a).mp ha
    rw [reads a b]
    exact paired.rev_nonnegative a b
  · intro a ha
    have b := (domain a).mp ha
    rw [index a b, domain]
    exact paired.rev_valid a b
  · intro a ha
    have b := (domain a).mp ha
    rw [index a b]
    exact paired.rev_distinct a b
  · intro a ha
    have b := (domain a).mp ha
    rw [index a b, index _ (paired.rev_valid a b)]
    exact paired.rev_symmetric a b
  · intro a ha
    have b := (domain a).mp ha
    rw [index a b, reads _ (paired.rev_valid a b), reads a b]
    exact paired.cost_antisym a b

end Vertices

end Proofs.Cpp.GraphFlow

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowPairLayout
open Proofs.Cpp.FlowCostSearch Proofs.Cpp.FlowDinic

namespace Proofs.Cpp.GraphFlow

variable [NumericTraits "Cost" Int] [ShiftInt Int]

/-- In the default edge type, the result is maximal over exactly the concrete residual slots. -/
theorem paired_max_flow (g : cp.FlowGraph Int (cp.FlowEdge Int)) (rows : PairedRows g.adj)
    (sizeEq : g.n_ = (g.adj.size : Int)) (s t : Nat) (hs : s < g.adj.size) (ht : t < g.adj.size) (diff : s ≠ t)
    (vertexBound : g.adj.size + 2 ≤ fuel) (arcBound : 8 * arcCount g + 1 ≤ fuel) (limPos : 0 < flowLimit)
    (stored : ∀ a : ArcOf g.adj, 0 ≤ capacity g.adj Subtype.val a ∧ capacity g.adj Subtype.val a ≤ 7 * flowLimit)
    (clock : Nat) :
    ∃ out amount finish,
      (cp.FlowGraph.max_flow g (s : Int) (t : Int)).run clock = some ((amount, out), finish) ∧
      SignedFeasible rows.network (allArcs g.adj) (capacity g.adj Subtype.val) s t amount
        (fun a => capacity g.adj Subtype.val a - capacity out.adj Subtype.val a) ∧
      (∀ f q, SignedFeasible rows.network (allArcs g.adj) (capacity g.adj Subtype.val) s t f q → f ≤ amount) ∧
      0 ≤ amount ∧ finish ≤ clock + 1 + (g.adj.size + 1) *
        (7 + 5 * g.adj.size + 4 * arcCount g + 8 * arcCount g * (3 + 2 * g.adj.size)) := by
  have h := max_flow_spec rows.network (allArcs g.adj) (allArcs_unique g.adj) (allArcs_complete g.adj)
    g Subtype.val (findArc g.adj) (canonicalLayout g rows sizeEq) flow_edge_cap_laws
    s t hs ht diff vertexBound (by rwa [allArcs_length]) limPos stored clock
  simpa only [phaseCharge, allArcs_length] using h

/-- Cost witnesses use the actual two-slot residual pairs, including parallel edges. -/
theorem paired_min_cost_flow (g : cp.FlowGraph Int (cp.FlowEdge Int)) (rows : PairedRows g.adj)
    (sizeEq : g.n_ = (g.adj.size : Int)) (s t : Nat) (hs : s < g.adj.size) (ht : t < g.adj.size)
    (vertexBound : g.adj.size ≤ fuel) (limPos : 0 < flowLimit) (demand : Int) (pos : 0 < demand)
    (demandBound : demand.toNat ≤ fuel) (stored : ∀ a : ArcOf g.adj, 0 ≤ capacity g.adj Subtype.val a)
    (feasible : ∃ p, FeasiblePotential rows.network (capacity g.adj Subtype.val) p) (clock : Nat) :
    ∃ answer out finish,
      (cp.FlowGraph.min_cost_flow g (s : Int) (t : Int) demand).run clock = some ((answer, out), finish) ∧
      (OptimalCost rows.network (allArcs g.adj) (capacity g.adj Subtype.val) s t demand answer ∨
        (answer = -1 ∧ ¬ ∃ f, SignedFeasible rows.network (allArcs g.adj) (capacity g.adj Subtype.val) s t demand f)) ∧
      finish ≤ clock + 3 + demand.toNat * roundCharge g :=
  min_cost_flow_spec rows.network (allArcs g.adj) (allArcs_unique g.adj) (allArcs_complete g.adj)
    g Subtype.val (findArc g.adj) flow_edge_cap_laws (canonicalLayout g rows sizeEq) s t hs ht
    vertexBound limPos demand pos demandBound stored feasible clock

theorem quarter_clamp_bound (maximum : Int) (atLeastFour : 4 ≤ maximum) : maximum ≤ 7 * (maximum / 4) := by
  omega

end Proofs.Cpp.GraphFlow

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowPairLayout Proofs.Cpp.FlowResidualView

namespace Proofs.Cpp.GraphFlow

/-- Each segment of the slope is optimal for the concrete residual graph. -/
theorem min_cost_flow_slope_spec [NumericTraits "Cost" Int] [ShiftInt Int]
    (g : cp.FlowGraph Int (cp.FlowEdge Int)) (rows : PairedRows g.adj)
    (sizeEq : g.n_ = (g.adj.size : Int)) (s t : Nat) (hs : s < g.adj.size) (ht : t < g.adj.size)
    (vertexBound : g.adj.size ≤ fuel) (limPos : 0 < FlowCostSearch.flowLimit)
    (cutoff : Int) (pos : 0 < cutoff) (roundBound : cutoff.toNat ≤ fuel)
    (stored : ∀ a : ArcOf g.adj, 0 ≤ capacity g.adj Subtype.val a)
    (feasible : ∃ p, FeasiblePotential rows.network (capacity g.adj Subtype.val) p) (clock : Nat) :
    ∃ out points amount cost finish,
      (cp.FlowGraph.min_cost_flow_slope g (s : Int) (t : Int) cutoff).run clock =
        some ((points, out), finish) ∧
      FlowCert rows.network (allArcs g.adj) (capacity g.adj Subtype.val)
        (capacity out.adj Subtype.val) s t amount cost ∧
      FlowCostSearch.CostCurve rows.network (allArcs g.adj) (capacity g.adj Subtype.val)
        s t points amount cost ∧
      FlowCostSearch.StopReason rows.network (allArcs g.adj) (capacity g.adj Subtype.val)
        s t cutoff points amount cost ∧
      points.size ≤ cutoff.toNat + 1 ∧
      finish ≤ clock + 2 + cutoff.toNat * FlowCostSearch.roundCharge g :=
  FlowCostSearch.slope_spec rows.network (allArcs g.adj) (allArcs_unique g.adj) (allArcs_complete g.adj)
    g Subtype.val (findArc g.adj) flow_edge_cap_laws (canonicalLayout g rows sizeEq) s t hs ht
    vertexBound limPos cutoff pos roundBound stored feasible clock


/-- A Dinic phase holds two vertex arrays. The remaining layers bound the number of active
constant-size DFS frames, because each eligible recursive call strictly decreases their rank. -/
theorem dfs_workspace_slots {E Arc : Type} [Inhabited E] [Field "cap" E Int]
    {g : cp.FlowGraph Int E} {n : Network Arc Nat} {slot : Arc → Slot} {t : Nat}
    (cursors : FlowDinic.Cursors n g slot t) (levels : g.level.size = g.adj.size) (depth : Nat) :
    g.level.size + g.iter.size + rank (List.range g.adj.size) (FlowBfs.levelsView g.level) depth ≤
      3 * g.adj.size := by
  have frames := rank_le (List.range g.adj.size) (FlowBfs.levelsView g.level) depth
  rw [List.length_range] at frames
  rw [levels, cursors.size]
  omega

/-- Bellman–Ford's three arrays can coexist with their value copies into the return tuple.
The slope also holds two entries for each breakpoint. -/
theorem slope_workspace_slots {n cutoff : Nat} {labels : FlowCostSearch.Pass Int}
    {points : Array (Int × Int)} (sizes : FlowCostSearch.LabelSizes n labels)
    (count : points.size ≤ cutoff + 1) :
    2 * (labels.1.size + labels.2.1.size + labels.2.2.1.size) + 2 * points.size ≤
      6 * n + 2 * (cutoff + 1) := by
  rw [sizes.distance, sizes.parent, sizes.edgeNumber]
  omega

end Proofs.Cpp.GraphFlow
