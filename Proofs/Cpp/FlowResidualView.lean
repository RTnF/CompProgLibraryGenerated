import Proofs.Cpp.FlowBfsEntry
import Proofs.Cpp.FlowResidualSlots
import Proofs.Math.FlowDinicLevels

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowBfs

namespace Proofs.Cpp.FlowResidualView

variable {E Arc : Type} [Inhabited E] [DecidableEq Arc]
  [Field "cap" E Int] [Field "to" E Int] [Field "rev" E Int] [Field "cost" E Int]

def capacity (adj : Array (Array E)) (slot : Arc → Slot) (a : Arc) : Int := cap (readSlot adj (slot a))

/-- Stable slot identities relate the C++ rows to a paired residual network. -/
structure Represents (n : Network Arc Nat) (adj : Array (Array E)) (slot : Arc → Slot) : Prop where
  injective : Function.Injective slot
  bounded : ∀ a, InBounds adj (slot a)
  tail_eq : ∀ a, (slot a).1 = n.tail a
  head_eq : ∀ a, dest (readSlot adj (slot a)) = (n.head a : Int)
  reverse_eq : ∀ a, reverseSlot adj (slot a) = slot (n.reverse a)
  cost_eq : ∀ a, price (readSlot adj (slot a)) = n.cost a

omit [DecidableEq Arc] in
theorem Represents.edge {n : Network Arc Nat} {g : cp.FlowGraph Int E} {slot : Arc → Slot}
    (model : Represents n g.adj slot) (a : Arc) (h : 0 < capacity g.adj slot a) :
    residual g (n.tail a) (n.head a) := by
  have hv := model.bounded a
  have hm : readSlot g.adj (slot a) ∈ edgesAt g (n.tail a) := by
    rw [← model.tail_eq a]
    unfold readSlot edgesAt
    have hi : (slot a).2 < (get g.adj (↑(slot a).1 : Int)).size := by simpa [get_eq] using hv.2
    simpa only [get_eq (get g.adj _) _, Int.toNat_natCast, getElem!_pos, hi] using Array.getElem_mem_toList hi
  exact ⟨model.tail_eq a ▸ hv.1, readSlot g.adj (slot a), hm, h, model.head_eq a⟩

omit [DecidableEq Arc] in
theorem bfs_levels (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (model : Represents n g.adj slot) (valid : Valid g) (s : Nat) (hs : s < g.adj.size)
    (fuel_bound : g.adj.size + 2 ≤ fuel) (t : Nat) :
    ∃ (lv : Array Int) (finish : Nat),
      (cp.FlowGraph.bfs g (s : Int)).run t = some ({ g with level := lv }, finish) ∧
      levelsView lv s = some 0 ∧ ValidDistance n (capacity g.adj slot) (levelsView lv) ∧
      finish ≤ t + 3 + 4 * g.adj.size + 2 * arcCount g := by
  obtain ⟨lv, finish, run, _, root, closed, _, time, _⟩ := bfs_spec g valid s hs fuel_bound t
  refine ⟨lv, finish, run, root, ?_, time⟩
  intro a ha j hj
  exact closed (n.tail a) j hj (n.head a) (model.edge a ha)

omit [DecidableEq Arc] in
/-- The terminal BFS labels define a cut with no outgoing positive residual capacity. -/
theorem bfs_unreachable_cut (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (model : Represents n g.adj slot) (valid : Valid g) (s target : Nat) (hs : s < g.adj.size)
    (fuel_bound : g.adj.size + 2 ≤ fuel) (t : Nat) :
    ∃ (lv : Array Int) (finish : Nat),
      (cp.FlowGraph.bfs g (s : Int)).run t = some ({ g with level := lv }, finish) ∧
      (get lv (target : Int) = -1 → ∃ inside : Nat → Bool, inside s = true ∧ inside target = false ∧
        ∀ a, inside (n.tail a) = true → inside (n.head a) = false → capacity g.adj slot a ≤ 0) := by
  obtain ⟨lv, finish, run, root, distances, _⟩ := bfs_levels n g slot model valid s hs fuel_bound t
  refine ⟨lv, finish, run, ?_⟩
  intro absent
  let inside (v : Nat) : Bool := (levelsView lv v).isSome
  have out : levelsView lv target = none := by
    have h : lv[target]! = -1 := absent
    simp [levelsView, h]
  refine ⟨inside, by simp [inside, root], by simp [inside, out], ?_⟩
  intro a ht hh
  by_contra h
  have hp : 0 < capacity g.adj slot a := by omega
  have chosen : ∃ i, levelsView lv (n.tail a) = some i := by
    cases hlevel : levelsView lv (n.tail a) with
    | none => simp [inside, hlevel] at ht
    | some i => exact ⟨i, rfl⟩
  obtain ⟨i, hi⟩ := chosen
  obtain ⟨j, hj, _⟩ := distances a hp i hi
  simp [inside, hj] at hh

omit [DecidableEq Arc] in
/-- At a reached vertex, Dinic's strict level comparison selects exactly the next layer. -/
theorem strict_level_is_unit_step (n : Network Arc Nat) (cap : Capacity Arc) (lv : Array Int)
    (labels : ValidDistance n cap (levelsView lv)) (a : Arc) (ha : 0 < cap a) (d : Nat)
    (reached : levelsView lv (n.tail a) = some d) :
    get lv (n.tail a : Int) < get lv (n.head a : Int) ↔ UnitStep n (levelsView lv) a := by
  obtain ⟨j, hj, bound⟩ := labels a ha d reached
  have asValue (v k : Nat) (h : levelsView lv v = some k) : get lv (v : Int) = (k : Int) := by
    have hb : v < lv.size := by
      by_contra hn
      simp [levelsView, hn] at h
    exact (view_some lv hb).mp h
  rw [asValue _ _ reached, asValue _ _ hj]
  constructor
  · intro h
    have eq : j = d + 1 := by omega
    exact ⟨d, reached, eq ▸ hj⟩
  · rintro ⟨i, hi, hi'⟩
    rw [reached, Option.some.injEq] at hi
    rw [hj, Option.some.injEq] at hi'
    omega

variable [WriteField "cap" E Int]

theorem Represents.adjust_capacity {n : Network Arc Nat} {adj : Array (Array E)} {slot : Arc → Slot}
    (model : Represents n adj slot) (laws : CapLaws (E := E)) (a : Arc) (d : Int) :
    capacity (adjust adj (slot a) d) slot = update n (capacity adj slot) a d :=
  adjust_projects n slot model.injective laws adj model.bounded model.reverse_eq a d

omit [DecidableEq Arc] in
theorem Represents.adjust {n : Network Arc Nat} {adj : Array (Array E)} {slot : Arc → Slot}
    (model : Represents n adj slot) (laws : CapLaws (E := E)) (a : Arc) (d : Int) :
    Represents n (FlowResidualSlots.adjust adj (slot a) d) slot := by
  have reverse_valid : InBounds adj (reverseSlot adj (slot a)) := by
    rw [model.reverse_eq a]
    exact model.bounded _
  have reverse_ne : reverseSlot adj (slot a) ≠ slot a := by
    rw [model.reverse_eq a]
    exact fun h => n.reverse_ne a (model.injective h)
  have projection (b : Arc) := adjust_metadata laws adj (slot a) d (model.bounded a) reverse_valid reverse_ne (slot b)
  refine ⟨model.injective, ?_, model.tail_eq, ?_, ?_, ?_⟩
  · intro b
    exact (adjust_bounds laws adj (slot a) d (model.bounded a) reverse_valid (slot b)).mpr (model.bounded b)
  · intro b
    exact (projection b).1.trans (model.head_eq b)
  · intro b
    unfold reverseSlot
    rw [(projection b).1, (projection b).2.1]
    exact model.reverse_eq b
  · intro b
    exact (projection b).2.2.trans (model.cost_eq b)

end Proofs.Cpp.FlowResidualView
