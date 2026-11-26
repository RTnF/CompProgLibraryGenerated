import Proofs.Cpp.FlowCostSlopeStep
import Proofs.Cpp.FlowCostSlopeMath

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int]

/-- The index layout remains valid after a pure capacity update. -/
def Layout.withRows (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (layout : Layout n g (capacity g.adj slot) atSlot)
    (slotEq : ∀ a, slot a = (n.tail a, layout.position a)) (out : Array (Array E)) (rep : Represents n out slot)
    (dims : out.size = g.adj.size ∧ ∀ v : Nat, out[v]!.size = g.adj[v]!.size) :
    Layout n {g with adj := out} (capacity out slot) atSlot where
  position := layout.position
  graph_size := by simp [dims.1, layout.graph_size]
  tailBound := by intro a; simpa [dims.1] using layout.tailBound a
  headBound := by intro a; simpa [dims.1] using layout.headBound a
  positionBound := by
    intro a
    simpa only [get_natCast, dims.2] using layout.positionBound a
  lookup := layout.lookup
  lookup_sound := layout.lookup_sound
  covers := by
    intro v hv i hi
    apply layout.covers v (by simpa [dims.1] using hv) i
    simpa only [get_natCast, dims.2] using hi
  dest := by
    intro a
    have h := rep.head_eq a
    rw [slotEq a] at h
    exact h
  cap := by
    intro a
    unfold capacity
    rw [slotEq a]
    rfl
  cost := by
    intro a
    have h := rep.cost_eq a
    rw [slotEq a] at h
    exact h

theorem arcCount_withRows (g : cp.FlowGraph Int E) (out : Array (Array E))
    (dims : out.size = g.adj.size ∧ ∀ v : Nat, out[v]!.size = g.adj[v]!.size) :
    arcCount {g with adj := out} = arcCount g := by
  unfold arcCount
  congr 1
  apply List.ext_getElem (by simp [dims.1])
  intro i hi hj
  simp only [List.length_map, Array.length_toList] at hi hj
  simp only [List.getElem_map, Array.getElem_toList]
  simpa only [getElem!_pos, hi, hj] using dims.2 i

structure CapacityLayout (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) where
  order : Layout n g (capacity g.adj slot) atSlot
  slotEq : ∀ a, slot a = (n.tail a, order.position a)
  represents : Represents n g.adj slot
  reverseIndices : ∀ a, 0 ≤ revIdx (readSlot g.adj (slot a))

def CapacityLayout.withRows {n : Network Arc Nat} {g : cp.FlowGraph Int E} {slot : Arc → Slot}
    {atSlot : Int → Int → Option Arc} (old : CapacityLayout n g slot atSlot) (out : Array (Array E))
    (rep : Represents n out slot) (dims : out.size = g.adj.size ∧ ∀ v : Nat, out[v]!.size = g.adj[v]!.size)
    (indices : ∀ a, 0 ≤ revIdx (readSlot out (slot a))) : CapacityLayout n {g with adj := out} slot atSlot :=
  ⟨old.order.withRows n g slot atSlot old.slotEq out rep dims, old.slotEq, rep, indices⟩

end Proofs.Cpp.FlowCostSearch
