import Proofs.Cpp.FlowPairLayout
import Proofs.Cpp.FlowCostSlopeState

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowPairLayout
open Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.GraphFlow

variable {E : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int] [Field "rev" E Int]

private instance (adj : Array (Array E)) (a : Slot) : Decidable (InBounds adj a) :=
  inferInstanceAs (Decidable (a.1 < adj.size ∧ a.2 < adj[a.1]!.size))

def findArc (adj : Array (Array E)) (v i : Int) : Option (ArcOf adj) :=
  if h : 0 ≤ v ∧ 0 ≤ i ∧ InBounds adj (v.toNat, i.toNat) then
    some ⟨(v.toNat, i.toNat), h.2.2⟩
  else none

theorem findArc_of_slot (adj : Array (Array E)) (a : ArcOf adj) :
    findArc adj ((a.val.1 : Nat) : Int) ((a.val.2 : Nat) : Int) = some a := by
  unfold findArc
  have yes : 0 ≤ (a.val.1 : Int) ∧ 0 ≤ (a.val.2 : Int) ∧
      InBounds adj (((a.val.1 : Nat) : Int).toNat, ((a.val.2 : Nat) : Int).toNat) := by simp [a.property]
  rw [dif_pos yes]
  congr 1

theorem findArc_sound (adj : Array (Array E)) (v i : Int) (a : ArcOf adj) (found : findArc adj v i = some a) :
    v = (a.val.1 : Int) ∧ i = (a.val.2 : Int) := by
  unfold findArc at found
  split at found
  next index =>
    have eq := congrArg Subtype.val (Option.some.inj found)
    rw [← eq]
    exact ⟨(Int.toNat_of_nonneg index.1).symm, (Int.toNat_of_nonneg index.2.1).symm⟩
  next => contradiction

/-- Every in-bounds residual row position is represented, with its original identity preserved. -/
def canonicalLayout (g : cp.FlowGraph Int E) (rows : PairedRows g.adj) (sizeEq : g.n_ = (g.adj.size : Int)) :
    CapacityLayout rows.network g Subtype.val (findArc g.adj) where
  order := {
    position := fun a => a.val.2
    graph_size := sizeEq
    tailBound := fun a => a.property.1
    headBound := fun a => (rows.rev_valid a.val a.property).1
    positionBound := fun a => a.property.2
    lookup := findArc_of_slot g.adj
    lookup_sound := findArc_sound g.adj
    covers := fun v hv i hi => ⟨⟨(v, i), ⟨hv, hi⟩⟩, rfl, rfl⟩
    dest := fun a => (Int.toNat_of_nonneg (rows.to_nonnegative a.val a.property)).symm
    cap := fun _ => rfl
    cost := fun _ => rfl
  }
  slotEq := fun _ => rfl
  represents := rows.represents
  reverseIndices := fun a => rows.rev_nonnegative a.val a.property

private def rowSlots (adj : Array (Array E)) (v : Nat) : List Slot :=
  (List.range adj[v]!.size).map (fun i => (v, i))

private def rawSlots (adj : Array (Array E)) : List Slot :=
  (List.range adj.size).flatMap (rowSlots adj)

private theorem mem_rawSlots (adj : Array (Array E)) (a : Slot) : a ∈ rawSlots adj ↔ InBounds adj a := by
  rcases a with ⟨v, i⟩
  simp [rawSlots, rowSlots, InBounds, List.mem_flatMap, List.mem_map]

private theorem rawSlots_unique (adj : Array (Array E)) : (rawSlots adj).Nodup := by
  unfold rawSlots List.Nodup
  rw [List.pairwise_flatMap]
  constructor
  · intro v _
    unfold rowSlots
    rw [List.pairwise_map]
    exact List.nodup_range.imp (by intro a b h he; exact h (congrArg Prod.snd he))
  · apply List.nodup_range.imp
    intro v w different a ha b hb he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
    exact different (congrArg Prod.fst he)

/-- Enumerate the concrete residual arc identities once, preserving parallel occurrences. -/
def allArcs (adj : Array (Array E)) : List (ArcOf adj) :=
  (rawSlots adj).pmap Subtype.mk (fun a h => (mem_rawSlots adj a).mp h)

theorem allArcs_complete (adj : Array (Array E)) (a : ArcOf adj) : a ∈ allArcs adj := by
  unfold allArcs
  exact List.mem_pmap.mpr ⟨a.val, (mem_rawSlots adj a.val).mpr a.property, Subtype.ext rfl⟩

theorem allArcs_unique (adj : Array (Array E)) : (allArcs adj).Nodup := by
  unfold allArcs List.Nodup
  rw [List.pairwise_pmap]
  exact (rawSlots_unique adj).imp (fun h _ _ eq => h (congrArg Subtype.val eq))

theorem allArcs_length (g : cp.FlowGraph Int E) : (allArcs g.adj).length = arcCount g := by
  rw [allArcs, List.length_pmap]
  unfold rawSlots arcCount
  rw [List.length_flatMap]
  have rr := range_map_get g.adj
  rw [range_zero_size, List.map_map] at rr
  rw [← rr, List.map_map]
  simp only [rowSlots, List.length_map, List.length_range, Function.comp_def, get_natCast]

end Proofs.Cpp.GraphFlow
