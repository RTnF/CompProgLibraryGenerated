import Proofs.Cpp.FlowCostSlopeState
import Proofs.Math.FlowLayerSearchMath

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.Cpp.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int]

def cursor {Cost E : Type} (g : cp.FlowGraph Cost E) (v : Nat) : Int := get g.iter (v : Int)

structure Cursors (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot) (t : Nat) : Prop where
  size : g.iter.size = g.adj.size
  within : ∀ v < g.adj.size, 0 ≤ cursor g v ∧ cursor g v ≤ Cpp.size (get g.adj (v : Int))
  prefix_dead : ∀ a, ((slot a).2 : Int) < cursor g (n.tail a) → Dead n (capacity g.adj slot) (levelsView g.level) t a

def Layout_changeIter (n : Network Arc Nat) (g : cp.FlowGraph Int E) (cap : Capacity Arc)
    (atSlot : Int → Int → Option Arc) (layout : Layout n g cap atSlot) (iter : Array Int) :
    Layout n {g with iter} cap atSlot := ⟨layout.position, layout.graph_size, layout.tailBound, layout.headBound,
      layout.positionBound, layout.lookup, layout.lookup_sound, layout.covers, layout.dest, layout.cap, layout.cost⟩

def layout_changeIter {n : Network Arc Nat} {g : cp.FlowGraph Int E} {slot : Arc → Slot} {atSlot : Int → Int → Option Arc}
    (h : CapacityLayout n g slot atSlot) (iter : Array Int) : CapacityLayout n {g with iter} slot atSlot :=
  ⟨Layout_changeIter n g _ atSlot h.order iter, h.slotEq, h.represents, h.reverseIndices⟩

def cursorCharge {Cost E : Type} (g : cp.FlowGraph Cost E) : Nat := (g.iter.toList.map Int.toNat).sum

theorem cursor_advanced (g : cp.FlowGraph Int E) (v : Nat) (i : Int) (hv : v < g.iter.size) (w : Nat) :
    cursor (advanceCursor g (v : Int) i) w = if w = v then i + 1 else cursor g w := by
  unfold cursor advanceCursor
  exact (by simpa only [get_natCast, Int.toNat_natCast] using
    getElemBang_set g.iter (v : Int) (i + 1) w (by simpa using hv))

private theorem sum_set {xs : List Int} {i : Nat} (bound : i < xs.length) (value : Int) :
    (((xs.set i value).map Int.toNat).sum + xs[i].toNat) = (xs.map Int.toNat).sum + value.toNat := by
  induction xs generalizing i with
  | nil => simp at bound
  | cons a rest ih =>
    cases i with
    | zero => simp; omega
    | succ i =>
      have hi : i < rest.length := by simpa using bound
      have h := ih hi
      simp only [List.set_cons_succ, List.getElem_cons_succ, List.map_cons, List.sum_cons]
      omega

theorem cursor_advance_charge (g : cp.FlowGraph Int E) (v i : Nat) (hv : v < g.iter.size) (atPos : cursor g v = (i : Int)) :
    cursorCharge (advanceCursor g (v : Int) (i : Int)) = cursorCharge g + 1 := by
  have bound : v < g.iter.toList.length := by simpa using hv
  have h := sum_set bound ((i : Int) + 1)
  simp only [Array.getElem_toList] at h
  have curr : g.iter[v] = (i : Int) := by simpa only [cursor, get_natCast, getElem!_pos, hv] using atPos
  rw [curr] at h
  unfold cursorCharge advanceCursor set
  simp only [Array.toList_set!, Int.toNat_natCast]
  omega

theorem cursor_bump {n : Network Arc Nat} {g : cp.FlowGraph Int E} {slot : Arc → Slot} {atSlot : Int → Int → Option Arc}
    {t : Nat} (layout : CapacityLayout n g slot atSlot) (ok : Cursors n g slot t) (v i : Nat)
    (hv : v < g.adj.size) (hi : i < (get g.adj (v : Int)).size) (current : cursor g v = (i : Int))
    (dead : ∀ a, slot a = (v, i) → Dead n (capacity g.adj slot) (levelsView g.level) t a) :
    Cursors n (advanceCursor g (v : Int) (i : Int)) slot t := by
  have iterBound : v < g.iter.size := by rwa [ok.size]
  refine ⟨by simp [advanceCursor, ok.size], ?_, ?_⟩
  · intro w hw
    have bounds := ok.within w hw
    rw [cursor_advanced g v (i : Int) iterBound]
    by_cases eq : w = v
    · subst w
      rw [ite_eq_left rfl]
      change 0 ≤ (i : Int) + 1 ∧ (i : Int) + 1 ≤ ((get g.adj (v : Int)).size : Int)
      omega
    · rwa [ite_eq_right eq]
  · intro a ha
    rw [cursor_advanced g v (i : Int) iterBound] at ha
    by_cases active : n.tail a = v
    · rw [ite_eq_left active] at ha
      have basis : ((slot a).2 : Int) ≤ (i : Int) := by omega
      by_cases eq : (slot a).2 = i
      · apply dead a
        exact Prod.ext ((layout.represents.tail_eq a).trans active) eq
      · apply ok.prefix_dead a
        rw [active, current]
        omega
    · rw [ite_eq_right active] at ha
      exact ok.prefix_dead a ha

theorem cursor_with_rows {n : Network Arc Nat} {g : cp.FlowGraph Int E} {slot : Arc → Slot} {t : Nat}
    (ok : Cursors n g slot t) (out : Array (Array E)) (dims : out.size = g.adj.size ∧ ∀ v : Nat, out[v]!.size = g.adj[v]!.size)
    (weakens : WeakensLayer n (levelsView g.level) (capacity g.adj slot) (capacity out slot)) :
    Cursors n {g with adj := out} slot t := by
  refine ⟨ok.size.trans dims.1.symm, ?_, ?_⟩
  · intro v hv
    simpa only [cursor, Cpp.size, get_natCast, dims.2] using ok.within v (by rwa [dims.1] at hv)
  · intro a ha
    exact weakens.dead (ok.prefix_dead a ha)

variable [WriteField "cap" E Int]

theorem eligible_usable (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (rep : Represents n g.adj slot) (labelValid : ValidDistance n (capacity g.adj slot) (levelsView g.level))
    (a : Arc) (nonneg : 0 ≤ capacity g.adj slot a) (d : Nat)
    (known : levelsView g.level (n.tail a) = some d) :
    eligible g (n.tail a : Int) ((slot a).2 : Int) = true ↔ Usable n (capacity g.adj slot) (levelsView g.level) a := by
  have atEq : atEdge g.adj (n.tail a : Int) ((slot a).2 : Int) = readSlot g.adj (slot a) := by
    rw [← rep.tail_eq a]
    rfl
  unfold eligible
  dsimp only
  rw [atEq]
  have hd : destOf (readSlot g.adj (slot a)) = (n.head a : Int) := rep.head_eq a
  rw [hd]
  have h (pos : 0 < capacity g.adj slot a) :=
    strict_level_is_unit_step n (capacity g.adj slot) g.level labelValid a pos d known
  have guard (z q : Prop) [Decidable z] [Decidable q] :
      (!(decide z || decide q)) = true ↔ ¬ z ∧ ¬ q := by
    by_cases hz : z <;> by_cases hq : q <;> simp [hz, hq]
  change (!(decide (capacity g.adj slot a = 0) ||
    decide (get g.level (n.tail a : Int) ≥ get g.level (n.head a : Int)))) = true ↔ _
  rw [guard]
  unfold Usable
  constructor
  · rintro ⟨capPos, next⟩
    have pos : 0 < capacity g.adj slot a := by omega
    exact ⟨pos, (h pos).mp (by omega)⟩
  · rintro ⟨pos, next⟩
    have strict := (h pos).mpr next
    exact ⟨by omega, by omega⟩

end Proofs.Cpp.FlowDinic
