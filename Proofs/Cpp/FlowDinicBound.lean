import Proofs.Cpp.FlowDinicBfsSpec

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.Cpp.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [DecidableEq Arc]

private theorem sum_le {α : Type} (xs : List α) (f g : α → Nat) (good : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have a := good x (List.mem_cons_self ..)
    have b := ih (fun y hy => good y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons] at b ⊢
    omega

theorem cursor_charge_bound (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot) (t : Nat)
    (st : Cursors n g slot t) : cursorCharge g ≤ FlowCostSearch.arcCount g := by
  have hi := range_map_get g.iter
  have ha := range_map_get g.adj
  rw [range_zero_size, List.map_map, st.size] at hi
  rw [range_zero_size, List.map_map] at ha
  unfold cursorCharge FlowCostSearch.arcCount
  rw [← hi, ← ha, List.map_map, List.map_map]
  apply sum_le
  intro v hv
  have le := (st.within v (List.mem_range.mp hv)).2
  change ((get g.iter (v : Int)).toNat) ≤ (get g.adj (v : Int)).size
  change get g.iter (v : Int) ≤ ((get g.adj (v : Int)).size : Int) at le
  omega

noncomputable def phaseEnergy (n : Network Arc Nat) (lv : Levels Nat) (cap : Capacity Arc)
    (arcs : List Arc) (upper total limit : Int) : Nat :=
  (activeArcs n lv cap arcs).length + (upper - total).toNat / limit.toNat

theorem bottleneck_saturates (n : Network Arc Nat) (g out : cp.FlowGraph Int E) (slot : Arc → Slot)
    (s t : Nat) (limit d : Int) (path : List Arc) (move : PathPush n g out slot s t limit d path) :
    d = limit ∨ ∃ a ∈ path, capacity g.adj slot a = d := by
  by_contra h
  have gap : d < limit := by
    have cap := move.within_limit
    by_contra neg
    have eq : d = limit := by omega
    exact h (Or.inl eq)
  have better (a : Arc) (ha : a ∈ path) : d + 1 ≤ capacity g.adj slot a := by
    have bound := move.supply a ha
    by_contra neg
    have eq : capacity g.adj slot a = d := by omega
    exact h (Or.inr ⟨a, ha, eq⟩)
  have largest := move.maximal (d + 1) (by omega) better
  omega

theorem energy_drops (n : Network Arc Nat) (g out : cp.FlowGraph Int E) (slot : Arc → Slot)
    (arcs : List Arc) (unique : arcs.Nodup) (all : ∀ a, a ∈ arcs) (s t : Nat) (limit d upper flow : Int)
    (limPos : 0 < limit) (within : flow + d ≤ upper) (path : List Arc)
    (move : PathPush n g out slot s t limit d path) :
    phaseEnergy n (levelsView g.level) (capacity out.adj slot) arcs upper (flow + d) limit <
      phaseEnergy n (levelsView g.level) (capacity g.adj slot) arcs upper flow limit := by
  have steps (a : Arc) (ha : a ∈ path) : UnitStep n (levelsView g.level) a := (move.usable a ha).2
  have nonzero := move.positive
  have weaker : WeakensLayer n (levelsView g.level) (capacity g.adj slot) (capacity out.adj slot) := by
    rw [move.after]
    exact layer_after_augment n (levelsView g.level) (capacity g.adj slot) path.reverse d
      (fun a ha => steps a (by simpa using ha)) (by omega)
  have quo : (upper - (flow + d)).toNat / limit.toNat ≤ (upper - flow).toNat / limit.toNat :=
    Nat.div_le_div_right (by omega)
  unfold phaseEnergy
  rcases bottleneck_saturates n g out slot s t limit d path move with equal | ⟨a, ha, cap⟩
  · have counts := active_not_growing n (levelsView g.level) (capacity g.adj slot) (capacity out.adj slot) arcs unique weaker
    have div : (upper - flow).toNat / limit.toNat = (upper - (flow + d)).toNat / limit.toNat + 1 := by
      have diff : (upper - flow).toNat = (upper - (flow + d)).toNat + limit.toNat := by omega
      rw [diff, Nat.add_div_right _ (by omega)]
    omega
  · have gone : ¬ Usable n (capacity out.adj slot) (levelsView g.level) a := by
      have distinct := (unit_path_distinct n (levelsView g.level) move.route steps).reverse
      have selected := augment_selected n (capacity g.adj slot) path.reverse d distinct a (by simpa using ha)
      rw [cap] at selected
      rw [move.after, Usable, selected, Int.sub_self]
      simp
    have counts := active_drops n (levelsView g.level) (capacity g.adj slot) (capacity out.adj slot) arcs unique weaker a
      (all a) (move.usable a ha) gone
    omega

omit [DecidableEq Arc] in
theorem energy_bound (n : Network Arc Nat) (lv : Levels Nat) (cap : Capacity Arc) (arcs : List Arc)
    (flow limit : Int) (nonnegative : 0 ≤ flow) (limPos : 0 < limit) :
    phaseEnergy n lv cap arcs ((arcs.length : Int) * (7 * limit)) flow limit ≤ 8 * arcs.length := by
  have active : (activeArcs n lv cap arcs).length ≤ arcs.length := List.length_filter_le ..
  have product : (((arcs.length : Int) * (7 * limit))).toNat = (7 * arcs.length) * limit.toNat := by
    rw [Int.toNat_mul (by omega) (by omega), Int.toNat_mul (by decide) (by omega)]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hquo : ((((arcs.length : Int) * (7 * limit)) - flow).toNat / limit.toNat) ≤ 7 * arcs.length := by
    have h := Nat.div_le_div_right (c := limit.toNat)
      (show (((arcs.length : Int) * (7 * limit)) - flow).toNat ≤ (((arcs.length : Int) * (7 * limit))).toNat by omega)
    rwa [product, Nat.mul_div_cancel _ (by omega)] at h
  unfold phaseEnergy
  omega

end Proofs.Cpp.FlowDinic
