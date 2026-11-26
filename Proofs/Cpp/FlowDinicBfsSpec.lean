import Proofs.Cpp.FlowDinicMaxProgram

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.FlowBfs Proofs.Cpp.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int] [Field "rev" E Int]

private theorem locate_edge (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (layout : CapacityLayout n g slot atSlot) (u : Nat) (hu : u < g.adj.size)
    (e : E) (occurs : e ∈ edgesAt g u) : ∃ a, n.tail a = u ∧ readSlot g.adj (slot a) = e := by
  let row := get g.adj (u : Int)
  have hm : e ∈ row := Array.mem_toList_iff.mp occurs
  obtain ⟨i, hi, eq⟩ := Array.getElem_of_mem hm
  obtain ⟨a, atU, pos⟩ := layout.order.covers u hu i hi
  refine ⟨a, atU, ?_⟩
  rw [layout.slotEq a, atU, pos]
  change get row (i : Int) = e
  simpa only [get_natCast, getElem!_pos, hi] using eq

theorem layout_bfs_valid (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (layout : CapacityLayout n g slot atSlot) : Valid g := by
  refine ⟨layout.order.graph_size, ?_⟩
  intro u hu e hm
  obtain ⟨a, _, rfl⟩ := locate_edge n g slot atSlot layout u hu e hm
  have he : FlowBfs.target (readSlot g.adj (slot a)) = (n.head a : Int) := layout.represents.head_eq a
  rw [he, layout.order.graph_size]
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast layout.order.headBound a⟩

theorem residual_arc (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (layout : CapacityLayout n g slot atSlot) (u v : Nat) :
    residual g u v ↔ ∃ a, n.tail a = u ∧ n.head a = v ∧ 0 < capacity g.adj slot a := by
  constructor
  · rintro ⟨hu, e, row, pos, atV⟩
    obtain ⟨a, atU, rfl⟩ := locate_edge n g slot atSlot layout u hu e row
    have h : FlowBfs.target (readSlot g.adj (slot a)) = (n.head a : Int) := layout.represents.head_eq a
    rw [h] at atV
    exact ⟨a, atU, by omega, pos⟩
  · rintro ⟨a, rfl, rfl, pos⟩
    exact layout.represents.edge a pos

private theorem prepend_walk {edge : Nat → Nat → Prop} {u w v d : Nat}
    (first : edge u w) (rest : Walk edge w v d) : Walk edge u v (d + 1) := by
  induction rest with
  | start => exact Walk.step Walk.start first
  | step earlier last ih => exact Walk.step ih last

theorem abstract_residual_walk (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (layout : CapacityLayout n g slot atSlot) (u v d : Nat) :
    Walk (residual g) u v d ↔ ∃ path, Path n u v path ∧ path.length = d ∧ ∀ a ∈ path, 0 < capacity g.adj slot a := by
  constructor
  · intro h
    induction h with
    | start => exact ⟨[], .nil _, rfl, by simp⟩
    | @step a b k walk arc ih =>
      obtain ⟨path, route, length, positive⟩ := ih
      obtain ⟨e, tail, head, available⟩ := (residual_arc n g slot atSlot layout a b).mp arc
      refine ⟨path ++ [e], head ▸ route.snoc e tail, by simp [length], ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact positive x hx
      · obtain rfl : x = e := by simpa using hx
        exact available
  · rintro ⟨path, route, rfl, pos⟩
    induction route with
    | nil => exact .start
    | @cons a v rest trail ih =>
      have arc := layout.represents.edge a (pos a (List.mem_cons_self ..))
      have h := ih (fun b hb => pos b (List.mem_cons_of_mem _ hb))
      exact prepend_walk arc h

private theorem arcCounts (g : cp.FlowGraph Int E) : FlowBfs.arcCount g = FlowCostSearch.arcCount g := by
  unfold FlowBfs.arcCount FlowCostSearch.arcCount
  induction g.adj.toList with
  | nil => rfl
  | cons row rest ih => simp [ih]

/-- The generated BFS labels are the exact minimum lengths over the capacity layout's arcs. -/
theorem bfs_phase (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (layout : CapacityLayout n g slot atSlot) (s : Nat) (hs : s < g.adj.size)
    (fuelBound : g.adj.size + 2 ≤ fuel) (clock : Nat) :
    ∃ (lv : Array Int) (finish : Nat), (cp.FlowGraph.bfs g (s : Int)).run clock = some ({g with level := lv}, finish) ∧
      lv.size = g.adj.size ∧ levelsView lv s = some 0 ∧ ValidDistance n (capacity g.adj slot) (levelsView lv) ∧
      (∀ v < g.adj.size, get lv (v : Int) = -1 ∨ ∃ d, levelsView lv v = some d ∧ d < g.adj.size ∧
        ∃ path, Path n s v path ∧ path.length = d ∧ ∀ a ∈ path, Usable n (capacity g.adj slot) (levelsView lv) a) ∧
      finish ≤ clock + 3 + 4 * g.adj.size + 2 * FlowCostSearch.arcCount g := by
  obtain ⟨lv, finish, run, len, root, closed, props, spend, storage⟩ :=
    bfs_spec g (layout_bfs_valid n g slot atSlot layout) s hs fuelBound clock
  have distance : ValidDistance n (capacity g.adj slot) (levelsView lv) := by
    intro a positive d hd
    exact closed (n.tail a) d hd (n.head a) (layout.represents.edge a positive)
  refine ⟨lv, finish, run, len, root, distance, ?_, by rwa [arcCounts] at spend⟩
  intro v hv
  by_cases unmarked : get lv (v : Int) = -1
  · exact Or.inl unmarked
  · have vk : v < lv.size := by rwa [len]
    have value : get lv (v : Int) = (((get lv (v : Int)).toNat : Nat) : Int) := by
      have h := storage v hv
      omega
    let d := (get lv (v : Int)).toNat
    have hvalue : get lv (v : Int) = (d : Int) := value
    have hlabel : levelsView lv v = some d := (view_some lv vk).mpr hvalue
    have shortest := ((props v hv).2 d hvalue).1
    obtain ⟨path, route, length, positive⟩ := (abstract_residual_walk n g slot atSlot layout s v d).mp shortest
    obtain ⟨j, hl, _, tight⟩ := walk_distance n (capacity g.adj slot) (levelsView lv) distance route positive 0 root
    have eq : j = d := Option.some.inj (hl.symm.trans hlabel)
    have all : ∀ a ∈ path, UnitStep n (levelsView lv) a := tight (by omega)
    have small := unit_length n (levelsView lv) (List.range g.adj.size) route all (List.mem_range.mpr hv)
      (fun a => List.mem_range.mpr (layout.order.tailBound a))
    refine Or.inr ⟨d, hlabel, by simpa only [List.length_range, length] using small, path, route, length, ?_⟩
    intro a ha
    exact ⟨positive a ha, all a ha⟩

end Proofs.Cpp.FlowDinic
