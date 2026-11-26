import Proofs.Cpp.FlowCostSearchProjection

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [DecidableEq Arc] [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]

def arcValue (g : cp.FlowGraph Int E) (v i : Nat) : E := get (get g.adj (v : Int)) (i : Int)

/-- All indexed entries belong to the residual network, and every residual slot has an index. -/
structure Layout (n : Network Arc Nat) (g : cp.FlowGraph Int E) (capacity : Capacity Arc)
    (atSlot : Int → Int → Option Arc) where
  position : Arc → Nat
  graph_size : g.n_ = (g.adj.size : Int)
  tailBound : ∀ a, n.tail a < g.adj.size
  headBound : ∀ a, n.head a < g.adj.size
  positionBound : ∀ a, position a < (get g.adj (n.tail a : Int)).size
  lookup : ∀ a, atSlot (n.tail a : Int) (position a : Int) = some a
  lookup_sound : ∀ v i a, atSlot v i = some a → v = (n.tail a : Int) ∧ i = (position a : Int)
  covers : ∀ v < g.adj.size, ∀ i < (get g.adj (v : Int)).size,
    ∃ a, n.tail a = v ∧ position a = i
  dest : ∀ a, target (arcValue g (n.tail a) (position a)) = (n.head a : Int)
  cap : ∀ a, Field.get (member := "cap") (Value := Int) (arcValue g (n.tail a) (position a)) = capacity a
  cost : ∀ a, Field.get (member := "cost") (Value := Int) (arcValue g (n.tail a) (position a)) = n.cost a

private theorem index_range {bound : Nat} {i : Int} : i ∈ range 0 (bound : Int) ↔ ∃ k < bound, (k : Int) = i := by
  simp [range, List.mem_map]

section Fold

variable {n : Network Arc Nat} {g : cp.FlowGraph Int E} {capacity : Capacity Arc}
  {atSlot : Int → Int → Option Arc} (layout : Layout n g capacity atSlot)
  (p : Nat → Int) (feasible : FeasiblePotential n capacity p) (source : Nat)

include layout p feasible

private theorem scan_row (v : Nat) (hv : v < g.adj.size) (indices : List Int)
    (these : indices ⊆ range 0 (size (get g.adj (v : Int))))
    (b : Pass Int) (sizes : LabelSizes g.adj.size b) (cert : SearchCert n capacity source atSlot b)
    (knownFrom : known b v = true) :
    let out := indices.foldl (edgeFold (get g.adj (v : Int)) (v : Int)) b
    LabelSizes g.adj.size out ∧ SearchCert n capacity source atSlot out ∧ Improves b out ∧
    ∀ a, n.tail a = v → ((layout.position a : Nat) : Int) ∈ indices → 0 < capacity a →
      HasLabel (known out) (label out) (n.head a) (label b v + n.cost a) := by
  induction indices generalizing b with
  | nil => exact ⟨sizes, cert, Improves.refl b, by simp⟩
  | cons i rest ih =>
    have hi : i ∈ range 0 (size (get g.adj (v : Int))) := these (List.mem_cons_self ..)
    obtain ⟨k, hk, rfl⟩ := index_range.mp (show i ∈ range 0 ((get g.adj (v : Int)).size : Int) from hi)
    obtain ⟨a, ha, hpos⟩ := layout.covers v hv k hk
    let row := get g.adj (v : Int)
    let mid := edgeFold row (v : Int) b (k : Int)
    have midSize := edgeFold_sizes row (v : Int) (k : Int) b sizes
    have midCert : SearchCert n capacity source atSlot mid := by
      have preserve := fold_preserves_cert n capacity p feasible source a atSlot row k b
        (by simpa only [ha, hpos] using layout.lookup a) (by rwa [ha])
        (by rw [sizes.distance]; exact layout.headBound a) (by rw [sizes.parent]; exact layout.headBound a)
        (by rw [sizes.edgeNumber]; exact layout.headBound a)
        (by simpa only [arcValue, ha, hpos, row] using layout.dest a)
        (by simpa only [arcValue, ha, hpos, row] using layout.cap a)
        (by simpa only [arcValue, ha, hpos, row] using layout.cost a) cert
      simpa only [mid, ha] using preserve
    have hbds := edgeFold_label_bounds n capacity p feasible source a atSlot row k b
      (by simpa only [ha, hpos] using layout.lookup a) (by rwa [ha]) sizes (layout.headBound a)
      (by simpa only [arcValue, ha, hpos, row] using layout.dest a)
      (by simpa only [arcValue, ha, hpos, row] using layout.cap a)
      (by simpa only [arcValue, ha, hpos, row] using layout.cost a) cert.sound
    rw [ha] at hbds
    have improve : Improves b mid := hbds.1
    have curr : HasLabel (known mid) (label mid) v (label b v) := improve _ _ ⟨knownFrom, le_rfl⟩
    obtain ⟨sizeOut, certOut, outer, closed⟩ := ih (fun _ member => these (List.mem_cons_of_mem _ member))
      mid midSize midCert curr.1
    refine ⟨sizeOut, certOut, improve.trans outer, ?_⟩
    intro e he hm hc
    rcases List.mem_cons.mp hm with hfirst | hlater
    · have index_eq : layout.position e = k := by omega
      have same : e = a := Option.some.inj (by
        have r := layout.lookup a
        have s := layout.lookup e
        rw [ha, hpos] at r
        rw [he, index_eq] at s
        exact s.symm.trans r)
      subst e
      exact outer _ _ (hbds.2 hc)
    · have ⟨marked, lower⟩ := closed e he hlater hc
      exact ⟨marked, le_trans lower (Int.add_le_add_right curr.2 _)⟩

theorem row_cert (v : Nat) (hv : v < g.adj.size) (b : Pass Int) (sizes : LabelSizes g.adj.size b)
    (cert : SearchCert n capacity source atSlot b) :
    let out := rowFold g.adj b (v : Int)
    LabelSizes g.adj.size out ∧ SearchCert n capacity source atSlot out ∧ Improves b out ∧
    (known b v = true → ∀ a, n.tail a = v → 0 < capacity a →
      HasLabel (known out) (label out) (n.head a) (label b v + n.cost a)) := by
  unfold rowFold
  split
  next closed =>
    refine ⟨sizes, cert, Improves.refl b, ?_⟩
    intro h
    exact False.elim ((known_iff b v).mp h |>.2 <| closed)
  next openRow =>
    have hv' : known b v = true := (known_iff b v).mpr ⟨by rwa [sizes.parent], openRow⟩
    obtain ⟨sz, good, improved, relaxations⟩ := scan_row layout p feasible source v hv
      (range 0 (size (get g.adj (v : Int)))) (fun _ h => h) b sizes cert hv'
    refine ⟨sz, good, improved, fun _ a ha hc => relaxations a ha ?_ hc⟩
    apply index_range.mpr
    exact ⟨layout.position a, by simpa only [ha] using layout.positionBound a, rfl⟩

private theorem rows_cert (rows : List Int) (rangeOk : rows ⊆ range 0 g.n_) (b : Pass Int)
    (sizes : LabelSizes g.adj.size b) (cert : SearchCert n capacity source atSlot b) :
    let out := rows.foldl (rowFold g.adj) b
    LabelSizes g.adj.size out ∧ SearchCert n capacity source atSlot out ∧ Improves b out ∧
    ∀ a, (n.tail a : Int) ∈ rows → known b (n.tail a) = true → 0 < capacity a →
      HasLabel (known out) (label out) (n.head a) (label b (n.tail a) + n.cost a) := by
  induction rows generalizing b with
  | nil => exact ⟨sizes, cert, Improves.refl b, by simp⟩
  | cons v rest ih =>
    have hv : v ∈ range 0 (g.adj.size : Int) := by
      rw [← layout.graph_size]
      exact rangeOk (List.mem_cons_self ..)
    obtain ⟨i, hi, rfl⟩ := index_range.mp hv
    let next := rowFold g.adj b (i : Int)
    obtain ⟨ns, nc, improves, firstRow⟩ := row_cert layout p feasible source i hi b sizes cert
    obtain ⟨os, oc, later, otherRows⟩ := ih (fun _ h => rangeOk (List.mem_cons_of_mem _ h)) next ns nc
    refine ⟨os, oc, improves.trans later, ?_⟩
    intro a ha knownBefore positive
    rcases List.mem_cons.mp ha with first | restAt
    · have h : n.tail a = i := by omega
      have lower := firstRow (by rwa [← h]) a h positive
      exact later _ _ (by simpa only [h] using lower)
    · have h : HasLabel (known next) (label next) (n.tail a) (label b (n.tail a)) :=
        improves _ _ ⟨knownBefore, le_rfl⟩
      obtain ⟨seen, bound⟩ := otherRows a restAt h.1 positive
      exact ⟨seen, le_trans bound (Int.add_le_add_right h.2 _)⟩

def clearFlag (b : Pass Int) : Pass Int := (b.1, b.2.1, b.2.2.1, false)

def nextSweep (g : cp.FlowGraph Int E) (b : Pass Int) : Pass Int := sweep g (labelPart b)

/-- One full sweep preserves valid witnesses and propagates every label across one more arc. -/
theorem sweep_cert (b : Pass Int) (sizes : LabelSizes g.adj.size b) (cert : SearchCert n capacity source atSlot b) :
    let out := nextSweep g b
    LabelSizes g.adj.size out ∧ SearchCert n capacity source atSlot out ∧ Improves b out ∧
    ∀ a, known b (n.tail a) = true → 0 < capacity a →
      HasLabel (known out) (label out) (n.head a) (label b (n.tail a) + n.cost a) := by
  obtain ⟨sz, nc, improves, bounds⟩ := rows_cert layout p feasible source (range 0 g.n_) (fun _ h => h)
    (clearFlag b) ⟨sizes.distance, sizes.parent, sizes.edgeNumber⟩ ⟨cert.sound, cert.parents⟩
  refine ⟨sz, nc, improves, ?_⟩
  intro a hv hp
  apply bounds a _ hv hp
  rw [layout.graph_size]
  exact index_range.mpr ⟨n.tail a, layout.tailBound a, rfl⟩

end Fold
end Proofs.Cpp.FlowCostSearch
