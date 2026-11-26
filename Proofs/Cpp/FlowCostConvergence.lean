import Proofs.Cpp.FlowCostSweepSound
import Proofs.Math.FlowResidualPaths

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual

namespace Proofs.Cpp.FlowCostSearch

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]

private theorem mem_indices {bound : Nat} {i : Int} : i ∈ range 0 (bound : Int) ↔ ∃ k < bound, (k : Int) = i := by
  simp [range, List.mem_map]

private theorem stable_same (g : cp.FlowGraph Int E) (labels : Labels Int) (stable : Stable g labels) :
    (sweep g labels).2.2.2 = false := by
  let b : Pass Int := (labels.1, labels.2.1, labels.2.2, false)
  have rows_no_change : ∀ rows : List Int, rows ⊆ range 0 g.n_ → rows.foldl (rowFold g.adj) b = b := by
    intro rows vertices
    induction rows with
    | nil => rfl
    | cons v rows ih =>
      have rowEq : rowFold g.adj b v = b := by
        unfold rowFold
        split
        · rfl
        next openRow =>
          have hv : v ∈ range 0 g.n_ := vertices (List.mem_cons_self ..)
          generalize hr : range 0 (size (get g.adj v)) = indices
          have unchanged : ∀ scan : List Int, scan ⊆ indices → scan.foldl (edgeFold (get g.adj v) v) b = b := by
            intro scan within
            induction scan with
            | nil => rfl
            | cons i scan ih =>
              have hi : i ∈ range 0 (size (get g.adj v)) := by
                rw [hr]
                exact within (List.mem_cons_self ..)
              have edgeEq : edgeFold (get g.adj v) v b i = b := by
                unfold edgeFold
                rw [show relaxes (get (get g.adj v) i) v b = false from stable v hv openRow i hi]
                rfl
              rw [List.foldl_cons, edgeEq]
              exact ih (fun _ h => within (List.mem_cons_of_mem _ h))
          exact unchanged indices (fun _ h => h)
      rw [List.foldl_cons, rowEq]
      exact ih (fun _ h => vertices (List.mem_cons_of_mem _ h))
  have h : sweep g labels = b := rows_no_change _ (fun _ h => h)
  rw [h]

variable {n : Network Arc Nat} {g : cp.FlowGraph Int E} {capacity : Capacity Arc} {atSlot : Int → Int → Option Arc}

def KnownWithin (n : Network Arc Nat) (cap : Capacity Arc) (s : Nat) (b : Pass Int) (k : Nat) : Prop :=
  ∀ v path, Path n s v path → (∀ a ∈ path, 0 < cap a) → path.length ≤ k →
    HasLabel (known b) (label b) v (path.map n.cost).sum

private theorem within_zero (s : Nat) (b : Pass Int) (cert : SearchCert n capacity s atSlot b) :
    KnownWithin n capacity s b 0 := by
  intro v path route _ hlen
  have empty : path = [] := List.length_eq_zero_iff.mp (by omega)
  obtain rfl : s = v := route.eq_of_empty empty
  exact ⟨cert.sound.root.1, by simp [cert.sound.root.2, empty]⟩

variable [DecidableEq Arc]

private theorem extends_window (layout : Layout n g capacity atSlot) (p : Nat → Int)
    (feasible : FeasiblePotential n capacity p) (s : Nat) (b : Pass Int) (k : Nat)
    (sizes : LabelSizes g.adj.size b) (cert : SearchCert n capacity s atSlot b)
    (before : KnownWithin n capacity s b k) : KnownWithin n capacity s (nextSweep g b) (k + 1) := by
  obtain ⟨_, _, keeps, reaches⟩ := sweep_cert layout p feasible s b sizes cert
  intro v path route positive hlen
  by_cases empty : path = []
  · exact keeps _ _ (before v path route positive (by simp [empty]))
  obtain ⟨front, a, eq, first, last⟩ := route.split_last empty
  have posPrefix : ∀ b ∈ front, 0 < capacity b := by
    intro b hb
    apply positive b
    rw [eq]
    exact List.mem_append.mpr (Or.inl hb)
  have shortPrefix : front.length ≤ k := by simp [eq] at hlen; omega
  obtain ⟨seen, lower⟩ := before (n.tail a) front first posPrefix shortPrefix
  have ha : a ∈ path := by simp [eq]
  obtain ⟨headKnown, headCost⟩ := reaches a seen (positive a ha)
  rw [last] at headKnown headCost
  refine ⟨headKnown, ?_⟩
  simp only [eq, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
  exact le_trans headCost (Int.add_le_add_right lower _)

private theorem final_window (layout : Layout n g capacity atSlot) (p : Nat → Int)
    (feasible : FeasiblePotential n capacity p) (s : Nat) (hs : s < g.adj.size) (b : Pass Int) (k : Nat)
    (window : KnownWithin n capacity s b k) (enough : g.adj.size ≤ k + 1) :
    ∀ v path, Path n s v path → (∀ a ∈ path, 0 < capacity a) →
      HasLabel (known b) (label b) v (path.map n.cost).sum := by
  intro v path route positive
  have hv : v < g.adj.size := by
    by_cases empty : path = []
    · rwa [← route.eq_of_empty empty]
    · obtain ⟨_, a, _, _, last⟩ := route.split_last empty
      rw [← last]
      exact layout.headBound a
  obtain ⟨simple, simpleRoute, simplePositive, hlen, min⟩ := shortest_simple n capacity p feasible
    (List.range g.adj.size) s v (List.mem_range.mpr hv) (fun a => List.mem_range.mpr (layout.tailBound a))
    _ ⟨path, route, positive, rfl⟩
  have hshort : simple.length ≤ k := by simp at hlen; omega
  have ⟨seen, cost⟩ := window v simple simpleRoute simplePositive hshort
  exact ⟨seen, le_trans cost (min _ ⟨path, route, positive, rfl⟩)⟩

private theorem all_paths_stable (layout : Layout n g capacity atSlot) (s : Nat) (b : Pass Int)
    (cert : SearchCert n capacity s atSlot b) (sizes : LabelSizes g.adj.size b)
    (complete : ∀ v path, Path n s v path → (∀ a ∈ path, 0 < capacity a) →
      HasLabel (known b) (label b) v (path.map n.cost).sum) : Stable g (labelPart b) := by
  intro fromRow inRows reachable col inColumns
  rw [layout.graph_size] at inRows
  obtain ⟨v, hv, eqV⟩ := mem_indices.mp inRows
  subst fromRow
  obtain ⟨i, hi, eqI⟩ := mem_indices.mp (show col ∈ range 0 ((get g.adj (v : Int)).size : Int) from inColumns)
  subst col
  obtain ⟨a, ht, hp⟩ := layout.covers v hv i hi
  let e := arcValue g v i
  have testRelaxes := relaxes_projects n capacity a (clearFlag b) e
    (by simpa only [ht, hp, e] using layout.dest a) (by simpa only [ht, hp, e] using layout.cap a)
    (by simpa only [ht, hp, e] using layout.cost a) (by change n.head a < b.2.1.size; rw [sizes.parent]; exact layout.headBound a)
  rw [ht] at testRelaxes
  change relaxes e (v : Int) (clearFlag b) = false
  cases fires : relaxes e (v : Int) (clearFlag b)
  · rfl
  · have ⟨pos, strict⟩ := testRelaxes.mp fires
    have seen : known b v = true := (known_iff b v).mpr ⟨by rwa [sizes.parent], reachable⟩
    obtain ⟨path, route, positive, exactCost⟩ := cert.sound.sound v seen
    have positive' : ∀ e ∈ path ++ [a], 0 < capacity e := by
      intro a' h
      rcases List.mem_append.mp h with earlier | last
      · exact positive a' earlier
      · obtain rfl : a' = a := by simpa using last
        exact pos
    obtain ⟨targetSeen, targetLabel⟩ := complete (n.head a) (path ++ [a]) (route.snoc a ht) positive'
    have improved := strict targetSeen
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Int.add_zero,
      exactCost] at targetLabel
    change label b v + n.cost a < label b (n.head a) at improved
    omega

/-- At most one full scan per vertex is needed, including the scan with no updates. -/
theorem stops_within_vertices (layout : Layout n g capacity atSlot) (p : Nat → Int)
    (feasible : FeasiblePotential n capacity p) (s : Nat) (hs : s < g.adj.size)
    (b : Pass Int) (sizes : LabelSizes g.adj.size b) (cert : SearchCert n capacity s atSlot b) :
    StopsBy g g.adj.size (labelPart b) := by
  have stepBound : ∀ rem k b, g.adj.size ≤ k + rem + 1 → LabelSizes g.adj.size b →
      SearchCert n capacity s atSlot b → KnownWithin n capacity s b k → StopsBy g (rem + 1) (labelPart b) := by
    intro rem
    induction rem with
    | zero =>
      intro k current enough sizeOk certOk knownOk
      exact Or.inl (stable_same g _ (all_paths_stable layout s current certOk sizeOk
        (final_window layout p feasible s hs current k knownOk (by omega))))
    | succ rem ih =>
      intro k current enough sizeOk certOk knownOk
      obtain ⟨sizeNext, certNext, _, _⟩ := sweep_cert layout p feasible s current sizeOk certOk
      have knowNext := extends_window layout p feasible s current k sizeOk certOk knownOk
      exact Or.inr (ih (k + 1) (nextSweep g current) (by omega) sizeNext certNext knowNext)
  have h := stepBound (g.adj.size - 1) 0 b (by omega) sizes cert (within_zero s b cert)
  simpa only [show g.adj.size - 1 + 1 = g.adj.size by omega] using h

end Proofs.Cpp.FlowCostSearch
