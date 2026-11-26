import Proofs.Cpp.Gen.GraphList
import Proofs.Cpp.ListTopologicalQueue

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ListTopological

variable {E : Type} [Field "to" E Int]

def target (e : E) : Int := Field.get (member := "to") e

def inc (counts : Array Int) (e : E) : Array Int :=
  set counts (target e) (get counts (target e) + 1)

def countRow (row : Array E) (counts : Array Int) : M (ForInStep (Array Int)) := do
  tick
  let counts ← forIn row counts fun e s => do
    tick
    return .yield (inc s e)
  return .yield counts

private theorem count_cons (edge : E) (edges : List E) (v : Int) :
    ((edge :: edges).map target).count v = (edges.map target).count v + if v = target edge then 1 else 0 := by
  by_cases h : v = target edge
  · simp [h]
  · have h' : target edge ≠ v := Ne.symm h
    simp [h, h']

theorem inc_size (counts : Array Int) (edge : E) : (inc counts edge).size = counts.size := size_set ..

theorem inc_value (counts : Array Int) (edge : E) (v : Nat) (hlo : 0 ≤ target edge)
    (hhi : target edge < (counts.size : Int)) :
    (get (inc counts edge) (v : Int) : Int) = get counts (v : Int) + if (v : Int) = target edge then 1 else 0 := by
  have ht := (show (target edge).toNat < counts.size by omega)
  have hc := getElemBang_set counts (target edge) (get counts (target edge) + 1) v ht
  change (inc counts edge)[v]! = counts[v]! + if (v : Int) = target edge then 1 else 0
  unfold inc
  rw [hc]
  by_cases hv : v = (target edge).toNat
  · simp [hv, get_eq, hlo]
  · have he : (v : Int) ≠ target edge := by omega
    simp [hv, he]

/-- One row contributes exactly one count per edge, including repeated targets. -/
theorem count_edges (edges : List E) (counts : Array Int) (clock : Nat)
    (valid : ∀ e ∈ edges, 0 ≤ target e ∧ target e < (counts.size : Int)) :
    let final := edges.foldl inc counts
    (forIn edges counts (fun e s => do tick; return .yield (inc s e))).run clock =
      some (final, clock + edges.length) ∧ final.size = counts.size ∧
      ∀ v : Nat, get final (v : Int) = get counts (v : Int) + ((edges.map target).count (v : Int) : Nat) := by
  induction edges generalizing counts clock with
  | nil => exact ⟨rfl, rfl, by simp⟩
  | cons edge edges ih =>
    dsimp only [List.foldl_cons]
    obtain ⟨hlo, hhi⟩ := valid edge (by simp)
    have hvalid : ∀ e ∈ edges, 0 ≤ target e ∧ target e < ((inc counts edge).size : Int) := by
      intro e he
      rw [inc_size]
      exact valid e (List.mem_cons_of_mem _ he)
    obtain ⟨hr, hs, hv⟩ := ih (inc counts edge) (clock + 1) hvalid
    refine ⟨?_, hs.trans (inc_size counts edge), ?_⟩
    · rw [List.forIn_cons]
      change (forIn edges (inc counts edge) (fun e s => do tick; return .yield (inc s e))).run (clock + 1) = _
      have hclock : clock + 1 + edges.length = clock + (edge :: edges).length := by simp; omega
      simpa only [hclock] using hr
    · intro v
      rw [hv, inc_value counts edge v hlo hhi, count_cons]
      split <;> (simp; try omega)

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem pure_run {α : Type} (a : α) (t : Nat) : (pure a : M α).run t = some (a, t) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

/-- The initial pass through the graph counts each incoming arc and performs one tick per row and arc. -/
theorem count_rows (rows : List (Array E)) (counts : Array Int) (clock : Nat)
    (valid : ∀ row ∈ rows, ∀ e ∈ row.toList, 0 ≤ target e ∧ target e < (counts.size : Int)) :
    let edges := rows.flatMap Array.toList
    let final := edges.foldl inc counts
    (forIn rows counts countRow).run clock = some (final, clock + rows.length + edges.length) ∧
    final.size = counts.size ∧
    ∀ v : Nat, get final (v : Int) = get counts (v : Int) + ((edges.map target).count (v : Int) : Nat) := by
  induction rows generalizing counts clock with
  | nil => exact ⟨rfl, rfl, by simp⟩
  | cons row rows ih =>
    simp only [List.flatMap_cons, List.foldl_append]
    let partialCounts := row.toList.foldl inc counts
    obtain ⟨hrow, hsize, hval⟩ := count_edges row.toList counts (clock + 1) (valid row (by simp))
    have hvalid : ∀ rs ∈ rows, ∀ e ∈ rs.toList, 0 ≤ target e ∧ target e < (partialCounts.size : Int) := by
      intro rs hrs e he
      rw [show partialCounts.size = counts.size from hsize]
      exact valid rs (List.mem_cons_of_mem _ hrs) e he
    obtain ⟨hr, hs, hv⟩ := ih partialCounts (clock + 1 + row.toList.length) hvalid
    refine ⟨?_, hs.trans hsize, ?_⟩
    · have row_run : (countRow row counts).run clock = some (.yield partialCounts, clock + 1 + row.toList.length) := by
        unfold countRow
        rw [← Array.forIn_toList]
        simp only [StateT.run_bind, tick_run, pure_run, some_bind, hrow, partialCounts]
      rw [List.forIn_cons, StateT.run_bind, row_run]
      change (forIn rows partialCounts countRow).run (clock + 1 + row.toList.length) = _
      rw [hr]
      simp only [List.length_append, List.length_cons]
      congr 2
      omega
    · intro v
      rw [hv, hval, List.map_append, List.count_append]
      omega

end Proofs.Cpp.ListTopological

open Proofs.Cpp Proofs.Cpp.Gen Proofs.ListTopoMath

namespace Proofs.Cpp.ListTopological

variable {Cost E : Type} [Field "to" E Int]

def outgoing (g : cp.ListGraph Cost E) (v : Nat) : List Int :=
  ((get g.adj (v : Int)).toList).map target

def arcCount (g : cp.ListGraph Cost E) : Nat :=
  (g.adj.toList.flatMap Array.toList).length

structure ValidGraph (g : cp.ListGraph Cost E) : Prop where
  size : g.n_ = (g.adj.size : Int)
  edges : ValidT g.adj.size (outgoing g)

private theorem targets_flattened (g : cp.ListGraph Cost E) :
    (g.adj.toList.flatMap Array.toList).map target = (List.range g.adj.size).flatMap (outgoing g) := by
  rw [List.map_flatMap]
  have hr := range_map_get g.adj
  rw [range_zero_size, List.map_map] at hr
  rw [← hr, List.flatMap_map]
  rfl

/-- Reading each edge and seeding the frontier gives exactly the initial invariant of Kahn's algorithm. -/
theorem initialise (g : cp.ListGraph Cost E) (valid : ValidGraph g) (mode : Discipline) (t : Nat) :
    ∃ (counts : Array Int) (queue : List Int) (tc tq : Nat),
      (forIn g.adj (replicate g.n_ 0) countRow).run t = some (counts, tc) ∧
      (forIn (range 0 g.n_) ([] : List Int) (seedStep mode counts)).run tc = some (queue, tq) ∧
      KInv g.adj.size (outgoing g) counts [] (queue.map Int.toNat) ∧
      (∀ x ∈ queue, 0 ≤ x) ∧
      tq ≤ t + g.adj.size + arcCount g + (1 + mode.limit g.adj.size) * g.adj.size := by
  let start := (replicate g.n_ 0 : Array Int)
  have hn : start.size = g.adj.size := by simp [start, replicate, valid.size]
  have htarget : ∀ row ∈ g.adj.toList, ∀ e ∈ row.toList,
      0 ≤ target e ∧ target e < (start.size : Int) := by
    intro row hrow edge hedge
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hrow
    have hi' : i < g.adj.size := by simpa using hi
    have hget : get g.adj (i : Int) = row := by simpa [get_eq, getElem!_pos, hi'] using he
    rw [hn]
    exact valid.edges i hi' (target edge) (by simp [outgoing, hget, List.mem_map.mpr ⟨edge, hedge, rfl⟩])
  obtain ⟨hc, hs, hv⟩ := count_rows g.adj.toList start t htarget
  let counts := (g.adj.toList.flatMap Array.toList).foldl inc start
  let tc := t + g.adj.size + arcCount g
  have hclock : t + g.adj.toList.length + (g.adj.toList.flatMap Array.toList).length = tc := by simp [tc, arcCount]
  have hrun : (forIn g.adj (replicate g.n_ 0) countRow).run t = some (counts, tc) := by
    rw [← Array.forIn_toList, ← hclock]
    exact hc
  have hstarts (w : Nat) (hw : w < g.adj.size) : get start (w : Int) = 0 := by
    simp [start, replicate, valid.size, get_eq, getElem!_pos, hw]
  have hcount (w : Nat) (hw : w < g.adj.size) :
      counts[w]! = (((List.range g.adj.size).flatMap (outgoing g)).count (w : Int) : Int) := by
    rw [← show get counts (w : Int) = counts[w]! from rfl, show get counts (w : Int) = _ from hv w,
      hstarts w hw, targets_flattened]
    simp
  have hrange : range 0 g.n_ = (List.range g.adj.size).map Int.ofNat := by
    change range 0 g.n_ = (List.range g.adj.size).map (fun k : Nat => (k : Int))
    simpa only [size, ← valid.size] using range_zero_size g.adj
  obtain ⟨queue, tq, hseed, hq⟩ := seed_loop mode g.adj.size counts (List.range g.adj.size)
    List.nodup_range [] tc (by simp) (by simp) (by simp) (by simp)
  have hi := kinv_init counts (hs.trans hn) hcount (queue.map Int.toNat) hq.nodup (by
    intro v
    rw [hq.membership]
    simp [get_eq])
  refine ⟨counts, queue, tc, tq, hrun, ?_, hi, hq.nonneg, ?_⟩
  · rw [hrange]
    exact hseed
  · have hw := hq.work
    simpa [tc] using hw

end Proofs.Cpp.ListTopological
