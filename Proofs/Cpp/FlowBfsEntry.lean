import Proofs.Cpp.FlowBfsLoop

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowBfs

namespace Proofs.Cpp.FlowBfs

variable {Cost E : Type} [Inhabited E] [Zero Cost] [LT Cost] [DecidableLT Cost]
  [Field "cap" E Cost] [Field "to" E Int]

def arcCount (g : cp.FlowGraph Cost E) : Nat := (g.adj.toList.flatMap Array.toList).length

private theorem sublist_sum {l r : List Nat} (h : l.Sublist r) : l.sum ≤ r.sum := by
  induction h with
  | slnil => simp
  | cons x _ ih => simp only [List.sum_cons]; omega
  | cons_cons x _ ih => simp only [List.sum_cons]; omega

private theorem sum_weights (rows : List (Array E)) :
    (rows.map (fun row => 3 + 2 * row.toList.length)).sum = 3 * rows.length + 2 * (rows.flatMap Array.toList).length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.map_cons, List.sum_cons, List.length_cons, List.flatMap_cons, List.length_append]; omega

private theorem scanCost_full (g : cp.FlowGraph Cost E) :
    scanCost g (List.range g.adj.size) = 3 * g.adj.size + 2 * arcCount g := by
  have h := range_map_get g.adj
  rw [range_zero_size, List.map_map] at h
  calc
    scanCost g (List.range g.adj.size) =
        (g.adj.toList.map (fun row => 3 + 2 * row.toList.length)).sum := by
      rw [← h, List.map_map]
      rfl
    _ = 3 * g.adj.size + 2 * arcCount g := by
      rw [sum_weights, Array.length_toList]
      rfl

theorem scanCost_bound (g : cp.FlowGraph Cost E) (processed : List Nat) (nd : processed.Nodup)
    (inGraph : ∀ v ∈ processed, v < g.adj.size) : scanCost g processed ≤ 3 * g.adj.size + 2 * arcCount g := by
  obtain ⟨mid, hp, hs⟩ := List.subperm_of_subset nd (l₂ := List.range g.adj.size)
    (fun v hv => List.mem_range.mpr (inGraph v hv))
  rw [← scanCost_full]
  unfold scanCost
  have hm := sublist_sum (hs.map (readRowCost g))
  have he := (hp.map (readRowCost g)).sum_eq
  omega

private theorem initialView (n : Int) : levelsView (replicate n (-1)) = fun _ => none := by
  funext v
  unfold levelsView
  by_cases h : v < n.toNat
  · simp [replicate, getElem!_pos, h]
  · simp [replicate, h]

private theorem initialScan (g : cp.FlowGraph Cost E) (valid : Valid g) (s : Nat) (hs : s < g.adj.size) :
    ScanState g s s [] (set (replicate g.n_ (-1)) (s : Int) 0, []) 0 := by
  have hsize : (replicate g.n_ (-1) : Array Int).size = g.adj.size := by simp [replicate, valid.size]
  have hsource : s < (replicate g.n_ (-1) : Array Int).size := by rwa [hsize]
  refine ⟨by simpa only [size_set] using hsize, ?_, by simp, ?_⟩
  · intro v hv
    simp only [size_set] at hv
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, marked_value _ _ _ hsource]
    by_cases hv' : v = s
    · simp [hv']
    · have h : v < g.n_.toNat := by simpa [replicate] using hv
      simp [hv', replicate, getElem!_pos, h]
  · have view : levelsView (set (replicate g.n_ (-1)) (s : Int) 0) =
        mark (levelsView (replicate g.n_ (-1))) s 0 := view_mark _ _ _ hsource
    change Scan (residual g) s s [] [] (levelsView (set (replicate g.n_ (-1)) (s : Int) 0)) 0
    rw [view, initialView]
    exact scan_init (residual g) s

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem tickN_run (k t : Nat) : (tickN k).run t = some ((), t + k) := rfl
private theorem first_enqueue (s : Int) (t : Nat) : (queuePush [] s).run t = some ([s], t + 1) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

/-- The generated BFS visits exactly the residual-reachable vertices and establishes shortest levels in linear work. -/
theorem bfs_spec (g : cp.FlowGraph Cost E) (valid : Valid g) (u : Nat) (hu : u < g.adj.size)
    (fuel_bound : g.adj.size + 2 ≤ fuel) (t0 : Nat) :
    ∃ (lv : Array Int) (t' : Nat),
      (cp.FlowGraph.bfs g (u : Int)).run t0 = some ({ g with level := lv }, t') ∧ lv.size = g.adj.size ∧
      levelsView lv u = some 0 ∧
      (∀ v d, levelsView lv v = some d → ∀ w, residual g v w → lowerAtMost (levelsView lv) w (d + 1)) ∧
      (∀ v < g.adj.size,
        (get lv (v : Int) = -1 ↔ ¬ ∃ d, Walk (residual g) u v d) ∧
        ∀ d : Nat, get lv (v : Int) = (d : Int) →
          Walk (residual g) u v d ∧ ∀ k, Walk (residual g) u v k → d ≤ k) ∧
      t' ≤ t0 + 3 + 4 * g.adj.size + 2 * arcCount g ∧
      (∀ v < g.adj.size, -1 ≤ get lv (v : Int)) := by
  let b : BfsState := (set (replicate g.n_ (-1)) (u : Int) 0, [])
  have hs := initialScan g valid u hu
  have small : g.adj.size < UInt64.size := by
    change g.adj.size < fuel
    omega
  obtain ⟨lv, visited, t', hrun, result, bound⟩ := bfs_loop g valid small u fuel u 0 [] b (t0 + 1 + g.n_.toNat + 1)
    hs (by simpa using fuel_bound)
  have hc (v : Nat) (hv : Reached (levelsView lv) v) : v ∈ visited := (result.seen v).mp hv
  have hcost := scanCost_bound g visited result.unique (by
    intro v hv
    obtain ⟨j, hj⟩ := (result.seen v).mpr hv
    by_contra ht
    have hn : ¬v < lv.size := by rwa [result.size]
    simp [levelsView, hn] at hj)
  have hrun' : (forIn forever (b.1, [(u : Int)]) (vertexStep (Cost := Cost) g.adj)).run (t0 + 1 + g.n_.toNat + 1) =
      some ((lv, []), t') := hrun
  refine ⟨lv, t', ?_, result.size, result.root, ?_, ?_, ?_, ?_⟩
  · rw [bfs_program]
    unfold bfsProgram
    simp only [StateT.run_bind, tick_run, tickN_run, first_enqueue, some_bind]
    change ((forIn forever (b.1, [(u : Int)]) (vertexStep (Cost := Cost) g.adj)).run (t0 + 1 + g.n_.toNat + 1) >>= _) = _
    rw [hrun']
    rfl
  · intro v d hv w hw
    exact result.closed v (hc v ⟨d, hv⟩) d hv w hw
  · intro v hv
    have hv' : v < lv.size := by rwa [result.size]
    obtain ⟨good, missing⟩ := terminal_levels (v := v) result.root result.closed hc result.paths
    change (lv[v]! = -1 ↔ _) ∧ (∀ d : Nat, lv[v]! = (d : Int) → _)
    exact ⟨(view_none lv hv' (result.stored v hv')).symm.trans missing,
      fun d hd => good d ((view_some lv hv').mpr hd)⟩
  · have ncast : g.n_.toNat = g.adj.size := by simp [valid.size]
    unfold scanCost at bound hcost
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at bound
    rw [ncast] at bound
    omega
  · intro v hv
    exact result.stored v (by rwa [result.size])

theorem bfs_workspace {g : cp.FlowGraph Cost E} {u v d : Nat} {done : List Nat} {b : BfsState}
    (st : ScanState g u v done b d) : b.1.size + 1 + b.2.length ≤ 2 * g.adj.size := by
  have h := scan_width st
  rw [st.size]
  omega

end Proofs.Cpp.FlowBfs
