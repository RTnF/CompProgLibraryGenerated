import Proofs.Cpp.FlowBfsRows
import Mathlib.Data.List.Perm.Subperm

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowBfs

namespace Proofs.Cpp.FlowBfs

variable {Cost E : Type} [Inhabited E] [Zero Cost] [LT Cost] [DecidableLT Cost]
  [Field "cap" E Cost] [Field "to" E Int]

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem pure_run {α : Type} (a : α) (t : Nat) : (pure a : M α).run t = some (a, t) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

private theorem word_nonempty (q : List Int) (h : q ≠ []) (small : q.length < UInt64.size) :
    UInt64.ofNat q.length ≠ 0 := by
  intro e
  have hz := congrArg UInt64.toNat e
  have he : (UInt64.ofNat q.length).toNat = q.length := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
  rw [he] at hz
  exact h (List.length_eq_zero_iff.mp hz)

def readRowCost (g : cp.FlowGraph Cost E) (v : Nat) : Nat := 3 + 2 * (edgesAt g v).length

def scanCost (g : cp.FlowGraph Cost E) (processed : List Nat) : Nat :=
  (processed.map (readRowCost g)).sum

private theorem scanCost_next (g : cp.FlowGraph Cost E) (done : List Nat) (u : Nat) :
    scanCost g (done ++ [u]) = scanCost g done + readRowCost g u := by simp [scanCost]

theorem vertex_step (g : cp.FlowGraph Cost E) (valid : Valid g) (small : g.adj.size < UInt64.size)
    (source u d : Nat) (done : List Nat) (b : BfsState) (st : ScanState g source u done b d) (t : Nat) :
    ∃ (out : BfsState) (t' : Nat),
      (vertexStep (Cost := Cost) g.adj () (b.1, (u : Int) :: b.2)).run t = some (.yield out, t') ∧
      ScanState g source u done out d ∧
      (∀ v, residual g u v → lowerAtMost (levelsView out.1) v (d + 1)) ∧
      t' ≤ t + readRowCost g u := by
  have hw := scan_width st
  have hq : ((u : Int) :: b.2).length < UInt64.size := by simp only [List.length_cons]; omega
  have hn := word_nonempty ((u : Int) :: b.2) (by simp) hq
  obtain ⟨out, t', hs, hout, _, bounds, bound⟩ := scan_row g valid source u d done (edgesAt g u)
    (fun _ h => h) b (t + 3) st
  refine ⟨out, t', ?_, hout, ?_, ?_⟩
  · unfold vertexStep
    dsimp only
    have hcond : ¬ (!decide (UInt64.ofNat (((u : Int) :: b.2).length) ≠ 0)) = true := by
      rw [decide_eq_true hn]
      decide
    rw [ite_eq_right hcond]
    have hfront (k : Nat) : (queueFront ((u : Int) :: b.2)).run k = some ((u : Int), k + 1) := rfl
    have hpop (k : Nat) : (queuePop ((u : Int) :: b.2)).run k = some (b.2, k + 1) := rfl
    simp only [StateT.run_bind, tick_run, some_bind, hfront, hpop]
    rw [← Array.forIn_toList]
    change ((forIn (edgesAt g u) b (edgeStep (Cost := Cost) (u : Int))).run (t + 3) >>= _) = _
    rw [hs]
    rfl
  · intro v hv
    obtain ⟨_, e, he, hp, hd⟩ := hv
    exact (by simpa only [hd, Int.toNat_natCast] using bounds e he hp)
  · unfold readRowCost
    omega

structure Finished (g : cp.FlowGraph Cost E) (source : Nat) (levels : Array Int) (done : List Nat) : Prop where
  size : levels.size = g.adj.size
  stored : ∀ v < levels.size, -1 ≤ levels[v]!
  root : levelsView levels source = some 0
  closed : Closed (residual g) (levelsView levels) done
  paths : HasWalks (residual g) source (levelsView levels)
  seen : ∀ v, Reached (levelsView levels) v ↔ v ∈ done
  unique : done.Nodup

private theorem vertex_empty (g : cp.FlowGraph Cost E) (lv : Array Int) (t : Nat) :
    (vertexStep (Cost := Cost) g.adj () (lv, [])).run t = some (.done (lv, []), t + 1) := rfl

/-- At most one row per distinct discovered vertex is consumed; the final empty-queue test costs one tick. -/
theorem bfs_loop (g : cp.FlowGraph Cost E) (valid : Valid g) (small : g.adj.size < UInt64.size)
    (s lim : Nat) : ∀ (u d : Nat) (done : List Nat) (b : BfsState) (t : Nat),
      ScanState g s u done b d → g.adj.size + 2 ≤ lim + done.length →
      ∃ (lv : Array Int) (visited : List Nat) (t' : Nat),
        (loopFuel lim (b.1, (u : Int) :: b.2) (vertexStep (Cost := Cost) g.adj)).run t = some ((lv, []), t') ∧
        Finished g s lv visited ∧ t' + scanCost g done ≤ t + scanCost g visited + 1 := by
  induction lim with
  | zero =>
    intro u d done b t st h
    have := scan_width st
    omega
  | succ remaining ih =>
    intro u d done b t st h
    obtain ⟨out, tm, hr, mid, closure, work⟩ := vertex_step g valid small s u d done b st t
    have org := scan_width st
    have hrem : 0 < remaining := by omega
    cases hq : out.2 with
    | nil =>
      have bridge : Scan (residual g) s u done [] (levelsView out.1) d := by
        simpa only [hq, List.map_nil] using mid.scan
      obtain ⟨cl, _⟩ := bridge.finish_all closure
      have hfin : Finished g s out.1 (done ++ [u]) := by
        refine ⟨mid.size, mid.stored, bridge.root, cl, bridge.paths, bridge.seen, bridge.unique⟩
      refine ⟨out.1, done ++ [u], tm + 1, ?_, hfin, ?_⟩
      · rw [loopFuel, StateT.run_bind, hr]
        change (loopFuel remaining out (vertexStep (Cost := Cost) g.adj)).run tm = _
        have hPair : out = (out.1, []) := by rw [← hq]
        rw [hPair]
        obtain ⟨rem, rfl⟩ : ∃ r, remaining = r + 1 := ⟨remaining - 1, by omega⟩
        rw [loopFuel, StateT.run_bind, vertex_empty]
        rfl
      · rw [scanCost_next]
        omega
    | cons next tail =>
      have bridge : Scan (residual g) s u done (next.toNat :: tail.map Int.toNat) (levelsView out.1) d := by
        simpa only [hq, List.map_cons] using mid.scan
      obtain ⟨k, _, _, nextState⟩ := bridge.activate_next closure
      have htail : ∀ x ∈ tail, 0 ≤ x := by
        intro x hx
        apply mid.queueNonnegative x
        rw [hq]
        exact List.mem_cons_of_mem _ hx
      have hNext : 0 ≤ next := by
        apply mid.queueNonnegative next
        rw [hq]
        exact List.mem_cons_self
      have hCast : (next.toNat : Int) = next := by omega
      let appear : BfsState := (out.1, tail)
      have state : ScanState g s next.toNat (done ++ [u]) appear k :=
        ⟨mid.size, mid.stored, htail, nextState⟩
      have potential : g.adj.size + 2 ≤ remaining + (done ++ [u]).length := by simp; omega
      obtain ⟨lv, visited, t', hrun, hf, hwork⟩ := ih next.toNat k (done ++ [u]) appear tm state potential
      refine ⟨lv, visited, t', ?_, hf, ?_⟩
      · rw [loopFuel, StateT.run_bind, hr]
        change (loopFuel remaining out (vertexStep (Cost := Cost) g.adj)).run tm = _
        have hp : out = (out.1, next :: tail) := by rw [← hq]
        rw [hp]
        simpa only [appear, hCast] using hrun
      · rw [scanCost_next] at hwork
        omega

end Proofs.Cpp.FlowBfs
