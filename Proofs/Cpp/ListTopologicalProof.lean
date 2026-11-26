import Proofs.Cpp.ListTopologicalProgram
import Mathlib.Data.List.Perm.Subperm

open Proofs.Cpp Proofs.Cpp.Gen Proofs.ListTopoMath

namespace Proofs.Cpp.ListTopological

variable {Cost E : Type} [Field "to" E Int]

abbrev ordered (s : TopologicalState) : List Nat := s.1.toList.map Int.toNat
abbrev ready (s : TopologicalState) : List Nat := s.2.2.map Int.toNat

structure Represents (mode : Discipline) (g : cp.ListGraph Cost E) (s : TopologicalState) : Prop where
  inv : KInv g.adj.size (outgoing g) s.2.1 (ordered s) (ready s)
  outputNonneg : ∀ x ∈ s.1.toList, 0 ≤ x
  queueNonneg : ∀ x ∈ s.2.2, 0 ≤ x
  greedy : mode = .minimum → GreedyPrefix g.adj.size (outgoing g) (ordered s)

private theorem budget_take (mode : Discipline) {len n : Nat} (positive : len ≠ 0) (maximum : len ≤ n) :
    mode.takeCost len ≤ mode.limit n + 1 := by
  cases mode with
  | stack => rfl
  | minimum =>
    change Nat.log2 len + 2 ≤ Nat.log2 (n + 1) + 1 + 1
    have hlog := (Nat.le_log2 (by omega : n + 1 ≠ 0)).mpr
      (Nat.le_trans (Nat.log2_self_le positive) (by omega))
    omega

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem pure_run {α : Type} (a : α) (t : Nat) : (pure a : M α).run t = some (a, t) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

/-- One iteration consumes a ready vertex, scans its original row once and inserts the newly ready targets. -/
theorem advance (mode : Discipline) (g : cp.ListGraph Cost E) (valid : ValidGraph g) (s : TopologicalState)
    (inv : Represents mode g s) (nonempty : s.2.2 ≠ []) (t : Nat) :
    ∃ (s' : TopologicalState) (v t' : Nat),
      (topoStep mode g.adj () s).run t = some (.yield s', t') ∧ Represents mode g s' ∧
      ordered s' = ordered s ++ [v] ∧ v < g.adj.size ∧
      t' + mode.limit g.adj.size * s.2.2.length ≤ t + (outgoing g v).length +
        2 * mode.limit g.adj.size + 3 + mode.limit g.adj.size * s'.2.2.length := by
  obtain ⟨x, rest, htake, hperm, hmin⟩ := take_run mode s.2.2 nonempty (t + 1)
  have hmem : x ∈ s.2.2 := hperm.mem_iff.mpr List.mem_cons_self
  have hx := inv.queueNonneg x hmem
  let v := x.toNat
  have hcast : (v : Int) = x := by omega
  have hv : v ∈ ready s := List.mem_map.mpr ⟨x, hmem, rfl⟩
  have hV := inv.inv.rlt v hv
  have htail : ∀ y ∈ rest, 0 ≤ y := by
    intro y hy
    exact inv.queueNonneg y (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hy))
  let row := (get g.adj x).toList
  have hr : row.map target = outgoing g v := by simp only [row, outgoing, hcast]
  have allTargets : ∀ e ∈ row, 0 ≤ target e := by
    intro e he
    apply (valid.edges v hV _ _).1
    rw [← hr]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  let initial := (s.2.1, rest)
  let after := row.foldl (fun s e => lower mode s (target e)) initial
  obtain ⟨t', hrun, hmono, haNN, hrowWork⟩ := row_process_run mode row initial
    (t + 1 + mode.takeCost s.2.2.length + 1) allTargets htail
  let s' := (s.1.push x, after.1, after.2)
  have hp : (ready s).Perm (v :: rest.map Int.toNat) := hperm.map Int.toNat
  have proj := row_process_project mode initial row
  rw [hr] at proj
  have hh := pick_step valid.edges mode.pushOrder (pushOrder_ok mode) inv.inv hp
  have hOrd : ordered s' = ordered s ++ [v] := by simp [s', ordered, v]
  have hi : KInv g.adj.size (outgoing g) s'.2.1 (ordered s') (ready s') := by
    rw [hOrd]
    change project after = _ at proj
    change let p := (outgoing g v).foldl (dstep mode.pushOrder) (project initial)
      KInv g.adj.size (outgoing g) p.1 (ordered s ++ [v]) p.2 at hh
    rw [← proj] at hh
    exact hh
  have hNN : ∀ y ∈ s'.1.toList, 0 ≤ y := by
    intro y hy
    have hy' : y ∈ s.1.toList ∨ y = x := by simpa [s'] using hy
    rcases hy' with hp | rfl
    · exact inv.outputNonneg y hp
    · exact hx
  have hGreedy (mn : mode = .minimum) : GreedyPrefix g.adj.size (outgoing g) (ordered s') := by
    rw [hOrd]
    apply greedy_extend (inv.greedy mn) inv.inv
    intro w hw
    obtain ⟨y, hmem, he⟩ := List.mem_map.mp hw
    have he' := hmin mn y hmem
    have hzero := inv.queueNonneg y hmem
    omega
  have hempty : s.2.2.isEmpty = false := by cases h : s.2.2 <;> simp_all
  have hlen : s.2.2.length = rest.length + 1 := hperm.length_eq
  have hsz := frontier_width hi
  have hszpre := frontier_width inv.inv
  have hready : after.2.length ≤ g.adj.size := by simp only [ready, List.length_map, s'] at hsz; omega
  have hreadypre : s.2.2.length ≤ g.adj.size := by simp only [ready, List.length_map] at hszpre; omega
  have hpos : s.2.2.length ≠ 0 := fun h => nonempty (List.length_eq_zero_iff.mp h)
  have hcost := budget_take mode hpos hreadypre
  have hrowsize : row.length = (outgoing g v).length := by rw [← hr, List.length_map]
  have hmono' : rest.length ≤ after.2.length := hmono
  have hlog : mode.limit after.2.length ≤ mode.limit g.adj.size := push_bound mode hready
  have hmul := Nat.mul_le_mul_right (after.2.length - rest.length) hlog
  have hcharged : mode.limit g.adj.size * s.2.2.length +
      mode.limit g.adj.size * (after.2.length - rest.length) =
        mode.limit g.adj.size * after.2.length + mode.limit g.adj.size := by
    have hpieces : s.2.2.length + (after.2.length - rest.length) = after.2.length + 1 := by omega
    rw [← Nat.mul_add, hpieces, Nat.mul_add, Nat.mul_one]
  have hb : t' ≤ t + 1 + mode.takeCost s.2.2.length + 1 + row.length +
       mode.limit after.2.length * (after.2.length - rest.length) := hrowWork
  refine ⟨s', v, t', ?_, ⟨hi, hNN, haNN, hGreedy⟩, hOrd, hV, ?_⟩
  · unfold topoStep
    dsimp only
    simp only [hempty, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, StateT.run_bind,
      tick_run, some_bind, htake, pure_run]
    rw [← Array.forIn_toList]
    change ((forIn row initial (decrementStep mode)).run (t + 1 + mode.takeCost s.2.2.length + 1) >>= _) = _
    rw [hrun]
    rfl
  · change _ ≤ t + (outgoing g v).length + 2 * mode.limit g.adj.size + 3 + mode.limit g.adj.size * after.2.length
    omega

end Proofs.Cpp.ListTopological

open Proofs.Cpp Proofs.Cpp.Gen Proofs.ListTopoMath

namespace Proofs.Cpp.ListTopological

variable {Cost E : Type} [Field "to" E Int]

def arcsUsed (g : cp.ListGraph Cost E) (processed : List Nat) : Nat :=
  (processed.map (fun v => (outgoing g v).length)).sum

def meter (mode : Discipline) (g : cp.ListGraph Cost E) (s : TopologicalState) : Nat :=
  (2 * mode.limit g.adj.size + 3) * (ordered s).length +
    mode.limit g.adj.size * s.2.2.length + arcsUsed g (ordered s)

private theorem sublist_sum {l r : List Nat} (h : l.Sublist r) : l.sum ≤ r.sum := by
  induction h with
  | slnil => simp
  | cons x _ ih => simp only [List.sum_cons]; omega
  | cons_cons x _ ih => simp only [List.sum_cons]; omega

private theorem arcsUsed_full (g : cp.ListGraph Cost E) : arcsUsed g (List.range g.adj.size) = arcCount g := by
  unfold arcsUsed arcCount outgoing
  simp only [List.length_map, ← List.length_flatMap]
  have h := range_map_get g.adj
  rw [range_zero_size, List.map_map] at h
  rw [← h, List.flatMap_map]
  rfl

theorem arcsUsed_bound (g : cp.ListGraph Cost E) (processed : List Nat) (nd : processed.Nodup)
    (sub : ∀ v ∈ processed, v < g.adj.size) : arcsUsed g processed ≤ arcCount g := by
  obtain ⟨common, perm, inside⟩ := List.subperm_of_subset nd (l₂ := List.range g.adj.size)
    (fun v hv => List.mem_range.mpr (sub v hv))
  rw [← arcsUsed_full]
  unfold arcsUsed
  have hs := sublist_sum (inside.map (fun v => (outgoing g v).length))
  have he := (perm.map (fun v => (outgoing g v).length)).sum_eq
  omega

private theorem empty_step (mode : Discipline) (g : cp.ListGraph Cost E) (s : TopologicalState)
    (h : s.2.2 = []) (t : Nat) : (topoStep mode g.adj () s).run t = some (.done s, t + 1) := by
  rcases s with ⟨output, counts, queue⟩
  change queue = [] at h
  subst queue
  rfl

/-- At most one vertex is processed per iteration, and each row is charged only when its vertex is processed. -/
theorem loop_done (mode : Discipline) (g : cp.ListGraph Cost E) (valid : ValidGraph g) (lim : Nat) :
    ∀ s t, Represents mode g s → g.adj.size + 1 ≤ lim + (ordered s).length →
      ∃ s' t', (loopFuel lim s (topoStep mode g.adj)).run t = some (s', t') ∧
        Represents mode g s' ∧ s'.2.2 = [] ∧ t' + meter mode g s ≤ t + meter mode g s' + 1 := by
  induction lim with
  | zero =>
    intro s t inv enough
    have := frontier_width inv.inv
    omega
  | succ rem ih =>
    intro s t inv enough
    by_cases empty : s.2.2 = []
    · have hs := empty_step mode g s empty t
      refine ⟨s, t + 1, ?_, inv, empty, by omega⟩
      rw [loopFuel, StateT.run_bind, hs]
      rfl
    · obtain ⟨mid, v, t1, hstep, hInv, hprocessed, hv, htime⟩ := advance mode g valid s inv empty t
      have hlen : (ordered mid).length = (ordered s).length + 1 := by simp [hprocessed]
      obtain ⟨r, t', hrun, hinv, hdone, hbound⟩ := ih mid t1 hInv (by omega)
      refine ⟨r, t', ?_, hinv, hdone, ?_⟩
      · rw [loopFuel, StateT.run_bind, hstep]
        exact hrun
      · have hwealth : t1 + meter mode g s ≤ t + meter mode g mid := by
          unfold meter arcsUsed
          rw [hlen, hprocessed, List.map_append, List.sum_append, Nat.mul_add, Nat.mul_one]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          omega
        omega

/-- A queue-free terminal state finished every vertex exactly when a complete order exists. -/
theorem terminal_correct (mode : Discipline) (g : cp.ListGraph Cost E) (s : TopologicalState)
    (inv : Represents mode g s) (empty : s.2.2 = []) :
    (s.1.size = g.adj.size → CompleteOrder g.adj.size (outgoing g) (ordered s)) ∧
    (s.1.size ≠ g.adj.size → ¬ ∃ xs, CompleteOrder g.adj.size (outgoing g) xs) := by
  have hs : (ordered s).length = s.1.size := by simp [ordered]
  have hi := inv.inv
  have he : ready s = [] := by simp [ready, empty]
  rw [he] at hi
  constructor
  · intro done
    have hperm : (ordered s).Perm (List.range g.adj.size) :=
      (List.subperm_of_subset hi.pnd (fun v hv => List.mem_range.mpr (hi.plt v hv))).perm_of_length_le (by simp [hs, done])
    exact ⟨hi.plt, hi.pnd, fun v hv => hperm.mem_iff.mpr (List.mem_range.mpr hv), hi.topo⟩
  · rintro notDone ⟨xs, hx⟩
    have hall := complete_if_order_exists hi hx
    have hle := List.nodup_range.length_le_of_subset (fun v hv => hall v (List.mem_range.mp hv))
    have hge := hi.pnd.length_le_of_subset (fun v hv => List.mem_range.mpr (hi.plt v hv))
    rw [hs, List.length_range] at hle hge
    exact notDone (Nat.le_antisymm hge hle)

end Proofs.Cpp.ListTopological

open Proofs.Cpp Proofs.Cpp.Gen Proofs.ListTopoMath

namespace Proofs.Cpp.ListTopological

variable {Cost E : Type} [Field "to" E Int]

private theorem tickN_run (m t : Nat) : (tickN m).run t = some ((), t + m) := rfl

structure TopologicalResult (mode : Discipline) (g : cp.ListGraph Cost E) (order : Array Int) : Prop where
  nonnegative : ∀ v ∈ order.toList, 0 ≤ v
  bound : order.size ≤ g.adj.size
  correct : if order.size = g.adj.size then
      CompleteOrder g.adj.size (outgoing g) (order.toList.map Int.toNat)
    else order.size = 0 ∧ ¬ ∃ other, CompleteOrder g.adj.size (outgoing g) other
  minimum : mode = .minimum → order.size = g.adj.size →
    GreedyPrefix g.adj.size (outgoing g) (order.toList.map Int.toNat)

theorem TopologicalResult.lexicographically_minimal {g : cp.ListGraph Cost E} {order : Array Int}
    (result : TopologicalResult .minimum g order) (complete : order.size = g.adj.size)
    (other : List Nat) (otherOrder : CompleteOrder g.adj.size (outgoing g) other) :
    let P := order.toList.map Int.toNat
    P ≠ other → ∃ j, ∃ hj : j < P.length, ∃ hq : j < other.length,
      P.take j = other.take j ∧ P[j] < other[j] := by
  intro P hne
  have hcorrect := result.correct
  rw [ite_eq_left complete] at hcorrect
  exact greedy_lex_first hcorrect otherOrder (result.minimum rfl complete) hne

def workBound (mode : Discipline) (g : cp.ListGraph Cost E) : Nat :=
  let n := g.adj.size
  let k := mode.limit n
  2 + 3 * n + 2 * arcCount g + (1 + k) * n + (2 * k + 3) * n

/-- The generated stack and heap versions share the correctness proof and charge their own queue costs. -/
theorem program_spec (mode : Discipline) (g : cp.ListGraph Cost E) (valid : ValidGraph g)
    (hfuel : g.adj.size < fuel) (t0 : Nat) :
    ∃ (order : Array Int) (t' : Nat), (sortProgram mode g).run t0 = some ((order, g), t') ∧
      TopologicalResult mode g order ∧ t' ≤ t0 + workBound mode g := by
  have ncast : g.n_.toNat = g.adj.size := by rw [valid.size]; simp
  obtain ⟨counts, queue, tc, tq, hcounts, hseed, inv, nonneg, hstartup⟩ :=
    initialise g valid mode (t0 + 1 + g.n_.toNat)
  let initial : TopologicalState := (([] : List Int).toArray, counts, queue)
  have hi : Represents mode g initial := ⟨inv, by simp [initial], nonneg, by
    intro _ j hj
    simp [initial, ordered] at hj⟩
  obtain ⟨terminal, te, hloop, hfinal, hdone, hcost⟩ := loop_done mode g valid fuel initial tq hi (by omega)
  have loop_run : (forIn forever initial (topoStep mode g.adj)).run tq = some (terminal, te) := hloop
  have hrun (finish : M (Array Int × cp.ListGraph Cost E))
      (hfinish : (if decide (size terminal.1 ≠ g.n_) then
        (pure (([] : List Int).toArray, g) : M (Array Int × cp.ListGraph Cost E))
        else (do tickN terminal.1.size; pure (terminal.1, g))) = finish) :
      (sortProgram mode g).run t0 = finish.run te := by
    unfold sortProgram
    simp only [StateT.run_bind, tick_run, tickN_run, some_bind, hcounts, hseed]
    change ((forIn forever initial (topoStep mode g.adj)).run tq >>= _) = _
    rw [loop_run, some_bind, hfinish]
  obtain ⟨hpass, hfail⟩ := terminal_correct mode g terminal hfinal hdone
  have hArc := arcsUsed_bound g (ordered terminal) hfinal.inv.pnd hfinal.inv.plt
  have hwidth := frontier_width hfinal.inv
  have hsize : (ordered terminal).length = terminal.1.size := by simp [ordered]
  rw [hsize] at hwidth
  have hN : terminal.1.size ≤ g.adj.size := by omega
  have hmul := Nat.mul_le_mul_left (2 * mode.limit g.adj.size + 3) hN
  have hbound : te + g.adj.size ≤ t0 + workBound mode g := by
    unfold meter at hcost
    rw [hsize, hdone, List.length_nil, Nat.mul_zero, Nat.add_zero] at hcost
    rw [ncast] at hstartup
    dsimp only [workBound]
    omega
  by_cases hfinished : terminal.1.size = g.adj.size
  · have hEq : size terminal.1 = g.n_ := by simp [size, hfinished, valid.size]
    have hexec := hrun (do tickN terminal.1.size; pure (terminal.1, g)) (by simp [hEq])
    refine ⟨terminal.1, te + terminal.1.size, hexec.trans (by rfl), ⟨hfinal.outputNonneg, hN, ?_, ?_⟩, by omega⟩
    · rw [ite_eq_left hfinished]
      exact hpass hfinished
    · intro hm _
      exact hfinal.greedy hm
  · have hn : size terminal.1 ≠ g.n_ := by simp [size, valid.size, hfinished]
    have hz : (0 : Nat) ≠ g.adj.size := by omega
    have hexec := hrun (pure (([] : List Int).toArray, g)) (by simp [hn])
    refine ⟨_, te, hexec.trans (by rfl), ⟨by simp, Nat.zero_le _, ?_, ?_⟩, by omega⟩
    · change (if (0 : Nat) = g.adj.size then _ else _)
      rw [ite_eq_right hz]
      exact ⟨rfl, hfail hfinished⟩
    · intro _ hh
      exact False.elim (hz hh)

theorem workspace {mode : Discipline} {g : cp.ListGraph Cost E} {s : TopologicalState}
    (inv : Represents mode g s) : s.1.size + s.2.1.size + s.2.2.length ≤ 2 * g.adj.size := by
  have h := frontier_width inv.inv
  have hsize := inv.inv.dsz
  simp only [ordered, ready, List.length_map, Array.length_toList] at h
  omega

end Proofs.Cpp.ListTopological
