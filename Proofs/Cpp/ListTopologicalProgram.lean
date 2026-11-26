import Proofs.Cpp.ListTopologicalInit

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ListTopological

variable {Cost E : Type} [Field "to" E Int]

abbrev DegreesQueue := Array Int × List Int
abbrev TopologicalState := Array Int × Array Int × List Int

def decrementStep (mode : Discipline) (edge : E) (state : DegreesQueue) : M (ForInStep DegreesQueue) := do
  tick
  let w := target edge
  let counts := set state.1 w (get state.1 w - 1)
  if decide (get counts w = 0) then
    let queued ← mode.push state.2 w
    return .yield (counts, queued)
  else
    return .yield (counts, state.2)

def topoStep (mode : Discipline) (adj : Array (Array E)) (_ : Unit) (state : TopologicalState) :
    M (ForInStep TopologicalState) := do
  tick
  if !(!(List.isEmpty state.2.2)) then
    return .done (state.1, state.2.1, state.2.2)
  else
    let picked ← mode.take state.2.2
    let v := picked.1
    let queue := picked.2
    tick
    let ready ← forIn (get adj v) (state.2.1, queue) (decrementStep mode)
    return .yield (state.1.push v, ready.1, ready.2)

def sortProgram (mode : Discipline) (g : cp.ListGraph Cost E) : M (Array Int × cp.ListGraph Cost E) := do
  tick
  tickN g.n_.toNat
  let counts ← forIn g.adj (replicate g.n_ 0) countRow
  let ready ← forIn (range 0 g.n_) ([] : List Int) (seedStep mode counts)
  let out ← forIn forever (([] : List Int).toArray, counts, ready) (topoStep mode g.adj)
  if decide (size out.1 ≠ g.n_) then
    return (([] : List Int).toArray, g)
  else
    tickN out.1.size
    return (out.1, g)

theorem topological_stack_program [Inhabited E] (g : cp.ListGraph Cost E) :
    cp.ListGraph.topological_sort g = sortProgram .stack g := by
  rw [cp.ListGraph.topological_sort]
  unfold sortProgram countRow inc seedStep topoStep Discipline.take Discipline.push decrementStep target
  dsimp only
  simp only [bind_assoc, pure_bind]
  rfl

theorem topological_minimum_program [Inhabited E] (g : cp.ListGraph Cost E) :
    cp.ListGraph.topological_sort_minimum g = sortProgram .minimum g := by
  rw [cp.ListGraph.topological_sort_minimum]
  unfold sortProgram countRow inc seedStep topoStep Discipline.take Discipline.push decrementStep target greater
  dsimp only
  simp only [bind_assoc, pure_bind]
  rfl

end Proofs.Cpp.ListTopological

open Proofs.Cpp Proofs.ListTopoMath

namespace Proofs.Cpp.ListTopological

variable {E : Type} [Field "to" E Int]

def enqueue (mode : Discipline) (queue : List Int) (v : Int) : List Int :=
  match mode with
  | .stack => v :: queue
  | .minimum => queue ++ [v]

def lower (mode : Discipline) (s : DegreesQueue) (v : Int) : DegreesQueue :=
  let d := set s.1 v (get s.1 v - 1)
  (d, if get d v = 0 then enqueue mode s.2 v else s.2)

def project (s : DegreesQueue) : Array Int × List Nat := (s.1, s.2.map Int.toNat)

theorem lower_project (mode : Discipline) (s : DegreesQueue) (v : Int) :
    project (lower mode s v) = dstep mode.pushOrder (project s) v := by
  unfold lower project dstep
  dsimp only
  split
  · cases mode <;> simp [enqueue, Discipline.pushOrder]
  · rfl

theorem row_process_project (mode : Discipline) (s : DegreesQueue) (edges : List E) :
    project (edges.foldl (fun s e => lower mode s (target e)) s) =
      (edges.map target).foldl (dstep mode.pushOrder) (project s) := by
  induction edges generalizing s with
  | nil => rfl
  | cons edge edges ih =>
    simp only [List.map_cons, List.foldl_cons, ih, lower_project]

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem pure_run {α : Type} (a : α) (t : Nat) : (pure a : M α).run t = some (a, t) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

/-- During a row update the queue only grows. Charge heap operations to the actual number of new
ready vertices, and charge each scanned edge once. -/
theorem row_process_run (mode : Discipline) (edges : List E) (s : DegreesQueue) (t : Nat)
    (nonneg : ∀ e ∈ edges, 0 ≤ target e) (queueNonneg : ∀ v ∈ s.2, 0 ≤ v) :
    let result := edges.foldl (fun s e => lower mode s (target e)) s
    ∃ t', (forIn edges s (decrementStep mode)).run t = some (result, t') ∧
      s.2.length ≤ result.2.length ∧ (∀ v ∈ result.2, 0 ≤ v) ∧
      t' ≤ t + edges.length + mode.limit result.2.length * (result.2.length - s.2.length) := by
  induction edges generalizing s t with
  | nil => exact ⟨t, rfl, Nat.le_refl _, queueNonneg, by simp⟩
  | cons edge edges ih =>
    dsimp only [List.foldl_cons]
    let w := target edge
    let counts := set s.1 w (get s.1 w - 1)
    let next := lower mode s w
    let result := edges.foldl (fun s e => lower mode s (target e)) next
    have hw : 0 ≤ w := nonneg edge (by simp)
    have htail : ∀ e ∈ edges, 0 ≤ target e := fun e he => nonneg e (List.mem_cons_of_mem _ he)
    have hstep : (decrementStep mode edge s).run t =
        some (.yield next, t + 1 + if get counts w = 0 then mode.pushCost s.2.length else 0) := by
      unfold decrementStep
      change ((do
        tick
        if decide (get counts w = 0) then
          let queue ← mode.push s.2 w
          pure (.yield (counts, queue))
        else pure (.yield (counts, s.2))) : M (ForInStep DegreesQueue)).run t = _
      unfold next lower
      change _ = some (ForInStep.yield (counts, if get counts w = 0 then enqueue mode s.2 w else s.2), _)
      by_cases hzero : get counts w = 0
      · obtain ⟨hp, _, _⟩ := push_run mode s.2 w (t + 1)
        simp only [hzero, decide_true, ite_true, StateT.run_bind, tick_run, some_bind, pure_run, hp]
        rfl
      · simp only [hzero, decide_false, Bool.false_eq_true, ite_false]
        rfl
    rw [List.forIn_cons, StateT.run_bind, hstep]
    by_cases hzero : get counts w = 0
    · have hn : next.2 = enqueue mode s.2 w := by
        change (if get counts w = 0 then enqueue mode s.2 w else s.2) = _
        exact ite_eq_left hzero
      have hlen : next.2.length = s.2.length + 1 := by rw [hn]; cases mode <;> simp [enqueue]
      have hnn : ∀ v ∈ next.2, 0 ≤ v := by
        rw [hn]
        intro v hv
        cases mode with
        | stack =>
          rw [enqueue, List.mem_cons] at hv
          rcases hv with rfl | h
          · exact hw
          · exact queueNonneg v h
        | minimum =>
          rw [enqueue, List.mem_append, List.mem_singleton] at hv
          rcases hv with h | rfl
          · exact queueNonneg v h
          · exact hw
      obtain ⟨t', hrun, hmono, hn', hb⟩ := ih next (t + 1 + mode.pushCost s.2.length) htail hnn
      have hm : next.2.length ≤ result.2.length := hmono
      have hlim := push_bound mode (len := s.2.length) (n := result.2.length) (by omega)
      have heq : result.2.length - s.2.length = (result.2.length - next.2.length) + 1 := by omega
      have hb' : t' ≤ t + 1 + mode.pushCost s.2.length + edges.length +
          mode.limit result.2.length * (result.2.length - next.2.length) := hb
      refine ⟨t', ?_, by change s.2.length ≤ result.2.length; omega, hn', ?_⟩
      · simpa only [hzero, ite_true, some_bind] using hrun
      · change t' ≤ t + (edge :: edges).length + mode.limit result.2.length * (result.2.length - s.2.length)
        rw [heq, List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
    · have hn : next.2 = s.2 := by
        change (if get counts w = 0 then enqueue mode s.2 w else s.2) = _
        exact ite_eq_right hzero
      obtain ⟨t', hrun, hmono, hn', hb⟩ := ih next (t + 1) htail (by rwa [hn])
      refine ⟨t', ?_, by simpa only [hn] using hmono, hn', ?_⟩
      · simpa only [hzero, ite_false, Nat.add_zero, some_bind] using hrun
      · have hb' : t' ≤ t + 1 + edges.length + mode.limit result.2.length * (result.2.length - next.2.length) := hb
        rw [hn] at hb'
        change t' ≤ t + (edge :: edges).length + mode.limit result.2.length * (result.2.length - s.2.length)
        simp only [List.length_cons]
        omega

end Proofs.Cpp.ListTopological
