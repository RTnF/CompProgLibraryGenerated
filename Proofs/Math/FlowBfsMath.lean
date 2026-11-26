import Proofs.Cpp.Lib.Basic

namespace Proofs.FlowBfs

/-- Walks in the positive-capacity residual graph carry their edge count. -/
inductive Walk (edge : Nat → Nat → Prop) (source : Nat) : Nat → Nat → Prop where
  | start : Walk edge source source 0
  | step {u v k : Nat} : Walk edge source u k → edge u v → Walk edge source v (k + 1)

abbrev Level := Nat → Option Nat

def Reached (level : Level) (v : Nat) : Prop := ∃ d, level v = some d

def lowerAtMost (level : Level) (v d : Nat) : Prop := ∃ k, level v = some k ∧ k ≤ d

def Closed (edge : Nat → Nat → Prop) (level : Level) (done : List Nat) : Prop :=
  ∀ u ∈ done, ∀ d, level u = some d → ∀ v, edge u v → lowerAtMost level v (d + 1)

def HasWalks (edge : Nat → Nat → Prop) (source : Nat) (level : Level) : Prop :=
  ∀ v d, level v = some d → Walk edge source v d

/-- Once every discovered vertex has been processed, every residual walk provides an upper bound on level. -/
theorem level_le_walk {edge : Nat → Nat → Prop} {s v d : Nat} {level : Level} {done : List Nat}
    (start : level s = some 0) (closed : Closed edge level done)
    (complete : ∀ u, Reached level u → u ∈ done) (walk : Walk edge s v d) : lowerAtMost level v d := by
  induction walk with
  | start => exact ⟨0, start, Nat.le_refl _⟩
  | @step u v d hwalk arc ih =>
    obtain ⟨j, hj, hjd⟩ := ih
    obtain ⟨k, hk, hbound⟩ := closed u (complete u ⟨j, hj⟩) j hj v arc
    exact ⟨k, hk, by omega⟩

/-- A finished vertex level is exactly the shortest residual distance. An unmarked vertex is unreachable. -/
theorem terminal_levels {edge : Nat → Nat → Prop} {s v : Nat} {level : Level} {done : List Nat}
    (start : level s = some 0) (closed : Closed edge level done)
    (complete : ∀ u, Reached level u → u ∈ done) (paths : HasWalks edge s level) :
    (∀ d, level v = some d → Walk edge s v d ∧ ∀ k, Walk edge s v k → d ≤ k) ∧
    (level v = none ↔ ¬ ∃ d, Walk edge s v d) := by
  constructor
  · intro d hd
    refine ⟨paths v d hd, ?_⟩
    intro k hk
    obtain ⟨j, hj, hjk⟩ := level_le_walk start closed complete hk
    rw [hd] at hj
    cases hj
    exact hjk
  · constructor
    · rintro hv ⟨d, hd⟩
      obtain ⟨j, hj, _⟩ := level_le_walk start closed complete hd
      rw [hv] at hj
      contradiction
    · intro hnone
      cases h : level v with
      | none => rfl
      | some d => exact False.elim (hnone ⟨d, paths v d h⟩)

def mark (level : Level) (v d : Nat) : Level :=
  fun u => if u = v then some d else level u

/-- A newly discovered vertex inherits an actual walk through the active row. -/
theorem mark_walks {edge : Nat → Nat → Prop} {s u v d : Nat} {level : Level}
    (old : HasWalks edge s level) (hu : level u = some d) (arc : edge u v) :
    HasWalks edge s (mark level v (d + 1)) := by
  intro w k h
  by_cases hEq : w = v
  · subst w
    simp [mark] at h
    subst k
    exact .step (old u d hu) arc
  · simp [mark, hEq] at h
    exact old w k h

/-- Updating a fresh vertex leaves the obligations of earlier rows intact. -/
theorem mark_closed {edge : Nat → Nat → Prop} {done : List Nat} {level : Level} {v d : Nat}
    (old : Closed edge level done) (fresh : level v = none) (notDone : v ∉ done) :
    Closed edge (mark level v d) done := by
  intro u hu du hdu w edge_uw
  have huv : u ≠ v := fun eq => notDone (eq ▸ hu)
  have hu' : level u = some du := by simpa [mark, huv] using hdu
  obtain ⟨dw, hdw, hbound⟩ := old u hu du hu' w edge_uw
  have hwv : w ≠ v := by
    intro eq
    subst w
    rw [fresh] at hdw
    contradiction
  exact ⟨dw, by simp [mark, hwv, hdw], hbound⟩

/-- With a row active at level `d`, the FIFO only contains levels `d` and `d + 1`. -/
structure Scan (edge : Nat → Nat → Prop) (source active : Nat) (done queue : List Nat)
    (level : Level) (d : Nat) : Prop where
  root : level source = some 0
  here : level active = some d
  seen : ∀ v, Reached level v ↔ v ∈ done ++ active :: queue
  unique : (done ++ active :: queue).Nodup
  paths : HasWalks edge source level
  closed : Closed edge level done
  earlier : ∀ v ∈ done, lowerAtMost level v d
  pending : ∀ v ∈ queue, ∃ k, level v = some k ∧ d ≤ k ∧ k ≤ d + 1
  order : queue.Pairwise (fun u v => (level u).getD 0 ≤ (level v).getD 0)

theorem Scan.level_known {edge : Nat → Nat → Prop} {s u d v : Nat} {done queue : List Nat} {level : Level}
    (state : Scan edge s u done queue level d) (known : Reached level v) : lowerAtMost level v (d + 1) := by
  obtain hv | hq := List.mem_append.mp ((state.seen v).mp known)
  · obtain ⟨k, hk, hle⟩ := state.earlier v hv
    exact ⟨k, hk, by omega⟩
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨d, state.here, by omega⟩
    · obtain ⟨k, hk, _, hle⟩ := state.pending v hq
      exact ⟨k, hk, hle⟩

/-- Discovering a fresh neighbour puts it last in the FIFO and preserves all earlier levels. -/
theorem Scan.discover {edge : Nat → Nat → Prop} {s u d v : Nat} {done queue : List Nat} {level : Level}
    (state : Scan edge s u done queue level d) (arc : edge u v) (fresh : level v = none) :
    Scan edge s u done (queue ++ [v]) (mark level v (d + 1)) d := by
  have notReached : ¬ Reached level v := by simp [Reached, fresh]
  have notSeen : v ∉ done ++ u :: queue := fun hm => notReached ((state.seen v).mpr hm)
  have notDone : v ∉ done := fun h => notSeen (List.mem_append.mpr (Or.inl h))
  have hsame (a : Nat) (ha : Reached level a) : mark level v (d + 1) a = level a := by
    have hneq : a ≠ v := fun e => notReached (e ▸ ha)
    simp [mark, hneq]
  have hs := hsame s ⟨_, state.root⟩
  have hu := hsame u ⟨_, state.here⟩
  have hv : mark level v (d + 1) v = some (d + 1) := by simp [mark]
  have hshape : done ++ u :: (queue ++ [v]) = (done ++ u :: queue) ++ [v] := by simp
  refine ⟨hs.trans state.root, hu.trans state.here, ?_, ?_, mark_walks state.paths state.here arc,
    mark_closed state.closed fresh notDone, ?_, ?_, ?_⟩
  · intro a
    rw [hshape, List.mem_append, List.mem_singleton]
    by_cases he : a = v
    · subst a; simp [Reached, hv]
    · have ha : mark level v (d + 1) a = level a := by simp [mark, he]
      simp only [Reached, ha, he, or_false]
      exact state.seen a
  · rw [hshape, List.nodup_append]
    refine ⟨state.unique, by simp, ?_⟩
    intro a ha b hb eq
    have h : a = v := eq.trans (List.mem_singleton.mp hb)
    exact notSeen (h ▸ ha)
  · intro a ha
    obtain ⟨k, hk, hle⟩ := state.earlier a ha
    exact ⟨k, (hsame a ⟨_, hk⟩).trans hk, hle⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · obtain ⟨k, hk, hlo, hhi⟩ := state.pending a h
      exact ⟨k, (hsame a ⟨_, hk⟩).trans hk, hlo, hhi⟩
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨d + 1, hv, by omega, Nat.le_refl _⟩
  · rw [List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · apply state.order.imp_of_mem
      intro a b ha hb h
      obtain ⟨ka, hka, _, _⟩ := state.pending a ha
      obtain ⟨kb, hkb, _, _⟩ := state.pending b hb
      rw [hsame a ⟨ka, hka⟩, hsame b ⟨kb, hkb⟩]
      exact h
    · intro a ha b hb
      obtain rfl := List.mem_singleton.mp hb
      obtain ⟨ka, hka, _, hhi⟩ := state.pending a ha
      rw [hsame a ⟨ka, hka⟩, hka, hv]
      exact hhi

/-- Closing a row records the bounds of all its outgoing arcs. -/
theorem Scan.finish_row {edge : Nat → Nat → Prop} {s u d : Nat} {done queue : List Nat} {level : Level}
    (state : Scan edge s u done queue level d) (scanned : ∀ v, edge u v → lowerAtMost level v (d + 1)) :
    Closed edge level (done ++ [u]) := by
  intro v hv k hk w arc
  rcases List.mem_append.mp hv with earlier | current
  · exact state.closed v earlier k hk w arc
  · obtain rfl := List.mem_singleton.mp current
    rw [state.here] at hk
    cases hk
    exact scanned w arc

/-- Pop the next queued vertex. FIFO ordering shifts the active layer by at most one. -/
theorem Scan.activate_next {edge : Nat → Nat → Prop} {s u d v : Nat} {done queue : List Nat} {level : Level}
    (state : Scan edge s u done (v :: queue) level d)
    (scanned : ∀ w, edge u w → lowerAtMost level w (d + 1)) :
    ∃ k, d ≤ k ∧ k ≤ d + 1 ∧ Scan edge s v (done ++ [u]) queue level k := by
  obtain ⟨k, hk, hLo, hHi⟩ := state.pending v (by simp)
  have hs : (done ++ [u]) ++ v :: queue = done ++ u :: v :: queue := by simp
  obtain ⟨headBefore, tailOrder⟩ := List.pairwise_cons.mp state.order
  refine ⟨k, hLo, hHi, ⟨state.root, hk, fun q => by rw [hs]; exact state.seen q,
    by rw [hs]; exact state.unique, state.paths, state.finish_row scanned, ?_, ?_, tailOrder⟩⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨j, hj, hle⟩ := state.earlier q hq
      exact ⟨j, hj, hle.trans hLo⟩
    · obtain rfl := List.mem_singleton.mp hq
      exact ⟨d, state.here, hLo⟩
  · intro w hw
    obtain ⟨j, hj, _, hle⟩ := state.pending w (List.mem_cons_of_mem _ hw)
    have hh := headBefore w hw
    rw [hk, hj] at hh
    exact ⟨j, hj, hh, by omega⟩

theorem Scan.finish_all {edge : Nat → Nat → Prop} {s u d : Nat} {done : List Nat} {level : Level}
    (state : Scan edge s u done [] level d) (scanned : ∀ v, edge u v → lowerAtMost level v (d + 1)) :
    Closed edge level (done ++ [u]) ∧ (∀ v, Reached level v → v ∈ done ++ [u]) :=
  ⟨state.finish_row scanned, fun _ h => (state.seen _).mp h⟩

theorem scan_init (edge : Nat → Nat → Prop) (s : Nat) :
    Scan edge s s [] [] (mark (fun _ => none) s 0) 0 := by
  have root : mark (fun _ => none) s 0 s = some 0 := by simp [mark]
  refine ⟨root, root, ?_, by simp, ?_, by simp [Closed], by simp, by simp, by simp⟩
  · intro v
    by_cases h : v = s <;> simp [mark, Reached, h]
  · intro v k hv
    by_cases h : v = s
    · subst v
      rw [root] at hv
      cases hv
      exact .start
    · simp [mark, h] at hv

end Proofs.FlowBfs
