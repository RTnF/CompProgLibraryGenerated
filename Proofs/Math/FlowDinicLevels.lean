import Proofs.Math.FlowResidualMath

namespace Proofs.FlowResidual

variable {Arc Vertex : Type}

abbrev Levels (Vertex : Type) := Vertex → Option Nat

def ValidDistance (n : Network Arc Vertex) (cap : Capacity Arc) (level : Levels Vertex) : Prop :=
  ∀ a, 0 < cap a → ∀ i, level (n.tail a) = some i →
    ∃ j, level (n.head a) = some j ∧ j ≤ i + 1

def UnitStep (n : Network Arc Vertex) (level : Levels Vertex) (a : Arc) : Prop :=
  ∃ i, level (n.tail a) = some i ∧ level (n.head a) = some (i + 1)

variable [DecidableEq Arc]

/-- Reversals of level-increasing edges point toward earlier levels. -/
theorem distances_after_update (n : Network Arc Vertex) (cap : Capacity Arc) (level : Levels Vertex)
    (a : Arc) (d : Int) (hd : 0 ≤ d) (old : ValidDistance n cap level) (step : UnitStep n level a) :
    ValidDistance n (update n cap a d) level := by
  intro b positive i hi
  by_cases hf : b = a
  · subst b
    rw [update_forward] at positive
    exact old a (by omega) i hi
  by_cases hr : b = n.reverse a
  · subst b
    rw [n.reverse_tail] at hi
    rw [n.reverse_head]
    obtain ⟨j, ht, hh⟩ := step
    refine ⟨j, ht, ?_⟩
    rw [hh, Option.some.injEq] at hi
    omega
  · rw [update_other _ _ _ _ _ hf hr] at positive
    exact old b positive i hi

theorem distances_after_augment (n : Network Arc Vertex) (cap : Capacity Arc) (level : Levels Vertex)
    (path : List Arc) (d : Int) (hd : 0 ≤ d) (old : ValidDistance n cap level)
    (steps : ∀ a ∈ path, UnitStep n level a) : ValidDistance n (augment n d cap path) level := by
  induction path generalizing cap with
  | nil => exact old
  | cons a rest ih =>
    exact ih (update n cap a d) (distances_after_update n cap level a d hd old
      (steps a (List.mem_cons_self ..))) (fun a ha => steps a (List.mem_cons_of_mem _ ha))

omit [DecidableEq Arc] in
/-- Distance labels remain lower bounds on the length of every new residual walk. -/
theorem walk_distance (n : Network Arc Vertex) (cap : Capacity Arc) (level : Levels Vertex)
    (distances : ValidDistance n cap level) {u v : Vertex} {path : List Arc}
    (walk : Path n u v path) (positive : ∀ a ∈ path, 0 < cap a) (i : Nat) (hi : level u = some i) :
    ∃ j, level v = some j ∧ j ≤ i + path.length ∧
      (j = i + path.length → ∀ a ∈ path, UnitStep n level a) := by
  induction walk generalizing i with
  | nil => exact ⟨i, hi, by simp, by simp⟩
  | @cons a v rest _ ih =>
    obtain ⟨k, hk, hl⟩ := distances a (positive a (List.mem_cons_self ..)) i hi
    obtain ⟨j, hj, bound, equal_path⟩ := ih (fun a ha => positive a (List.mem_cons_of_mem _ ha)) k hk
    refine ⟨j, hj, by simp; omega, ?_⟩
    intro equal b hb
    simp only [List.length_cons] at equal
    have he : k = i + 1 := by omega
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨i, hi, he ▸ hk⟩
    · exact equal_path (by omega) b hb

omit [DecidableEq Arc] in
/-- After blocking the old level graph, every remaining source-to-sink walk is longer. -/
theorem blocking_increases (n : Network Arc Vertex) (cap : Capacity Arc) (level : Levels Vertex)
    (distances : ValidDistance n cap level) (s t : Vertex) (d : Nat)
    (hs : level s = some 0) (ht : level t = some d)
    (blocked : ∀ path, Path n s t path → (∀ a ∈ path, 0 < cap a) →
      ¬ (∀ a ∈ path, UnitStep n level a)) (path : List Arc)
    (walk : Path n s t path) (positive : ∀ a ∈ path, 0 < cap a) : d < path.length := by
  obtain ⟨j, hj, bound, allTight⟩ := walk_distance n cap level distances walk positive 0 hs
  rw [ht, Option.some.injEq] at hj
  subst j
  have hne : d ≠ 0 + path.length := fun eq => blocked path walk positive (allTight eq)
  omega

omit [DecidableEq Arc] in
theorem unit_walk (n : Network Arc Vertex) (level : Levels Vertex) {u v : Vertex} {path : List Arc}
    (walk : Path n u v path) (steps : ∀ a ∈ path, UnitStep n level a) (d : Nat) (origin : level u = some d) :
    level v = some (d + path.length) ∧
    ∀ a ∈ path, ∃ j, d ≤ j ∧ j < d + path.length ∧ level (n.tail a) = some j := by
  induction walk generalizing d with
  | nil => exact ⟨by simpa using origin, by simp⟩
  | @cons a v tail _ ih =>
    obtain ⟨j, hj, head⟩ := steps a (List.mem_cons_self ..)
    rw [origin, Option.some.injEq] at hj
    subst j
    obtain ⟨ends, middle⟩ := ih (fun b hb => steps b (List.mem_cons_of_mem _ hb)) (d + 1) head
    constructor
    · convert ends using 2
      simp only [List.length_cons]
      omega
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨d, le_rfl, by simp, origin⟩
      · obtain ⟨k, hk, hlt, hl⟩ := middle b hb
        refine ⟨k, by omega, ?_, hl⟩
        simp only [List.length_cons]
        omega

omit [DecidableEq Arc] in
theorem unit_reverse_impossible (n : Network Arc Vertex) (level : Levels Vertex) (a : Arc)
    (forward : UnitStep n level a) (backward : UnitStep n level (n.reverse a)) : False := by
  obtain ⟨i, t, h⟩ := forward
  obtain ⟨j, tr, hr⟩ := backward
  rw [n.reverse_tail, h, Option.some.injEq] at tr
  rw [n.reverse_head, t, Option.some.injEq] at hr
  omega

omit [DecidableEq Arc] in
theorem unit_path_distinct (n : Network Arc Vertex) (level : Levels Vertex) {u v : Vertex} {path : List Arc}
    (walk : Path n u v path) (steps : ∀ a ∈ path, UnitStep n level a) : DistinctPairs n path := by
  induction walk with
  | nil => exact .nil
  | @cons a v tail tailPath ih =>
    have step := steps a (List.mem_cons_self ..)
    have tailSteps (b : Arc) (hb : b ∈ tail) := steps b (List.mem_cons_of_mem _ hb)
    refine .cons ?_ (fun hb => unit_reverse_impossible n level a step (tailSteps _ hb)) (ih tailSteps)
    intro revisit
    obtain ⟨j, startLevel, endLevel⟩ := step
    obtain ⟨k, bound, _, h⟩ := (unit_walk n level tailPath tailSteps (j + 1) endLevel).2 a revisit
    rw [startLevel, Option.some.injEq] at h
    omega

end Proofs.FlowResidual
