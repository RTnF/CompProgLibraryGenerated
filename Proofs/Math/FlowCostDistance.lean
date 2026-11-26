import Proofs.Math.FlowCostSeen

namespace Proofs.FlowResidual

variable {Arc Vertex : Type} [DecidableEq Vertex]

def HasLabel (seen : Vertex → Bool) (label : Vertex → Int) (v : Vertex) (cost : Int) : Prop :=
  seen v = true ∧ label v ≤ cost

structure SoundLabels (n : Network Arc Vertex) (cap : Capacity Arc) (s : Vertex)
    (seen : Vertex → Bool) (label : Vertex → Int) : Prop where
  root : seen s = true ∧ label s = 0
  sound : ∀ v, seen v = true → ∃ path, Path n s v path ∧ (∀ a ∈ path, 0 < cap a) ∧ (path.map n.cost).sum = label v

omit [DecidableEq Vertex] in
theorem SoundLabels.lower [DecidableEq Arc] {n : Network Arc Vertex} {cap : Capacity Arc} {s : Vertex}
    {seen : Vertex → Bool} {label p : Vertex → Int} (h : SoundLabels n cap s seen label)
    (hp : FeasiblePotential n cap p) (v : Vertex) (hv : seen v = true) : p v - p s ≤ label v := by
  obtain ⟨path, walk, positive, cost⟩ := h.sound v hv
  rw [← cost]
  exact path_cost_lower n cap p hp walk positive

theorem labels_initial (n : Network Arc Vertex) (cap : Capacity Arc) (s : Vertex) (initial : Int) :
    SoundLabels n cap s (overwrite (fun _ => false) s true) (overwrite (fun _ => initial) s 0) := by
  refine ⟨by simp [overwrite], ?_⟩
  intro v hv
  have h : v = s := by simpa [overwrite] using hv
  subst v
  exact ⟨[], .nil _, by simp, by simp [overwrite]⟩

theorem relax_keeps_lower (n : Network Arc Vertex) (a : Arc) (seen : Vertex → Bool) (label : Vertex → Int)
    (strict : seen (n.head a) = true → label (n.tail a) + n.cost a < label (n.head a))
    (v : Vertex) (d : Int) (good : HasLabel seen label v d) :
    HasLabel (overwrite seen (n.head a) true) (overwrite label (n.head a) (label (n.tail a) + n.cost a)) v d := by
  obtain ⟨seenV, le⟩ := good
  by_cases h : v = n.head a
  · subst v
    unfold HasLabel
    simp only [overwrite, ite_true, true_and]
    exact le_trans (Int.le_of_lt (strict seenV)) le
  · exact ⟨by simpa [overwrite, h] using seenV, by simpa [overwrite, h] using le⟩

theorem relax_sound [DecidableEq Arc] (n : Network Arc Vertex) (cap : Capacity Arc) (s : Vertex) (a : Arc)
    (seen : Vertex → Bool) (label p : Vertex → Int) (sound : SoundLabels n cap s seen label)
    (potential : FeasiblePotential n cap p) (hpos : 0 < cap a) (fromKnown : seen (n.tail a) = true)
    (better : seen (n.head a) = true → label (n.tail a) + n.cost a < label (n.head a)) :
    SoundLabels n cap s (overwrite seen (n.head a) true) (overwrite label (n.head a) (label (n.tail a) + n.cost a)) := by
  have notRoot : s ≠ n.head a := by
    intro h
    have feasible := potential a hpos
    have lower := sound.lower potential (n.tail a) fromKnown
    have strict := better (h ▸ sound.root.1)
    rw [← h] at feasible strict
    have start := sound.root.2
    omega
  refine ⟨by simpa [overwrite, notRoot] using sound.root, ?_⟩
  intro v seenV
  by_cases h : v = n.head a
  · subst v
    obtain ⟨path, walk, positive, exactCost⟩ := sound.sound (n.tail a) fromKnown
    refine ⟨path ++ [a], walk.snoc a rfl, ?_, ?_⟩
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact positive b hb
      · obtain rfl : b = a := by simpa using hb
        exact hpos
    · simp [overwrite, List.map_append, List.sum_append, exactCost]
  · obtain ⟨path, walk, positive, exactCost⟩ := sound.sound v (by simpa [overwrite, h] using seenV)
    exact ⟨path, walk, positive, by simpa [overwrite, h] using exactCost⟩

omit [DecidableEq Vertex] in
/-- In a stable pass, every source-reachable walk bounds the recorded label. -/
theorem closed_walk (n : Network Arc Vertex) (cap : Capacity Arc) (seen : Vertex → Bool) (label : Vertex → Int)
    (closed : ∀ a, 0 < cap a → seen (n.tail a) = true →
      HasLabel seen label (n.head a) (label (n.tail a) + n.cost a))
    {u v : Vertex} {path : List Arc} (walk : Path n u v path) (positive : ∀ a ∈ path, 0 < cap a)
    (known : seen u = true) : HasLabel seen label v (label u + (path.map n.cost).sum) := by
  induction walk with
  | nil => exact ⟨known, by simp⟩
  | cons a _ ih =>
    obtain ⟨headSeen, headLabel⟩ := closed a (positive a (List.mem_cons_self ..)) known
    obtain ⟨endSeen, bound⟩ := ih (fun b hb => positive b (List.mem_cons_of_mem _ hb)) headSeen
    refine ⟨endSeen, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    omega

omit [DecidableEq Vertex] in
theorem closed_shortest (n : Network Arc Vertex) (cap : Capacity Arc) (s : Vertex)
    (seen : Vertex → Bool) (label : Vertex → Int) (sound : SoundLabels n cap s seen label)
    (closed : ∀ a, 0 < cap a → seen (n.tail a) = true →
      HasLabel seen label (n.head a) (label (n.tail a) + n.cost a)) (v : Vertex) :
    (seen v = true ↔ ∃ path, Path n s v path ∧ ∀ a ∈ path, 0 < cap a) ∧
      ∀ path, Path n s v path → (∀ a ∈ path, 0 < cap a) → label v ≤ (path.map n.cost).sum := by
  constructor
  · constructor
    · intro hv
      obtain ⟨path, route, positive, _⟩ := sound.sound v hv
      exact ⟨path, route, positive⟩
    · rintro ⟨path, route, positive⟩
      exact (closed_walk n cap seen label closed route positive sound.root.1).1
  · intro path route positive
    have h := (closed_walk n cap seen label closed route positive sound.root.1).2
    simpa [sound.root.2] using h

end Proofs.FlowResidual
