import Proofs.Math.FlowDinicLevels
import Proofs.Math.FlowResidualPaths

namespace Proofs.FlowResidual

variable {Arc Vertex : Type}

def Usable (n : Network Arc Vertex) (cap : Capacity Arc) (lv : Levels Vertex) (a : Arc) : Prop :=
  0 < cap a ∧ UnitStep n lv a

def LayerPath (n : Network Arc Vertex) (cap : Capacity Arc) (lv : Levels Vertex) (u v : Vertex) : Prop :=
  ∃ path, Path n u v path ∧ ∀ a ∈ path, Usable n cap lv a

def Dead (n : Network Arc Vertex) (cap : Capacity Arc) (lv : Levels Vertex) (t : Vertex) (a : Arc) : Prop :=
  Usable n cap lv a → ¬ LayerPath n cap lv (n.head a) t

theorem layer_path_first (n : Network Arc Vertex) (cap : Capacity Arc) (lv : Levels Vertex) (u t : Vertex)
    (different : u ≠ t) (path : LayerPath n cap lv u t) :
    ∃ a, n.tail a = u ∧ Usable n cap lv a ∧ LayerPath n cap lv (n.head a) t := by
  obtain ⟨arcs, walk, good⟩ := path
  cases walk with
  | nil => exact False.elim (different rfl)
  | @cons a v rest tail =>
    exact ⟨a, rfl, good a (List.mem_cons_self ..), rest, tail, fun b h => good b (List.mem_cons_of_mem _ h)⟩

def WeakensLayer (n : Network Arc Vertex) (lv : Levels Vertex) (old new : Capacity Arc) : Prop :=
  ∀ a, Usable n new lv a → Usable n old lv a

theorem WeakensLayer.refl (n : Network Arc Vertex) (lv : Levels Vertex) (cap : Capacity Arc) :
    WeakensLayer n lv cap cap := fun _ h => h

theorem WeakensLayer.trans {n : Network Arc Vertex} {lv : Levels Vertex} {a b c : Capacity Arc}
    (ab : WeakensLayer n lv a b) (bc : WeakensLayer n lv b c) : WeakensLayer n lv a c :=
  fun a h => ab a (bc a h)

theorem WeakensLayer.dead {n : Network Arc Vertex} {lv : Levels Vertex} {old new : Capacity Arc} {t : Vertex}
    (weaker : WeakensLayer n lv old new) {a : Arc} (dead : Dead n old lv t a) : Dead n new lv t a := by
  rintro h ⟨path, walk, useful⟩
  exact dead (weaker a h) ⟨path, walk, fun b hb => weaker b (useful b hb)⟩

variable [DecidableEq Arc]

theorem layer_after_update (n : Network Arc Vertex) (lv : Levels Vertex) (cap : Capacity Arc) (a : Arc) (d : Int)
    (forward : UnitStep n lv a) (nonneg : 0 ≤ d) : WeakensLayer n lv cap (update n cap a d) := by
  intro b hb
  refine ⟨?_, hb.2⟩
  by_cases forwardArc : b = a
  · subst b
    have h := hb.1
    rw [update_forward] at h
    omega
  by_cases reverseArc : b = n.reverse a
  · subst b
    exact False.elim (unit_reverse_impossible n lv a forward hb.2)
  · have h := hb.1
    rwa [update_other _ _ _ _ _ forwardArc reverseArc] at h

theorem layer_after_augment (n : Network Arc Vertex) (lv : Levels Vertex) (cap : Capacity Arc) (path : List Arc) (d : Int)
    (forward : ∀ a ∈ path, UnitStep n lv a) (nonneg : 0 ≤ d) : WeakensLayer n lv cap (augment n d cap path) := by
  induction path generalizing cap with
  | nil => exact .refl n lv cap
  | cons a rest ih =>
    exact (layer_after_update n lv cap a d (forward a (List.mem_cons_self ..)) nonneg).trans
      (ih (update n cap a d) (fun a ha => forward a (List.mem_cons_of_mem _ ha)))

omit [DecidableEq Arc] in
theorem parent_not_in_child (n : Network Arc Vertex) (lv : Levels Vertex) (a : Arc)
    (forward : UnitStep n lv a) {t : Vertex} {path : List Arc} (child : Path n (n.head a) t path)
    (all : ∀ b ∈ path, UnitStep n lv b) : a ∉ path ∧ n.reverse a ∉ path := by
  refine ⟨?_, fun h => unit_reverse_impossible n lv a forward (all _ h)⟩
  intro h
  obtain ⟨d, hd, he⟩ := forward
  obtain ⟨k, lower, _, hk⟩ := (unit_walk n lv child all (d + 1) he).2 a h
  rw [hd, Option.some.injEq] at hk
  omega

omit [DecidableEq Arc] in
theorem unit_simple (n : Network Arc Vertex) (lv : Levels Vertex) {u t : Vertex} {path : List Arc}
    (route : Path n u t path) (steps : ∀ a ∈ path, UnitStep n lv a) : (routeVertices n t path).Nodup := by
  induction route with
  | nil => simp [routeVertices]
  | @cons a t rest tail ih =>
    have sub (b : Arc) (hb : b ∈ rest) := steps b (List.mem_cons_of_mem _ hb)
    obtain ⟨d, hu, hw⟩ := steps a (List.mem_cons_self ..)
    obtain ⟨endLabel, between⟩ := unit_walk n lv tail sub (d + 1) hw
    change (n.tail a :: routeVertices n t rest).Nodup
    refine List.nodup_cons.mpr ⟨?_, ih sub⟩
    intro occurs
    rw [routeVertices, List.mem_append] at occurs
    rcases occurs with middle | last
    · obtain ⟨b, hb, eq⟩ := List.mem_map.mp middle
      obtain ⟨i, lower, _, hl⟩ := between b hb
      rw [eq, hu, Option.some.injEq] at hl
      omega
    · have eq : n.tail a = t := by simpa using last
      rw [← eq, hu, Option.some.injEq] at endLabel
      omega

omit [DecidableEq Arc] in
theorem unit_length (n : Network Arc Vertex) (lv : Levels Vertex) (vertices : List Vertex)
    {u t : Vertex} {path : List Arc} (route : Path n u t path)
    (steps : ∀ a ∈ path, UnitStep n lv a) (sink : t ∈ vertices) (tails : ∀ a, n.tail a ∈ vertices) :
    path.length < vertices.length := by
  have sub : routeVertices n t path ⊆ vertices := by
    intro v hv
    rw [routeVertices, List.mem_append] at hv
    rcases hv with more | last
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp more
      exact tails a
    · obtain rfl : v = t := by simpa using last
      exact sink
  have le := (unit_simple n lv route steps).length_le_of_subset sub
  simpa [routeVertices, Nat.succ_le_iff] using le

noncomputable def activeArcs (n : Network Arc Vertex) (lv : Levels Vertex) (cap : Capacity Arc) (arcs : List Arc) : List Arc :=
  arcs.filter (fun a => @decide (Usable n cap lv a) (Classical.propDecidable _))

omit [DecidableEq Arc] in
theorem active_member (n : Network Arc Vertex) (lv : Levels Vertex) (cap : Capacity Arc) (arcs : List Arc) (a : Arc) :
    a ∈ activeArcs n lv cap arcs ↔ a ∈ arcs ∧ Usable n cap lv a := by
  simp [activeArcs]

omit [DecidableEq Arc] in
theorem active_not_growing (n : Network Arc Vertex) (lv : Levels Vertex) (old new : Capacity Arc) (arcs : List Arc)
    (nd : arcs.Nodup) (keeps : WeakensLayer n lv old new) : (activeArcs n lv new arcs).length ≤ (activeArcs n lv old arcs).length := by
  have uniq : (activeArcs n lv new arcs).Nodup := nd.filter _
  apply uniq.length_le_of_subset
  intro a ha
  obtain ⟨occurs, useful⟩ := (active_member n lv new arcs a).mp ha
  exact (active_member n lv old arcs a).mpr ⟨occurs, keeps a useful⟩

omit [DecidableEq Arc] in
theorem active_drops (n : Network Arc Vertex) (lv : Levels Vertex) (old new : Capacity Arc) (arcs : List Arc)
    (nd : arcs.Nodup) (keeps : WeakensLayer n lv old new) (a : Arc) (has : a ∈ arcs)
    (was : Usable n old lv a) (gone : ¬ Usable n new lv a) :
    (activeArcs n lv new arcs).length < (activeArcs n lv old arcs).length := by
  have nd' : (a :: activeArcs n lv new arcs).Nodup :=
    List.nodup_cons.mpr ⟨fun ha => gone ((active_member n lv new arcs a).mp ha).2, nd.filter _⟩
  have subset : (a :: activeArcs n lv new arcs) ⊆ activeArcs n lv old arcs := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | other
    · exact (active_member n lv old arcs b).mpr ⟨has, was⟩
    · obtain ⟨hm, useful⟩ := (active_member n lv new arcs b).mp other
      exact (active_member n lv old arcs b).mpr ⟨hm, keeps b useful⟩
  exact Nat.succ_le_iff.mp (nd'.length_le_of_subset subset)

section Rank

variable [DecidableEq Vertex]

def atOrAbove (vertices : List Vertex) (level : Levels Vertex) (d : Nat) : List Vertex :=
  vertices.filter fun v => match level v with
    | some k => decide (d ≤ k)
    | none => false

def rank (vertices : List Vertex) (level : Levels Vertex) (d : Nat) : Nat := (atOrAbove vertices level d).length

omit [DecidableEq Arc] [DecidableEq Vertex] in
theorem rank_le (vertices : List Vertex) (level : Levels Vertex) (d : Nat) : rank vertices level d ≤ vertices.length :=
  List.length_filter_le ..

omit [DecidableEq Arc] in
theorem rank_step (vertices : List Vertex) (level : Levels Vertex) (unique : vertices.Nodup)
    (u : Vertex) (mem : u ∈ vertices) (d : Nat) (start : level u = some d) :
    rank vertices level (d + 1) < rank vertices level d := by
  have absent : u ∉ atOrAbove vertices level (d + 1) := by
    simp [atOrAbove, start]
  have sub : u :: atOrAbove vertices level (d + 1) ⊆ atOrAbove vertices level d := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · simp [atOrAbove, start, mem]
    · simp only [atOrAbove, List.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      cases h : level v with
      | none => simp [h] at hv
      | some k =>
        simp only [h, decide_eq_true_eq] at hv ⊢
        omega
  have nd : (u :: atOrAbove vertices level (d + 1)).Nodup :=
    List.nodup_cons.mpr ⟨absent, unique.filter _⟩
  have h := nd.length_le_of_subset sub
  simp only [rank, List.length_cons] at h ⊢
  omega

end Rank
end Proofs.FlowResidual
