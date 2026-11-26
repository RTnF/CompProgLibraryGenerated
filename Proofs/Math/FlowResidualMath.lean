import Proofs.Cpp.Lib.Basic

namespace Proofs.FlowResidual

/-- Each residual slot has its own identity, even between the same endpoints. -/
structure Network (Arc Vertex : Type) where
  tail : Arc → Vertex
  head : Arc → Vertex
  reverse : Arc → Arc
  reverse_reverse : ∀ a, reverse (reverse a) = a
  reverse_ne : ∀ a, reverse a ≠ a
  reverse_tail : ∀ a, tail (reverse a) = head a
  reverse_head : ∀ a, head (reverse a) = tail a
  cost : Arc → Int
  reverse_cost : ∀ a, cost (reverse a) = -cost a

variable {Arc Vertex : Type} [DecidableEq Arc]

abbrev Capacity (Arc : Type) := Arc → Int

def update (n : Network Arc Vertex) (cap : Capacity Arc) (a : Arc) (delta : Int) : Capacity Arc :=
  fun b => if b = a then cap b - delta else if b = n.reverse a then cap b + delta else cap b

@[simp] theorem update_forward (n : Network Arc Vertex) (cap : Capacity Arc) (a : Arc) (delta : Int) :
    update n cap a delta a = cap a - delta := ite_eq_left rfl

@[simp] theorem update_reverse (n : Network Arc Vertex) (cap : Capacity Arc) (a : Arc) (delta : Int) :
    update n cap a delta (n.reverse a) = cap (n.reverse a) + delta := by
  simp [update, n.reverse_ne a]

theorem update_other (n : Network Arc Vertex) (cap : Capacity Arc) (a b : Arc) (delta : Int)
    (hf : b ≠ a) (hr : b ≠ n.reverse a) : update n cap a delta b = cap b := by
  simp [update, hf, hr]

theorem update_nonneg (n : Network Arc Vertex) (cap : Capacity Arc) (a : Arc) (delta : Int)
    (hcap : ∀ b, 0 ≤ cap b) (hd : 0 ≤ delta) (hbound : delta ≤ cap a) :
    ∀ b, 0 ≤ update n cap a delta b := by
  intro b
  by_cases hf : b = a
  · subst b
    rw [update_forward]
    omega
  by_cases hr : b = n.reverse a
  · subst b
    rw [update_reverse]
    exact add_nonneg (hcap _) hd
  · rw [update_other _ _ _ _ _ hf hr]
    exact hcap b

theorem pair_capacity (n : Network Arc Vertex) (cap : Capacity Arc) (a b : Arc) (delta : Int) :
    update n cap a delta b + update n cap a delta (n.reverse b) = cap b + cap (n.reverse b) := by
  by_cases hf : b = a
  · subst b
    rw [update_forward, update_reverse]
    omega
  by_cases hr : b = n.reverse a
  · subst b
    rw [n.reverse_reverse, update_reverse, update_forward]
    omega
  have hrf : n.reverse b ≠ a := fun h => hr (by rw [← h, n.reverse_reverse])
  have hrr : n.reverse b ≠ n.reverse a := fun h => hf (by
    have := congrArg n.reverse h
    simpa only [n.reverse_reverse] using this)
  rw [update_other _ _ _ _ _ hf hr, update_other _ _ _ _ _ hrf hrr]

/-- A potential is feasible when every positive residual slot has nonnegative reduced cost. -/
def FeasiblePotential (n : Network Arc Vertex) (cap : Capacity Arc) (p : Vertex → Int) : Prop :=
  ∀ a, 0 < cap a → p (n.head a) ≤ p (n.tail a) + n.cost a

def Tight (n : Network Arc Vertex) (p : Vertex → Int) (a : Arc) : Prop :=
  p (n.head a) = p (n.tail a) + n.cost a

/-- Reversing along a shortest path cannot create a negative reduced-cost residual edge. -/
theorem potential_after_update (n : Network Arc Vertex) (cap : Capacity Arc) (p : Vertex → Int)
    (a : Arc) (delta : Int) (hp : FeasiblePotential n cap p) (hd : 0 ≤ delta) (ht : Tight n p a) :
    FeasiblePotential n (update n cap a delta) p := by
  intro b hb
  by_cases hf : b = a
  · subst b
    rw [update_forward] at hb
    exact hp a (by omega)
  by_cases hr : b = n.reverse a
  · subst b
    rw [n.reverse_tail, n.reverse_head, n.reverse_cost]
    unfold Tight at ht
    omega
  · rw [update_other _ _ _ _ _ hf hr] at hb
    exact hp b hb

/-- Ordered residual slots of a walk, retaining the exact parallel-edge choices. -/
inductive Path (n : Network Arc Vertex) : Vertex → Vertex → List Arc → Prop where
  | nil (u : Vertex) : Path n u u []
  | cons (a : Arc) {v : Vertex} {rest : List Arc} :
      Path n (n.head a) v rest → Path n (n.tail a) v (a :: rest)

theorem path_cost_lower (n : Network Arc Vertex) (cap : Capacity Arc) (p : Vertex → Int)
    (hp : FeasiblePotential n cap p) {u v : Vertex} {path : List Arc} (walk : Path n u v path)
    (positive : ∀ a ∈ path, 0 < cap a) : p v - p u ≤ (path.map n.cost).sum := by
  induction walk with
  | nil => simp
  | cons a _ ih =>
    have h := hp a (positive a (List.mem_cons_self ..))
    have hr := ih (fun b hb => positive b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem tight_path_cost (n : Network Arc Vertex) (p : Vertex → Int)
    {u v : Vertex} {path : List Arc} (walk : Path n u v path)
    (tight : ∀ a ∈ path, Tight n p a) : p v - p u = (path.map n.cost).sum := by
  induction walk with
  | nil => simp
  | cons a _ ih =>
    have h := tight a (List.mem_cons_self ..)
    unfold Tight at h
    have hr := ih (fun b hb => tight b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem path_tight_of_cost (n : Network Arc Vertex) (cap : Capacity Arc) (p : Vertex → Int)
    (hp : FeasiblePotential n cap p) {u v : Vertex} {path : List Arc} (walk : Path n u v path)
    (positive : ∀ a ∈ path, 0 < cap a) (cost : (path.map n.cost).sum = p v - p u) :
    ∀ a ∈ path, Tight n p a := by
  induction walk with
  | nil => simp
  | @cons a v rest walk ih =>
    have ha := hp a (positive a (List.mem_cons_self ..))
    have ht (b : Arc) (hb : b ∈ rest) := positive b (List.mem_cons_of_mem _ hb)
    have bound := path_cost_lower n cap p hp walk ht
    simp only [List.map_cons, List.sum_cons] at cost
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · unfold Tight
      omega
    · exact ih ht (by omega) b hb

def augment (n : Network Arc Vertex) (delta : Int) (cap : Capacity Arc) (path : List Arc) : Capacity Arc :=
  path.foldl (fun c a => update n c a delta) cap

theorem pair_capacity_after_augment (n : Network Arc Vertex) (cap : Capacity Arc) (delta : Int)
    (path : List Arc) (b : Arc) :
    augment n delta cap path b + augment n delta cap path (n.reverse b) = cap b + cap (n.reverse b) := by
  induction path generalizing cap with
  | nil => rfl
  | cons a path ih =>
    change augment n delta (update n cap a delta) path b +
      augment n delta (update n cap a delta) path (n.reverse b) = _
    rw [ih, pair_capacity]

theorem potential_after_augment (n : Network Arc Vertex) (cap : Capacity Arc) (p : Vertex → Int)
    (path : List Arc) (delta : Int) (hp : FeasiblePotential n cap p) (hd : 0 ≤ delta)
    (tight : ∀ a ∈ path, Tight n p a) : FeasiblePotential n (augment n delta cap path) p := by
  induction path generalizing cap with
  | nil => exact hp
  | cons a path ih =>
    exact ih (update n cap a delta) (potential_after_update n cap p a delta hp hd
      (tight a (List.mem_cons_self ..))) (fun b hb => tight b (List.mem_cons_of_mem _ hb))

theorem augment_unrelated (n : Network Arc Vertex) (cap : Capacity Arc) (path : List Arc) (d : Int) (a : Arc)
    (first : a ∉ path) (second : n.reverse a ∉ path) : augment n d cap path a = cap a := by
  induction path generalizing cap with
  | nil => rfl
  | cons b tail ih =>
    have f : a ≠ b := fun h => first (List.mem_cons.mpr (Or.inl h))
    have r : a ≠ n.reverse b := by
      intro h
      apply second
      apply List.mem_cons.mpr
      left
      rw [h, n.reverse_reverse]
    change augment n d (update n cap b d) tail a = _
    rw [ih _ (fun h => first (List.mem_cons_of_mem _ h)) (fun h => second (List.mem_cons_of_mem _ h))]
    exact update_other n cap b a d f r

/-- A simple augmentation uses each pair at most once, so later bounds survive earlier updates. -/
inductive DistinctPairs (n : Network Arc Vertex) : List Arc → Prop where
  | nil : DistinctPairs n []
  | cons {a : Arc} {rest : List Arc} : a ∉ rest → n.reverse a ∉ rest →
      DistinctPairs n rest → DistinctPairs n (a :: rest)

theorem nonneg_after_augment (n : Network Arc Vertex) (cap : Capacity Arc) (path : List Arc)
    (delta : Int) (hd : 0 ≤ delta) (valid : ∀ a, 0 ≤ cap a)
    (pairs : DistinctPairs n path) (supplies : ∀ a ∈ path, delta ≤ cap a) :
    ∀ a, 0 ≤ augment n delta cap path a := by
  induction pairs generalizing cap with
  | nil => exact valid
  | @cons a rest hf hr _ ih =>
    apply ih (update n cap a delta) (update_nonneg _ _ _ _ valid hd (supplies _ (List.mem_cons_self ..)))
    intro b hb
    have hfb : b ≠ a := fun h => hf (h ▸ hb)
    have hrb : b ≠ n.reverse a := fun h => hr (h ▸ hb)
    rw [update_other n cap a b delta hfb hrb]
    exact supplies b (List.mem_cons_of_mem _ hb)

theorem augment_selected (n : Network Arc Vertex) (cap : Capacity Arc) (path : List Arc) (delta : Int)
    (pairs : DistinctPairs n path) (a : Arc) (inside : a ∈ path) : augment n delta cap path a = cap a - delta := by
  induction pairs generalizing cap with
  | nil => cases inside
  | @cons b rest hf hr _ ih =>
    change augment n delta (update n cap b delta) rest a = _
    rcases List.mem_cons.mp inside with rfl | later
    · rw [augment_unrelated _ _ _ _ _ hf hr, update_forward]
    · have h1 : a ≠ b := fun h => hf (h ▸ later)
      have h2 : a ≠ n.reverse b := fun h => hr (h ▸ later)
      rw [ih _ later, update_other _ _ _ _ _ h1 h2]

section Balance

variable [DecidableEq Vertex]

def indicator (u v : Vertex) : Int := if u = v then 1 else 0

def balanceDelta (n : Network Arc Vertex) (v : Vertex) (path : List Arc) : Int :=
  (path.map fun a => indicator (n.tail a) v - indicator (n.head a) v).sum

theorem path_balance (n : Network Arc Vertex) {source sink : Vertex} {path : List Arc}
    (walk : Path n source sink path) (v : Vertex) :
    balanceDelta n v path = indicator source v - indicator sink v := by
  induction walk with
  | nil => simp [balanceDelta]
  | cons a _ ih =>
    simp only [balanceDelta, List.map_cons, List.sum_cons] at ih ⊢
    omega

end Balance

end Proofs.FlowResidual
