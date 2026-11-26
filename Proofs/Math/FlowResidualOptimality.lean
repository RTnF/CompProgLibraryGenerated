import Proofs.Math.FlowResidualMath

namespace Proofs.FlowResidual

variable {Arc Vertex : Type} [DecidableEq Vertex]

private def total {α : Type} (items : List α) (f : α → Int) : Int := (items.map f).sum

private theorem total_add {α : Type} (items : List α) (f g : α → Int) :
    total items (fun x => f x + g x) = total items f + total items g := by
  induction items with
  | nil => rfl
  | cons x rest ih =>
    simp only [total, List.map_cons, List.sum_cons] at ih ⊢
    omega

private theorem total_sub {α : Type} (items : List α) (f g : α → Int) :
    total items (fun x => f x - g x) = total items f - total items g := by
  induction items with
  | nil => rfl
  | cons x rest ih =>
    simp only [total, List.map_cons, List.sum_cons] at ih ⊢
    omega

private theorem total_mono {α : Type} (items : List α) (f g : α → Int)
    (h : ∀ x ∈ items, f x ≤ g x) : total items f ≤ total items g := by
  induction items with
  | nil => exact Int.le_refl _
  | cons x rest ih =>
    have hrest := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self ..)
    simp only [total, List.map_cons, List.sum_cons] at hrest ⊢
    omega

private theorem total_mul {α : Type} (items : List α) (d : Int) (f : α → Int) :
    total items (fun x => d * f x) = d * total items f := by
  induction items with
  | nil => simp [total]
  | cons x rest ih =>
    simp only [total, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Int.mul_add]

private theorem sum_indicator (vs : List Vertex) (nd : vs.Nodup) (u : Vertex) (p : Vertex → Int) :
    total vs (fun v => p v * indicator u v) = if u ∈ vs then p u else 0 := by
  induction vs with
  | nil => simp [total]
  | cons v rest ih =>
    obtain ⟨notMem, ndRest⟩ := List.nodup_cons.mp nd
    have tail := ih ndRest
    change p v * indicator u v + total rest (fun w => p w * indicator u w) = _
    rw [tail]
    by_cases h : u = v
    · subst u
      simp [indicator, notMem]
    · simp [indicator, h]

/-- Net additional flow leaving a vertex, measured in the original residual orientation. -/
def divergence (n : Network Arc Vertex) (arcs : List Arc) (f : Arc → Int) (v : Vertex) : Int :=
  total arcs (fun a => f a * (indicator (n.tail a) v - indicator (n.head a) v))

def transportCost (n : Network Arc Vertex) (arcs : List Arc) (f : Arc → Int) : Int :=
  total arcs (fun a => f a * n.cost a)

private theorem weighted_divergence (n : Network Arc Vertex) (arcs : List Arc) (vs : List Vertex)
    (nd : vs.Nodup) (inRange : ∀ a ∈ arcs, n.tail a ∈ vs ∧ n.head a ∈ vs)
    (f : Arc → Int) (p : Vertex → Int) :
    total vs (fun v => p v * divergence n arcs f v) = total arcs (fun a => f a * (p (n.tail a) - p (n.head a))) := by
  induction arcs with
  | nil =>
    simp [divergence, total]
  | cons a rest ih =>
    obtain ⟨ht, hh⟩ := inRange a (List.mem_cons_self ..)
    have ih' := ih (fun b hb => inRange b (List.mem_cons_of_mem _ hb))
    change total vs (fun v => p v * (f a * (indicator (n.tail a) v - indicator (n.head a) v) +
      divergence n rest f v)) = f a * (p (n.tail a) - p (n.head a)) + _
    simp only [Int.mul_add]
    rw [total_add, ih']
    congr 1
    conv =>
      lhs
      arg 2
      intro v
      rw [Int.mul_left_comm, Int.mul_sub]
    rw [total_mul, total_sub, sum_indicator vs nd _ p, sum_indicator vs nd _ p,
      ite_eq_left ht, ite_eq_left hh]

private theorem weighted_terminal (vs : List Vertex) (nd : vs.Nodup) (s t : Vertex)
    (hs : s ∈ vs) (ht : t ∈ vs) (p : Vertex → Int) (amount : Int) :
    total vs (fun v => p v * (amount * (indicator s v - indicator t v))) = amount * (p s - p t) := by
  conv =>
    lhs
    arg 2
    intro v
    rw [Int.mul_left_comm, Int.mul_sub]
  rw [total_mul, total_sub, sum_indicator vs nd _ p, sum_indicator vs nd _ p, ite_eq_left hs, ite_eq_left ht]

/-- A cut without outgoing positive residual capacity rules out any positive feasible additional flow. -/
theorem cut_maximal (n : Network Arc Vertex) (cap : Capacity Arc) (arcs : List Arc) (vs : List Vertex)
    (nd : vs.Nodup) (inside : Vertex → Bool) (s t : Vertex) (hs : s ∈ vs) (ht : t ∈ vs)
    (vertices : ∀ a ∈ arcs, n.tail a ∈ vs ∧ n.head a ∈ vs) (source_in : inside s = true)
    (sink_out : inside t = false)
    (closed : ∀ a ∈ arcs, inside (n.tail a) = true → inside (n.head a) = false → cap a ≤ 0)
    (f : Arc → Int) (amount : Int) (available : ∀ a ∈ arcs, 0 ≤ f a ∧ f a ≤ cap a)
    (balance : ∀ v, divergence n arcs f v = amount * (indicator s v - indicator t v)) : amount ≤ 0 := by
  let p (v : Vertex) : Int := if inside v then 1 else 0
  have hsum := weighted_divergence n arcs vs nd vertices f p
  have hsval : p s = 1 := by simp [p, source_in]
  have htval : p t = 0 := by simp [p, sink_out]
  rw [show (fun v => p v * divergence n arcs f v) =
    (fun v => p v * (amount * (indicator s v - indicator t v))) from funext (fun v => by rw [balance v]),
    weighted_terminal vs nd s t hs ht p amount, hsval, htval] at hsum
  have h := total_mono arcs (fun a => f a * (p (n.tail a) - p (n.head a))) (fun _ => 0) (by
    intro a ha
    obtain ⟨nonneg, bnd⟩ := available a ha
    cases hu : inside (n.tail a) <;> cases hv : inside (n.head a)
    · simp [p, hu, hv]
    · simp [p, hu, hv, nonneg]
    · have hz := closed a ha hu hv
      simp [p, hu, hv]
      omega
    · simp [p, hu, hv])
  simp [total] at h
  simp only [Int.sub_zero, Int.mul_one] at hsum
  rw [hsum]
  exact h

/-- A feasible price potential bounds the cost of every feasible additional transport. -/
theorem potential_lower_bound (n : Network Arc Vertex) (cap : Capacity Arc) (arcs : List Arc) (vs : List Vertex)
    (nd : vs.Nodup) (s t : Vertex) (hs : s ∈ vs) (ht : t ∈ vs)
    (vertices : ∀ a ∈ arcs, n.tail a ∈ vs ∧ n.head a ∈ vs)
    (p : Vertex → Int) (potential : FeasiblePotential n cap p)
    (f : Arc → Int) (amount : Int) (available : ∀ a ∈ arcs, 0 ≤ f a ∧ f a ≤ cap a)
    (balance : ∀ v, divergence n arcs f v = amount * (indicator s v - indicator t v)) :
    -(amount * (p s - p t)) ≤ transportCost n arcs f := by
  have hsum := weighted_divergence n arcs vs nd vertices f p
  rw [show (fun v => p v * divergence n arcs f v) =
    (fun v => p v * (amount * (indicator s v - indicator t v))) from funext (fun v => by rw [balance v]),
    weighted_terminal vs nd s t hs ht p amount] at hsum
  have geom := total_mono arcs (fun a => f a * (p (n.head a) - p (n.tail a))) (fun a => f a * n.cost a) (by
    intro a ha
    obtain ⟨nonneg, bound⟩ := available a ha
    by_cases h : 0 < f a
    · have dist := potential a (by omega)
      exact Int.mul_le_mul_of_nonneg_left (by omega) nonneg
    · have zero : f a = 0 := by omega
      simp [zero])
  have neg : total arcs (fun a => f a * (p (n.head a) - p (n.tail a))) =
      -(total arcs (fun a => f a * (p (n.tail a) - p (n.head a)))) := by
    simp only [Int.mul_sub, total_sub]
    omega
  rw [← hsum] at neg
  unfold transportCost
  rwa [neg] at geom

omit [DecidableEq Vertex] in
/-- Extend source-reachable distances by shifting the old potential on unreachable vertices. -/
theorem extend_potential (n : Network Arc Vertex) (cap : Capacity Arc) (seen : Vertex → Bool)
    (dist old : Vertex → Int) (shift : Int) (oldFeasible : FeasiblePotential n cap old)
    (distClosed : ∀ a, 0 < cap a → seen (n.tail a) = true →
      seen (n.head a) = true ∧ dist (n.head a) ≤ dist (n.tail a) + n.cost a)
    (shiftBound : ∀ a, 0 < cap a → seen (n.tail a) = false → seen (n.head a) = true →
      dist (n.head a) - old (n.tail a) - n.cost a ≤ shift) :
    FeasiblePotential n cap (fun v => if seen v then dist v else old v + shift) := by
  intro a ha
  cases tail : seen (n.tail a)
  · cases head : seen (n.head a)
    · have keep := oldFeasible a ha
      simp [tail, head]
      omega
    · have lower := shiftBound a ha tail head
      simp [tail, head]
      omega
  · obtain ⟨head, bound⟩ := distClosed a ha tail
    simpa [tail, head] using bound

omit [DecidableEq Vertex] in
theorem reachable_potential (n : Network Arc Vertex) (cap : Capacity Arc) (arcs : List Arc)
    (every : ∀ a, a ∈ arcs) (seen : Vertex → Bool) (dist old : Vertex → Int)
    (oldFeasible : FeasiblePotential n cap old)
    (distClosed : ∀ a, 0 < cap a → seen (n.tail a) = true →
      seen (n.head a) = true ∧ dist (n.head a) ≤ dist (n.tail a) + n.cost a) :
    ∃ p : Vertex → Int, FeasiblePotential n cap p ∧ ∀ v, seen v = true → p v = dist v := by
  let need (a : Arc) := dist (n.head a) - old (n.tail a) - n.cost a
  let margin := (arcs.map need).foldr max 0
  have largest {xs : List Int} {x : Int} (h : x ∈ xs) : x ≤ xs.foldr max 0 := by
    induction xs with
    | nil => cases h
    | cons y ys ih =>
      rcases List.mem_cons.mp h with rfl | tail
      · exact le_max_left _ _
      · exact le_trans (ih tail) (le_max_right _ _)
  refine ⟨fun v => if seen v then dist v else old v + margin,
    extend_potential n cap seen dist old margin oldFeasible distClosed ?_, ?_⟩
  · intro a _ _ _
    exact largest (List.mem_map.mpr ⟨a, every a, rfl⟩)
  · intro v hv
    simp [hv]

section PathTransport

variable [DecidableEq Arc]

private theorem total_select (all chosen : List Arc) (ndAll : all.Nodup) (ndChosen : chosen.Nodup)
    (subset : chosen ⊆ all) (f : Arc → Int) :
    total all (fun a => if a ∈ chosen then f a else 0) = total chosen f := by
  induction chosen with
  | nil => simp [total]
  | cons a rest ih =>
    obtain ⟨absent, nd⟩ := List.nodup_cons.mp ndChosen
    have hAll : a ∈ all := subset (List.mem_cons_self ..)
    have eq : (fun b => if b ∈ a :: rest then f b else 0) =
        (fun b => f b * indicator a b + if b ∈ rest then f b else 0) := by
      funext b
      by_cases h : b = a
      · subst b
        simp [absent, indicator]
      · simp [h, Ne.symm h, indicator]
    rw [eq, total_add, sum_indicator all ndAll a f, ite_eq_left hAll,
      ih nd (fun b hb => subset (List.mem_cons_of_mem _ hb))]
    rfl

def along (path : List Arc) (amount : Int) (a : Arc) : Int := if a ∈ path then amount else 0

theorem along_divergence (n : Network Arc Vertex) (all path : List Arc) (ndAll : all.Nodup)
    (ndPath : path.Nodup) (subset : path ⊆ all) (amount : Int) {s t : Vertex} (route : Path n s t path) (v : Vertex) :
    divergence n all (along path amount) v = amount * (indicator s v - indicator t v) := by
  unfold divergence
  have eq : (fun a => along path amount a * (indicator (n.tail a) v - indicator (n.head a) v)) =
      (fun a => if a ∈ path then amount * (indicator (n.tail a) v - indicator (n.head a) v) else 0) := by
    funext a
    by_cases ha : a ∈ path <;> simp [along, ha]
  rw [eq, total_select all path ndAll ndPath subset, total_mul]
  change amount * balanceDelta n v path = _
  rw [path_balance n route v]

omit [DecidableEq Vertex] in
theorem along_cost (n : Network Arc Vertex) (all path : List Arc) (ndAll : all.Nodup)
    (ndPath : path.Nodup) (subset : path ⊆ all) (amount : Int) :
    transportCost n all (along path amount) = amount * (path.map n.cost).sum := by
  unfold transportCost
  have eq : (fun a => along path amount a * n.cost a) =
      (fun a => if a ∈ path then amount * n.cost a else 0) := by
    funext a
    by_cases ha : a ∈ path <;> simp [along, ha]
  rw [eq, total_select all path ndAll ndPath subset, total_mul]
  rfl

/-- Every amount from zero to the bottleneck has optimal incremental cost on the tight path. -/
theorem tight_transport_optimal (n : Network Arc Vertex) (cap : Capacity Arc) (arcs : List Arc) (vs : List Vertex)
    (ndArcs : arcs.Nodup) (ndVs : vs.Nodup) (s t : Vertex) (hs : s ∈ vs) (ht : t ∈ vs)
    (vertices : ∀ a ∈ arcs, n.tail a ∈ vs ∧ n.head a ∈ vs)
    (p : Vertex → Int) (potential : FeasiblePotential n cap p) (nonnegative : ∀ a ∈ arcs, 0 ≤ cap a)
    (path : List Arc) (route : Path n s t path) (simple : path.Nodup) (subset : path ⊆ arcs)
    (tight : ∀ a ∈ path, Tight n p a) (amount : Int) (nonneg : 0 ≤ amount)
    (bottleneck : ∀ a ∈ path, amount ≤ cap a) :
    (∀ a ∈ arcs, 0 ≤ along path amount a ∧ along path amount a ≤ cap a) ∧
      (∀ v, divergence n arcs (along path amount) v = amount * (indicator s v - indicator t v)) ∧
      (∀ f : Arc → Int, (∀ a ∈ arcs, 0 ≤ f a ∧ f a ≤ cap a) →
        (∀ v, divergence n arcs f v = amount * (indicator s v - indicator t v)) →
        transportCost n arcs (along path amount) ≤ transportCost n arcs f) := by
  refine ⟨?_, along_divergence n arcs path ndArcs simple subset amount route, ?_⟩
  · intro a ha
    by_cases h : a ∈ path
    · simp [along, h, nonneg, bottleneck a h]
    · simp [along, h, nonnegative a ha]
  · intro f available balance
    have hc := tight_path_cost n p route tight
    rw [along_cost n arcs path ndArcs simple subset amount, ← hc]
    have h := potential_lower_bound n cap arcs vs ndVs s t hs ht vertices p potential f amount available balance
    simpa only [Int.mul_sub, Int.neg_sub] using h

end PathTransport

section Accounting
variable [DecidableEq Arc]

def charged (arcs : List Arc) (start finish : Capacity Arc) (weight : Arc → Int) : Int :=
  total arcs (fun a => (start a - finish a) * weight a)

omit [DecidableEq Arc] [DecidableEq Vertex] in
theorem charged_add (arcs : List Arc) (start mid finish : Capacity Arc) (weight : Arc → Int) :
    charged arcs start finish weight = charged arcs start mid weight + charged arcs mid finish weight := by
  unfold charged
  rw [← total_add]
  congr 1
  funext a
  rw [← Int.add_mul]
  rw [show start a - mid a + (mid a - finish a) = start a - finish a by omega]

omit [DecidableEq Vertex] in
private theorem charged_step (n : Network Arc Vertex) (arcs : List Arc) (nd : arcs.Nodup)
    (cap : Capacity Arc) (a : Arc) (here : a ∈ arcs) (back : n.reverse a ∈ arcs) (d : Int) (weight : Arc → Int) :
    charged arcs cap (update n cap a d) weight = d * (weight a - weight (n.reverse a)) := by
  unfold charged
  have eq : (fun b => (cap b - update n cap a d b) * weight b) =
      (fun b => d * (weight b * indicator a b - weight b * indicator (n.reverse a) b)) := by
    funext b
    by_cases bf : b = a
    · subst b
      simp [indicator, n.reverse_ne]
    by_cases br : b = n.reverse a
    · subst b
      simp [indicator, (n.reverse_ne a).symm]
    · simp [update_other n cap a b d bf br, indicator, Ne.symm bf, Ne.symm br]
  rw [eq, total_mul, total_sub, sum_indicator arcs nd a weight, sum_indicator arcs nd (n.reverse a) weight,
    ite_eq_left here, ite_eq_left back]

omit [DecidableEq Vertex] in
theorem charged_augment (n : Network Arc Vertex) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (cap : Capacity Arc) (path : List Arc) (d : Int) (weight : Arc → Int) :
    charged arcs cap (augment n d cap path) weight = d * (path.map fun a => weight a - weight (n.reverse a)).sum := by
  induction path generalizing cap with
  | nil =>
    unfold charged
    simp [augment, total]
  | cons a rest ih =>
    change charged arcs cap (augment n d (update n cap a d) rest) weight = _
    rw [charged_add arcs cap (update n cap a d), charged_step n arcs nd cap a (all a) (all _) d, ih]
    simp [Int.mul_add]

omit [DecidableEq Vertex] in
theorem charged_cost (n : Network Arc Vertex) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (cap : Capacity Arc) (path : List Arc) (d : Int) :
    charged arcs cap (augment n d cap path.reverse) n.cost = 2 * (d * (path.map n.cost).sum) := by
  rw [charged_augment n arcs nd all]
  have term (a : Arc) : n.cost a - n.cost (n.reverse a) = 2 * n.cost a := by rw [n.reverse_cost]; omega
  simp_rw [term]
  change d * total path.reverse (fun a => 2 * n.cost a) = _
  rw [total_mul]
  simp [total, List.map_reverse, List.sum_reverse, Int.mul_left_comm]

theorem charged_balance (n : Network Arc Vertex) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (cap : Capacity Arc) (path : List Arc) (d : Int) {s t : Vertex} (route : Path n s t path) (v : Vertex) :
    charged arcs cap (augment n d cap path.reverse) (fun a => indicator (n.tail a) v - indicator (n.head a) v) =
      2 * (d * (indicator s v - indicator t v)) := by
  rw [charged_augment n arcs nd all]
  have term (a : Arc) : (indicator (n.tail a) v - indicator (n.head a) v) -
      (indicator (n.tail (n.reverse a)) v - indicator (n.head (n.reverse a)) v) =
      2 * (indicator (n.tail a) v - indicator (n.head a) v) := by
    rw [n.reverse_tail, n.reverse_head]
    omega
  simp_rw [term]
  change d * total path.reverse (fun a => 2 * (indicator (n.tail a) v - indicator (n.head a) v)) = _
  rw [total_mul]
  have hp : total path.reverse (fun a => indicator (n.tail a) v - indicator (n.head a) v) = balanceDelta n v path := by
    simp [total, balanceDelta, List.map_reverse, List.sum_reverse]
  rw [hp, path_balance n route v, Int.mul_left_comm]

end Accounting

/-- Signed flows use both directed slots of each pair, with opposite values. -/
def SignedFeasible (n : Network Arc Vertex) (arcs : List Arc) (base : Capacity Arc)
    (s t : Vertex) (amount : Int) (f : Arc → Int) : Prop :=
  (∀ a, f (n.reverse a) = -f a) ∧ (∀ a, f a ≤ base a) ∧
    (∀ v, divergence n arcs f v = 2 * (amount * (indicator s v - indicator t v)))

private theorem residual_price (n : Network Arc Vertex) (arcs : List Arc) (vs : List Vertex)
    (nd : vs.Nodup) (vertices : ∀ a ∈ arcs, n.tail a ∈ vs ∧ n.head a ∈ vs)
    (cap : Capacity Arc) (p : Vertex → Int) (feasible : FeasiblePotential n cap p)
    (f : Arc → Int) (paired : ∀ a, f (n.reverse a) = -f a) (bound : ∀ a, f a ≤ cap a)
    (balanced : ∀ v, divergence n arcs f v = 0) : 0 ≤ transportCost n arcs f := by
  have hsum := weighted_divergence n arcs vs nd vertices f p
  simp only [balanced, Int.mul_zero] at hsum
  have hzero : total arcs (fun a => f a * (p (n.tail a) - p (n.head a))) = 0 := by
    rw [← hsum]
    simp [total]
  have neg : total arcs (fun a => f a * (p (n.head a) - p (n.tail a))) = 0 := by
    simp only [Int.mul_sub, total_sub] at hzero ⊢
    omega
  unfold transportCost
  rw [← neg]
  apply total_mono
  intro a _
  by_cases h : 0 < f a
  · have dist := feasible a (lt_of_lt_of_le h (bound a))
    exact Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt h)
  by_cases zero : f a = 0
  · simp [zero]
  have reversePos : 0 < cap (n.reverse a) := by
    have hb := bound (n.reverse a)
    rw [paired] at hb
    omega
  have dist := feasible (n.reverse a) reversePos
  rw [n.reverse_tail, n.reverse_head, n.reverse_cost] at dist
  exact Int.mul_le_mul_of_nonpos_left (by omega) (by omega)

/-- A feasible residual potential certifies a flow's cost among all transshipments of that amount. -/
theorem signed_optimal (n : Network Arc Vertex) (arcs : List Arc) (vs : List Vertex)
    (nd : vs.Nodup) (vertices : ∀ a ∈ arcs, n.tail a ∈ vs ∧ n.head a ∈ vs)
    (base cap : Capacity Arc) (p : Vertex → Int) (potential : FeasiblePotential n cap p)
    (s t : Vertex) (amount : Int) (q : Arc → Int)
    (current : SignedFeasible n arcs base s t amount (fun a => base a - cap a))
    (competing : SignedFeasible n arcs base s t amount q) :
    charged arcs base cap n.cost ≤ transportCost n arcs q := by
  let delta (a : Arc) := q a - (base a - cap a)
  have paired (a : Arc) : delta (n.reverse a) = -delta a := by
    have h := current.1 a
    have hh := competing.1 a
    dsimp only [delta] at h hh ⊢
    omega
  have bound (a : Arc) : delta a ≤ cap a := by
    have h := competing.2.1 a
    unfold delta
    omega
  have balanced (v : Vertex) : divergence n arcs delta v = 0 := by
    have first := current.2.2 v
    have second := competing.2.2 v
    change total arcs (fun a => q a * (indicator (n.tail a) v - indicator (n.head a) v)) = _ at second
    change total arcs (fun a => (base a - cap a) * (indicator (n.tail a) v - indicator (n.head a) v)) = _ at first
    unfold divergence delta
    simp only [Int.sub_mul, total_sub] at first ⊢
    omega
  have h := residual_price n arcs vs nd vertices cap p potential delta paired bound balanced
  unfold transportCost delta at h
  simp only [Int.sub_mul, total_sub] at h
  unfold charged transportCost
  simp only [Int.sub_mul, total_sub]
  omega

theorem signed_cut_maximal (n : Network Arc Vertex) (arcs : List Arc) (vs : List Vertex)
    (nd : vs.Nodup) (vertices : ∀ a ∈ arcs, n.tail a ∈ vs ∧ n.head a ∈ vs)
    (base cap : Capacity Arc) (inside : Vertex → Bool) (s t : Vertex) (hs : s ∈ vs) (ht : t ∈ vs)
    (hSource : inside s = true) (hSink : inside t = false)
    (closed : ∀ a, inside (n.tail a) = true → inside (n.head a) = false → cap a ≤ 0)
    (amount other : Int) (q : Arc → Int)
    (cur : SignedFeasible n arcs base s t amount (fun a => base a - cap a))
    (alt : SignedFeasible n arcs base s t other q) : other ≤ amount := by
  let delta (a : Arc) := q a - (base a - cap a)
  let weight (v : Vertex) : Int := if inside v then 1 else 0
  have paired (a : Arc) : delta (n.reverse a) = -delta a := by
    have h := cur.1 a
    have hh := alt.1 a
    dsimp only [delta] at h hh ⊢
    omega
  have bound (a : Arc) : delta a ≤ cap a := by
    have h := alt.2.1 a
    unfold delta
    omega
  have balanced (v : Vertex) : divergence n arcs delta v = 2 * ((other - amount) * (indicator s v - indicator t v)) := by
    have first := cur.2.2 v
    have second := alt.2.2 v
    change total arcs (fun a => q a * (indicator (n.tail a) v - indicator (n.head a) v)) = _ at second
    change total arcs (fun a => (base a - cap a) * (indicator (n.tail a) v - indicator (n.head a) v)) = _ at first
    unfold divergence delta
    simp only [Int.sub_mul, total_sub, Int.mul_sub] at first second ⊢
    omega
  have hsum := weighted_divergence n arcs vs nd vertices delta weight
  have he : (fun v => weight v * divergence n arcs delta v) =
      (fun v => weight v * ((2 * (other - amount)) * (indicator s v - indicator t v))) := by
    funext v
    rw [balanced, Int.mul_assoc]
  have hv : weight s = 1 := by simp [weight, hSource]
  have hw : weight t = 0 := by simp [weight, hSink]
  rw [he, weighted_terminal vs nd s t hs ht weight, hv, hw, Int.sub_zero, Int.mul_one] at hsum
  have h := total_mono arcs (fun a => delta a * (weight (n.tail a) - weight (n.head a))) (fun _ => 0) (by
    intro a _
    cases u : inside (n.tail a) <;> cases v : inside (n.head a)
    · simp [weight, u, v]
    · have hc := closed (n.reverse a) (by simpa only [n.reverse_tail] using v) (by simpa only [n.reverse_head] using u)
      have hb := bound (n.reverse a)
      rw [paired] at hb
      simp [weight, u, v]
      omega
    · have hc := closed a u v
      have hb := bound a
      simp [weight, u, v]
      omega
    · simp [weight, u, v])
  rw [← hsum] at h
  simp [total] at h
  omega

section Updates
variable [DecidableEq Arc]

theorem signed_augmentation (n : Network Arc Vertex) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (base cap : Capacity Arc) (s t : Vertex) (amount : Int) (path : List Arc) (r : Path n s t path)
    (current : SignedFeasible n arcs base s t amount (fun a => base a - cap a)) (d : Int)
    (nonnegative : ∀ a, 0 ≤ augment n d cap path.reverse a) :
    SignedFeasible n arcs base s t (amount + d) (fun a => base a - augment n d cap path.reverse a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    have before := current.1 a
    have same := pair_capacity_after_augment n cap d path.reverse a
    dsimp only at before ⊢
    omega
  · intro a
    have h := nonnegative a
    dsimp only
    omega
  · intro v
    let w (a : Arc) := indicator (n.tail a) v - indicator (n.head a) v
    change charged arcs base (augment n d cap path.reverse) w = _
    rw [charged_add arcs base cap, charged_balance n arcs nd all cap path d r v]
    have h : charged arcs base cap w = _ := current.2.2 v
    rw [h, Int.add_mul, Int.mul_add]

end Updates

/-- A uniform capacity bound controls the total integral flow independently of the chosen augmentations. -/
theorem signed_capacity_bound (n : Network Arc Vertex) (arcs : List Arc) (base : Capacity Arc) (s t : Vertex)
    (different : s ≠ t) (maximum amount : Int) (nonnegative : 0 ≤ maximum) (edgeBound : ∀ a, base a ≤ maximum)
    (f : Arc → Int) (flow : SignedFeasible n arcs base s t amount f) : amount ≤ (arcs.length : Int) * maximum := by
  have out := flow.2.2 s
  simp only [indicator, ite_true, show t ≠ s from Ne.symm different, ite_false, Int.sub_zero, Int.mul_one] at out
  have per (a : Arc) (_ : a ∈ arcs) : f a * (indicator (n.tail a) s - indicator (n.head a) s) ≤ maximum := by
    have hw : f a ≤ maximum := le_trans (flow.2.1 a) (edgeBound a)
    have hr : -f a ≤ maximum := by rw [← flow.1 a]; exact le_trans (flow.2.1 _) (edgeBound _)
    by_cases first : n.tail a = s <;> by_cases last : n.head a = s <;> simp [indicator, first, last, nonnegative, hw, hr]
  have sumbound := total_mono arcs _ (fun _ => maximum) per
  have constant : total arcs (fun _ => maximum) = (arcs.length : Int) * maximum := by
    clear sumbound out per flow
    induction arcs with
    | nil => simp [total]
    | cons e tail ih =>
      simp only [total, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      rw [ih, Int.natCast_succ, Int.add_mul, Int.one_mul, Int.add_comm]
  rw [constant] at sumbound
  have nonnegUpper := Int.mul_nonneg (Int.natCast_nonneg arcs.length) nonnegative
  exact (by change divergence n arcs f s ≤ _ at sumbound; rw [out] at sumbound; omega)

end Proofs.FlowResidual
