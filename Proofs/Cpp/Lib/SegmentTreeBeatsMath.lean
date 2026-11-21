import Proofs.Cpp.Lib.SegmentTreeMath

/-! # Summaries of a segment tree beats node: maximum, second maximum, count, and the same for the minimum. -/

namespace Proofs.Cpp.SegmentTreeBeatsMath

/-- The sentinel of the C++ code. -/
def INF : Int := 4000000000000000000

def lmax (L : List Int) : Int := L.foldr max (-INF)
def lmin (L : List Int) : Int := L.foldr min INF
def smax (L : List Int) : Int := lmax (L.filter (· < lmax L))
def smin (L : List Int) : Int := lmin (L.filter (· > lmin L))
def cmax (L : List Int) : Int := L.count (lmax L)
def cmin (L : List Int) : Int := L.count (lmin L)

/-- The values strictly inside the sentinels. -/
def InR (L : List Int) : Prop := ∀ v ∈ L, -INF < v ∧ v < INF

theorem lmax_ge (L : List Int) : ∀ v ∈ L, v ≤ lmax L := by
  induction L with
  | nil => simp
  | cons a t ih =>
    intro v hv
    simp only [lmax, List.foldr_cons] at *
    rcases List.mem_cons.mp hv with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih v h) (le_max_right _ _)

theorem lmin_le (L : List Int) : ∀ v ∈ L, lmin L ≤ v := by
  induction L with
  | nil => simp
  | cons a t ih =>
    intro v hv
    simp only [lmin, List.foldr_cons] at *
    rcases List.mem_cons.mp hv with rfl | h
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih v h)

theorem lmax_mem (L : List Int) (h : L ≠ []) (hR : InR L) : lmax L ∈ L := by
  induction L with
  | nil => exact absurd rfl h
  | cons a t ih =>
    simp only [lmax, List.foldr_cons]
    by_cases ht : t = []
    · subst ht; have := (hR a (by simp)).1; simp [max_eq_left (le_of_lt this)]
    · have hm := ih ht (fun v hv => hR v (List.mem_cons_of_mem _ hv))
      rcases max_choice a (List.foldr max (-INF) t) with e | e
      · rw [e]; simp
      · rw [e]; exact List.mem_cons_of_mem _ hm

theorem lmin_mem (L : List Int) (h : L ≠ []) (hR : InR L) : lmin L ∈ L := by
  induction L with
  | nil => exact absurd rfl h
  | cons a t ih =>
    simp only [lmin, List.foldr_cons]
    by_cases ht : t = []
    · subst ht; have := (hR a (by simp)).2; simp [min_eq_left (le_of_lt this)]
    · have hm := ih ht (fun v hv => hR v (List.mem_cons_of_mem _ hv))
      rcases min_choice a (List.foldr min INF t) with e | e
      · rw [e]; simp
      · rw [e]; exact List.mem_cons_of_mem _ hm

theorem lmax_ge_ninf (L : List Int) : -INF ≤ lmax L := by
  induction L with
  | nil => exact le_refl _
  | cons a t ih => simp only [lmax, List.foldr_cons] at *; exact le_trans ih (le_max_right _ _)

theorem lmin_le_inf (L : List Int) : lmin L ≤ INF := by
  induction L with
  | nil => exact le_refl _
  | cons a t ih => simp only [lmin, List.foldr_cons] at *; exact le_trans (min_le_right _ _) ih

theorem lmax_append (A B : List Int) : lmax (A ++ B) = max (lmax A) (lmax B) := by
  induction A with
  | nil => have := lmax_ge_ninf B; simp only [lmax, List.nil_append, List.foldr_nil] at *; omega
  | cons a t ih => simp only [lmax, List.cons_append, List.foldr_cons] at *; rw [ih, max_assoc]

theorem lmin_append (A B : List Int) : lmin (A ++ B) = min (lmin A) (lmin B) := by
  induction A with
  | nil => have := lmin_le_inf B; simp only [lmin, List.nil_append, List.foldr_nil] at *; omega
  | cons a t ih => simp only [lmin, List.cons_append, List.foldr_cons] at *; rw [ih, min_assoc]

theorem lmax_nil : lmax [] = -INF := rfl
theorem lmin_nil : lmin [] = INF := rfl

/-- `lmax` is the least upper bound above `-INF`. -/
theorem lmax_le_iff (L : List Int) (c : Int) (hc : -INF ≤ c) : lmax L ≤ c ↔ ∀ v ∈ L, v ≤ c := by
  induction L with
  | nil => simp [lmax_nil, hc]
  | cons a t ih => simp only [lmax, List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp] at *; rw [ih]

theorem le_lmin_iff (L : List Int) (c : Int) (hc : c ≤ INF) : c ≤ lmin L ↔ ∀ v ∈ L, c ≤ v := by
  induction L with
  | nil => simp [lmin_nil, hc]
  | cons a t ih => simp only [lmin, List.foldr_cons, le_min_iff, List.mem_cons, forall_eq_or_imp] at *; rw [ih]

theorem filter_all (A : List Int) (p : Int → Bool) (h : ∀ v ∈ A, p v = true) : A.filter p = A :=
  List.filter_eq_self.mpr h

theorem count_zero (A : List Int) (M : Int) (h : lmax A < M) : A.count M = 0 := by
  apply List.count_eq_zero.mpr
  intro hm; have := lmax_ge A M hm; omega

theorem count_zero_min (A : List Int) (M : Int) (h : M < lmin A) : A.count M = 0 := by
  apply List.count_eq_zero.mpr
  intro hm; have := lmin_le A M hm; omega

theorem smax_append_lt (A B : List Int) (h : lmax A < lmax B) :
    lmax (A ++ B) = lmax B ∧ smax (A ++ B) = max (lmax A) (smax B) ∧ cmax (A ++ B) = cmax B := by
  have e : lmax (A ++ B) = lmax B := by rw [lmax_append]; omega
  refine ⟨e, ?_, ?_⟩
  · unfold smax; rw [e, List.filter_append, lmax_append,
      filter_all A _ (fun v hv => by have := lmax_ge A v hv; simp; omega)]
  · unfold cmax; rw [e, List.count_append, count_zero A _ h]; simp

theorem smax_append_gt (A B : List Int) (h : lmax B < lmax A) :
    lmax (A ++ B) = lmax A ∧ smax (A ++ B) = max (smax A) (lmax B) ∧ cmax (A ++ B) = cmax A := by
  have e : lmax (A ++ B) = lmax A := by rw [lmax_append]; omega
  refine ⟨e, ?_, ?_⟩
  · unfold smax; rw [e, List.filter_append, lmax_append,
      filter_all B _ (fun v hv => by have := lmax_ge B v hv; simp; omega)]
  · unfold cmax; rw [e, List.count_append, count_zero B _ h]; simp

theorem smax_append_eq (A B : List Int) (h : lmax A = lmax B) :
    lmax (A ++ B) = lmax A ∧ smax (A ++ B) = max (smax A) (smax B) ∧ cmax (A ++ B) = cmax A + cmax B := by
  have e : lmax (A ++ B) = lmax A := by rw [lmax_append]; omega
  refine ⟨e, ?_, ?_⟩
  · unfold smax; rw [e, List.filter_append, lmax_append, ← h]
  · unfold cmax; rw [e, List.count_append, ← h]; push_cast; ring

theorem smin_append_lt (A B : List Int) (h : lmin A < lmin B) :
    lmin (A ++ B) = lmin A ∧ smin (A ++ B) = min (smin A) (lmin B) ∧ cmin (A ++ B) = cmin A := by
  have e : lmin (A ++ B) = lmin A := by rw [lmin_append]; omega
  refine ⟨e, ?_, ?_⟩
  · unfold smin; rw [e, List.filter_append, lmin_append,
      filter_all B _ (fun v hv => by have := lmin_le B v hv; simp; omega)]
  · unfold cmin; rw [e, List.count_append, count_zero_min B _ h]; simp

theorem smin_append_gt (A B : List Int) (h : lmin B < lmin A) :
    lmin (A ++ B) = lmin B ∧ smin (A ++ B) = min (lmin A) (smin B) ∧ cmin (A ++ B) = cmin B := by
  have e : lmin (A ++ B) = lmin B := by rw [lmin_append]; omega
  refine ⟨e, ?_, ?_⟩
  · unfold smin; rw [e, List.filter_append, lmin_append,
      filter_all A _ (fun v hv => by have := lmin_le A v hv; simp; omega)]
  · unfold cmin; rw [e, List.count_append, count_zero_min A _ h]; simp

theorem smin_append_eq (A B : List Int) (h : lmin A = lmin B) :
    lmin (A ++ B) = lmin A ∧ smin (A ++ B) = min (smin A) (smin B) ∧ cmin (A ++ B) = cmin A + cmin B := by
  have e : lmin (A ++ B) = lmin A := by rw [lmin_append]; omega
  refine ⟨e, ?_, ?_⟩
  · unfold smin; rw [e, List.filter_append, lmin_append, ← h]
  · unfold cmin; rw [e, List.count_append, ← h]; push_cast; ring

/-! ## The minimum side is the maximum side of the negated values -/

theorem lmin_neg (L : List Int) : lmin L = -lmax (L.map (- ·)) := by
  induction L with
  | nil => simp [lmin, lmax]
  | cons a t ih => simp only [lmin, lmax, List.foldr_cons, List.map_cons] at *; rw [ih]; omega

theorem filter_map_neg (L : List Int) (m : Int) :
    (L.map (- ·)).filter (· < -m) = (L.filter (· > m)).map (- ·) := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : a > m
    · simp [h, show -a < -m by omega, ih]
    · simp [h, show ¬ (-a < -m) by omega, ih]

theorem smin_neg (L : List Int) : smin L = -smax (L.map (- ·)) := by
  unfold smin smax
  have e : lmax (L.map (- ·)) = -lmin L := by rw [lmin_neg]; omega
  rw [e, filter_map_neg, lmin_neg (L.filter _)]

theorem count_neg (L : List Int) (m : Int) : (L.map (- ·)).count (-m) = L.count m := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.count_cons, ih]
    by_cases h : a = m <;> simp [h]

theorem cmin_neg (L : List Int) : cmin L = cmax (L.map (- ·)) := by
  unfold cmin cmax
  have e : lmax (L.map (- ·)) = -lmin L := by rw [lmin_neg]; omega
  rw [e, count_neg]

theorem inr_neg (L : List Int) (h : InR L) : InR (L.map (- ·)) := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  have := h w hw; constructor <;> omega

/-! ## Monotone maps -/

theorem lmax_map_mono (L : List Int) (f : Int → Int) (hf : Monotone f) (hne : L ≠ [])
    (hR : InR L) (hR' : InR (L.map f)) : lmax (L.map f) = f (lmax L) := by
  induction L with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    simp only [lmax, List.map_cons, List.foldr_cons]
    by_cases ht : t = []
    · subst ht
      have h1 := (hR a (by simp)).1
      have h2 := (hR' (f a) (by simp)).1
      simp [max_eq_left (le_of_lt h1), max_eq_left (le_of_lt h2)]
    · have := ih ht (fun v hv => hR v (List.mem_cons_of_mem _ hv))
        (fun v hv => hR' v (List.mem_cons_of_mem _ hv))
      simp only [lmax] at this
      rw [this, hf.map_max]

theorem filter_map_comm (L : List Int) (f : Int → Int) (p q : Int → Bool) (h : ∀ v ∈ L, p (f v) = q v) :
    (L.map f).filter p = (L.filter q).map f := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.filter_cons]
    rw [h a (by simp), ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]
    split <;> simp

theorem count_map_iff (L : List Int) (f : Int → Int) (a b : Int) (h : ∀ v ∈ L, (f v = a ↔ v = b)) :
    (L.map f).count a = L.count b := by
  induction L with
  | nil => rfl
  | cons c t ih =>
    simp only [List.map_cons, List.count_cons]
    rw [ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]
    have := h c (by simp)
    by_cases e : c = b
    · subst e; simp [this.mpr rfl]
    · simp [e, show ¬ f c = a from fun h' => e (this.mp h')]

theorem elem_le_smax (L : List Int) : ∀ v ∈ L, v < lmax L → v ≤ smax L := by
  intro v hv hlt
  exact lmax_ge _ v (List.mem_filter.mpr ⟨hv, by simpa using hlt⟩)

theorem smax_lt (L : List Int) (hR : InR L) (hne : L ≠ []) : smax L < lmax L ∨ smax L = -INF := by
  by_cases h : L.filter (· < lmax L) = []
  · right; unfold smax; rw [h]; rfl
  · left
    have hm := lmax_mem _ h (fun v hv => hR v (List.mem_filter.mp hv).1)
    have := (List.mem_filter.mp hm).2
    unfold smax; simpa using this

theorem smax_ge_ninf (L : List Int) : -INF ≤ smax L := lmax_ge_ninf _

/-! ## The max side after the operations on a node -/

theorem max_side_add (L : List Int) (x : Int) (hne : L ≠ []) (hR : InR L) (hR' : InR (L.map (· + x))) :
    lmax (L.map (· + x)) = lmax L + x ∧
      smax (L.map (· + x)) = (if smax L = -INF then -INF else smax L + x) ∧
      cmax (L.map (· + x)) = cmax L := by
  have hmono : Monotone (· + x : Int → Int) := fun a b h => by simp; omega
  have e1 := lmax_map_mono L _ hmono hne hR hR'
  refine ⟨e1, ?_, ?_⟩
  · unfold smax
    rw [e1, filter_map_comm L _ _ (· < lmax L) (fun v _ => by simp)]
    by_cases hf : L.filter (· < lmax L) = []
    · rw [hf]; simp [lmax_nil]
    · have hR1 : InR (L.filter (· < lmax L)) := fun v hv => hR v (List.mem_filter.mp hv).1
      have hR2 : InR ((L.filter (· < lmax L)).map (· + x)) := fun v hv => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        exact hR' _ (List.mem_map.mpr ⟨w, (List.mem_filter.mp hw).1, rfl⟩)
      rw [lmax_map_mono _ _ hmono hf hR1 hR2]
      have := (hR1 _ (lmax_mem _ hf hR1)).1
      rw [if_neg (by omega)]
  · unfold cmax; rw [e1]; congr 1; exact count_map_iff L _ _ _ (fun v _ => by simp)

theorem max_side_chmin (L : List Int) (x : Int) (hR : InR L) (h1 : smax L < x) (h2 : x < lmax L) :
    lmax (L.map (min · x)) = x ∧ smax (L.map (min · x)) = smax L ∧ cmax (L.map (min · x)) = cmax L := by
  have hne : L ≠ [] := by intro h; subst h; simp [lmax_nil, smax, lmax] at h1 h2; omega
  have hmono : Monotone (min · x : Int → Int) := fun a b h => min_le_min_right x h
  have hR' : InR (L.map (min · x)) := fun v hv => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have := hR w hw; have := smax_ge_ninf L; constructor <;> simp <;> omega
  have e1 : lmax (L.map (min · x)) = x := by rw [lmax_map_mono L _ hmono hne hR hR']; simp; omega
  refine ⟨e1, ?_, ?_⟩
  · unfold smax
    rw [e1, filter_map_comm L _ _ (· < lmax L) (fun v hv => by
      have := lmax_ge L v hv
      by_cases hv2 : v < lmax L
      · have := elem_le_smax L v hv hv2; simp [hv2]; omega
      · simp [hv2]; omega)]
    have hid : (L.filter (· < lmax L)).map (min · x) = L.filter (· < lmax L) := by
      conv_rhs => rw [← List.map_id (L.filter (· < lmax L))]
      apply List.map_congr_left
      intro v hv
      have := elem_le_smax L v (List.mem_filter.mp hv).1 (by simpa using (List.mem_filter.mp hv).2)
      simp; omega
    rw [hid]
  · unfold cmax; rw [e1]; congr 1
    exact count_map_iff L (min · x) x (lmax L) (fun v hv => by
      have := lmax_ge L v hv
      constructor
      · intro h; by_contra hc
        have := elem_le_smax L v hv (by omega); simp at h; omega
      · intro h; simp; omega)

theorem lmin_le_lmax (L : List Int) (hR : InR L) (hne : L ≠ []) : lmin L ≤ lmax L :=
  lmin_le L _ (lmax_mem L hne hR) |>.trans (le_refl _)

theorem all_eq_of (L : List Int) (h : lmax L = lmin L) : ∀ v ∈ L, v = lmax L := by
  intro v hv; have := lmax_ge L v hv; have := lmin_le L v hv; omega

theorem smax_single (L : List Int) (h : lmax L = lmin L) : smax L = -INF := by
  unfold smax
  rw [List.filter_eq_nil_iff.mpr (fun v hv => by have := all_eq_of L h v hv; simp; omega)]; rfl

theorem lmin_le_smax (L : List Int) (hR : InR L) (hne : L ≠ []) (h : lmax L ≠ lmin L) : lmin L ≤ smax L := by
  have hm := lmin_mem L hne hR
  have := lmin_le_lmax L hR hne
  exact elem_le_smax L _ hm (by omega)

theorem max_side_chmax (L : List Int) (y : Int) (hR : InR L) (hne : L ≠ []) (h1 : lmin L < y)
    (h2 : ∀ v ∈ L, lmin L < v → y < v) (hy : y < INF) :
    (lmax L = lmin L → lmax (L.map (max · y)) = y ∧ smax (L.map (max · y)) = -INF ∧
        cmax (L.map (max · y)) = cmax L) ∧
    (lmax L ≠ lmin L → lmax (L.map (max · y)) = lmax L ∧ smax (L.map (max · y)) = max (smax L) y ∧
        cmax (L.map (max · y)) = cmax L) := by
  have hmono : Monotone (max · y : Int → Int) := fun a b h => max_le_max h (le_refl y)
  have hR' : InR (L.map (max · y)) := fun v hv => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have := hR w hw; have := lmin_le L w hw; have := lmin_le_inf L; constructor <;> simp <;> omega
  have e1 := lmax_map_mono L _ hmono hne hR hR'
  have hle := lmin_le_lmax L hR hne
  constructor
  · intro he
    have hall := all_eq_of L he
    have ex : lmax (L.map (max · y)) = y := by rw [e1]; simp; omega
    refine ⟨ex, ?_, ?_⟩
    · unfold smax
      rw [ex, List.filter_eq_nil_iff.mpr (fun v hv => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        have := hall w hw
        show ¬ (decide (max w y < y) = true)
        simp)]
      rfl
    · unfold cmax; rw [ex]; congr 1
      exact count_map_iff L (max · y) y (lmax L) (fun v hv => by have := hall v hv; simp; omega)
  · intro hne2
    have ex : lmax (L.map (max · y)) = lmax L := by
      rw [e1]; have := h2 (lmax L) (lmax_mem L hne hR) (by omega); simp; omega
    refine ⟨ex, ?_, ?_⟩
    · unfold smax
      rw [ex, filter_map_comm L _ _ (· < lmax L) (fun v hv => by
        have := h2 (lmax L) (lmax_mem L hne hR) (by omega)
        by_cases hv2 : v < lmax L <;> simp [hv2] <;> omega)]
      have hf : L.filter (· < lmax L) ≠ [] := by
        intro h; have := List.filter_eq_nil_iff.mp h _ (lmin_mem L hne hR); simp at this; omega
      have hR1 : InR (L.filter (· < lmax L)) := fun v hv => hR v (List.mem_filter.mp hv).1
      have hR2 : InR ((L.filter (· < lmax L)).map (max · y)) := fun v hv => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        exact hR' _ (List.mem_map.mpr ⟨w, (List.mem_filter.mp hw).1, rfl⟩)
      rw [lmax_map_mono _ _ hmono hf hR1 hR2]
    · unfold cmax; rw [ex]; congr 1
      exact count_map_iff L (max · y) (lmax L) (lmax L) (fun v hv => by
        have := h2 (lmax L) (lmax_mem L hne hR) (by omega)
        have := lmin_le L v hv
        constructor
        · intro h; rcases max_choice v y with e | e <;> rw [e] at h <;> omega
        · intro h; rw [h]; exact max_eq_left (by omega))

/-! ## Node summaries -/

/-- The six stored numbers of a node summarize the values `L`. -/
structure Summ (L : List Int) (mx smx mxc mn smn mnc : Int) : Prop where
  mx : mx = lmax L
  smx : smx = smax L
  mxc : mxc = cmax L
  mn : mn = lmin L
  smn : smn = smin L
  mnc : mnc = cmin L

theorem summ_nil : Summ [] (-INF) (-INF) 0 INF INF 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem summ_replicate (m : Nat) (x : Int) (hm : 1 ≤ m) (hx : -INF < x ∧ x < INF) :
    Summ (List.replicate m x) x (-INF) m x INF m := by
  have hR : InR (List.replicate m x) := fun v hv => by rw [List.eq_of_mem_replicate hv]; exact hx
  have hne : List.replicate m x ≠ [] := by simp; omega
  have hmax : lmax (List.replicate m x) = x := by
    have h1 := lmax_mem _ hne hR; rw [List.eq_of_mem_replicate h1]
  have hmin : lmin (List.replicate m x) = x := by
    have h1 := lmin_mem _ hne hR; rw [List.eq_of_mem_replicate h1]
  refine ⟨hmax.symm, ?_, ?_, hmin.symm, ?_, ?_⟩
  · unfold smax; rw [hmax, List.filter_eq_nil_iff.mpr (fun v hv => by
      rw [List.eq_of_mem_replicate hv]; simp)]; rfl
  · unfold cmax; rw [hmax]; simp
  · unfold smin; rw [hmin, List.filter_eq_nil_iff.mpr (fun v hv => by
      rw [List.eq_of_mem_replicate hv]; simp)]; rfl
  · unfold cmin; rw [hmin]; simp

/-- `update(k)`: the summary of the concatenation from the children's summaries. -/
def combMax (ma sa ca mb sb cb : Int) : Int × Int × Int :=
  if ma < mb then (mb, max ma sb, cb) else if ma > mb then (ma, max sa mb, ca) else (ma, max sa sb, ca + cb)

def combMin (ma sa ca mb sb cb : Int) : Int × Int × Int :=
  if ma < mb then (ma, min sa mb, ca) else if ma > mb then (mb, min ma sb, cb) else (ma, min sa sb, ca + cb)

theorem summ_append (A B : List Int) (a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : Int)
    (hA : Summ A a1 a2 a3 a4 a5 a6) (hB : Summ B b1 b2 b3 b4 b5 b6) :
    Summ (A ++ B) (combMax a1 a2 a3 b1 b2 b3).1 (combMax a1 a2 a3 b1 b2 b3).2.1 (combMax a1 a2 a3 b1 b2 b3).2.2
      (combMin a4 a5 a6 b4 b5 b6).1 (combMin a4 a5 a6 b4 b5 b6).2.1 (combMin a4 a5 a6 b4 b5 b6).2.2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hB
  subst h1 h2 h3 h4 h5 h6 g1 g2 g3 g4 g5 g6
  have mx : ∀ P : Int × Int × Int → Prop, (P (lmax (A ++ B), smax (A ++ B), cmax (A ++ B))) →
      P (combMax (lmax A) (smax A) (cmax A) (lmax B) (smax B) (cmax B)) := by
    intro P hP; unfold combMax
    split_ifs with c1 c2
    · obtain ⟨e1, e2, e3⟩ := smax_append_lt A B c1; rw [e1, e2, e3] at hP; exact hP
    · obtain ⟨e1, e2, e3⟩ := smax_append_gt A B c2; rw [e1, e2, e3] at hP; exact hP
    · obtain ⟨e1, e2, e3⟩ := smax_append_eq A B (by omega); rw [e1, e2, e3] at hP; exact hP
  have mn : ∀ P : Int × Int × Int → Prop, (P (lmin (A ++ B), smin (A ++ B), cmin (A ++ B))) →
      P (combMin (lmin A) (smin A) (cmin A) (lmin B) (smin B) (cmin B)) := by
    intro P hP; unfold combMin
    split_ifs with c1 c2
    · obtain ⟨e1, e2, e3⟩ := smin_append_lt A B c1; rw [e1, e2, e3] at hP; exact hP
    · obtain ⟨e1, e2, e3⟩ := smin_append_gt A B c2; rw [e1, e2, e3] at hP; exact hP
    · obtain ⟨e1, e2, e3⟩ := smin_append_eq A B (by omega); rw [e1, e2, e3] at hP; exact hP
  exact ⟨mx (fun t => t.1 = lmax (A ++ B)) rfl, mx (fun t => t.2.1 = smax (A ++ B)) rfl,
    mx (fun t => t.2.2 = cmax (A ++ B)) rfl, mn (fun t => t.1 = lmin (A ++ B)) rfl,
    mn (fun t => t.2.1 = smin (A ++ B)) rfl, mn (fun t => t.2.2 = cmin (A ++ B)) rfl⟩


theorem map_neg_neg (L : List Int) : (L.map (- ·)).map (- ·) = L := by simp [List.map_map]

theorem summ_neg (L : List Int) (a1 a2 a3 a4 a5 a6 : Int) (h : Summ L a1 a2 a3 a4 a5 a6) :
    Summ (L.map (- ·)) (-a4) (-a5) a6 (-a1) (-a2) a3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have l1 := lmin_neg (L.map (- ·)); rw [map_neg_neg] at l1
  have l2 := smin_neg (L.map (- ·)); rw [map_neg_neg] at l2
  have l3 := cmin_neg (L.map (- ·)); rw [map_neg_neg] at l3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4, lmin_neg]; omega
  · rw [h5, smin_neg]; omega
  · rw [h6, cmin_neg]
  · rw [h1]; omega
  · rw [h2]; omega
  · rw [h3, l3]

theorem summ_of_neg (L : List Int) (a1 a2 a3 a4 a5 a6 : Int)
    (h : Summ (L.map (- ·)) (-a4) (-a5) a6 (-a1) (-a2) a3) : Summ L a1 a2 a3 a4 a5 a6 := by
  have := summ_neg _ _ _ _ _ _ _ h
  rw [map_neg_neg] at this
  simpa using this

theorem inr_map (L : List Int) (f : Int → Int) (h : ∀ v ∈ L, -INF < f v ∧ f v < INF) : InR (L.map f) := by
  intro v hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact h w hw

/-- `add_all(k, x)`. -/
theorem summ_add (L : List Int) (x a1 a2 a3 a4 a5 a6 : Int) (h : Summ L a1 a2 a3 a4 a5 a6) (hne : L ≠ [])
    (hR : InR L) (hR' : InR (L.map (· + x))) :
    Summ (L.map (· + x)) (a1 + x) (if a2 = -INF then -INF else a2 + x) a3 (a4 + x)
      (if a5 = INF then INF else a5 + x) a6 := by
  have hs := h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨m1, m2, m3⟩ := max_side_add L x hne hR hR'
  have hN := summ_neg _ _ _ _ _ _ _ hs
  have hneN : L.map (- ·) ≠ [] := by simpa using hne
  have eq : (L.map (· + x)).map (- ·) = (L.map (- ·)).map (· + -x) := by simp [List.map_map]; intro a _; omega
  have hRN' : InR ((L.map (- ·)).map (· + -x)) := by rw [← eq]; exact inr_neg _ hR'
  obtain ⟨n1, n2, n3⟩ := max_side_add (L.map (- ·)) (-x) hneN (inr_neg _ hR) hRN'
  rw [← eq] at n1 n2 n3
  have hN1 := hN.mx; have hN2 := hN.smx; have hN3 := hN.mxc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m1, h1]
  · rw [m2, h2]
  · rw [m3, h3]
  · rw [lmin_neg, n1, ← hN1]; ring
  · rw [smin_neg, n2, ← hN2]; split_ifs <;> omega
  · rw [cmin_neg, n3, ← hN3]

theorem smax_mem (L : List Int) (hR : InR L) (hne : L ≠ []) (h : lmax L ≠ lmin L) : smax L ∈ L := by
  have hf : L.filter (· < lmax L) ≠ [] := by
    intro hf
    have h1 := List.filter_eq_nil_iff.mp hf _ (lmin_mem L hne hR)
    have := lmin_le_lmax L hR hne
    simp at h1; omega
  exact (List.mem_filter.mp (lmax_mem _ hf (fun v hv => hR v (List.mem_filter.mp hv).1))).1

theorem smin_facts (L : List Int) (hR : InR L) (hne : L ≠ []) (h : lmax L ≠ lmin L) :
    smin L ∈ L ∧ lmin L < smin L ∧ smin L ≤ lmax L := by
  have hM := inr_neg L hR
  have hneM : L.map (- ·) ≠ [] := by simpa using hne
  have e1 : lmax (L.map (- ·)) = -lmin L := by rw [lmin_neg]; omega
  have e2 : lmin (L.map (- ·)) = -lmax L := by
    have := lmin_neg (L.map (- ·)); rw [map_neg_neg] at this; omega
  have hne2 : lmax (L.map (- ·)) ≠ lmin (L.map (- ·)) := by omega
  have m := smax_mem _ hM hneM hne2
  have l := lmin_le_smax _ hM hneM hne2
  have sl := smax_lt _ hM hneM
  have es := smin_neg L
  obtain ⟨w, hw, hw2⟩ := List.mem_map.mp m
  have := lmin_le L w hw
  refine ⟨by rw [es, ← hw2]; simpa using hw, ?_, by rw [es]; omega⟩
  rcases sl with sl | sl
  · rw [es]; omega
  · have := (hR w hw).2; rw [sl] at hw2; omega

theorem smin_single (L : List Int) (h : lmax L = lmin L) : smin L = INF := by
  unfold smin
  rw [List.filter_eq_nil_iff.mpr (fun v hv => by have := all_eq_of L h v hv; simp; omega)]; rfl

/-- `update_node_max(k, x)`: chmin of the values with `x` strictly between the second maximum and the maximum. -/
theorem summ_chmin (L : List Int) (x a1 a2 a3 a4 a5 a6 : Int) (h : Summ L a1 a2 a3 a4 a5 a6) (hR : InR L)
    (hx1 : a2 < x) (hx2 : x < a1) :
    Summ (L.map (min · x)) x a2 a3 (if a1 = a4 then x else a4) (if a1 = a4 then a5 else if a1 = a5 then x else a5)
      a6 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  subst h1 h2 h3 h4 h5 h6
  have hne : L ≠ [] := by intro e; subst e; simp [lmax_nil, smax, lmax] at hx1 hx2; omega
  obtain ⟨m1, m2, m3⟩ := max_side_chmin L x hR hx1 hx2
  have hM := inr_neg L hR
  have hneM : L.map (- ·) ≠ [] := by simpa using hne
  have e1 : lmax (L.map (- ·)) = -lmin L := by rw [lmin_neg]; omega
  have e2 : lmin (L.map (- ·)) = -lmax L := by
    have := lmin_neg (L.map (- ·)); rw [map_neg_neg] at this; omega
  have eq : (L.map (min · x)).map (- ·) = (L.map (- ·)).map (max · (-x)) := by
    rw [List.map_map, List.map_map]; apply List.map_congr_left; intro a _
    show -(min a x) = max (-a) (-x); omega
  obtain ⟨c1, c2⟩ := max_side_chmax (L.map (- ·)) (-x) hM hneM (by omega)
    (fun v hv hlt => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      have := elem_le_smax L w hw (by omega); omega)
    (by have := smax_ge_ninf L; unfold INF at *; omega)
  have hcm := cmin_neg L
  refine ⟨m1.symm, m2.symm, m3.symm, ?_, ?_, ?_⟩
  · rw [lmin_neg (L.map (min · x)), eq]
    by_cases he : lmax L = lmin L
    · rw [if_pos he, (c1 (by omega)).1]; ring
    · rw [if_neg he, (c2 (by omega)).1, e1]; ring
  · rw [smin_neg (L.map (min · x)), eq]
    by_cases he : lmax L = lmin L
    · rw [if_pos he, (c1 (by omega)).2.1, smin_single L he]; ring
    · rw [if_neg he, (c2 (by omega)).2.1]
      have es := smin_neg L
      obtain ⟨f1, f2, f3⟩ := smin_facts L hR hne he
      by_cases e3 : lmax L = smin L
      · rw [if_pos e3]; omega
      · rw [if_neg e3]
        have := elem_le_smax L _ f1 (by omega)
        omega
  · rw [cmin_neg (L.map (min · x)), eq]
    by_cases he : lmax L = lmin L
    · rw [(c1 (by omega)).2.2, ← cmin_neg]
    · rw [(c2 (by omega)).2.2, ← cmin_neg]

/-- `update_node_min(k, y)`: chmax of the values with `y` strictly between the minimum and the second minimum. -/
theorem summ_chmax (L : List Int) (y a1 a2 a3 a4 a5 a6 : Int) (h : Summ L a1 a2 a3 a4 a5 a6) (hR : InR L)
    (hy1 : a4 < y) (hy2 : y < a5) :
    Summ (L.map (max · y)) (if a1 = a4 then y else a1) (if a1 = a4 then a2 else if a2 = a4 then y else a2) a3 y a5
      a6 := by
  have hN := summ_neg _ _ _ _ _ _ _ h
  have hc := summ_chmin _ (-y) _ _ _ _ _ _ hN (inr_neg L hR) (by omega) (by omega)
  have hc2 := summ_neg _ _ _ _ _ _ _ hc
  have eq : ((L.map (- ·)).map (min · (-y))).map (- ·) = L.map (max · y) := by
    rw [List.map_map, List.map_map]; apply List.map_congr_left; intro a _
    show -(min (-a) (-y)) = max a y; omega
  rw [eq] at hc2
  have e1 : (-a4 = -a1) = (a1 = a4) := by apply propext; omega
  have e2 : (-a4 = -a2) = (a2 = a4) := by apply propext; omega
  simp only [e1, e2] at hc2
  convert hc2 using 1 <;> (try split_ifs) <;> omega

end Proofs.Cpp.SegmentTreeBeatsMath
/-! # The tree of segment tree beats as functions of the node index -/

namespace Proofs.Cpp.SegmentTreeBeatsMath

/-- The nine arrays of the class as functions of the node index. -/
structure BS where
  mx : Nat → Int
  sx : Nat → Int
  cx : Nat → Int
  mn : Nat → Int
  sn : Nat → Int
  cn : Nat → Int
  len : Nat → Int
  la : Nat → Int
  lv : Nat → Int

/-- The pending operations of an inner node on a value of its children: add, then clamp to `[mn, mx]`. -/
def tau (s : BS) (k : Nat) (v : Int) : Int := max (s.mn k) (min (s.mx k) (v + s.la k))

/-- The values of the real leaves below node `k` of height `h` whose first leaf is `lo`, as seen at `k`. -/
def T (s : BS) (n : Nat) : Nat → Nat → Nat → List Int
  | 0, k, lo => if lo < n then [s.mx k] else []
  | h + 1, k, lo => (T s n h (2 * k + 1) lo ++ T s n h (2 * k + 2) (lo + 2 ^ h)).map (tau s k)

/-- `j` is in the subtree of height `h` rooted at `k`. -/
def Sub : Nat → Nat → Nat → Prop
  | 0, k, j => j = k
  | h + 1, k, j => j = k ∨ Sub h (2 * k + 1) j ∨ Sub h (2 * k + 2) j

/-- Two states agree at node `j`. -/
def AgreeAt (s t : BS) (j : Nat) : Prop :=
  s.mx j = t.mx j ∧ s.sx j = t.sx j ∧ s.cx j = t.cx j ∧ s.mn j = t.mn j ∧ s.sn j = t.sn j ∧ s.cn j = t.cn j ∧
    s.len j = t.len j ∧ s.la j = t.la j ∧ s.lv j = t.lv j

theorem T_frame (s t : BS) (n : Nat) : ∀ h k lo, (∀ j, Sub h k j → AgreeAt s t j) → T s n h k lo = T t n h k lo := by
  intro h
  induction h with
  | zero => intro k lo hA; have := hA k rfl; simp [T, this.1]
  | succ h ih =>
    intro k lo hA
    have hk := hA k (Or.inl rfl)
    simp only [T]
    rw [ih (2 * k + 1) lo (fun j hj => hA j (Or.inr (Or.inl hj))),
      ih (2 * k + 2) _ (fun j hj => hA j (Or.inr (Or.inr hj)))]
    congr 1
    funext v; simp [tau, hk.1, hk.2.2.2.1, hk.2.2.2.2.2.2.2.1]

theorem sub_ge : ∀ h k j, Sub h k j → k ≤ j := by
  intro h
  induction h with
  | zero => intro k j hj; simp [Sub] at hj; omega
  | succ h ih =>
    intro k j hj
    rcases hj with rfl | hj | hj
    · exact le_refl _
    · have := ih _ _ hj; omega
    · have := ih _ _ hj; omega

end Proofs.Cpp.SegmentTreeBeatsMath
namespace Proofs.Cpp.SegmentTreeBeatsMath

def upF (f : Nat → Int) (k : Nat) (v : Int) : Nat → Int := fun j => if j = k then v else f j

/-- `update_node_max(k, x)`. -/
def unm (s : BS) (k : Nat) (x : Int) : BS :=
  let s1 : BS := if s.mx k = s.mn k then { s with mx := upF s.mx k x, mn := upF s.mn k x }
    else if s.mx k = s.sn k then { s with mx := upF s.mx k x, sn := upF s.sn k x }
    else { s with mx := upF s.mx k x }
  if s.lv k ≠ INF ∧ x < s.lv k then { s1 with lv := upF s.lv k x } else s1

/-- `update_node_min(k, x)`. -/
def unmin (s : BS) (k : Nat) (x : Int) : BS :=
  let s1 : BS := if s.mx k = s.mn k then { s with mx := upF s.mx k x, mn := upF s.mn k x }
    else if s.sx k = s.mn k then { s with mn := upF s.mn k x, sx := upF s.sx k x }
    else { s with mn := upF s.mn k x }
  if s.lv k ≠ INF ∧ s.lv k < x then { s1 with lv := upF s.lv k x } else s1

/-- `add_all(k, x)`. -/
def addAll (s : BS) (k : Nat) (x : Int) : BS :=
  { s with mx := upF s.mx k (s.mx k + x),
           sx := if s.sx k ≠ -INF then upF s.sx k (s.sx k + x) else s.sx,
           mn := upF s.mn k (s.mn k + x),
           sn := if s.sn k ≠ INF then upF s.sn k (s.sn k + x) else s.sn,
           la := if s.lv k = INF then upF s.la k (s.la k + x) else s.la,
           lv := if s.lv k = INF then s.lv else upF s.lv k (s.lv k + x) }

/-- `update_all(k, x)`. -/
def updAll (s : BS) (k : Nat) (x : Int) : BS :=
  { s with mx := upF s.mx k x, sx := upF s.sx k (-INF), mn := upF s.mn k x, sn := upF s.sn k INF,
           cx := upF s.cx k (s.len k), cn := upF s.cn k (s.len k), lv := upF s.lv k x, la := upF s.la k 0 }

/-- `update(k)`. -/
def upd (s : BS) (k : Nat) : BS :=
  let a := 2 * k + 1
  let b := 2 * k + 2
  let M := combMax (s.mx a) (s.sx a) (s.cx a) (s.mx b) (s.sx b) (s.cx b)
  let N := combMin (s.mn a) (s.sn a) (s.cn a) (s.mn b) (s.sn b) (s.cn b)
  { s with mx := upF s.mx k M.1, sx := upF s.sx k M.2.1, cx := upF s.cx k M.2.2,
           mn := upF s.mn k N.1, sn := upF s.sn k N.2.1, cn := upF s.cn k N.2.2 }

/-- The caps of `push(k)` on child `c`. -/
def caps (s : BS) (k c : Nat) : BS :=
  let s1 := if s.mx k < s.mx c then unm s c (s.mx k) else s
  if s1.mn c < s1.mn k then unmin s1 c (s1.mn k) else s1

/-- `push(k)` on an inner node. -/
def setLv (s : BS) (k : Nat) (v : Int) : BS := { s with lv := upF s.lv k v }
def setLa (s : BS) (k : Nat) (v : Int) : BS := { s with la := upF s.la k v }

def push (s : BS) (k : Nat) : BS :=
  if s.lv k ≠ INF then
    setLv (updAll (updAll s (2 * k + 1) (s.lv k)) (2 * k + 2) (s.lv k)) k INF
  else
    let s1 := if s.la k ≠ 0 then
      setLa (addAll (addAll s (2 * k + 1) (s.la k)) (2 * k + 2) (s.la k)) k 0 else s
    caps (caps s1 k (2 * k + 1)) k (2 * k + 2)

/-! ## The invariant -/

def SummK (s : BS) (k : Nat) (L : List Int) : Prop := Summ L (s.mx k) (s.sx k) (s.cx k) (s.mn k) (s.sn k) (s.cn k)

/-- The pending tags of an inner node `k` agree with a child's values `L` (before the tags). -/
def ChildOK (s : BS) (k : Nat) (L0 : List Int) : Prop :=
  let L := L0.map (· + s.la k)
  (s.mx k < lmax L → smax L < s.mx k) ∧ (lmin L < s.mn k → s.mn k < smin L) ∧
    (s.mx k = s.mn k → lmax L = lmin L ∨ L = [])

/-- The tree invariant below node `k` of height `h` with first leaf `lo` (of `n` real leaves). -/
def Inv (s : BS) (n : Nat) : Nat → Nat → Nat → Prop
  | 0, k, lo => SummK s k (T s n 0 k lo) ∧ s.len k = 1
  | h + 1, k, lo => Inv s n h (2 * k + 1) lo ∧ Inv s n h (2 * k + 2) (lo + 2 ^ h) ∧
      SummK s k (T s n (h + 1) k lo) ∧ s.len k = 2 ^ (h + 1) ∧
      (n < lo + 2 ^ (h + 1) → s.la k = 0 ∧ s.lv k = INF) ∧
      (s.lv k ≠ INF → s.mx k = s.lv k ∧ s.mn k = s.lv k ∧ s.la k = 0 ∧ -INF < s.lv k) ∧
      (s.lv k = INF → ChildOK s k (T s n h (2 * k + 1) lo) ∧ ChildOK s k (T s n h (2 * k + 2) (lo + 2 ^ h)))

/-- All values with the pending adds of any number of ancestors (the offsets `O`) stay within `B`. -/
def Safe (s : BS) (n : Nat) (B : Int) : Nat → Nat → Nat → List Int → Prop
  | 0, k, lo, O => ∀ o ∈ O, ∀ v ∈ T s n 0 k lo, |v + o| ≤ B
  | h + 1, k, lo, O => (∀ o ∈ O, ∀ v ∈ T s n (h + 1) k lo, |v + o| ≤ B) ∧
      (s.lv k = INF → Safe s n B h (2 * k + 1) lo (0 :: O.map (· + s.la k)) ∧
        Safe s n B h (2 * k + 2) (lo + 2 ^ h) (0 :: O.map (· + s.la k)))

end Proofs.Cpp.SegmentTreeBeatsMath
namespace Proofs.Cpp.SegmentTreeBeatsMath

theorem sub_child1 (h k j : Nat) (hj : Sub h (2 * k + 1) j) : Sub (h + 1) k j := Or.inr (Or.inl hj)
theorem sub_child2 (h k j : Nat) (hj : Sub h (2 * k + 2) j) : Sub (h + 1) k j := Or.inr (Or.inr hj)

theorem inv_frame (s t : BS) (n : Nat) : ∀ h k lo, (∀ j, Sub h k j → AgreeAt s t j) → Inv s n h k lo →
    Inv t n h k lo := by
  intro h
  induction h with
  | zero =>
    intro k lo hA hI
    have hk := hA k rfl
    obtain ⟨h1, h2⟩ := hI
    rw [T_frame s t n 0 k lo hA] at h1
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, -, -⟩ := hk
    show SummK t k _ ∧ _
    unfold SummK at *; rw [← a1, ← a2, ← a3, ← a4, ← a5, ← a6]
    exact ⟨h1, by rw [← a7]; exact h2⟩
  | succ h ih =>
    intro k lo hA hI
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
    have hk := hA k (Or.inl rfl)
    have f1 := T_frame s t n h (2 * k + 1) lo (fun j hj => hA j (sub_child1 h k j hj))
    have f2 := T_frame s t n h (2 * k + 2) (lo + 2 ^ h) (fun j hj => hA j (sub_child2 h k j hj))
    have f0 := T_frame s t n (h + 1) k lo hA
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hk
    refine ⟨ih _ _ (fun j hj => hA j (sub_child1 h k j hj)) i1, ih _ _ (fun j hj => hA j (sub_child2 h k j hj)) i2,
      ?_, by rw [← a7]; exact i4, by rw [← a8, ← a9]; exact i5, ?_, ?_⟩
    · unfold SummK at *; rw [← f0, ← a1, ← a2, ← a3, ← a4, ← a5, ← a6]; exact i3
    · rw [← a1, ← a4, ← a8, ← a9]; exact i6
    · rw [← f1, ← f2]; unfold ChildOK; rw [← a1, ← a4, ← a8, ← a9]; exact i7

/-- A state that changes only node `k` agrees with the old one below the children of `k`. -/
theorem agree_upF_child (s t : BS) (h k c : Nat) (hc : k < c)
    (hagree : ∀ j, j ≠ k → AgreeAt s t j) : ∀ j, Sub h c j → AgreeAt s t j :=
  fun j hj => hagree j (by have := sub_ge h c j hj; omega)

theorem upd_agree (s : BS) (k : Nat) : ∀ j, j ≠ k → AgreeAt s (upd s k) j := by
  intro j hj
  simp [AgreeAt, upd, upF, Function.update, hj]

theorem clamp_id (lo hi v : Int) (h1 : lo ≤ v) (h2 : v ≤ hi) : max lo (min hi (v + 0)) = v := by omega

theorem inv_summ (s : BS) (n : Nat) : ∀ h k lo, Inv s n h k lo → SummK s k (T s n h k lo)
  | 0, _, _, hI => hI.1
  | _ + 1, _, _, hI => hI.2.2.1

theorem inv_len (s : BS) (n : Nat) : ∀ h k lo, Inv s n h k lo → s.len k = 2 ^ h
  | 0, _, _, hI => by simpa using hI.2
  | _ + 1, _, _, hI => hI.2.2.2.1

theorem map_clamp_id (L : List Int) (lo hi : Int) (h : ∀ v ∈ L, lo ≤ v ∧ v ≤ hi) :
    L.map (fun v => max lo (min hi (v + 0))) = L := by
  conv_rhs => rw [← List.map_id L]
  apply List.map_congr_left; intro v hv; have := h v hv; simp; omega

theorem upd_spec (s : BS) (n h k lo : Nat) (hc1 : Inv s n h (2 * k + 1) lo) (hc2 : Inv s n h (2 * k + 2) (lo + 2 ^ h))
    (hR1 : InR (T s n h (2 * k + 1) lo)) (hR2 : InR (T s n h (2 * k + 2) (lo + 2 ^ h)))
    (hla : s.la k = 0) (hlv : s.lv k = INF) (hlen : s.len k = 2 ^ (h + 1)) :
    Inv (upd s k) n (h + 1) k lo ∧
      T (upd s k) n (h + 1) k lo = T s n h (2 * k + 1) lo ++ T s n h (2 * k + 2) (lo + 2 ^ h) := by
  have hag := upd_agree s k
  have g1 := agree_upF_child s (upd s k) h k (2 * k + 1) (by omega) hag
  have g2 := agree_upF_child s (upd s k) h k (2 * k + 2) (by omega) hag
  have t1 := T_frame s (upd s k) n h _ lo g1
  have t2 := T_frame s (upd s k) n h _ (lo + 2 ^ h) g2
  set A := T s n h (2 * k + 1) lo
  set B := T s n h (2 * k + 2) (lo + 2 ^ h)
  have sA := inv_summ s n h _ _ hc1
  have sB := inv_summ s n h _ _ hc2
  have hs := summ_append A B _ _ _ _ _ _ _ _ _ _ _ _ sA sB
  have hR : InR (A ++ B) := fun v hv => by
    rcases List.mem_append.mp hv with h | h; exacts [hR1 v h, hR2 v h]
  have hT : T (upd s k) n (h + 1) k lo = A ++ B := by
    simp only [T]
    rw [← t1, ← t2]
    have e1 : (upd s k).mx k = lmax (A ++ B) := by simp [upd, upF]; exact hs.mx
    have e2 : (upd s k).mn k = lmin (A ++ B) := by simp [upd, upF]; exact hs.mn
    have e3 : (upd s k).la k = 0 := by simp [upd, hla]
    have : tau (upd s k) k = fun v => max (lmin (A ++ B)) (min (lmax (A ++ B)) (v + 0)) := by
      funext v; simp only [tau, e1, e2, e3]
    rw [this, map_clamp_id]
    intro v hv; exact ⟨lmin_le _ v hv, lmax_ge _ v hv⟩
  refine ⟨⟨inv_frame s _ n h _ _ g1 hc1, inv_frame s _ n h _ _ g2 hc2, ?_, ?_, ?_, ?_, ?_⟩, hT⟩
  · unfold SummK; rw [hT]; simpa [upd, upF] using hs
  · simpa [upd] using hlen
  · intro _; simp [upd, hla, hlv]
  · intro h; simp [upd, hlv] at h
  · intro _
    rw [← t1, ← t2]
    have e1 : (upd s k).mx k = lmax (A ++ B) := by simp [upd, upF]; exact hs.mx
    have e2 : (upd s k).mn k = lmin (A ++ B) := by simp [upd, upF]; exact hs.mn
    have e3 : (upd s k).la k = 0 := by simp [upd, hla]
    have mA : A.map (· + 0) = A := by simp
    have mB : B.map (· + 0) = B := by simp
    unfold ChildOK; simp only [e1, e2, e3, mA, mB]
    rw [lmax_append, lmin_append]
    refine ⟨⟨fun h => by omega, fun h => by omega, fun he => ?_⟩, ⟨fun h => by omega, fun h => by omega, fun he => ?_⟩⟩
    · by_cases hA : A = []
      · exact Or.inr hA
      · left; have := lmin_le_lmax A hR1 hA; omega
    · by_cases hB : B = []
      · exact Or.inr hB
      · left; have := lmin_le_lmax B hR2 hB; omega

end Proofs.Cpp.SegmentTreeBeatsMath
namespace Proofs.Cpp.SegmentTreeBeatsMath

theorem unm_agree (s : BS) (k : Nat) (x : Int) : ∀ j, j ≠ k → AgreeAt s (unm s k x) j := by
  intro j hj
  unfold unm
  split_ifs <;> simp [AgreeAt, upF, Function.update, hj]

theorem unm_fields (s : BS) (k : Nat) (x : Int) :
    (unm s k x).mx k = x ∧ (unm s k x).sx k = s.sx k ∧ (unm s k x).cx k = s.cx k ∧
    (unm s k x).mn k = (if s.mx k = s.mn k then x else s.mn k) ∧
    (unm s k x).sn k = (if s.mx k = s.mn k then s.sn k else if s.mx k = s.sn k then x else s.sn k) ∧
    (unm s k x).cn k = s.cn k ∧ (unm s k x).len k = s.len k ∧ (unm s k x).la k = s.la k ∧
    (unm s k x).lv k = (if s.lv k ≠ INF ∧ x < s.lv k then x else s.lv k) := by
  by_cases h1 : s.mx k = s.mn k
  · by_cases h3 : s.lv k ≠ INF ∧ x < s.lv k
    · simp only [unm, if_pos h1, if_pos h3, upF, Function.update_self]; simp [h1, h3]
    · simp only [unm, if_pos h1, if_neg h3, upF, Function.update_self]; simp [h1, h3]
  · by_cases h2 : s.mx k = s.sn k
    · by_cases h3 : s.lv k ≠ INF ∧ x < s.lv k
      · simp only [unm, if_neg h1, if_pos h2, if_pos h3, upF, Function.update_self]; simp [h1, h3]
      · simp only [unm, if_neg h1, if_pos h2, if_neg h3, upF, Function.update_self]; simp [h1, h3]
    · by_cases h3 : s.lv k ≠ INF ∧ x < s.lv k
      · simp only [unm, if_neg h1, if_neg h2, if_pos h3, upF, Function.update_self]; simp [h1, h2, h3]
      · simp only [unm, if_neg h1, if_neg h2, if_neg h3, upF, Function.update_self]; simp [h1, h2, h3]

theorem summK_chmin (s : BS) (k : Nat) (x : Int) (L : List Int) (hS : SummK s k L) (hR : InR L)
    (h1 : s.sx k < x) (h2 : x < s.mx k) : SummK (unm s k x) k (L.map (min · x)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, -, -, -⟩ := unm_fields s k x
  unfold SummK; rw [f1, f2, f3, f4, f5, f6]
  exact summ_chmin L x _ _ _ _ _ _ hS hR h1 h2

theorem unm_leaf (s : BS) (n k lo : Nat) (x : Int) (hI : Inv s n 0 k lo) (hR : InR (T s n 0 k lo))
    (h1 : s.sx k < x) (h2 : x < s.mx k) :
    Inv (unm s k x) n 0 k lo ∧ T (unm s k x) n 0 k lo = (T s n 0 k lo).map (min · x) := by
  obtain ⟨f1, -, -, -, -, -, f7, -, -⟩ := unm_fields s k x
  have hT : T (unm s k x) n 0 k lo = (T s n 0 k lo).map (min · x) := by
    simp only [T]; split_ifs <;> simp [f1]; omega
  refine ⟨⟨?_, by rw [f7]; exact hI.2⟩, hT⟩
  rw [hT]; exact summK_chmin s k x _ hI.1 hR h1 h2

theorem smax_mem_of (L : List Int) (hR : InR L) (h : -INF < smax L) : smax L ∈ L ∧ smax L < lmax L := by
  unfold smax at *
  by_cases hf : L.filter (· < lmax L) = []
  · rw [hf] at h; simp [lmax_nil] at h
  · have hm := lmax_mem _ hf (fun v hv => hR v (List.mem_filter.mp hv).1)
    exact ⟨(List.mem_filter.mp hm).1, by simpa using (List.mem_filter.mp hm).2⟩

theorem cap_lemma (L T : List Int) (mn mx x : Int) (hsub : ∀ p ∈ L, max mn (min mx p) ∈ T)
    (hmxT : mx = lmax T) (hlt : mn < mx) (hx1 : smax T < x) (hx2 : x < mx)
    (hold : mx < lmax L → smax L < mx) (hRL : InR L) : x < lmax L → smax L < x := by
  intro hq
  by_contra hc
  have hp : -INF < smax L := by
    have := smax_ge_ninf T; omega
  obtain ⟨pm, plt⟩ := smax_mem_of L hRL hp
  have hcT := hsub _ pm
  by_cases hcm : max mn (min mx (smax L)) < mx
  · have := elem_le_smax T _ hcT (by omega)
    omega
  · have : mx ≤ smax L := by omega
    have := hold (by omega)
    omega

theorem mem_T_of_child (s : BS) (k : Nat) (A B : List Int) (p : Int) (hp : p ∈ A.map (· + s.la k) ∨ p ∈ B.map (· + s.la k)) :
    max (s.mn k) (min (s.mx k) p) ∈ (A ++ B).map (tau s k) := by
  rcases hp with hp | hp <;> obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp <;>
    exact List.mem_map.mpr ⟨w, by simp [hw], rfl⟩

theorem childok_unm (L Tk : List Int) (mn mx x : Int) (hL : InR L) (hRT : InR Tk) (hTne : Tk ≠ [])
    (hsub : ∀ p ∈ L, max mn (min mx p) ∈ Tk) (hmx : mx = lmax Tk) (hmn : mn = lmin Tk) (hsx : smax Tk < x)
    (hx2 : x < mx) (hmxI : mx < INF)
    (old : (mx < lmax L → smax L < mx) ∧ (lmin L < mn → mn < smin L) ∧ (mx = mn → lmax L = lmin L ∨ L = [])) :
    (x < lmax L → smax L < x) ∧ (lmin L < (if mx = mn then x else mn) → (if mx = mn then x else mn) < smin L) ∧
      (x = (if mx = mn then x else mn) → lmax L = lmin L ∨ L = []) := by
  obtain ⟨o1, o2, o3⟩ := old
  have hsxI := smax_ge_ninf Tk
  by_cases hs : mx = mn
  · rw [if_pos hs]
    rcases o3 hs with hsing | hemp
    · refine ⟨fun _ => by rw [smax_single L hsing]; omega, fun _ => by rw [smin_single L hsing]; omega,
        fun _ => Or.inl hsing⟩
    · subst hemp
      exact ⟨fun h => by simp [lmax_nil] at h; omega, fun h => by simp [lmin_nil] at h; omega, fun _ => Or.inr rfl⟩
  · rw [if_neg hs]
    have hmns : mn ≤ smax Tk := by rw [hmn]; exact lmin_le_smax Tk hRT hTne (by rw [← hmx, ← hmn]; exact hs)
    have hlt : mn < mx := by
      have := lmin_le_lmax Tk hRT hTne; rw [← hmx, ← hmn] at this; omega
    exact ⟨cap_lemma L Tk mn mx x hsub hmx hlt hsx hx2 o1 hL, o2, fun h => by omega⟩

theorem unm_inner (s : BS) (n h k lo : Nat) (x : Int) (hI : Inv s n (h + 1) k lo) (hR : InR (T s n (h + 1) k lo))
    (hRA : s.lv k = INF → InR ((T s n h (2 * k + 1) lo).map (· + s.la k)))
    (hRB : s.lv k = INF → InR ((T s n h (2 * k + 2) (lo + 2 ^ h)).map (· + s.la k)))
    (h1 : s.sx k < x) (h2 : x < s.mx k) :
    Inv (unm s k x) n (h + 1) k lo ∧ T (unm s k x) n (h + 1) k lo = (T s n (h + 1) k lo).map (min · x) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := unm_fields s k x
  have hag := unm_agree s k x
  have g1 := agree_upF_child s (unm s k x) h k (2 * k + 1) (by omega) hag
  have g2 := agree_upF_child s (unm s k x) h k (2 * k + 2) (by omega) hag
  have t1 := T_frame s (unm s k x) n h _ lo g1
  have t2 := T_frame s (unm s k x) n h _ (lo + 2 ^ h) g2
  set A := T s n h (2 * k + 1) lo
  set B := T s n h (2 * k + 2) (lo + 2 ^ h)
  have hTk : T s n (h + 1) k lo = (A ++ B).map (tau s k) := rfl
  have hS := i3
  have hne : T s n (h + 1) k lo ≠ [] := by
    intro he; rw [he] at hS; have := hS.mx; have := hS.smx; simp [lmax_nil, smax, lmax] at *; omega
  have hmn : s.mn k ≤ s.mx k := by rw [hS.mx, hS.mn]; exact lmin_le_lmax _ hR hne
  have hmxI : s.mx k < INF := by rw [hS.mx]; exact (hR _ (lmax_mem _ hne hR)).2
  have hT : T (unm s k x) n (h + 1) k lo = (T s n (h + 1) k lo).map (min · x) := by
    simp only [T]
    rw [← t1, ← t2, List.map_map]
    apply List.map_congr_left
    intro v _
    simp only [Function.comp, tau, f1, f4, f8]
    split_ifs with hs
    · omega
    · have : s.mn k ≤ s.sx k := by
        rw [hS.mn, hS.smx]; exact lmin_le_smax _ hR hne (by rw [← hS.mx, ← hS.mn]; exact hs)
      omega
  refine ⟨⟨inv_frame s _ n h _ _ g1 i1, inv_frame s _ n h _ _ g2 i2, ?_, by rw [f7]; exact i4, ?_, ?_, ?_⟩, hT⟩
  · unfold SummK; rw [hT]; exact summK_chmin s k x _ i3 hR h1 h2
  · intro hp; obtain ⟨a, b⟩ := i5 hp
    exact ⟨by rw [f8]; exact a, by rw [f9, if_neg (fun hc => hc.1 b)]; exact b⟩
  · intro hlv
    rw [f9] at hlv
    split_ifs at hlv with hc
    · have := (i6 hc.1); rw [f1, f4, f9, f8, if_pos hc, if_pos (by omega)]; exact ⟨rfl, rfl, this.2.2.1, by have := smax_ge_ninf (T s n (h + 1) k lo); rw [← hS.smx] at this; omega⟩
    · rw [f1, f4, f9, f8, if_neg hc]
      have := i6 hlv
      exact absurd (show x < s.lv k by omega) (fun hx => hc ⟨hlv, hx⟩)
  · intro hlv
    rw [f9] at hlv
    have hlv0 : s.lv k = INF := by
      split_ifs at hlv with hc
      · omega
      · exact hlv
    obtain ⟨c1, c2⟩ := i7 hlv0
    rw [← t1, ← t2]
    unfold ChildOK at *
    rw [f1, f4, f8]
    have hsx : smax (T s n (h + 1) k lo) < x := by rw [← hS.smx]; exact h1
    exact ⟨childok_unm _ _ _ _ _ (hRA hlv0) hR hne (fun p hp => mem_T_of_child s k A B p (Or.inl hp)) hS.mx hS.mn hsx h2
        hmxI c1,
      childok_unm _ _ _ _ _ (hRB hlv0) hR hne (fun p hp => mem_T_of_child s k A B p (Or.inr hp)) hS.mx hS.mn hsx h2
        hmxI c2⟩

end Proofs.Cpp.SegmentTreeBeatsMath
namespace Proofs.Cpp.SegmentTreeBeatsMath

/-- The state of the negated values: maximum and minimum sides exchanged. -/
def negS (s : BS) : BS where
  mx := fun j => -s.mn j
  sx := fun j => -s.sn j
  cx := s.cn
  mn := fun j => -s.mx j
  sn := fun j => -s.sx j
  cn := s.cx
  len := s.len
  la := fun j => -s.la j
  lv := fun j => if s.lv j = INF then INF else -s.lv j

theorem negS_lv_inf (s : BS) (j : Nat) (h0 : s.lv j ≠ INF → -INF < s.lv j) : (negS s).lv j = INF ↔ s.lv j = INF := by
  simp only [negS]; split_ifs with h <;> simp [h]; have := h0 h; omega

/-- Every node of the subtree has values strictly inside the sentinels. -/
def AllInR (s : BS) (n : Nat) : Nat → Nat → Nat → Prop
  | 0, k, lo => InR (T s n 0 k lo)
  | h + 1, k, lo => InR (T s n (h + 1) k lo) ∧ AllInR s n h (2 * k + 1) lo ∧ AllInR s n h (2 * k + 2) (lo + 2 ^ h)

theorem allInR_top (s : BS) (n : Nat) : ∀ h k lo, AllInR s n h k lo → InR (T s n h k lo)
  | 0, _, _, h => h
  | _ + 1, _, _, h => h.1

theorem T_neg (s : BS) (n : Nat) : ∀ h k lo, Inv s n h k lo → AllInR s n h k lo →
    T (negS s) n h k lo = (T s n h k lo).map (- ·) := by
  intro h
  induction h with
  | zero =>
    intro k lo hI hR
    simp only [AllInR] at hR
    simp only [T]
    split_ifs with hlo
    · have hS := hI.1; simp only [T, if_pos hlo] at hS
      have e := hS.mx; have e2 := hS.mn
      have : lmax [s.mx k] = s.mx k := by have := (hR (s.mx k) (by simp [T, hlo])).1; simp [lmax]; omega
      have : lmin [s.mx k] = s.mx k := by have := (hR (s.mx k) (by simp [T, hlo])).2; simp [lmin]; omega
      simp [negS]; omega
    · rfl
  | succ h ih =>
    intro k lo hI hR
    obtain ⟨i1, i2, i3, -⟩ := hI
    obtain ⟨r0, r1, r2⟩ := hR
    show ((T (negS s) n h (2 * k + 1) lo ++ T (negS s) n h (2 * k + 2) (lo + 2 ^ h)).map (tau (negS s) k)) =
      ((T s n h (2 * k + 1) lo ++ T s n h (2 * k + 2) (lo + 2 ^ h)).map (tau s k)).map (- ·)
    rw [ih _ _ i1 r1, ih _ _ i2 r2, ← List.map_append, List.map_map, List.map_map]
    by_cases hne : T s n (h + 1) k lo = []
    · have : T s n h (2 * k + 1) lo ++ T s n h (2 * k + 2) (lo + 2 ^ h) = [] := by
        simpa [T] using hne
      rw [this]; rfl
    · have hmn : s.mn k ≤ s.mx k := by rw [i3.mx, i3.mn]; exact lmin_le_lmax _ r0 hne
      apply List.map_congr_left
      intro v _
      simp only [Function.comp, tau, negS]
      omega

end Proofs.Cpp.SegmentTreeBeatsMath
namespace Proofs.Cpp.SegmentTreeBeatsMath

theorem lmax_neg (L : List Int) : lmax L = -lmin (L.map (- ·)) := by
  have := lmin_neg (L.map (- ·)); rw [map_neg_neg] at this; omega

theorem smax_neg (L : List Int) : smax L = -smin (L.map (- ·)) := by
  have := smin_neg (L.map (- ·)); rw [map_neg_neg] at this; omega

theorem lmax_of_neg (L : List Int) : lmax (L.map (- ·)) = -lmin L := by rw [lmin_neg]; omega
theorem smax_of_neg (L : List Int) : smax (L.map (- ·)) = -smin L := by rw [smin_neg]; omega
theorem lmin_of_neg (L : List Int) : lmin (L.map (- ·)) = -lmax L := by rw [lmax_neg]; omega
theorem smin_of_neg (L : List Int) : smin (L.map (- ·)) = -smax L := by rw [smax_neg]; omega

theorem cap_lemma_min (L T : List Int) (mn mx y : Int) (hsub : ∀ p ∈ L, max mn (min mx p) ∈ T)
    (hmnT : mn = lmin T) (hlt : mn < mx) (hy1 : mn < y) (hy2 : y < smin T)
    (hold : lmin L < mn → mn < smin L) (hRL : InR L) : lmin L < y → y < smin L := by
  have c := cap_lemma (L.map (- ·)) (T.map (- ·)) (-mx) (-mn) (-y)
    (fun p hp => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
      have := hsub w hw
      have e : max (-mx) (min (-mn) (-w)) = -(max mn (min mx w)) := by omega
      rw [e]; exact List.mem_map.mpr ⟨_, this, rfl⟩)
    (by rw [lmax_of_neg]; omega) (by omega) (by rw [smax_of_neg]; omega) (by omega)
    (fun h => by rw [lmax_of_neg] at h; rw [smax_of_neg]; have := hold (by omega); omega) (inr_neg L hRL)
  rw [lmax_of_neg, smax_of_neg] at c
  intro h; have := c (by omega); omega

theorem unmin_agree (s : BS) (k : Nat) (x : Int) : ∀ j, j ≠ k → AgreeAt s (unmin s k x) j := by
  intro j hj
  unfold unmin
  split_ifs <;> simp [AgreeAt, upF, Function.update, hj]

theorem unmin_fields (s : BS) (k : Nat) (x : Int) :
    (unmin s k x).mx k = (if s.mx k = s.mn k then x else s.mx k) ∧
    (unmin s k x).sx k = (if s.mx k = s.mn k then s.sx k else if s.sx k = s.mn k then x else s.sx k) ∧
    (unmin s k x).cx k = s.cx k ∧ (unmin s k x).mn k = x ∧ (unmin s k x).sn k = s.sn k ∧
    (unmin s k x).cn k = s.cn k ∧ (unmin s k x).len k = s.len k ∧ (unmin s k x).la k = s.la k ∧
    (unmin s k x).lv k = (if s.lv k ≠ INF ∧ s.lv k < x then x else s.lv k) := by
  by_cases h1 : s.mx k = s.mn k
  · by_cases h3 : s.lv k ≠ INF ∧ s.lv k < x
    · simp only [unmin, if_pos h1, if_pos h3, upF, Function.update_self]; simp [h1, h3]
    · simp only [unmin, if_pos h1, if_neg h3, upF, Function.update_self]; simp [h1, h3]
  · by_cases h2 : s.sx k = s.mn k
    · by_cases h3 : s.lv k ≠ INF ∧ s.lv k < x
      · simp only [unmin, if_neg h1, if_pos h2, if_pos h3, upF, Function.update_self]; simp [h1, h3]
      · simp only [unmin, if_neg h1, if_pos h2, if_neg h3, upF, Function.update_self]; simp [h1, h3]
    · by_cases h3 : s.lv k ≠ INF ∧ s.lv k < x
      · simp only [unmin, if_neg h1, if_neg h2, if_pos h3, upF, Function.update_self]; simp [h1, h2, h3]
      · simp only [unmin, if_neg h1, if_neg h2, if_neg h3, upF, Function.update_self]; simp [h1, h2, h3]

theorem summK_chmax (s : BS) (k : Nat) (x : Int) (L : List Int) (hS : SummK s k L) (hR : InR L)
    (h1 : s.mn k < x) (h2 : x < s.sn k) : SummK (unmin s k x) k (L.map (max · x)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, -, -, -⟩ := unmin_fields s k x
  unfold SummK; rw [f1, f2, f3, f4, f5, f6]
  exact summ_chmax L x _ _ _ _ _ _ hS hR h1 h2

theorem unmin_leaf (s : BS) (n k lo : Nat) (x : Int) (hI : Inv s n 0 k lo) (hR : InR (T s n 0 k lo))
    (h1 : s.mn k < x) (h2 : x < s.sn k) :
    Inv (unmin s k x) n 0 k lo ∧ T (unmin s k x) n 0 k lo = (T s n 0 k lo).map (max · x) := by
  obtain ⟨f1, -, -, -, -, -, f7, -, -⟩ := unmin_fields s k x
  have hS := hI.1
  have hT : T (unmin s k x) n 0 k lo = (T s n 0 k lo).map (max · x) := by
    simp only [T] at hS ⊢
    split_ifs with hlo
    · rw [if_pos hlo] at hS
      have e1 := hS.mx; have e2 := hS.mn
      have : lmax [s.mx k] = s.mx k := by have := (hR (s.mx k) (by simp [T, hlo])).1; simp [lmax]; omega
      have : lmin [s.mx k] = s.mx k := by have := (hR (s.mx k) (by simp [T, hlo])).2; simp [lmin]; omega
      rw [f1, if_pos (by omega)]; simp; omega
    · rfl
  refine ⟨⟨?_, by rw [f7]; exact hI.2⟩, hT⟩
  rw [hT]; exact summK_chmax s k x _ hI.1 hR h1 h2

theorem childok_unmin (L Tk : List Int) (mn mx y : Int) (hL : InR L) (hRT : InR Tk) (hTne : Tk ≠ [])
    (hsub : ∀ p ∈ L, max mn (min mx p) ∈ Tk) (hmx : mx = lmax Tk) (hmn : mn = lmin Tk) (hsn : y < smin Tk)
    (hy1 : mn < y) (hmnI : -INF < mn)
    (old : (mx < lmax L → smax L < mx) ∧ (lmin L < mn → mn < smin L) ∧ (mx = mn → lmax L = lmin L ∨ L = [])) :
    ((if mx = mn then y else mx) < lmax L → smax L < (if mx = mn then y else mx)) ∧ (lmin L < y → y < smin L) ∧
      ((if mx = mn then y else mx) = y → lmax L = lmin L ∨ L = []) := by
  obtain ⟨o1, o2, o3⟩ := old
  have hsnI : smin Tk ≤ INF := lmin_le_inf _
  by_cases hs : mx = mn
  · rw [if_pos hs]
    rcases o3 hs with hsing | hemp
    · refine ⟨fun _ => by rw [smax_single L hsing]; omega, fun _ => by rw [smin_single L hsing]; omega,
        fun _ => Or.inl hsing⟩
    · subst hemp
      exact ⟨fun h => by simp [lmax_nil] at h; omega, fun h => by simp [lmin_nil] at h; omega,
        fun _ => Or.inr rfl⟩
  · rw [if_neg hs]
    obtain ⟨-, -, f3⟩ := smin_facts Tk hRT hTne (by rw [← hmx, ← hmn]; exact hs)
    have hlt : mn < mx := by
      have := lmin_le_lmax Tk hRT hTne; rw [← hmx, ← hmn] at this; omega
    exact ⟨o1, cap_lemma_min L Tk mn mx y hsub hmn hlt hy1 hsn o2 hL, fun h => by omega⟩

theorem unmin_inner (s : BS) (n h k lo : Nat) (x : Int) (hI : Inv s n (h + 1) k lo) (hR : InR (T s n (h + 1) k lo))
    (hRA : s.lv k = INF → InR ((T s n h (2 * k + 1) lo).map (· + s.la k)))
    (hRB : s.lv k = INF → InR ((T s n h (2 * k + 2) (lo + 2 ^ h)).map (· + s.la k)))
    (h1 : s.mn k < x) (h2 : x < s.sn k) :
    Inv (unmin s k x) n (h + 1) k lo ∧ T (unmin s k x) n (h + 1) k lo = (T s n (h + 1) k lo).map (max · x) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := unmin_fields s k x
  have hag := unmin_agree s k x
  have g1 := agree_upF_child s (unmin s k x) h k (2 * k + 1) (by omega) hag
  have g2 := agree_upF_child s (unmin s k x) h k (2 * k + 2) (by omega) hag
  have t1 := T_frame s (unmin s k x) n h _ lo g1
  have t2 := T_frame s (unmin s k x) n h _ (lo + 2 ^ h) g2
  set A := T s n h (2 * k + 1) lo
  set B := T s n h (2 * k + 2) (lo + 2 ^ h)
  have hS := i3
  have hne : T s n (h + 1) k lo ≠ [] := by
    intro he; rw [he] at hS; have := hS.mn; have := hS.smn; simp [lmin_nil, smin, lmin] at *; omega
  have hmn : s.mn k ≤ s.mx k := by rw [hS.mx, hS.mn]; exact lmin_le_lmax _ hR hne
  have hmnI : -INF < s.mn k := by rw [hS.mn]; exact (hR _ (lmin_mem _ hne hR)).1
  have hT : T (unmin s k x) n (h + 1) k lo = (T s n (h + 1) k lo).map (max · x) := by
    simp only [T]
    rw [← t1, ← t2, List.map_map]
    apply List.map_congr_left
    intro v _
    simp only [Function.comp, tau, f1, f4, f8]
    split_ifs with hs
    · omega
    · obtain ⟨-, -, f3⟩ := smin_facts _ hR hne (by rw [← hS.mx, ← hS.mn]; exact hs)
      rw [← hS.smn, ← hS.mx] at f3
      omega
  refine ⟨⟨inv_frame s _ n h _ _ g1 i1, inv_frame s _ n h _ _ g2 i2, ?_, by rw [f7]; exact i4, ?_, ?_, ?_⟩, hT⟩
  · unfold SummK; rw [hT]; exact summK_chmax s k x _ i3 hR h1 h2
  · intro hp; obtain ⟨a, b⟩ := i5 hp
    exact ⟨by rw [f8]; exact a, by rw [f9, if_neg (fun hc => hc.1 b)]; exact b⟩
  · intro hlv
    rw [f9] at hlv
    split_ifs at hlv with hc
    · have := (i6 hc.1); rw [f1, f4, f9, f8, if_pos hc, if_pos (by omega)]
      exact ⟨rfl, rfl, this.2.2.1, by omega⟩
    · rw [f1, f4, f9, f8, if_neg hc]
      have := i6 hlv
      exact absurd (show s.lv k < x by omega) (fun hx => hc ⟨hlv, hx⟩)
  · intro hlv
    rw [f9] at hlv
    have hsnI : s.sn k ≤ INF := by rw [hS.smn]; exact lmin_le_inf _
    have hlv0 : s.lv k = INF := by
      split_ifs at hlv with hc
      · omega
      · exact hlv
    obtain ⟨c1, c2⟩ := i7 hlv0
    rw [← t1, ← t2]
    unfold ChildOK at *
    rw [f1, f4, f8]
    have hsn : x < smin (T s n (h + 1) k lo) := by rw [← hS.smn]; exact h2
    exact ⟨childok_unmin _ _ _ _ _ (hRA hlv0) hR hne (fun p hp => mem_T_of_child s k A B p (Or.inl hp)) hS.mx hS.mn hsn h1
        hmnI c1,
      childok_unmin _ _ _ _ _ (hRB hlv0) hR hne (fun p hp => mem_T_of_child s k A B p (Or.inr hp)) hS.mx hS.mn hsn h1
        hmnI c2⟩

end Proofs.Cpp.SegmentTreeBeatsMath
namespace Proofs.Cpp.SegmentTreeBeatsMath

theorem T_length (s : BS) (n : Nat) : ∀ h k lo, (T s n h k lo).length = min (2 ^ h) (n - lo) := by
  intro h
  induction h with
  | zero => intro k lo; simp only [T]; split_ifs <;> simp <;> omega
  | succ h ih =>
    intro k lo; simp only [T, List.length_map, List.length_append, ih, pow_succ]
    have := Nat.two_pow_pos h
    omega

theorem addAll_agree (s : BS) (k : Nat) (x : Int) : ∀ j, j ≠ k → AgreeAt s (addAll s k x) j := by
  intro j hj
  simp only [AgreeAt, addAll]
  split_ifs <;> simp [upF, Function.update, hj]

theorem addAll_fields (s : BS) (k : Nat) (x : Int) :
    (addAll s k x).mx k = s.mx k + x ∧ (addAll s k x).sx k = (if s.sx k = -INF then -INF else s.sx k + x) ∧
    (addAll s k x).cx k = s.cx k ∧ (addAll s k x).mn k = s.mn k + x ∧
    (addAll s k x).sn k = (if s.sn k = INF then INF else s.sn k + x) ∧ (addAll s k x).cn k = s.cn k ∧
    (addAll s k x).len k = s.len k ∧
    (addAll s k x).la k = (if s.lv k = INF then s.la k + x else s.la k) ∧
    (addAll s k x).lv k = (if s.lv k = INF then INF else s.lv k + x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [addAll] <;> (try split_ifs) <;> simp_all [upF]

theorem summK_add (s : BS) (k : Nat) (x : Int) (L : List Int) (hS : SummK s k L) (hne : L ≠ []) (hR : InR L)
    (hR' : InR (L.map (· + x))) : SummK (addAll s k x) k (L.map (· + x)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, -, -, -⟩ := addAll_fields s k x
  unfold SummK; rw [f1, f2, f3, f4, f5, f6]
  exact summ_add L x _ _ _ _ _ _ hS hne hR hR'

theorem addAll_leaf (s : BS) (n k lo : Nat) (x : Int) (hI : Inv s n 0 k lo) (hlo : lo < n)
    (hR : InR (T s n 0 k lo)) (hR' : InR ((T s n 0 k lo).map (· + x))) :
    Inv (addAll s k x) n 0 k lo ∧ T (addAll s k x) n 0 k lo = (T s n 0 k lo).map (· + x) := by
  obtain ⟨f1, -, -, -, -, -, f7, -, -⟩ := addAll_fields s k x
  have hT : T (addAll s k x) n 0 k lo = (T s n 0 k lo).map (· + x) := by simp [T, hlo, f1]
  refine ⟨⟨?_, by rw [f7]; exact hI.2⟩, hT⟩
  rw [hT]; exact summK_add s k x _ hI.1 (by simp [T, hlo]) hR hR'

/-- Shifting a child list keeps the tag conditions when the shift is applied to the tags too. -/
theorem childok_shift (L : List Int) (mx mn x : Int) (hL : InR L) (hL' : InR (L.map (· + x)))
    (hmx : -INF < mx + x) (hmn : mn + x < INF)
    (old : (mx < lmax L → smax L < mx) ∧ (lmin L < mn → mn < smin L) ∧ (mx = mn → lmax L = lmin L ∨ L = [])) :
    (mx + x < lmax (L.map (· + x)) → smax (L.map (· + x)) < mx + x) ∧
      (lmin (L.map (· + x)) < mn + x → mn + x < smin (L.map (· + x))) ∧
      (mx + x = mn + x → lmax (L.map (· + x)) = lmin (L.map (· + x)) ∨ L.map (· + x) = []) := by
  obtain ⟨o1, o2, o3⟩ := old
  by_cases hne : L = []
  · subst hne; simp [lmax_nil, lmin_nil]; omega
  obtain ⟨a1, a2, -⟩ := max_side_add L x hne hL hL'
  have hN := inr_neg L hL
  have hneN : L.map (- ·) ≠ [] := by simpa using hne
  have eq : (L.map (· + x)).map (- ·) = (L.map (- ·)).map (· + -x) := by
    rw [List.map_map, List.map_map]; apply List.map_congr_left; intro a _; show -(a + x) = -a + -x; ring
  have hRN' : InR ((L.map (- ·)).map (· + -x)) := by rw [← eq]; exact inr_neg _ hL'
  obtain ⟨b1, b2, -⟩ := max_side_add (L.map (- ·)) (-x) hneN hN hRN'
  rw [← eq] at b1 b2
  simp only [lmax_of_neg, smax_of_neg] at b1 b2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [a1] at h; rw [a2]
    have h1 : mx < lmax L := by omega
    have h2 := o1 h1
    split_ifs with hc
    · exact hmx
    · omega
  · have : lmin (L.map (· + x)) = lmin L + x := by omega
    rw [this] at h; have := o2 (by omega)
    have : smin (L.map (· + x)) = (if smin L = INF then INF else smin L + x) := by
      by_cases hc : smin L = INF
      · rw [if_pos (by omega)] at b2; rw [if_pos hc]; omega
      · rw [if_neg (by omega)] at b2; rw [if_neg hc]; omega
    rw [this]; split_ifs with hc
    · unfold INF at *; omega
    · omega
  · rcases o3 (by omega) with hs | hs
    · left; rw [a1]; have : lmin (L.map (· + x)) = lmin L + x := by omega
      rw [this]; omega
    · exact absurd hs hne

theorem map_add_add (L : List Int) (a b : Int) : L.map (· + (a + b)) = (L.map (· + a)).map (· + b) := by
  rw [List.map_map]; apply List.map_congr_left; intro v _; show v + (a + b) = v + a + b; ring

theorem addAll_inner (s : BS) (n h k lo : Nat) (x : Int) (hI : Inv s n (h + 1) k lo) (hreal : lo + 2 ^ (h + 1) ≤ n)
    (hR : InR (T s n (h + 1) k lo)) (hR' : InR ((T s n (h + 1) k lo).map (· + x)))
    (hRA : s.lv k = INF → InR ((T s n h (2 * k + 1) lo).map (· + s.la k)))
    (hRB : s.lv k = INF → InR ((T s n h (2 * k + 2) (lo + 2 ^ h)).map (· + s.la k)))
    (hRA' : s.lv k = INF → InR (((T s n h (2 * k + 1) lo).map (· + s.la k)).map (· + x)))
    (hRB' : s.lv k = INF → InR (((T s n h (2 * k + 2) (lo + 2 ^ h)).map (· + s.la k)).map (· + x))) :
    Inv (addAll s k x) n (h + 1) k lo ∧ T (addAll s k x) n (h + 1) k lo = (T s n (h + 1) k lo).map (· + x) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := addAll_fields s k x
  have hag := addAll_agree s k x
  have g1 := agree_upF_child s (addAll s k x) h k (2 * k + 1) (by omega) hag
  have g2 := agree_upF_child s (addAll s k x) h k (2 * k + 2) (by omega) hag
  have t1 := T_frame s (addAll s k x) n h _ lo g1
  have t2 := T_frame s (addAll s k x) n h _ (lo + 2 ^ h) g2
  have hne : T s n (h + 1) k lo ≠ [] := by
    intro he; have hl := T_length s n (h + 1) k lo; rw [he, List.length_nil] at hl
    have := Nat.two_pow_pos (h + 1); omega
  have hS := i3
  have hT : T (addAll s k x) n (h + 1) k lo = (T s n (h + 1) k lo).map (· + x) := by
    simp only [T]
    rw [← t1, ← t2, List.map_map]
    apply List.map_congr_left
    intro v _
    simp only [Function.comp, tau, f1, f4, f8]
    split_ifs with hlv
    · omega
    · obtain ⟨e1, e2, e3, -⟩ := i6 hlv; rw [e1, e2, e3]; omega
  refine ⟨⟨inv_frame s _ n h _ _ g1 i1, inv_frame s _ n h _ _ g2 i2, ?_, by rw [f7]; exact i4,
    fun hp => absurd hreal (by omega), ?_, ?_⟩, hT⟩
  · unfold SummK; rw [hT]; exact summK_add s k x _ i3 hne hR hR'
  · intro hlv
    rw [f9] at hlv
    split_ifs at hlv with hc
    · exact absurd rfl hlv
    · obtain ⟨e1, e2, e3, e4⟩ := i6 hc
      have hmem : s.lv k + x ∈ (T s n (h + 1) k lo).map (· + x) := by
        rw [← e1, hS.mx]; exact List.mem_map.mpr ⟨_, lmax_mem _ hne hR, rfl⟩
      rw [f1, f4, f8, f9, if_neg hc, if_neg hc, e1, e2]
      exact ⟨rfl, rfl, e3, (hR' _ hmem).1⟩
  · intro hlv
    rw [f9] at hlv
    have hlv0 : s.lv k = INF := by
      by_contra hc; rw [if_neg hc] at hlv
      have := i6 hc
      have hmem : s.lv k + x ∈ (T s n (h + 1) k lo).map (· + x) := by
        rw [← this.1, hS.mx]; exact List.mem_map.mpr ⟨_, lmax_mem _ hne hR, rfl⟩
      have := (hR' _ hmem).2; omega
    obtain ⟨c1, c2⟩ := i7 hlv0
    rw [← t1, ← t2]
    unfold ChildOK at *
    rw [f1, f4, f8, if_pos hlv0, map_add_add, map_add_add]
    have hmx1 : -INF < s.mx k + x := by
      rw [hS.mx]; exact (hR' _ (List.mem_map.mpr ⟨_, lmax_mem _ hne hR, rfl⟩)).1
    have hmn1 : s.mn k + x < INF := by
      rw [hS.mn]; exact (hR' _ (List.mem_map.mpr ⟨_, lmin_mem _ hne hR, rfl⟩)).2
    exact ⟨childok_shift _ _ _ _ (hRA hlv0) (hRA' hlv0) hmx1 hmn1 c1, childok_shift _ _ _ _ (hRB hlv0) (hRB' hlv0) hmx1 hmn1 c2⟩

theorem updAll_agree (s : BS) (k : Nat) (x : Int) : ∀ j, j ≠ k → AgreeAt s (updAll s k x) j := by
  intro j hj; simp [AgreeAt, updAll, upF, Function.update, hj]

theorem updAll_spec (s : BS) (n h k lo : Nat) (x : Int) (hI : Inv s n h k lo) (hreal : lo + 2 ^ h ≤ n)
    (hx : -INF < x ∧ x < INF) :
    Inv (updAll s k x) n h k lo ∧ T (updAll s k x) n h k lo = List.replicate (2 ^ h) x := by
  have hlen := inv_len s n h k lo hI
  have hag := updAll_agree s k x
  have hSum : ∀ L : List Int, L = List.replicate (2 ^ h) x → SummK (updAll s k x) k L := by
    intro L hL; subst hL
    have := summ_replicate (2 ^ h) x Nat.one_le_two_pow hx
    unfold SummK; simp only [updAll, upF, Function.update_self, hlen]; exact_mod_cast this
  cases h with
  | zero =>
    have hT : T (updAll s k x) n 0 k lo = List.replicate (2 ^ 0) x := by
      simp [T, show lo < n by omega, updAll, upF]
    refine ⟨⟨hSum _ hT, by simpa [updAll] using hlen⟩, hT⟩
  | succ h =>
    obtain ⟨i1, i2, -, i4, -, -, -⟩ := hI
    have g1 := agree_upF_child s (updAll s k x) h k (2 * k + 1) (by omega) hag
    have g2 := agree_upF_child s (updAll s k x) h k (2 * k + 2) (by omega) hag
    have t1 := T_frame s (updAll s k x) n h _ lo g1
    have t2 := T_frame s (updAll s k x) n h _ (lo + 2 ^ h) g2
    have hT : T (updAll s k x) n (h + 1) k lo = List.replicate (2 ^ (h + 1)) x := by
      simp only [T]
      rw [← t1, ← t2]
      apply List.eq_replicate_iff.mpr
      constructor
      · simp only [List.length_map, List.length_append, T_length, pow_succ]
        have := Nat.two_pow_pos h; omega
      · intro b hb
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp hb
        simp [tau, updAll, upF]
    refine ⟨⟨inv_frame s _ n h _ _ g1 i1, inv_frame s _ n h _ _ g2 i2, hSum _ hT, by simpa [updAll] using i4,
      fun hp => absurd hreal (by omega), fun _ => ?_, fun hlv => ?_⟩, hT⟩
    · simp [updAll, upF]; exact hx.1
    · simp [updAll, upF] at hlv; omega

end Proofs.Cpp.SegmentTreeBeatsMath
namespace Proofs.Cpp.SegmentTreeBeatsMath

theorem safe_top (s : BS) (n : Nat) (B : Int) : ∀ h k lo O, Safe s n B h k lo O →
    ∀ o ∈ O, ∀ v ∈ T s n h k lo, |v + o| ≤ B
  | 0, _, _, _, hS => hS
  | _ + 1, _, _, _, hS => hS.1

theorem inR_of_bound (L : List Int) (o B : Int) (hB : B < INF) (h : ∀ v ∈ L, |v + o| ≤ B) :
    InR (L.map (· + o)) := by
  intro w hw; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  have := h v hv; rw [abs_le] at this; constructor <;> omega

theorem safe_inR (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int)
    (hS : Safe s n B h k lo O) (o : Int) (ho : o ∈ O) : InR ((T s n h k lo).map (· + o)) :=
  inR_of_bound _ o B hB (fun v hv => safe_top s n B h k lo O hS o ho v hv)

theorem inR_zero (L : List Int) (h : InR (L.map (· + 0))) : InR L := by simpa using h

/-- The children of a safe inner node, seen with the node's pending add. -/
theorem safe_children (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int)
    (hS : Safe s n B (h + 1) k lo O) (o : Int) (ho : o ∈ O) (hlv : s.lv k = INF) :
    InR ((T s n h (2 * k + 1) lo).map (· + (o + s.la k))) ∧
      InR ((T s n h (2 * k + 2) (lo + 2 ^ h)).map (· + (o + s.la k))) := by
  obtain ⟨s1, s2⟩ := hS.2 hlv
  have hm : o + s.la k ∈ 0 :: O.map (· + s.la k) := List.mem_cons_of_mem _ (List.mem_map.mpr ⟨o, ho, rfl⟩)
  exact ⟨safe_inR s n B hB h _ lo _ s1 _ hm, safe_inR s n B hB h _ _ _ s2 _ hm⟩

theorem unm_node (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h c lo : Nat) (O : List Int) (h0 : 0 ∈ O)
    (hI : Inv s n h c lo) (hS : Safe s n B h c lo O) (x : Int) (h1 : s.sx c < x) (h2 : x < s.mx c) :
    Inv (unm s c x) n h c lo ∧ T (unm s c x) n h c lo = (T s n h c lo).map (min · x) := by
  have hR := inR_zero _ (safe_inR s n B hB h c lo O hS 0 h0)
  cases h with
  | zero => exact unm_leaf s n c lo x hI hR h1 h2
  | succ h =>
    exact unm_inner s n h c lo x hI hR (fun hl => by simpa using (safe_children s n B hB h c lo O hS 0 h0 hl).1)
      (fun hl => by simpa using (safe_children s n B hB h c lo O hS 0 h0 hl).2) h1 h2

theorem unmin_node (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h c lo : Nat) (O : List Int) (h0 : 0 ∈ O)
    (hI : Inv s n h c lo) (hS : Safe s n B h c lo O) (x : Int) (h1 : s.mn c < x) (h2 : x < s.sn c) :
    Inv (unmin s c x) n h c lo ∧ T (unmin s c x) n h c lo = (T s n h c lo).map (max · x) := by
  have hR := inR_zero _ (safe_inR s n B hB h c lo O hS 0 h0)
  cases h with
  | zero => exact unmin_leaf s n c lo x hI hR h1 h2
  | succ h =>
    exact unmin_inner s n h c lo x hI hR (fun hl => by simpa using (safe_children s n B hB h c lo O hS 0 h0 hl).1)
      (fun hl => by simpa using (safe_children s n B hB h c lo O hS 0 h0 hl).2) h1 h2

/-- `add_all(c, x)` where `x` is one of the offsets of `c` (a pending add of an ancestor). -/
theorem addAll_node (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h c lo : Nat) (O : List Int) (h0 : 0 ∈ O)
    (hI : Inv s n h c lo) (hS : Safe s n B h c lo O) (hreal : lo + 2 ^ h ≤ n) (x : Int) (hx : x ∈ O) :
    Inv (addAll s c x) n h c lo ∧ T (addAll s c x) n h c lo = (T s n h c lo).map (· + x) := by
  have hR := inR_zero _ (safe_inR s n B hB h c lo O hS 0 h0)
  have hR' := safe_inR s n B hB h c lo O hS x hx
  cases h with
  | zero => exact addAll_leaf s n c lo x hI (by omega) hR hR'
  | succ h =>
    refine addAll_inner s n h c lo x hI hreal hR hR'
      (fun hl => by simpa using (safe_children s n B hB h c lo O hS 0 h0 hl).1)
      (fun hl => by simpa using (safe_children s n B hB h c lo O hS 0 h0 hl).2)
      (fun hl => by have := (safe_children s n B hB h c lo O hS x hx hl).1; rwa [add_comm x, map_add_add] at this)
      (fun hl => by have := (safe_children s n B hB h c lo O hS x hx hl).2; rwa [add_comm x, map_add_add] at this)

end Proofs.Cpp.SegmentTreeBeatsMath
namespace Proofs.Cpp.SegmentTreeBeatsMath

theorem safe_frame (s t : BS) (n : Nat) (B : Int) : ∀ h k lo O, (∀ j, Sub h k j → AgreeAt s t j) →
    Safe s n B h k lo O → Safe t n B h k lo O := by
  intro h
  induction h with
  | zero => intro k lo O hA hS; show ∀ _ ∈ _, _; rw [← T_frame s t n 0 k lo hA]; exact hS
  | succ h ih =>
    intro k lo O hA hS
    have hk := hA k (Or.inl rfl)
    refine ⟨by rw [← T_frame s t n (h + 1) k lo hA]; exact hS.1, fun hlv => ?_⟩
    rw [← hk.2.2.2.2.2.2.2.2] at hlv
    obtain ⟨s1, s2⟩ := hS.2 hlv
    rw [← hk.2.2.2.2.2.2.2.1]
    exact ⟨ih _ _ _ (fun j hj => hA j (sub_child1 h k j hj)) s1, ih _ _ _ (fun j hj => hA j (sub_child2 h k j hj)) s2⟩

theorem safe_mono (s : BS) (n : Nat) (B : Int) : ∀ h k lo O O', (∀ o ∈ O', o ∈ O) →
    Safe s n B h k lo O → Safe s n B h k lo O' := by
  intro h
  induction h with
  | zero => intro k lo O O' hO hS o ho v hv; exact hS o (hO o ho) v hv
  | succ h ih =>
    intro k lo O O' hO hS
    refine ⟨fun o ho v hv => hS.1 o (hO o ho) v hv, fun hlv => ?_⟩
    obtain ⟨s1, s2⟩ := hS.2 hlv
    have hm : ∀ o ∈ 0 :: O'.map (· + s.la k), o ∈ 0 :: O.map (· + s.la k) := by
      intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact List.mem_cons_self
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ho
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, hO w hw, rfl⟩)
    exact ⟨ih _ _ _ _ hm s1, ih _ _ _ _ hm s2⟩

/-- An operation that changes only the fields of node `c` (not its pending add) keeps the bounds below `c`. -/
theorem safe_change_top (s t : BS) (n : Nat) (B : Int) (h c lo : Nat) (O : List Int)
    (hag : ∀ j, j ≠ c → AgreeAt s t j) (hla : t.la c = s.la c) (hlv : t.lv c = INF ↔ s.lv c = INF)
    (hS : Safe s n B h c lo O) (htop : ∀ o ∈ O, ∀ v ∈ T t n h c lo, |v + o| ≤ B) : Safe t n B h c lo O := by
  cases h with
  | zero => exact htop
  | succ h =>
    refine ⟨htop, fun hl => ?_⟩
    obtain ⟨s1, s2⟩ := hS.2 (hlv.mp hl)
    rw [hla]
    exact ⟨safe_frame s t n B h _ _ _ (agree_upF_child s t h c _ (by omega) hag) s1,
      safe_frame s t n B h _ _ _ (agree_upF_child s t h c _ (by omega) hag) s2⟩

theorem abs_min_le (v x o B : Int) (h1 : |v + o| ≤ B) (h2 : |x + o| ≤ B) : |min v x + o| ≤ B := by
  rw [abs_le] at *; constructor <;> omega

theorem abs_max_le (v x o B : Int) (h1 : |v + o| ≤ B) (h2 : |x + o| ≤ B) : |max v x + o| ≤ B := by
  rw [abs_le] at *; constructor <;> omega

theorem lmax_map_min_id (L : List Int) (m : Int) (h : lmax L ≤ m) : L.map (min · m) = L := by
  conv_rhs => rw [← List.map_id L]
  apply List.map_congr_left; intro v hv; have := lmax_ge L v hv; simp; omega

theorem lmin_map_max_id (L : List Int) (m : Int) (h : m ≤ lmin L) : L.map (max · m) = L := by
  conv_rhs => rw [← List.map_id L]
  apply List.map_congr_left; intro v hv; have := lmin_le L v hv; simp; omega

theorem lmin_map_min (L : List Int) (m : Int) (hR : InR L) (hne : L ≠ []) (hlt : lmin L < m) :
    lmin (L.map (min · m)) = lmin L := by
  have h1 : lmin L ≤ lmin (L.map (min · m)) := by
    rw [le_lmin_iff _ _ (lmin_le_inf L)]
    intro v hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; have := lmin_le L w hw; simp; omega
  have h2 := lmin_le (L.map (min · m)) (min (lmin L) m) (List.mem_map.mpr ⟨_, lmin_mem L hne hR, rfl⟩)
  have : min (lmin L) m = lmin L := by omega
  omega

theorem lmin_map_min_ge (L : List Int) (m : Int) (hm : m ≤ INF) : min (lmin L) m ≤ lmin (L.map (min · m)) := by
  rw [le_lmin_iff _ _ (by have := lmin_le_inf L; omega)]
  intro v hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; have := lmin_le L w hw; simp; omega

theorem lt_smin_map_min (L : List Int) (m c : Int) (hR : InR L) (hne : L ≠ []) (hlt : lmin L < m)
    (hc1 : c < smin L) (hc2 : c < m) (hcI : c < INF) : c < smin (L.map (min · m)) := by
  have e1 := lmin_map_min L m hR hne hlt
  unfold smin
  rw [e1, filter_map_comm L _ _ (· > lmin L) (fun v _ => by
    by_cases hv : v > lmin L <;> simp [hv] <;> omega)]
  have key : c + 1 ≤ lmin ((L.filter (· > lmin L)).map (min · m)) := by
    rw [le_lmin_iff _ _ (by omega)]
    intro v hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have : smin L ≤ w := lmin_le _ w hw
    simp; omega
  omega

theorem caps_spec (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h c lo : Nat) (O : List Int) (h0 : 0 ∈ O)
    (k : Nat) (hck : k ≠ c) (hI : Inv s n h c lo) (hS : Safe s n B h c lo O)
    (hk0 : -INF ≤ s.mx k ∧ s.mn k ≤ INF) (hmn' : T s n h c lo ≠ [] → s.mn k ≤ s.mx k)
    (hbx' : T s n h c lo ≠ [] → ∀ o ∈ O, |s.mx k + o| ≤ B ∧ |s.mn k + o| ≤ B)
    (ok : (s.mx k < lmax (T s n h c lo) → smax (T s n h c lo) < s.mx k) ∧
      (lmin (T s n h c lo) < s.mn k → s.mn k < smin (T s n h c lo)) ∧
      (s.mx k = s.mn k → lmax (T s n h c lo) = lmin (T s n h c lo) ∨ T s n h c lo = [])) :
    Inv (caps s k c) n h c lo ∧ Safe (caps s k c) n B h c lo O ∧
      T (caps s k c) n h c lo = (T s n h c lo).map (fun v => max (s.mn k) (min (s.mx k) v)) ∧
      ∀ j, j ≠ c → AgreeAt s (caps s k c) j := by
  set L := T s n h c lo with hL
  have hSum := inv_summ s n h c lo hI
  have hR := inR_zero _ (safe_inR s n B hB h c lo O hS 0 h0)
  by_cases hLe : L = []
  · have hLe' : T s n h c lo = [] := hLe
    have hmxc : s.mx c = -INF := by rw [hSum.mx, hLe']; rfl
    have hmnc : s.mn c = INF := by rw [hSum.mn, hLe']; rfl
    have hc : caps s k c = s := by
      simp only [caps, if_neg (show ¬ s.mx k < s.mx c by omega), if_neg (show ¬ s.mn c < s.mn k by omega)]
    rw [hc, hLe']
    exact ⟨hI, hS, by rw [show L = [] from hLe]; rfl, fun j _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hmn := hmn' hLe
  have hbx := hbx' hLe
  obtain ⟨bx0, bn0⟩ := hbx 0 h0
  simp only [add_zero] at bx0 bn0
  rw [abs_le] at bx0 bn0
  -- the cap from above
  obtain ⟨I1, S1, T1, A1⟩ : Inv (if s.mx k < s.mx c then unm s c (s.mx k) else s) n h c lo ∧
      Safe (if s.mx k < s.mx c then unm s c (s.mx k) else s) n B h c lo O ∧
      T (if s.mx k < s.mx c then unm s c (s.mx k) else s) n h c lo = L.map (min · (s.mx k)) ∧
      ∀ j, j ≠ c → AgreeAt s (if s.mx k < s.mx c then unm s c (s.mx k) else s) j := by
    split_ifs with hc
    · have hsx : s.sx c < s.mx k := by rw [hSum.smx]; exact ok.1 (by rw [← hSum.mx]; exact hc)
      obtain ⟨i, t⟩ := unm_node s n B hB h c lo O h0 hI hS (s.mx k) hsx hc
      obtain ⟨-, -, -, -, -, -, -, f8, f9⟩ := unm_fields s c (s.mx k)
      refine ⟨i, safe_change_top s _ n B h c lo O (unm_agree s c _) f8 (by
          rw [f9]; split_ifs with hh
          · constructor <;> intro <;> unfold INF at * <;> omega
          · exact Iff.rfl) hS (fun o ho v hv => by
          rw [t] at hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
          exact abs_min_le _ _ _ _ (safe_top s n B h c lo O hS o ho w hw) (hbx o ho).1), t, unm_agree s c _⟩
    · refine ⟨hI, hS, (lmax_map_min_id L _ (by rw [← hSum.mx]; omega)).symm, fun j _ => ?_⟩
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  set s1 := (if s.mx k < s.mx c then unm s c (s.mx k) else s) with hs1
  have hk1 : AgreeAt s s1 k := A1 k hck
  have hSum1 := inv_summ s1 n h c lo I1
  rw [T1] at hSum1
  have hcaps : caps s k c = if s1.mn c < s1.mn k then unmin s1 c (s1.mn k) else s1 := rfl
  rw [hcaps, ← hk1.2.2.2.1]
  split_ifs with hc
  · have hlt : lmin (L.map (min · (s.mx k))) < s.mn k := by rw [← hSum1.mn]; exact hc
    have hLne : L ≠ [] := by intro he; rw [he] at hlt; simp [lmin_nil] at hlt; omega
    have hlt0 : lmin L < s.mn k := by
      have := lmin_map_min_ge L (s.mx k) (by omega); omega
    have hsn : s.mn k < s1.sn c := by
      rw [hSum1.smn]
      have hs2 := ok.2.1 hlt0
      by_cases he : s.mx k = s.mn k
      · rcases ok.2.2 he with hsing | hemp
        · have hmx' : lmax L < s.mx k := by have := lmin_le_lmax L hR hLne; omega
          rw [lmax_map_min_id L _ (by omega), smin_single L hsing]; omega
        · exact absurd hemp hLne
      · exact lt_smin_map_min L _ _ hR hLne (by omega) hs2 (by omega) (by omega)
    obtain ⟨i, t⟩ := unmin_node s1 n B hB h c lo O h0 I1 S1 (s.mn k) hc hsn
    obtain ⟨-, -, -, -, -, -, -, f8, f9⟩ := unmin_fields s1 c (s.mn k)
    have hcomp : (T s n h c lo).map (fun v => max (s.mn k) (min (s.mx k) v)) =
        ((T s n h c lo).map (min · (s.mx k))).map (max · (s.mn k)) := by
      rw [List.map_map]; apply List.map_congr_left; intro v _; simp only [Function.comp_apply]; omega
    refine ⟨i, safe_change_top s1 _ n B h c lo O (unmin_agree s1 c _) f8 (by
        rw [f9]; split_ifs with hh
        · constructor <;> intro <;> unfold INF at * <;> omega
        · exact Iff.rfl) S1 (fun o ho v hv => by
        rw [t, T1] at hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        exact abs_max_le _ _ _ _ (safe_top s1 n B h c lo O S1 o ho w (by rw [T1]; exact hw)) (hbx o ho).2),
      by rw [t, T1, hcomp], fun j hj => ?_⟩
    have a1 := A1 j hj; have a2 := unmin_agree s1 c (s.mn k) j hj
    exact ⟨a1.1.trans a2.1, a1.2.1.trans a2.2.1, a1.2.2.1.trans a2.2.2.1, a1.2.2.2.1.trans a2.2.2.2.1,
      a1.2.2.2.2.1.trans a2.2.2.2.2.1, a1.2.2.2.2.2.1.trans a2.2.2.2.2.2.1, a1.2.2.2.2.2.2.1.trans a2.2.2.2.2.2.2.1,
      a1.2.2.2.2.2.2.2.1.trans a2.2.2.2.2.2.2.2.1, a1.2.2.2.2.2.2.2.2.trans a2.2.2.2.2.2.2.2.2⟩
  · have hge : s.mn k ≤ lmin (L.map (min · (s.mx k))) := by rw [← hSum1.mn]; omega
    refine ⟨I1, S1, ?_, A1⟩
    rw [T1]
    have hcomp : (T s n h c lo).map (fun v => max (s.mn k) (min (s.mx k) v)) =
        ((T s n h c lo).map (min · (s.mx k))).map (max · (s.mn k)) := by
      rw [List.map_map]; apply List.map_congr_left; intro v _; simp only [Function.comp_apply]; omega
    rw [hcomp, lmin_map_max_id _ _ hge]

end Proofs.Cpp.SegmentTreeBeatsMath
namespace Proofs.Cpp.SegmentTreeBeatsMath

/-- The add pushed from the parent: the child's offsets lose the parent's pending add. -/
theorem safe_addAll (s : BS) (n : Nat) (B : Int) (h c lo : Nat) (O0 : List Int) (x : Int) (h0 : 0 ∈ O0)
    (hS : Safe s n B h c lo (0 :: O0.map (· + x)))
    (hT : T (addAll s c x) n h c lo = (T s n h c lo).map (· + x))
    (hlvB : 0 < h → s.lv c ≠ INF → s.lv c + x ≠ INF) :
    Safe (addAll s c x) n B h c lo (0 :: O0) := by
  obtain ⟨-, -, -, -, -, -, -, f8, f9⟩ := addAll_fields s c x
  have htop : ∀ o ∈ 0 :: O0, ∀ v ∈ T (addAll s c x) n h c lo, |v + o| ≤ B := by
    intro o ho v hv
    rw [hT] at hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have := safe_top s n B h c lo _ hS (o + x) (by
      rcases List.mem_cons.mp ho with rfl | ho
      · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨0, h0, by ring⟩)
      · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨o, ho, rfl⟩)) w hw
    rw [show w + x + o = w + (o + x) by ring]; exact this
  cases h with
  | zero => exact htop
  | succ h =>
    refine ⟨htop, fun hl => ?_⟩
    have hlv : s.lv c = INF := by
      rw [f9] at hl; split_ifs at hl with hc
      · exact hc
      · exact absurd hl (hlvB (by omega) hc)
    obtain ⟨s1, s2⟩ := hS.2 hlv
    have hag := addAll_agree s c x
    rw [f8, if_pos hlv]
    have hm : ∀ o ∈ 0 :: (0 :: O0).map (· + (s.la c + x)), o ∈ 0 :: (0 :: O0.map (· + x)).map (· + s.la c) := by
      intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact List.mem_cons_self
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ho
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨0 + x, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨0, h0, rfl⟩),
            by ring⟩)
        · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w + x, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, hw, rfl⟩),
            by ring⟩)
    exact ⟨safe_mono _ n B h _ _ _ _ hm (safe_frame s _ n B h _ _ _ (agree_upF_child s _ h c _ (by omega) hag) s1),
      safe_mono _ n B h _ _ _ _ hm (safe_frame s _ n B h _ _ _ (agree_upF_child s _ h c _ (by omega) hag) s2)⟩

/-- A child set to `x` by the parent's pending assignment. -/
theorem safe_updAll (s : BS) (n : Nat) (B : Int) (h c lo : Nat) (O : List Int) (x : Int)
    (hx : -INF < x ∧ x < INF) (hT : T (updAll s c x) n h c lo = List.replicate (2 ^ h) x)
    (hb : ∀ o ∈ O, |x + o| ≤ B) : Safe (updAll s c x) n B h c lo O := by
  have htop : ∀ o ∈ O, ∀ v ∈ T (updAll s c x) n h c lo, |v + o| ≤ B := by
    intro o ho v hv; rw [hT] at hv; rw [List.eq_of_mem_replicate hv]; exact hb o ho
  cases h with
  | zero => exact htop
  | succ h =>
    refine ⟨htop, fun hl => ?_⟩
    simp [updAll, upF] at hl; omega

/-- What `push(k)` gives on an inner node `k` of height `h + 1`. -/
def PushPost (s t : BS) (n : Nat) (B : Int) (h k lo : Nat) (O : List Int) : Prop :=
  Inv t n (h + 1) k lo ∧ Safe t n B (h + 1) k lo O ∧ T t n (h + 1) k lo = T s n (h + 1) k lo ∧
    t.la k = 0 ∧ t.lv k = INF ∧ t.mx k = s.mx k ∧ t.sx k = s.sx k ∧ t.cx k = s.cx k ∧ t.mn k = s.mn k ∧
    t.sn k = s.sn k ∧ t.cn k = s.cn k ∧ t.len k = s.len k ∧
    (∀ j, j ≠ k → j ≠ 2 * k + 1 → j ≠ 2 * k + 2 → AgreeAt s t j) ∧
    T t n h (2 * k + 1) lo = (T s n h (2 * k + 1) lo).map (tau s k) ∧
    T t n h (2 * k + 2) (lo + 2 ^ h) = (T s n h (2 * k + 2) (lo + 2 ^ h)).map (tau s k)

theorem agree_trans (a b c : BS) (j : Nat) (h1 : AgreeAt a b j) (h2 : AgreeAt b c j) : AgreeAt a c j := by
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9⟩ := h1
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9⟩ := h2
  exact ⟨x1.trans y1, x2.trans y2, x3.trans y3, x4.trans y4, x5.trans y5, x6.trans y6, x7.trans y7, x8.trans y8,
    x9.trans y9⟩

theorem sub_disjoint (h k j : Nat) (hj : Sub h (2 * k + 2) j) : j ≠ 2 * k + 1 := by
  have := sub_ge h _ j hj; omega

theorem sub_eq_or_ge (h c j : Nat) (hj : Sub h c j) : j = c ∨ 2 * c + 1 ≤ j := by
  cases h with
  | zero => left; exact hj
  | succ h =>
    rcases hj with rfl | hj | hj
    · left; rfl
    · right; exact sub_ge h _ j hj
    · right; have := sub_ge h _ j hj; omega

theorem sub_disjoint' (h k j : Nat) (hj : Sub h (2 * k + 1) j) : j ≠ 2 * k + 2 := by
  rcases sub_eq_or_ge h _ j hj with e | e <;> omega

theorem setLv_agree (s : BS) (k : Nat) (v : Int) : ∀ j, j ≠ k → AgreeAt s (setLv s k v) j := by
  intro j hj; simp [AgreeAt, setLv, upF, Function.update, hj]

theorem setLa_agree (s : BS) (k : Nat) (v : Int) : ∀ j, j ≠ k → AgreeAt s (setLa s k v) j := by
  intro j hj; simp [AgreeAt, setLa, upF, Function.update, hj]

theorem map_const_eq (L : List Int) (f : Int → Int) (c : Int) (m : Nat) (hf : ∀ v, f v = c) (hl : L.length = m) :
    L.map f = List.replicate m c := by
  apply List.eq_replicate_iff.mpr; refine ⟨by simp [hl], fun b hb => ?_⟩
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hb; exact hf v

theorem inv_real_length (s : BS) (n h k lo : Nat) (hreal : lo + 2 ^ h ≤ n) : (T s n h k lo).length = 2 ^ h := by
  rw [T_length]; omega

theorem push_set (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int) (h0 : 0 ∈ O)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O) (hlv : s.lv k ≠ INF) :
    PushPost s (push s k) n B h k lo O := by
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := hI
  obtain ⟨e1, e2, e3, e4⟩ := i6 hlv
  have hreal : lo + 2 ^ (h + 1) ≤ n := by
    by_contra hc; exact hlv (i5 (by omega)).2
  have hreal2 : lo + 2 ^ h + 2 ^ h ≤ n := by rw [pow_succ] at hreal; omega
  have hreal1 : lo + 2 ^ h ≤ n := Nat.le_trans (Nat.le_add_right _ _) hreal2
  have hRk := inR_zero _ (safe_inR s n B hB (h + 1) k lo O hS 0 h0)
  have hne : T s n (h + 1) k lo ≠ [] := by
    intro he; have hl := inv_real_length s n (h + 1) k lo hreal; rw [he] at hl
    have := Nat.two_pow_pos (h + 1); simp at hl; omega
  have hmem : s.lv k ∈ T s n (h + 1) k lo := by rw [← e1, i3.mx]; exact lmax_mem _ hne hRk
  have hx : -INF < s.lv k ∧ s.lv k < INF := hRk _ hmem
  have hb : ∀ o ∈ 0 :: O, |s.lv k + o| ≤ B := by
    intro o ho; rcases List.mem_cons.mp ho with rfl | ho
    · exact safe_top s n B _ _ _ _ hS 0 h0 _ hmem
    · exact safe_top s n B _ _ _ _ hS o ho _ hmem
  have htau : ∀ v, tau s k v = s.lv k := by intro v; simp only [tau, e1, e2, e3]; omega
  -- the two children
  set s1 := updAll s (2 * k + 1) (s.lv k) with hs1
  obtain ⟨I1, T1⟩ := updAll_spec s n h (2 * k + 1) lo (s.lv k) i1 hreal1 hx
  have g12 := agree_upF_child s s1 h (2 * k + 1) (2 * k + 2) (by omega) (updAll_agree s _ _)
  have i2' := inv_frame s s1 n h _ _ (fun j hj => updAll_agree s _ _ j (sub_disjoint h k j hj)) i2
  set s2 := updAll s1 (2 * k + 2) (s.lv k) with hs2
  obtain ⟨I2, T2⟩ := updAll_spec s1 n h (2 * k + 2) (lo + 2 ^ h) (s.lv k) i2' hreal2 hx
  have a21 : ∀ j, Sub h (2 * k + 1) j → AgreeAt s1 s2 j := fun j hj => updAll_agree s1 _ _ j (sub_disjoint' h k j hj)
  have I1' := inv_frame s1 s2 n h _ _ a21 I1
  have T1' : T s2 n h (2 * k + 1) lo = List.replicate (2 ^ h) (s.lv k) := by rw [← T_frame s1 s2 n h _ _ a21, T1]
  have S1 := safe_updAll s n B h (2 * k + 1) lo (0 :: O) (s.lv k) hx T1 hb
  have S1' := safe_frame s1 s2 n B h _ _ _ a21 S1
  have S2 := safe_updAll s1 n B h (2 * k + 2) (lo + 2 ^ h) (0 :: O) (s.lv k) hx T2 hb
  have hpush : push s k = setLv s2 k INF := by unfold push; rw [if_pos hlv]
  set t := setLv s2 k INF with ht
  have atk : ∀ j, Sub h (2 * k + 1) j ∨ Sub h (2 * k + 2) j → AgreeAt s2 t j := by
    intro j hj; apply setLv_agree s2 k INF j
    rcases hj with hj | hj <;> have := sub_ge h _ j hj <;> omega
  have It1 := inv_frame s2 t n h _ _ (fun j hj => atk j (Or.inl hj)) I1'
  have It2 := inv_frame s2 t n h _ _ (fun j hj => atk j (Or.inr hj)) I2
  have Tt1 : T t n h (2 * k + 1) lo = List.replicate (2 ^ h) (s.lv k) := by
    rw [← T_frame s2 t n h _ _ (fun j hj => atk j (Or.inl hj)), T1']
  have Tt2 : T t n h (2 * k + 2) (lo + 2 ^ h) = List.replicate (2 ^ h) (s.lv k) := by
    rw [← T_frame s2 t n h _ _ (fun j hj => atk j (Or.inr hj)), T2]
  -- the fields of `k`
  have fk : t.mx k = s.mx k ∧ t.sx k = s.sx k ∧ t.cx k = s.cx k ∧ t.mn k = s.mn k ∧ t.sn k = s.sn k ∧
      t.cn k = s.cn k ∧ t.len k = s.len k ∧ t.la k = s.la k ∧ t.lv k = INF := by
    have a1 := updAll_agree s (2 * k + 1) (s.lv k) k (by omega)
    have a2 := updAll_agree s1 (2 * k + 2) (s.lv k) k (by omega)
    have a12 := agree_trans _ _ _ k a1 a2
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, -⟩ := a12
    simp only [ht, setLv, upF, Function.update_self]
    exact ⟨x1.symm, x2.symm, x3.symm, x4.symm, x5.symm, x6.symm, x7.symm, x8.symm, by simp⟩
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := fk
  have htau' : ∀ v, tau t k v = s.lv k := by intro v; simp only [tau, k1, k4, k8, e1, e2, e3]; omega
  rw [hpush]
  have hTk : T t n (h + 1) k lo = T s n (h + 1) k lo := by
    show (T t n h _ lo ++ T t n h _ _).map (tau t k) = (T s n h _ lo ++ T s n h _ _).map (tau s k)
    have hl : (T s n h (2 * k + 1) lo ++ T s n h (2 * k + 2) (lo + 2 ^ h)).length = 2 ^ h + 2 ^ h := by
      rw [List.length_append, inv_real_length s n h _ _ hreal1, inv_real_length s n h _ _ hreal2]
    rw [map_const_eq _ _ _ _ htau hl, Tt1, Tt2, map_const_eq _ _ _ (2 ^ h + 2 ^ h) htau' (by simp)]
  refine ⟨⟨It1, It2, ?_, by rw [k7]; exact i4, fun hp => ⟨by rw [k8]; exact e3, k9⟩, fun hl => absurd k9 hl,
      fun _ => ?_⟩, ⟨by rw [hTk]; exact hS.1, fun _ => ?_⟩, hTk, by rw [k8]; exact e3, k9, k1, k2, k3, k4, k5, k6, k7,
      fun j hj1 hj2 hj3 => ?_, ?_, ?_⟩
  · unfold SummK; rw [hTk, k1, k2, k3, k4, k5, k6]; exact i3
  · rw [Tt1, Tt2]
    unfold ChildOK
    rw [k1, k4, k8, e1, e2, e3]
    have hr : (List.replicate (2 ^ h) (s.lv k)).map (· + 0) = List.replicate (2 ^ h) (s.lv k) := by simp
    have hs := summ_replicate (2 ^ h) (s.lv k) Nat.one_le_two_pow hx
    simp only [hr]
    rw [← hs.mx, ← hs.mn]
    exact ⟨⟨fun h => by omega, fun h => by omega, fun _ => Or.inl rfl⟩,
      ⟨fun h => by omega, fun h => by omega, fun _ => Or.inl rfl⟩⟩
  · rw [k8, e3]
    have hO : (0 :: O.map (· + 0)) = 0 :: O := by simp
    rw [hO]
    exact ⟨safe_frame s2 t n B h _ _ _ (fun j hj => atk j (Or.inl hj)) S1',
      safe_frame s2 t n B h _ _ _ (fun j hj => atk j (Or.inr hj)) S2⟩
  · exact agree_trans _ _ _ j (agree_trans _ _ _ j (updAll_agree s _ _ j hj2) (updAll_agree s1 _ _ j hj3))
      (setLv_agree s2 k INF j hj1)
  · rw [Tt1]; exact (map_const_eq _ _ _ _ htau (inv_real_length s n h _ _ hreal1)).symm
  · rw [Tt2]; exact (map_const_eq _ _ _ _ htau (inv_real_length s n h _ _ hreal2)).symm

/-- The state after the add part of `push(k)`: the children hold the values with the pending add. -/
def Stage1 (s s1 : BS) (n : Nat) (B : Int) (h k lo : Nat) (O : List Int) : Prop :=
  Inv s1 n h (2 * k + 1) lo ∧ Inv s1 n h (2 * k + 2) (lo + 2 ^ h) ∧
    Safe s1 n B h (2 * k + 1) lo (0 :: O) ∧ Safe s1 n B h (2 * k + 2) (lo + 2 ^ h) (0 :: O) ∧
    T s1 n h (2 * k + 1) lo = (T s n h (2 * k + 1) lo).map (· + s.la k) ∧
    T s1 n h (2 * k + 2) (lo + 2 ^ h) = (T s n h (2 * k + 2) (lo + 2 ^ h)).map (· + s.la k) ∧
    s1.la k = 0 ∧ s1.lv k = s.lv k ∧ s1.mx k = s.mx k ∧ s1.sx k = s.sx k ∧ s1.cx k = s.cx k ∧
    s1.mn k = s.mn k ∧ s1.sn k = s.sn k ∧ s1.cn k = s.cn k ∧ s1.len k = s.len k ∧
    (∀ j, j ≠ k → j ≠ 2 * k + 1 → j ≠ 2 * k + 2 → AgreeAt s s1 j)

theorem lv_bound_of_inv (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h c lo : Nat) (O : List Int) (o : Int)
    (ho : o ∈ O) (h0 : 0 ∈ O) (hI : Inv s n (h + 1) c lo) (hS : Safe s n B (h + 1) c lo O) (hl : s.lv c ≠ INF) :
    s.lv c + o ≠ INF := by
  obtain ⟨-, -, i3, -, -, i6, -⟩ := hI
  obtain ⟨e1, -, -, e4⟩ := i6 hl
  have hne : T s n (h + 1) c lo ≠ [] := by intro he; rw [i3.mx, he] at e1; rw [← e1] at e4; simp [lmax_nil] at e4
  have hmem : s.lv c ∈ T s n (h + 1) c lo := by
    rw [← e1, i3.mx]; exact lmax_mem _ hne (inR_zero _ (safe_inR s n B hB _ _ _ _ hS 0 h0))
  have := safe_top s n B _ _ _ _ hS o ho _ hmem
  rw [abs_le] at this; omega

theorem notsub_k (h k j : Nat) (hj : Sub h (2 * k + 1) j ∨ Sub h (2 * k + 2) j) : j ≠ k := by
  rcases hj with hj | hj <;> have := sub_ge h _ j hj <;> omega

theorem push_stage1 (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int) (h0 : 0 ∈ O)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O) (hlv : s.lv k = INF) :
    Stage1 s (if s.la k ≠ 0 then setLa (addAll (addAll s (2 * k + 1) (s.la k)) (2 * k + 2) (s.la k)) k 0 else s)
      n B h k lo O := by
  obtain ⟨i1, i2, -, -, i5, -, -⟩ := hI
  obtain ⟨S1, S2⟩ := hS.2 hlv
  have hO1 : 0 ∈ 0 :: O.map (· + s.la k) := List.mem_cons_self
  have hla1 : s.la k ∈ 0 :: O.map (· + s.la k) := List.mem_cons_of_mem _ (List.mem_map.mpr ⟨0, h0, by ring⟩)
  split_ifs with hla
  · have hreal : lo + 2 ^ (h + 1) ≤ n := by by_contra hc; exact hla (i5 (by omega)).1
    have hreal2 : lo + 2 ^ h + 2 ^ h ≤ n := by rw [pow_succ] at hreal; omega
    have hreal1 : lo + 2 ^ h ≤ n := Nat.le_trans (Nat.le_add_right _ _) hreal2
    have hlvB : ∀ c lo', Inv s n h c lo' → Safe s n B h c lo' (0 :: O.map (· + s.la k)) →
        0 < h → s.lv c ≠ INF → s.lv c + s.la k ≠ INF := by
      intro c lo' hIc hSc hpos hl
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      exact lv_bound_of_inv s n B hB h' c lo' _ _ hla1 hO1 hIc hSc hl
    set a1 := addAll s (2 * k + 1) (s.la k)
    obtain ⟨I1, T1⟩ := addAll_node s n B hB h _ lo _ hO1 i1 S1 hreal1 _ hla1
    have SS1 := safe_addAll s n B h _ lo O (s.la k) h0 S1 T1 (hlvB _ _ i1 S1)
    have ag1 := addAll_agree s (2 * k + 1) (s.la k)
    have f2 : ∀ j, Sub h (2 * k + 2) j → AgreeAt s a1 j := fun j hj => ag1 j (sub_disjoint h k j hj)
    have i2' := inv_frame s a1 n h _ _ f2 i2
    have S2' := safe_frame s a1 n B h _ _ _ f2 S2
    have hlak : a1.la k = s.la k := (ag1 k (by omega)).2.2.2.2.2.2.2.1.symm
    set a2 := addAll a1 (2 * k + 2) (s.la k)
    have T2a := T_frame s a1 n h _ (lo + 2 ^ h) f2
    obtain ⟨I2, T2⟩ := addAll_node a1 n B hB h _ _ _ hO1 i2' S2' hreal2 _ hla1
    have SS2 := safe_addAll a1 n B h _ _ O (s.la k) h0 S2' T2 (fun hp hl => by
      have e : s.lv (2 * k + 2) = a1.lv (2 * k + 2) := (ag1 _ (by omega)).2.2.2.2.2.2.2.2
      rw [← e] at hl ⊢; exact hlvB _ _ i2 S2 hp hl)
    have ag2 := addAll_agree a1 (2 * k + 2) (s.la k)
    have f1 : ∀ j, Sub h (2 * k + 1) j → AgreeAt a1 a2 j := fun j hj => ag2 j (sub_disjoint' h k j hj)
    have ag3 := setLa_agree a2 k 0
    have f3 : ∀ j, Sub h (2 * k + 1) j ∨ Sub h (2 * k + 2) j → AgreeAt a2 (setLa a2 k 0) j :=
      fun j hj => ag3 j (notsub_k h k j hj)
    have fk : AgreeAt s a2 k := agree_trans _ _ _ k (ag1 k (by omega)) (ag2 k (by omega))
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, -, x9⟩ := fk
    refine ⟨inv_frame _ _ n h _ _ (fun j hj => f3 j (Or.inl hj)) (inv_frame a1 a2 n h _ _ f1 I1),
      inv_frame _ _ n h _ _ (fun j hj => f3 j (Or.inr hj)) I2,
      safe_frame _ _ n B h _ _ _ (fun j hj => f3 j (Or.inl hj)) (safe_frame a1 a2 n B h _ _ _ f1 SS1),
      safe_frame _ _ n B h _ _ _ (fun j hj => f3 j (Or.inr hj)) SS2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun j hj1 hj2 hj3 => agree_trans _ _ _ j (agree_trans _ _ _ j (ag1 j hj2) (ag2 j hj3)) (ag3 j hj1)⟩
    · rw [← T_frame _ _ n h _ _ (fun j hj => f3 j (Or.inl hj)), ← T_frame a1 a2 n h _ _ f1, T1]
    · rw [← T_frame _ _ n h _ _ (fun j hj => f3 j (Or.inr hj)), T2, ← T2a]
    · simp [setLa, upF]
    all_goals simp only [setLa, upF, Function.update, ↓reduceDIte]
    all_goals first | exact x1.symm | exact x2.symm | exact x3.symm | exact x4.symm | exact x5.symm |
      exact x6.symm | exact x7.symm | exact x9.symm
  · have e0 : s.la k = 0 := by simpa using hla
    have m0 : ∀ L : List Int, L.map (· + s.la k) = L := fun L => by rw [e0]; simp
    have o0 : 0 :: O.map (· + s.la k) = 0 :: O := by rw [m0]
    rw [o0] at S1 S2
    exact ⟨i1, i2, S1, S2, (m0 _).symm, (m0 _).symm, e0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun j _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem T_child_nonempty (s : BS) (n h k lo : Nat) (c lo' : Nat) (hc : c = 2 * k + 1 ∧ lo' = lo ∨ c = 2 * k + 2 ∧ lo' = lo + 2 ^ h)
    (hne : (T s n h c lo').map (· + s.la k) ≠ []) : T s n (h + 1) k lo ≠ [] := by
  intro he
  simp only [T, List.map_eq_nil_iff, List.append_eq_nil_iff] at he
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

theorem childok_clamped (L0 : List Int) (mn mx : Int) (hR : InR (L0.map (fun v => max mn (min mx v))))
    (hle : L0 ≠ [] → mn ≤ mx) (hk : -INF ≤ mx ∧ mn ≤ INF) :
    let L := (L0.map (fun v => max mn (min mx v))).map (· + 0)
    (mx < lmax L → smax L < mx) ∧ (lmin L < mn → mn < smin L) ∧ (mx = mn → lmax L = lmin L ∨ L = []) := by
  intro L
  have hL : L = L0.map (fun v => max mn (min mx v)) := by simp [L]
  by_cases hne : L0 = []
  · subst hne
    have : L = [] := by simp [L]
    rw [this, lmax_nil, lmin_nil]
    exact ⟨fun h => by omega, fun h => by omega, fun _ => Or.inr rfl⟩
  have hle' := hle hne
  have hR' : InR L := by rw [hL]; exact hR
  have hne' : L ≠ [] := by rw [hL]; simpa using hne
  have hub : lmax L ≤ mx := by
    rw [lmax_le_iff _ _ (by have := (hR' _ (lmax_mem _ hne' hR')).1; have := lmax_ge L _ (lmax_mem _ hne' hR'); omega)]
    intro v hv; rw [hL] at hv; obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv; omega
  have hlb : mn ≤ lmin L := by
    rw [le_lmin_iff _ _ (by have := (hR' _ (lmin_mem _ hne' hR')).2; have := lmin_le L _ (lmin_mem _ hne' hR'); omega)]
    intro v hv; rw [hL] at hv; obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv; omega
  refine ⟨fun h => by omega, fun h => by omega, fun he => Or.inl ?_⟩
  have := lmin_le_lmax L hR' hne'; omega

theorem push_add (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int) (h0 : 0 ∈ O)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O) (hlv : s.lv k = INF) :
    PushPost s (push s k) n B h k lo O := by
  have hI0 := hI
  obtain ⟨-, -, i3, i4, i5, -, i7⟩ := hI
  obtain ⟨c1, c2⟩ := i7 hlv
  set s1 := (if s.la k ≠ 0 then setLa (addAll (addAll s (2 * k + 1) (s.la k)) (2 * k + 2) (s.la k)) k 0 else s)
    with hs1
  obtain ⟨I1, I2, S1, S2, T1, T2, l1, l2, m1, m2, m3, m4, m5, m6, m7, A1⟩ := push_stage1 s n B hB h k lo O h0 hI0 hS hlv
  have hpush : push s k = caps (caps s1 k (2 * k + 1)) k (2 * k + 2) := by
    unfold push; rw [if_neg (by simpa using hlv)]
  have hRk := inR_zero _ (safe_inR s n B hB (h + 1) k lo O hS 0 h0)
  have hk0 : -INF ≤ s1.mx k ∧ s1.mn k ≤ INF := by
    rw [m1, m4, i3.mx, i3.mn]; exact ⟨lmax_ge_ninf _, lmin_le_inf _⟩
  have hmnF : T s n (h + 1) k lo ≠ [] → s1.mn k ≤ s1.mx k := by
    intro hne; rw [m1, m4, i3.mx, i3.mn]; exact lmin_le_lmax _ hRk hne
  have hbxF : T s n (h + 1) k lo ≠ [] → ∀ o ∈ 0 :: O, |s1.mx k + o| ≤ B ∧ |s1.mn k + o| ≤ B := by
    intro hne o ho
    have ho' : o ∈ O := by rcases List.mem_cons.mp ho with rfl | ho; exacts [h0, ho]
    rw [m1, m4, i3.mx, i3.mn]
    exact ⟨safe_top s n B _ _ _ _ hS o ho' _ (lmax_mem _ hne hRk),
      safe_top s n B _ _ _ _ hS o ho' _ (lmin_mem _ hne hRk)⟩
  have ok1 : (s1.mx k < lmax (T s1 n h (2 * k + 1) lo) → smax (T s1 n h (2 * k + 1) lo) < s1.mx k) ∧
      (lmin (T s1 n h (2 * k + 1) lo) < s1.mn k → s1.mn k < smin (T s1 n h (2 * k + 1) lo)) ∧
      (s1.mx k = s1.mn k → lmax (T s1 n h (2 * k + 1) lo) = lmin (T s1 n h (2 * k + 1) lo) ∨
        T s1 n h (2 * k + 1) lo = []) := by rw [T1, m1, m4]; exact c1
  have ok2 : (s1.mx k < lmax (T s1 n h (2 * k + 2) (lo + 2 ^ h)) → smax (T s1 n h (2 * k + 2) (lo + 2 ^ h)) < s1.mx k) ∧
      (lmin (T s1 n h (2 * k + 2) (lo + 2 ^ h)) < s1.mn k → s1.mn k < smin (T s1 n h (2 * k + 2) (lo + 2 ^ h))) ∧
      (s1.mx k = s1.mn k → lmax (T s1 n h (2 * k + 2) (lo + 2 ^ h)) = lmin (T s1 n h (2 * k + 2) (lo + 2 ^ h)) ∨
        T s1 n h (2 * k + 2) (lo + 2 ^ h) = []) := by rw [T2, m1, m4]; exact c2
  have ne1 : T s1 n h (2 * k + 1) lo ≠ [] → T s n (h + 1) k lo ≠ [] := fun hn =>
    T_child_nonempty s n h k lo _ _ (Or.inl ⟨rfl, rfl⟩) (by rw [← T1]; exact hn)
  have ne2 : T s1 n h (2 * k + 2) (lo + 2 ^ h) ≠ [] → T s n (h + 1) k lo ≠ [] := fun hn =>
    T_child_nonempty s n h k lo _ _ (Or.inr ⟨rfl, rfl⟩) (by rw [← T2]; exact hn)
  obtain ⟨J1, R1, U1, B1⟩ := caps_spec s1 n B hB h (2 * k + 1) lo (0 :: O) List.mem_cons_self k (by omega) I1 S1 hk0
    (fun hn => hmnF (ne1 hn)) (fun hn => hbxF (ne1 hn)) ok1
  set t1 := caps s1 k (2 * k + 1)
  have f2 : ∀ j, Sub h (2 * k + 2) j → AgreeAt s1 t1 j := fun j hj => B1 j (sub_disjoint h k j hj)
  have I2' := inv_frame s1 t1 n h _ _ f2 I2
  have S2' := safe_frame s1 t1 n B h _ _ _ f2 S2
  have T2' := T_frame s1 t1 n h _ (lo + 2 ^ h) f2
  have ak1 := B1 k (by omega)
  have hk0' : -INF ≤ t1.mx k ∧ t1.mn k ≤ INF := by rw [← ak1.1, ← ak1.2.2.2.1]; exact hk0
  have ok2' := ok2
  rw [T2', ak1.1, ak1.2.2.2.1] at ok2'
  obtain ⟨J2, R2, U2, B2⟩ := caps_spec t1 n B hB h (2 * k + 2) (lo + 2 ^ h) (0 :: O) List.mem_cons_self k (by omega)
    I2' S2' hk0' (fun hn => by rw [← ak1.1, ← ak1.2.2.2.1]; exact hmnF (ne2 (by rw [T2']; exact hn)))
    (fun hn => by rw [← ak1.1, ← ak1.2.2.2.1]; exact hbxF (ne2 (by rw [T2']; exact hn))) ok2'
  set t2 := caps t1 k (2 * k + 2)
  have f1 : ∀ j, Sub h (2 * k + 1) j → AgreeAt t1 t2 j := fun j hj => B2 j (sub_disjoint' h k j hj)
  have ak2 := B2 k (by omega)
  have ak := agree_trans _ _ _ k ak1 ak2
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9⟩ := ak
  have hp' : push s k = t2 := hpush
  rw [hp']
  have Tc1 : T t2 n h (2 * k + 1) lo = (T s n h (2 * k + 1) lo).map (tau s k) := by
    rw [← T_frame t1 t2 n h _ _ f1, U1, T1, List.map_map, m1, m4]
    apply List.map_congr_left; intro v _; rfl
  have Tc2 : T t2 n h (2 * k + 2) (lo + 2 ^ h) = (T s n h (2 * k + 2) (lo + 2 ^ h)).map (tau s k) := by
    rw [U2, ← T2', T2, List.map_map, ← ak1.1, ← ak1.2.2.2.1, m1, m4]
    apply List.map_congr_left; intro v _; rfl
  have fx : t2.mx k = s.mx k := by rw [← y1, m1]
  have fn : t2.mn k = s.mn k := by rw [← y4, m4]
  have fla : t2.la k = 0 := by rw [← y8, l1]
  have flv : t2.lv k = INF := by rw [← y9, l2, hlv]
  have hTk : T t2 n (h + 1) k lo = T s n (h + 1) k lo := by
    show (T t2 n h _ lo ++ T t2 n h _ _).map (tau t2 k) = (T s n h _ lo ++ T s n h _ _).map (tau s k)
    rw [Tc1, Tc2, ← List.map_append, List.map_map]
    apply List.map_congr_left; intro v _
    simp only [Function.comp_apply, tau, fx, fn, fla]; omega
  have hRc : ∀ c lo', T t2 n h c lo' = (T s n h c lo').map (tau s k) → (c = 2 * k + 1 ∧ lo' = lo ∨
      c = 2 * k + 2 ∧ lo' = lo + 2 ^ h) → InR (T t2 n h c lo') := by
    intro c lo' hc hcc v hv
    rw [hc] at hv
    exact hRk v (by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      exact List.mem_map.mpr ⟨w, by rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hw], rfl⟩)
  have hclamp : ∀ c lo', T t2 n h c lo' = (T s n h c lo').map (tau s k) →
      T t2 n h c lo' = ((T s n h c lo').map (· + s.la k)).map (fun v => max (s.mn k) (min (s.mx k) v)) := by
    intro c lo' hc; rw [hc, List.map_map]; rfl
  have hk' : -INF ≤ s.mx k ∧ s.mn k ≤ INF := by rw [← m1, ← m4]; exact hk0
  have hle1 : (T s n h (2 * k + 1) lo).map (· + s.la k) ≠ [] → s.mn k ≤ s.mx k := fun hn =>
    by rw [← m1, ← m4]; exact hmnF (T_child_nonempty s n h k lo _ _ (Or.inl ⟨rfl, rfl⟩) hn)
  have hle2 : (T s n h (2 * k + 2) (lo + 2 ^ h)).map (· + s.la k) ≠ [] → s.mn k ≤ s.mx k := fun hn =>
    by rw [← m1, ← m4]; exact hmnF (T_child_nonempty s n h k lo _ _ (Or.inr ⟨rfl, rfl⟩) hn)
  refine ⟨⟨inv_frame t1 t2 n h _ _ f1 J1, J2, ?_, by rw [← y7, m7]; exact i4, fun _ => ⟨fla, flv⟩,
      fun hl => absurd flv hl, fun _ => ?_⟩, ⟨by rw [hTk]; exact hS.1, fun _ => ?_⟩, hTk, fla, flv, fx,
      by rw [← y2, m2], by rw [← y3, m3], fn, by rw [← y5, m5], by rw [← y6, m6], by rw [← y7, m7],
      fun j hj1 hj2 hj3 => agree_trans _ _ _ j (agree_trans _ _ _ j (A1 j hj1 hj2 hj3) (B1 j hj2)) (B2 j hj3),
      Tc1, Tc2⟩
  · unfold SummK; rw [hTk, ← y1, ← y2, ← y3, ← y4, ← y5, ← y6, m1, m2, m3, m4, m5, m6]; exact i3
  · unfold ChildOK
    rw [fx, fn, fla]
    have e1 := hclamp _ _ Tc1
    have e2 := hclamp _ _ Tc2
    have r1 := hRc _ _ Tc1 (Or.inl ⟨rfl, rfl⟩)
    have r2 := hRc _ _ Tc2 (Or.inr ⟨rfl, rfl⟩)
    rw [e1] at r1 ⊢; rw [e2] at r2 ⊢
    exact ⟨childok_clamped _ _ _ r1 hle1 hk', childok_clamped _ _ _ r2 hle2 hk'⟩
  · rw [fla]
    have hO : (0 :: O.map (· + 0)) = 0 :: O := by simp
    rw [hO]
    exact ⟨safe_frame t1 t2 n B h _ _ _ f1 R1, R2⟩

end Proofs.Cpp.SegmentTreeBeatsMath
