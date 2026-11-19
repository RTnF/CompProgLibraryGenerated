namespace Proofs.PrimMath

/-- Reflexive transitive closure. -/
inductive Rtc (R : Nat → Nat → Prop) : Nat → Nat → Prop
  | refl (a : Nat) : Rtc R a a
  | tail {a b c : Nat} : Rtc R a b → R b c → Rtc R a c

theorem Rtc.single {R : Nat → Nat → Prop} {a b : Nat} (h : R a b) : Rtc R a b := Rtc.tail (Rtc.refl a) h

theorem Rtc.trans {R : Nat → Nat → Prop} {a b c : Nat} (h1 : Rtc R a b) (h2 : Rtc R b c) : Rtc R a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hbc ih => exact Rtc.tail ih hbc

theorem Rtc.head {R : Nat → Nat → Prop} {a b c : Nat} (h : R a b) (h2 : Rtc R b c) : Rtc R a c :=
  Rtc.trans (Rtc.single h) h2

theorem Rtc.mono {R S : Nat → Nat → Prop} (h : ∀ a b, R a b → S a b) {a b : Nat} (hr : Rtc R a b) : Rtc S a b := by
  induction hr with
  | refl => exact Rtc.refl _
  | tail _ hbc ih => exact Rtc.tail ih (h _ _ hbc)

theorem Rtc.symm {R : Nat → Nat → Prop} (hs : ∀ a b, R a b → R b a) {a b : Nat} (h : Rtc R a b) : Rtc R b a := by
  induction h with
  | refl => exact Rtc.refl _
  | tail _ hbc ih => exact Rtc.head (hs _ _ hbc) ih

/-- The first step of a path. -/
theorem Rtc.cases_head {R : Nat → Nat → Prop} {a c : Nat} (h : Rtc R a c) : a = c ∨ ∃ b, R a b ∧ Rtc R b c := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hab hbc ih =>
    rcases ih with rfl | ⟨b', hb', hrest⟩
    · exact Or.inr ⟨_, hbc, Rtc.refl _⟩
    · exact Or.inr ⟨b', hb', Rtc.tail hrest hbc⟩

/-- If `a` has no outgoing step, a path from `a` is trivial. -/
theorem Rtc.eq_of_stuck {R : Nat → Nat → Prop} {a c : Nat} (hs : ∀ x, ¬ R a x) (h : Rtc R a c) : c = a := by
  induction h with
  | refl => rfl
  | tail hab hbc ih =>
    subst ih
    exact absurd hbc (hs _)

/-! ### Graphs and rooted forests -/

abbrev Arc := Nat × Nat × Nat

/-- A symmetric arc list on the vertices `< n`, all weights `≤ B`. -/
structure Graph (n B : Nat) (E : List Arc) : Prop where
  lt : ∀ a ∈ E, a.1 < n ∧ a.2.1 < n
  sym : ∀ a ∈ E, (a.2.1, a.1, a.2.2) ∈ E
  bound : ∀ a ∈ E, a.2.2 ≤ B

/-- The arcs of weight below `t`, as a relation. -/
def Gt (E : List Arc) (t : Nat) (u v : Nat) : Prop := ∃ w, w < t ∧ (u, v, w) ∈ E

/-- The parent step of a rooted forest (parent weight below `t`). -/
def PS (par : Nat → Option (Nat × Nat)) (t : Nat) (u p : Nat) : Prop := ∃ w, w < t ∧ par u = some (p, w)

def FAdj (par : Nat → Option (Nat × Nat)) (t : Nat) (u v : Nat) : Prop := PS par t u v ∨ PS par t v u

/-- `par v = some (p, w)`: the parent of `v` is `p` through an arc of weight `w`; `rank` decreases along parents. -/
structure Forest (n : Nat) (E : List Arc) (par : Nat → Option (Nat × Nat)) (rank : Nat → Nat) : Prop where
  par_ok : ∀ v, v < n → ∀ p w, par v = some (p, w) → p < n ∧ (v, p, w) ∈ E ∧ rank p < rank v
  par_out : ∀ v, n ≤ v → par v = none

/-- Every arc is covered by the forest (the forest spans every component), for the arcs of weight below `t`. -/
def Spans (E : List Arc) (par : Nat → Option (Nat × Nat)) (t : Nat) : Prop :=
  ∀ a ∈ E, a.2.2 < t → Rtc (FAdj par t) a.1 a.2.1

def IsRoot (par : Nat → Option (Nat × Nat)) (t v : Nat) : Prop := ¬ ∃ p w, w < t ∧ par v = some (p, w)

theorem isRoot_stuck (par : Nat → Option (Nat × Nat)) (t v : Nat) (h : IsRoot par t v) : ∀ x, ¬ PS par t v x := by
  intro x ⟨w, hw, hp⟩
  exact h ⟨x, w, hw, hp⟩

/-- Every vertex reaches a root along parent steps. -/
theorem chain_to_root {n : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} {rank : Nat → Nat}
    (F : Forest n E par rank) (t : Nat) : ∀ (k v : Nat), rank v ≤ k → v < n → ∃ ρ, ρ < n ∧ IsRoot par t ρ ∧ Rtc (PS par t) v ρ := by
  intro k
  induction k with
  | zero =>
    intro v hk hv
    by_cases hr : IsRoot par t v
    · exact ⟨v, hv, hr, Rtc.refl _⟩
    · unfold IsRoot at hr
      rw [Classical.not_not] at hr
      obtain ⟨p, w, hw, hp⟩ := hr
      have := (F.par_ok v hv p w hp).2.2
      omega
  | succ k ih =>
    intro v hk hv
    by_cases hr : IsRoot par t v
    · exact ⟨v, hv, hr, Rtc.refl _⟩
    · unfold IsRoot at hr
      rw [Classical.not_not] at hr
      obtain ⟨p, w, hw, hp⟩ := hr
      obtain ⟨hpn, _, hrk⟩ := F.par_ok v hv p w hp
      obtain ⟨ρ, hρ, hρr, hρc⟩ := ih p (by omega) hpn
      exact ⟨ρ, hρ, hρr, Rtc.head ⟨w, hw, hp⟩ hρc⟩

/-- Confluence: two vertices joined by forest arcs have a common ancestor. -/
theorem common_ancestor {par : Nat → Option (Nat × Nat)} {t : Nat} {a b : Nat} (h : Rtc (FAdj par t) a b) :
    ∃ c, Rtc (PS par t) a c ∧ Rtc (PS par t) b c := by
  induction h with
  | refl => exact ⟨_, Rtc.refl _, Rtc.refl _⟩
  | tail hab hbc ih =>
    obtain ⟨c, hac, hbc'⟩ := ih
    rcases hbc with hps | hps
    · -- the parent of `b'` is `b''`
      rename_i b' b''
      rcases Rtc.cases_head hbc' with heq | ⟨x, hx, hxc⟩
      · subst heq
        exact ⟨b'', Rtc.tail hac hps, Rtc.refl _⟩
      · have : x = b'' := by
          obtain ⟨w1, _, h1⟩ := hps
          obtain ⟨w2, _, h2⟩ := hx
          rw [h1] at h2
          exact (Prod.mk.inj (Option.some.inj h2)).1.symm
        subst this
        exact ⟨c, hac, hxc⟩
    · exact ⟨c, hac, Rtc.head hps hbc'⟩

theorem root_unique {par : Nat → Option (Nat × Nat)} {t a b : Nat} (h : Rtc (FAdj par t) a b) (ha : IsRoot par t a)
    (hb : IsRoot par t b) : a = b := by
  obtain ⟨c, hac, hbc⟩ := common_ancestor h
  have h1 := Rtc.eq_of_stuck (isRoot_stuck par t a ha) hac
  have h2 := Rtc.eq_of_stuck (isRoot_stuck par t b hb) hbc
  rw [← h1, ← h2]

/-! ### Counting -/

open Classical in
noncomputable def rootsL (n : Nat) (par : Nat → Option (Nat × Nat)) (t : Nat) : List Nat :=
  (List.range n).filter (fun v => decide (IsRoot par t v))

def IsRep (E : List Arc) (t n v : Nat) : Prop := v < n ∧ ∀ u, u < n → Rtc (Gt E t) u v → v ≤ u

open Classical in
noncomputable def repsL (n : Nat) (E : List Arc) (t : Nat) : List Nat :=
  (List.range n).filter (fun v => decide (IsRep E t n v))

open Classical in
theorem mem_rootsL {n : Nat} {par : Nat → Option (Nat × Nat)} {t v : Nat} : v ∈ rootsL n par t ↔ v < n ∧ IsRoot par t v := by
  unfold rootsL
  rw [List.mem_filter, decide_eq_true_iff, List.mem_range]

open Classical in
theorem mem_repsL {n : Nat} {E : List Arc} {t v : Nat} : v ∈ repsL n E t ↔ IsRep E t n v := by
  unfold repsL
  rw [List.mem_filter, decide_eq_true_iff, List.mem_range]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨h.1, h⟩

theorem nodup_rootsL (n : Nat) (par : Nat → Option (Nat × Nat)) (t : Nat) : (rootsL n par t).Nodup :=
  List.Nodup.sublist List.filter_sublist List.nodup_range

theorem nodup_repsL (n : Nat) (E : List Arc) (t : Nat) : (repsL n E t).Nodup :=
  List.Nodup.sublist List.filter_sublist List.nodup_range

theorem nodup_map_inj {l : List Nat} (hl : l.Nodup) (f : Nat → Nat) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hl
    refine ⟨?_, ih hl.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    intro hmem
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
    have := hinj a (by simp) b (List.mem_cons_of_mem _ hb) hfb.symm
    exact hl.1 (this ▸ hb)

theorem card_le_of_inj {l1 l2 : List Nat} (hl : l1.Nodup) (f : Nat → Nat) (hmap : ∀ x ∈ l1, f x ∈ l2)
    (hinj : ∀ x ∈ l1, ∀ y ∈ l1, f x = f y → x = y) : l1.length ≤ l2.length := by
  have hnd := nodup_map_inj hl f hinj
  have hsub : l1.map f ⊆ l2 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hmap x hx
  have := List.Nodup.length_le_of_subset hnd hsub
  simpa using this

theorem exists_least (P : Nat → Prop) (h : ∃ x, P x) : ∃ x, P x ∧ ∀ y, P y → x ≤ y := by
  obtain ⟨x, hx⟩ := h
  have key : ∀ (k x : Nat), x ≤ k → P x → ∃ x, P x ∧ ∀ y, P y → x ≤ y := by
    intro k
    induction k with
    | zero =>
      intro x hxk hPx
      refine ⟨x, hPx, ?_⟩
      intro y hy
      omega
    | succ k ih =>
      intro x hxk hPx
      by_cases hlow : ∃ y, y < x ∧ P y
      · obtain ⟨y, hy, hPy⟩ := hlow
        exact ih y (by omega) hPy
      · refine ⟨x, hPx, ?_⟩
        intro y hy
        exact Classical.byContradiction fun hlt => hlow ⟨y, by omega, hy⟩
  exact key x x (Nat.le_refl _) hx

theorem Gt_symm {n B : Nat} {E : List Arc} (G : Graph n B E) (t : Nat) : ∀ a b, Gt E t a b → Gt E t b a := by
  intro a b ⟨w, hw, hmem⟩
  exact ⟨w, hw, G.sym _ hmem⟩

/-- A forest arc below `t` is a graph arc below `t`. -/
theorem PS_Gt {n : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} {rank : Nat → Nat} (F : Forest n E par rank)
    (t : Nat) {a b : Nat} (hlt : a < n) (h : PS par t a b) : Gt E t a b := by
  obtain ⟨w, hw, hp⟩ := h
  exact ⟨w, hw, (F.par_ok a hlt b w hp).2.1⟩

theorem PS_lt {n : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} {rank : Nat → Nat} (F : Forest n E par rank)
    (t : Nat) {a b : Nat} (hlt : a < n) (h : PS par t a b) : b < n := by
  obtain ⟨w, hw, hp⟩ := h
  exact (F.par_ok a hlt b w hp).1

theorem Rtc_PS_Gt {n : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} {rank : Nat → Nat}
    (F : Forest n E par rank) (t : Nat) {a b : Nat} (ha : a < n) (h : Rtc (PS par t) a b) :
    b < n ∧ Rtc (Gt E t) a b := by
  induction h with
  | refl => exact ⟨ha, Rtc.refl _⟩
  | tail hab hbc ih =>
    obtain ⟨hbn, hb⟩ := ih
    exact ⟨PS_lt F t hbn hbc, Rtc.tail hb (PS_Gt F t hbn hbc)⟩

/-- There are at least as many roots of the forest below `t` as classes of the graph below `t`. -/
theorem reps_le_roots {n B : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} {rank : Nat → Nat} (G : Graph n B E)
    (F : Forest n E par rank) (t : Nat) : (repsL n E t).length ≤ (rootsL n par t).length := by
  classical
  let f : Nat → Nat := fun r => if h : r < n then Classical.choose (chain_to_root F t (rank r) r (Nat.le_refl _) h) else 0
  have hf : ∀ r, r < n → f r < n ∧ IsRoot par t (f r) ∧ Rtc (PS par t) r (f r) := by
    intro r hr
    have := Classical.choose_spec (chain_to_root F t (rank r) r (Nat.le_refl _) hr)
    simpa [f, hr] using this
  refine card_le_of_inj (nodup_repsL n E t) f ?_ ?_
  · intro r hr
    have hrep := mem_repsL.mp hr
    obtain ⟨h1, h2, _⟩ := hf r hrep.1
    exact mem_rootsL.mpr ⟨h1, h2⟩
  · intro r hr r' hr' heq
    have hrep := mem_repsL.mp hr
    have hrep' := mem_repsL.mp hr'
    obtain ⟨h1, h2, h3⟩ := hf r hrep.1
    obtain ⟨h1', h2', h3'⟩ := hf r' hrep'.1
    have c1 := (Rtc_PS_Gt F t hrep.1 h3).2
    have c2 := (Rtc_PS_Gt F t hrep'.1 h3').2
    rw [← heq] at c2
    have hs := Gt_symm G t
    have a1 : Rtc (Gt E t) r' r := Rtc.trans c2 (Rtc.symm hs c1)
    have a2 : Rtc (Gt E t) r r' := Rtc.trans c1 (Rtc.symm hs c2)
    have := hrep.2 r' hrep'.1 a1
    have := hrep'.2 r hrep.1 a2
    omega

/-- If the forest connects everything the graph below `t` connects, it has no more roots than the graph has classes. -/
theorem roots_le_reps {n B : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} {rank : Nat → Nat} (G : Graph n B E)
    (F : Forest n E par rank) (t : Nat)
    (hclaim : ∀ a b, a < n → b < n → Rtc (Gt E t) a b → Rtc (FAdj par t) a b) :
    (rootsL n par t).length ≤ (repsL n E t).length := by
  classical
  have hex : ∀ ρ, ρ < n → ∃ x, (x < n ∧ Rtc (Gt E t) x ρ) ∧ ∀ y, (y < n ∧ Rtc (Gt E t) y ρ) → x ≤ y :=
    fun ρ hρ => exists_least _ ⟨ρ, hρ, Rtc.refl _⟩
  let g : Nat → Nat := fun ρ => if h : ρ < n then Classical.choose (hex ρ h) else 0
  have hg : ∀ ρ, ρ < n → (g ρ < n ∧ Rtc (Gt E t) (g ρ) ρ) ∧ ∀ y, (y < n ∧ Rtc (Gt E t) y ρ) → g ρ ≤ y := by
    intro ρ hρ
    have := Classical.choose_spec (hex ρ hρ)
    simpa [g, hρ] using this
  have hs := Gt_symm G t
  refine card_le_of_inj (nodup_rootsL n par t) g ?_ ?_
  · intro ρ hρ
    have hr := mem_rootsL.mp hρ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hg ρ hr.1
    refine mem_repsL.mpr ⟨h1, ?_⟩
    intro u hu hc
    exact h3 u ⟨hu, Rtc.trans hc h2⟩
  · intro ρ hρ ρ' hρ' heq
    have hr := mem_rootsL.mp hρ
    have hr' := mem_rootsL.mp hρ'
    obtain ⟨⟨h1, h2⟩, _⟩ := hg ρ hr.1
    obtain ⟨⟨h1', h2'⟩, _⟩ := hg ρ' hr'.1
    rw [← heq] at h2'
    have hc : Rtc (Gt E t) ρ ρ' := Rtc.trans (Rtc.symm hs h2) h2'
    exact root_unique (hclaim ρ ρ' hr.1 hr'.1 hc) hr.2 hr'.2

/-! ### The weight of a forest as a sum over thresholds -/

def wt (par : Nat → Option (Nat × Nat)) (v : Nat) : Nat :=
  match par v with
  | some (_, w) => w
  | none => 0

def Weight (n : Nat) (par : Nat → Option (Nat × Nat)) : Nat := ((List.range n).map (wt par)).sum

/-- `∑_{k < m} f k`. -/
def ssum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, f => ssum k f + f k

theorem ssum_add (m : Nat) (f g : Nat → Nat) : ssum m (fun k => f k + g k) = ssum m f + ssum m g := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [ssum]; rw [ih]; omega

theorem ssum_mono (m : Nat) (f g : Nat → Nat) (h : ∀ k, k < m → f k ≤ g k) : ssum m f ≤ ssum m g := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    simp only [ssum]
    have := ih (fun k hk => h k (by omega))
    have := h m (by omega)
    omega

theorem ssum_congr (m : Nat) (f g : Nat → Nat) (h : ∀ k, k < m → f k = g k) : ssum m f = ssum m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [ssum]
    rw [ih (fun k hk => h k (by omega)), h m (by omega)]

theorem ssum_zero (m : Nat) : ssum m (fun _ => 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [ssum]; rw [ih]

theorem ssum_indicator_min (B a : Nat) : ssum B (fun s => if s + 1 ≤ a then 1 else 0) = min a B := by
  induction B with
  | zero => simp [ssum]
  | succ B ih =>
    simp only [ssum]
    rw [ih]
    by_cases h : B + 1 ≤ a
    · simp [h]; omega
    · simp [h]; omega

theorem ssum_indicator (B a : Nat) (ha : a ≤ B) : ssum B (fun s => if s + 1 ≤ a then 1 else 0) = a := by
  rw [ssum_indicator_min]; omega

/-- `l.sum` as a sum over thresholds of the number of entries above the threshold. -/
theorem sum_thresholds (B : Nat) : ∀ (l : List Nat), (∀ x ∈ l, x ≤ B) →
    l.sum = ssum B (fun s => (l.map (fun x => if s + 1 ≤ x then 1 else 0)).sum) := by
  intro l
  induction l with
  | nil =>
    intro _
    simp [ssum_zero]
  | cons a l ih =>
    intro h
    have ha : a ≤ B := h a (by simp)
    have hl : ∀ x ∈ l, x ≤ B := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.sum_cons, ih hl]
    have e : ssum B (fun s => ((a :: l).map (fun x => if s + 1 ≤ x then 1 else 0)).sum) =
        ssum B (fun s => (if s + 1 ≤ a then 1 else 0) + (l.map (fun x => if s + 1 ≤ x then 1 else 0)).sum) := by
      apply ssum_congr
      intro k _
      simp
    rw [e, ssum_add, ssum_indicator B a ha]

theorem sum_map_add (l : List Nat) (f g : Nat → Nat) : (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; omega

open Classical in
theorem length_filter_eq_sum (l : List Nat) (p : Nat → Prop) :
    (l.filter (fun v => decide (p v))).length = (l.map (fun v => if p v then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a
    · simp [List.filter_cons, h, ih]; omega
    · simp [List.filter_cons, h, ih]

open Classical in
theorem rootsL_length (n : Nat) (par : Nat → Option (Nat × Nat)) (t : Nat) :
    (rootsL n par t).length = ((List.range n).map (fun v => if IsRoot par t v then 1 else 0)).sum := by
  unfold rootsL
  exact length_filter_eq_sum _ _

theorem map_congr_mem (l : List Nat) (f g : Nat → Nat) (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons]
    rw [h a (by simp), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

open Classical in
/-- The weight of a forest is the sum over the thresholds `s + 1` of the number of vertices whose parent arc is at least `s + 1`. -/
theorem weight_eq {n B : Nat} {par : Nat → Option (Nat × Nat)} (hB : ∀ v p w, par v = some (p, w) → w ≤ B) :
    Weight n par = ssum B (fun s => (rootsL n par (s + 1)).length - (rootsL n par (B + 1)).length) := by
  have hwt : ∀ v, wt par v ≤ B := by
    intro v
    cases h : par v with
    | none => simp [wt, h]
    | some pw => simpa [wt, h] using hB v pw.1 pw.2 h
  unfold Weight
  rw [sum_thresholds B ((List.range n).map (wt par)) (by
    intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact hwt v)]
  apply ssum_congr
  intro s hs
  rw [List.map_map]
  have hind : ∀ v, (if IsRoot par (s + 1) v then 1 else 0) =
      (if IsRoot par (B + 1) v then 1 else 0) + (if s + 1 ≤ wt par v then 1 else 0) := by
    intro v
    unfold wt IsRoot
    cases h : par v with
    | none => simp
    | some pw =>
      obtain ⟨p, w⟩ := pw
      have hw := hB v p w h
      by_cases h1 : s + 1 ≤ w
      · have : ¬ ∃ p' w', w' < s + 1 ∧ some (p, w) = some (p', w') := by
          intro ⟨p', w', hw', he⟩
          have := Option.some.inj he
          have := (Prod.mk.inj this).2
          omega
        have h2 : (∃ p' w', w' < B + 1 ∧ some (p, w) = some (p', w')) := ⟨p, w, by omega, rfl⟩
        have hlt : w < B + 1 := by omega
        simp [this, h2, h1, hlt]
      · have h3 : (∃ p' w', w' < s + 1 ∧ some (p, w) = some (p', w')) := ⟨p, w, by omega, rfl⟩
        have h2 : (∃ p' w', w' < B + 1 ∧ some (p, w) = some (p', w')) := ⟨p, w, by omega, rfl⟩
        have hlt : w < B + 1 := by omega
        simp [h3, h2, h1, hlt]
  have e : ((List.range n).map ((fun x => if s + 1 ≤ x then 1 else 0) ∘ wt par)) =
      (List.range n).map (fun v => (if IsRoot par (s + 1) v then 1 else 0) - (if IsRoot par (B + 1) v then 1 else 0)) := by
    apply map_congr_mem
    intro v _
    have := hind v
    simp only [Function.comp]
    omega
  rw [e]
  have hsum := rootsL_length n par (s + 1)
  have hsum2 := rootsL_length n par (B + 1)
  have hadd : ((List.range n).map (fun v => if IsRoot par (s + 1) v then 1 else 0)).sum =
      ((List.range n).map (fun v => if IsRoot par (B + 1) v then 1 else 0)).sum +
      ((List.range n).map (fun v => (if IsRoot par (s + 1) v then 1 else 0) - (if IsRoot par (B + 1) v then 1 else 0))).sum := by
    rw [← sum_map_add]
    congr 1
    apply map_congr_mem
    intro v _
    have := hind v
    omega
  omega

/-- The minimum weight of a spanning forest, as a function of the graph only. -/
noncomputable def MSTW (n B : Nat) (E : List Arc) : Nat := ssum B (fun s => (repsL n E (s + 1)).length - (repsL n E (B + 1)).length)

theorem forest_bound {n B : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} {rank : Nat → Nat} (G : Graph n B E)
    (F : Forest n E par rank) : ∀ v p w, par v = some (p, w) → w ≤ B := by
  intro v p w h
  have hv : v < n := Classical.byContradiction fun hn => by
    have := F.par_out v (by omega)
    rw [this] at h
    cases h
  exact G.bound _ (F.par_ok v hv p w h).2.1

theorem spans_claim {n B : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} (G : Graph n B E) (hsp : Spans E par (B + 1)) :
    ∀ a b, a < n → b < n → Rtc (Gt E (B + 1)) a b → Rtc (FAdj par (B + 1)) a b := by
  intro a b ha hb h
  clear ha hb
  induction h with
  | refl => exact Rtc.refl _
  | tail hab hbc ih =>
    obtain ⟨w, hw, hmem⟩ := hbc
    exact Rtc.trans ih (hsp _ hmem hw)

/-- Every spanning rooted forest weighs at least `MSTW`. -/
theorem weight_ge_mstw {n B : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} {rank : Nat → Nat} (G : Graph n B E)
    (F : Forest n E par rank) (hsp : Spans E par (B + 1)) : MSTW n B E ≤ Weight n par := by
  rw [weight_eq (forest_bound G F)]
  unfold MSTW
  have hr := roots_le_reps G F (B + 1) (spans_claim G hsp)
  apply ssum_mono
  intro s _
  have := reps_le_roots G F (s + 1)
  omega

/-- A forest whose roots below every threshold are as few as the graph's classes weighs exactly `MSTW`. -/
theorem weight_eq_mstw {n B : Nat} {E : List Arc} {par : Nat → Option (Nat × Nat)} {rank : Nat → Nat} (G : Graph n B E)
    (F : Forest n E par rank)
    (hclaim : ∀ t, 1 ≤ t → t ≤ B + 1 → ∀ a b, a < n → b < n → Rtc (Gt E t) a b → Rtc (FAdj par t) a b) :
    Weight n par = MSTW n B E := by
  rw [weight_eq (forest_bound G F)]
  unfold MSTW
  apply ssum_congr
  intro s hs
  have h1 := roots_le_reps G F (s + 1) (hclaim (s + 1) (by omega) (by omega))
  have h2 := reps_le_roots G F (s + 1)
  have h3 := roots_le_reps G F (B + 1) (hclaim (B + 1) (by omega) (Nat.le_refl _))
  have h4 := reps_le_roots G F (B + 1)
  omega

/-! ### Prim's order of visits -/

/-- Visit `j` is the vertex `vert j` (position `pos v` of vertex `v`); `c j` is the cost of the arc that brought the vertex in
(0 when a new component starts, which happens only when no arc leaves the visited set). Every attached arc is a lightest arc
leaving the visited set. -/
structure PrimRun (n : Nat) (E : List Arc) (vert pos c : Nat → Nat) : Prop where
  vp : ∀ j, j < n → vert j < n ∧ pos (vert j) = j
  pv : ∀ v, v < n → pos v < n ∧ vert (pos v) = v
  step : ∀ j, j < n →
    (c j = 0 ∧ ∀ a ∈ E, pos a.1 < j → pos a.2.1 < j) ∨
    (∃ y, y < n ∧ pos y < j ∧ (y, vert j, c j) ∈ E ∧ ∀ a ∈ E, pos a.1 < j → j ≤ pos a.2.1 → c j ≤ a.2.2)

open Classical in
/-- The forest of Prim's run. -/
noncomputable def primPar (n : Nat) (E : List Arc) (pos c : Nat → Nat) (v : Nat) : Option (Nat × Nat) :=
  if v < n then
    (if h : ∃ y, y < n ∧ pos y < pos v ∧ (y, v, c (pos v)) ∈ E then some (Classical.choose h, c (pos v)) else none)
  else none

theorem primPar_attach {n : Nat} {E : List Arc} {vert pos c : Nat → Nat} (R : PrimRun n E vert pos c) {v : Nat} (hv : v < n)
    (h : ∃ y, y < n ∧ pos y < pos v ∧ (y, v, c (pos v)) ∈ E) :
    ∃ y, y < n ∧ pos y < pos v ∧ (y, v, c (pos v)) ∈ E ∧ primPar n E pos c v = some (y, c (pos v)) := by
  classical
  have hc := Classical.choose_spec h
  refine ⟨Classical.choose h, hc.1, hc.2.1, hc.2.2, ?_⟩
  unfold primPar
  simp [hv, h]

theorem primPar_start {n : Nat} {E : List Arc} {pos c : Nat → Nat} {v : Nat} (hv : v < n)
    (h : ¬ ∃ y, y < n ∧ pos y < pos v ∧ (y, v, c (pos v)) ∈ E) : primPar n E pos c v = none := by
  classical
  unfold primPar
  simp [hv, h]

theorem primPar_out {n : Nat} {E : List Arc} {pos c : Nat → Nat} {v : Nat} (hv : n ≤ v) : primPar n E pos c v = none := by
  unfold primPar
  simp [Nat.not_lt.mpr hv]

theorem primPar_forest {n B : Nat} {E : List Arc} {vert pos c : Nat → Nat} (G : Graph n B E) (R : PrimRun n E vert pos c) :
    Forest n E (primPar n E pos c) pos := by
  classical
  refine ⟨?_, fun v hv => primPar_out hv⟩
  intro v hv p w hpar
  by_cases h : ∃ y, y < n ∧ pos y < pos v ∧ (y, v, c (pos v)) ∈ E
  · obtain ⟨y, hy, hpy, hmem, hp⟩ := primPar_attach R hv h
    rw [hp] at hpar
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpar)
    exact ⟨hy, G.sym _ hmem, hpy⟩
  · rw [primPar_start hv h] at hpar
    cases hpar

theorem primPar_wt {n B : Nat} {E : List Arc} {vert pos c : Nat → Nat} (G : Graph n B E) (R : PrimRun n E vert pos c) {v : Nat}
    (hv : v < n) : wt (primPar n E pos c) v = c (pos v) := by
  classical
  by_cases h : ∃ y, y < n ∧ pos y < pos v ∧ (y, v, c (pos v)) ∈ E
  · obtain ⟨y, hy, hpy, hmem, hp⟩ := primPar_attach R hv h
    simp [wt, hp]
  · have hn := primPar_start hv h (E := E) (c := c)
    unfold wt
    rw [hn]
    rcases R.step (pos v) (R.pv v hv).1 with ⟨h0, _⟩ | ⟨y, hy, hpy, hmem, _⟩
    · simp [h0]
    · rw [(R.pv v hv).2] at hmem
      exact absurd ⟨y, hy, hpy, hmem⟩ h

/-- A path from a vertex at position `≥ j` to one at position `< j` uses an arc across the cut. -/
theorem path_crosses {E : List Arc} {t : Nat} {pos : Nat → Nat} {j a b : Nat} (h : Rtc (Gt E t) a b) (ha : j ≤ pos a)
    (hb : pos b < j) : ∃ p q w, w < t ∧ (p, q, w) ∈ E ∧ j ≤ pos p ∧ pos q < j := by
  induction h with
  | refl => omega
  | tail hab hbc ih =>
    rename_i b' c'
    obtain ⟨w, hw, hmem⟩ := hbc
    by_cases hb' : pos b' < j
    · exact ih hb'
    · exact ⟨b', c', w, hw, hmem, by omega, hb⟩

theorem prim_claim {n B : Nat} {E : List Arc} {vert pos c : Nat → Nat} (G : Graph n B E) (R : PrimRun n E vert pos c)
    (t : Nat) : ∀ j, j ≤ n → ∀ x x', x < n → x' < n → pos x < j → pos x' < j → Rtc (Gt E t) x x' →
      Rtc (FAdj (primPar n E pos c) t) x x' := by
  have hGs := Gt_symm G t
  have hFs : ∀ a b, FAdj (primPar n E pos c) t a b → FAdj (primPar n E pos c) t b a := fun a b h => h.symm
  intro j
  induction j with
  | zero => intro _ x x' _ _ h; omega
  | succ j ih =>
    intro hj x x' hx hx' hpx hpx' hpath
    have hjn : j < n := by omega
    have hv := (R.vp j hjn).1
    have hpv := (R.vp j hjn).2
    -- the case of one endpoint being `vert j`
    have key : ∀ x', x' < n → pos x' < j → Rtc (Gt E t) (vert j) x' → Rtc (FAdj (primPar n E pos c) t) (vert j) x' := by
      intro x' hx' hpx' hp
      rcases R.step j hjn with ⟨h0, hnone⟩ | ⟨y, hy, hpy, hmem, hmin⟩
      · obtain ⟨p, q, w, hw, hmemE, hp1, hq1⟩ := path_crosses hp (j := j) (by omega) hpx'
        have := hnone _ (G.sym _ hmemE) hq1
        simp at this
        omega
      · have hex : ∃ y', y' < n ∧ pos y' < pos (vert j) ∧ (y', vert j, c (pos (vert j))) ∈ E := by
          rw [hpv]; exact ⟨y, hy, hpy, hmem⟩
        obtain ⟨y', hy', hpy', hmem', hp'⟩ := primPar_attach R hv hex
        rw [hpv] at hpy' hmem' hp'
        by_cases hct : c j < t
        · have hps : PS (primPar n E pos c) t (vert j) y' := ⟨c j, hct, hp'⟩
          have g1 : Rtc (Gt E t) y' (vert j) := Rtc.single ⟨c j, hct, hmem'⟩
          have g2 : Rtc (Gt E t) y' x' := Rtc.trans g1 hp
          have f : Rtc (FAdj (primPar n E pos c) t) y' x' := ih (by omega) y' x' hy' hx' hpy' hpx' g2
          exact Rtc.head (Or.inl hps) f
        · obtain ⟨p, q, w, hw, hmemE, hp1, hq1⟩ := path_crosses hp (j := j) (by omega) hpx'
          have := hmin _ (G.sym _ hmemE) hq1 (by omega)
          simp at this
          omega
    have hxv : pos x < j ∨ x = vert j := by
      by_cases h : pos x < j
      · exact Or.inl h
      · right
        have : pos x = j := by omega
        have h2 := (R.pv x hx).2
        rw [this] at h2
        exact h2.symm
    have hxv' : pos x' < j ∨ x' = vert j := by
      by_cases h : pos x' < j
      · exact Or.inl h
      · right
        have : pos x' = j := by omega
        have h2 := (R.pv x' hx').2
        rw [this] at h2
        exact h2.symm
    rcases hxv with h1 | rfl
    · rcases hxv' with h2 | rfl
      · exact ih (by omega) x x' hx hx' h1 h2 hpath
      · have hp' := Rtc.symm hGs hpath
        exact Rtc.symm hFs (key x hx h1 hp')
    · rcases hxv' with h2 | rfl
      · exact key x' hx' h2 hpath
      · exact Rtc.refl _

theorem ssum_eq_sum (k : Nat) (f : Nat → Nat) : ssum k f = ((List.range k).map f).sum := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append]; simp [ssum, ih]

theorem pos_perm {n : Nat} {E : List Arc} {vert pos c : Nat → Nat} (R : PrimRun n E vert pos c) :
    ((List.range n).map pos).Perm (List.range n) := by
  rw [List.perm_ext_iff_of_nodup (nodup_map_inj List.nodup_range pos (by
    intro x hx y hy h
    have hx' := List.mem_range.mp hx
    have hy' := List.mem_range.mp hy
    have := (R.pv x hx').2
    have h2 := (R.pv y hy').2
    rw [h] at this
    rw [this] at h2
    exact h2)) List.nodup_range]
  intro a
  rw [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (R.pv v (List.mem_range.mp hv)).1
  · intro ha
    exact ⟨vert a, List.mem_range.mpr (R.vp a ha).1, (R.vp a ha).2⟩

/-- Prim's total cost is the weight of a minimum spanning forest. -/
theorem prim_spec {n B : Nat} {E : List Arc} {vert pos c : Nat → Nat} (G : Graph n B E) (R : PrimRun n E vert pos c) :
    ssum n c = MSTW n B E ∧
    (∃ par rank, Forest n E par rank ∧ Spans E par (B + 1) ∧ Weight n par = ssum n c) ∧
    ∀ par rank, Forest n E par rank → Spans E par (B + 1) → ssum n c ≤ Weight n par := by
  have F := primPar_forest G R
  have hclaim : ∀ t, ∀ a b, a < n → b < n → Rtc (Gt E t) a b → Rtc (FAdj (primPar n E pos c) t) a b :=
    fun t a b ha hb h => prim_claim G R t n (Nat.le_refl _) a b ha hb (R.pv a ha).1 (R.pv b hb).1 h
  have hsp : Spans E (primPar n E pos c) (B + 1) := by
    intro a ha hw
    exact hclaim (B + 1) a.1 a.2.1 (G.lt a ha).1 (G.lt a ha).2 (Rtc.single ⟨a.2.2, hw, ha⟩)
  have hW : Weight n (primPar n E pos c) = ssum n c := by
    unfold Weight
    rw [ssum_eq_sum]
    have e : (List.range n).map (wt (primPar n E pos c)) = (List.range n).map (fun v => c (pos v)) := by
      apply map_congr_mem
      intro v hv
      exact primPar_wt G R (List.mem_range.mp hv)
    rw [e]
    have hm : (List.range n).map (fun v => c (pos v)) = ((List.range n).map pos).map c := by
      rw [List.map_map]; rfl
    rw [hm]
    exact (List.Perm.map c (pos_perm R)).sum_nat
  have hM : Weight n (primPar n E pos c) = MSTW n B E :=
    weight_eq_mstw G F (fun t _ _ => hclaim t)
  refine ⟨by rw [← hW, hM], ⟨_, _, F, hsp, hW⟩, ?_⟩
  intro par rank F' hsp'
  have := weight_ge_mstw G F' hsp'
  rw [← hW, hM]
  exact this

end Proofs.PrimMath
