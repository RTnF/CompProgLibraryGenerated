import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Nodup

/-! # Warshall-Floyd with parents, in place (`MatrixGraph::warshall_floyd`)

The pure model of the triple loop of `library/graph/graph_matrix.hpp` on functions `Nat → Nat → Int`: `step k i j`
relaxes the entry `(i, j)` through `k` in place and copies the parent `P k j`. Walks are lists of intermediate
vertices (`wt W i l j` is the weight of `i → l₀ → … → j`, at least one edge).

* `fw_walk`: every entry is the weight of a walk through vertices `< n`.
* `fw_le_simple`: every entry is at most the weight of every walk whose vertices are distinct (no assumption).
* `fw_le`: without a negative closed walk (`NoNeg`), every entry is at most the weight of every walk.
* `neg_iff`: a diagonal entry is negative iff there is a negative closed walk.
* `PInv`: without a negative closed walk, the parents describe walks whose weight is at most the entry, and in each
  row they decrease a rank (so following them stops). -/

namespace Proofs.GraphMatrixMath

/-- The weight of the walk `i → l₀ → … → l_{m-1} → j`. -/
def wt (W : Nat → Nat → Int) : Nat → List Nat → Nat → Int
  | i, [], j => W i j
  | i, v :: l, j => W i v + wt W v l j

theorem wt_append (W : Nat → Nat → Int) (i k j : Nat) (l1 l2 : List Nat) :
    wt W i (l1 ++ k :: l2) j = wt W i l1 k + wt W k l2 j := by
  induction l1 generalizing i with
  | nil => simp [wt]
  | cons v l ih => simp only [List.cons_append, wt, ih]; omega

theorem split_first {k : Nat} {l : List Nat} (h : k ∈ l) : ∃ l1 l2, l = l1 ++ k :: l2 ∧ k ∉ l1 := by
  induction l with
  | nil => simp at h
  | cons v l ih =>
    by_cases e : v = k
    · exact ⟨[], l, by simp [e], by simp⟩
    · have : k ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      obtain ⟨l1, l2, h1, h2⟩ := ih this
      exact ⟨v :: l1, l2, by simp [h1], by simp only [List.mem_cons, not_or]; exact ⟨fun x => e x.symm, h2⟩⟩

theorem split_last {k : Nat} {l : List Nat} (h : k ∈ l) : ∃ l1 l2, l = l1 ++ k :: l2 ∧ k ∉ l2 := by
  induction l with
  | nil => simp at h
  | cons v l ih =>
    by_cases e : k ∈ l
    · obtain ⟨l1, l2, h1, h2⟩ := ih e
      exact ⟨v :: l1, l2, by simp [h1], h2⟩
    · have : v = k := by
        rcases List.mem_cons.mp h with h | h
        · exact h.symm
        · exact absurd h e
      exact ⟨[], l, by simp [this], e⟩

theorem split_dup {l : List Nat} (h : ¬ l.Nodup) : ∃ a x b c, l = a ++ x :: (b ++ x :: c) := by
  induction l with
  | nil => simp at h
  | cons y t ih =>
    rw [List.nodup_cons] at h
    by_cases e : y ∈ t
    · obtain ⟨b, c, hbc⟩ := List.append_of_mem e
      exact ⟨[], y, b, c, by simp [hbc]⟩
    · obtain ⟨a, x, b, c, habc⟩ := ih (by tauto)
      exact ⟨y :: a, x, b, c, by simp [habc]⟩

/-- All vertices of `l` are `< b`. -/
def Below (b : Nat) (l : List Nat) : Prop := ∀ x ∈ l, x < b

theorem below_mono {a b : Nat} {l : List Nat} (h : Below a l) (hab : a ≤ b) : Below b l :=
  fun x hx => Nat.lt_of_lt_of_le (h x hx) hab

theorem below_append {b k : Nat} {l1 l2 : List Nat} :
    Below b (l1 ++ k :: l2) ↔ Below b l1 ∧ k < b ∧ Below b l2 := by
  simp only [Below, List.mem_append, List.mem_cons]
  constructor
  · intro h; exact ⟨fun x hx => h x (Or.inl hx), h k (Or.inr (Or.inl rfl)), fun x hx => h x (Or.inr (Or.inr hx))⟩
  · rintro ⟨h1, hk, h2⟩ x (hx | rfl | hx)
    · exact h1 x hx
    · exact hk
    · exact h2 x hx

/-- Removing `k` from a list of vertices `< k + 1`. -/
theorem below_succ {k : Nat} {l : List Nat} (h : Below (k + 1) l) (hk : k ∉ l) : Below k l := by
  intro x hx
  have := h x hx
  have : x ≠ k := fun e => hk (e ▸ hx)
  omega

/-- No closed walk through vertices `< n` has a negative weight. -/
def NoNeg (W : Nat → Nat → Int) (n : Nat) : Prop := ∀ v l, v < n → Below n l → 0 ≤ wt W v l v

/-! ## The in-place loop -/

/-- The distances and the parents. -/
structure St where
  D : Nat → Nat → Int
  P : Nat → Nat → Int

def upd (f : Nat → Nat → Int) (i j : Nat) (v : Int) : Nat → Nat → Int :=
  fun p q => if p = i ∧ q = j then v else f p q

/-- The body of the innermost loop. -/
def step (k i j : Nat) (s : St) : St :=
  if s.D i k + s.D k j < s.D i j then ⟨upd s.D i j (s.D i k + s.D k j), upd s.P i j (s.P k j)⟩ else s

/-- The first `j` entries of row `i` in round `k`. -/
def rowJ (k i : Nat) : Nat → St → St
  | 0, s => s
  | j + 1, s => step k i j (rowJ k i j s)

/-- The first `i` rows of round `k`. -/
def roundI (n k : Nat) : Nat → St → St
  | 0, s => s
  | i + 1, s => rowJ k i n (roundI n k i s)

/-- The first `k` rounds. -/
def fwK (n : Nat) : Nat → St → St
  | 0, s => s
  | k + 1, s => roundI n k n (fwK n k s)

/-! ## Values: walks and lower bounds -/

/-- In round `k` with the cursor at `(i, j)`, the entry `(p, q)` was already relaxed through `k`. -/
abbrev done (i j p q : Nat) : Prop := p < i ∨ (p = i ∧ q < j)

/-- The vertices allowed in the walks of the entry `(p, q)`: `< k + 1` once relaxed in round `k`, else `< k`. -/
def lev (k i j p q : Nat) : Nat := if done i j p q then k + 1 else k

theorem k_le_lev (k i j p q : Nat) : k ≤ lev k i j p q := by unfold lev; split <;> omega

theorem lev_le (k i j p q : Nat) : lev k i j p q ≤ k + 1 := by unfold lev; split <;> omega

/-- The invariant of the values: `(A)` every entry is a walk weight, `(B')` it is at most every walk with distinct
vertices, `(B)` without negative closed walks it is at most every walk. -/
structure VInv (W : Nat → Nat → Int) (n k i j : Nat) (D : Nat → Nat → Int) : Prop where
  walk : ∀ p q, p < n → q < n → ∃ l, Below (lev k i j p q) l ∧ D p q = wt W p l q
  simple : ∀ p q, p < n → q < n → ∀ l, Below (lev k i j p q) l → l.Nodup → p ∉ l → q ∉ l → D p q ≤ wt W p l q
  le : NoNeg W n → ∀ p q, p < n → q < n → ∀ l, Below (lev k i j p q) l → D p q ≤ wt W p l q

theorem lev_step (k i j p q : Nat) (h : ¬ (p = i ∧ q = j)) : lev k i (j + 1) p q = lev k i j p q := by
  unfold lev done
  by_cases h1 : p < i ∨ p = i ∧ q < j
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

theorem lev_here (k i j : Nat) : lev k i (j + 1) i j = k + 1 := by unfold lev done; rw [if_pos (by omega)]

/-- The upper bound of the relaxed entry through `k`, from the bounds of `(i, k)` and `(k, j)`. -/
theorem vstep (W : Nat → Nat → Int) (n k i j : Nat) (hk : k < n) (hi : i < n) (hj : j < n)
    (D : Nat → Nat → Int) (h : VInv W n k i j D) :
    VInv W n k i (j + 1) (if D i k + D k j < D i j then upd D i j (D i k + D k j) else D) := by
  have hlik := k_le_lev k i j i k
  have hlkj := k_le_lev k i j k j
  have hlij := lev_le k i j i j
  have hlij0 := k_le_lev k i j i j
  -- the new value of (i, j) is the minimum of the old one and the walks through k
  have new_le : ∀ (l : List Nat), Below (k + 1) l → (k ∉ l → D i j ≤ wt W i l j) →
      (∀ l1 l2, l = l1 ++ k :: l2 → D i k + D k j ≤ wt W i l j) →
      (if D i k + D k j < D i j then upd D i j (D i k + D k j) else D) i j ≤ wt W i l j := by
    intro l hl h1 h2
    by_cases hkl : k ∈ l
    · obtain ⟨l1, l2, rfl, _⟩ := split_first hkl
      have := h2 l1 l2 rfl
      split
      · simp [upd]; exact this
      · omega
    · have := h1 hkl
      split
      · simp only [upd, and_self, ite_true]; omega
      · exact this
  refine ⟨fun p q hp hq => ?_, fun p q hp hq l hl hnd hpl hql => ?_, fun hN p q hp hq l hl => ?_⟩
  · by_cases e : p = i ∧ q = j
    · obtain ⟨rfl, rfl⟩ := e
      rw [lev_here]
      split
      · obtain ⟨l1, hl1, e1⟩ := h.walk p k hp hk
        obtain ⟨l2, hl2, e2⟩ := h.walk k q hk hq
        refine ⟨l1 ++ k :: l2, below_append.mpr ⟨below_mono hl1 (lev_le _ _ _ _ _), by omega, below_mono hl2 (lev_le _ _ _ _ _)⟩, ?_⟩
        simp only [upd, and_self, ite_true, wt_append, e1, e2]
      · obtain ⟨l, hl, e⟩ := h.walk p q hp hq
        exact ⟨l, below_mono hl (by omega), e⟩
    · rw [lev_step _ _ _ _ _ e]
      have hv : (if D i k + D k j < D i j then upd D i j (D i k + D k j) else D) p q = D p q := by
        split
        · simp only [upd]; rw [if_neg e]
        · rfl
      rw [hv]; exact h.walk p q hp hq
  · by_cases e : p = i ∧ q = j
    · obtain ⟨rfl, rfl⟩ := e
      rw [lev_here] at hl
      refine new_le l hl (fun hkl => h.simple p q hp hq l (below_mono (below_succ hl hkl) hlij0) hnd hpl hql) ?_
      intro l1 l2 e
      subst e
      rw [wt_append]
      obtain ⟨hb1, _, hb2⟩ := below_append.mp hl
      have hnd' := hnd
      rw [List.nodup_append] at hnd'
      have hk1 : k ∉ l1 := fun hm => by
        have := hnd'.2.2 k hm k (by simp); exact this rfl
      have hk2 : k ∉ l2 := fun hm => by
        have := (List.nodup_cons.mp hnd'.2.1).1; exact this hm
      have a1 := h.simple p k hp hk l1 (below_mono (below_succ hb1 hk1) hlik) hnd'.1
        (fun hm => hpl (by simp [hm])) hk1
      have a2 := h.simple k q hk hq l2 (below_mono (below_succ hb2 hk2) hlkj) (List.nodup_cons.mp hnd'.2.1).2 hk2
        (fun hm => hql (by simp [hm]))
      omega
    · rw [lev_step _ _ _ _ _ e] at hl
      have hv : (if D i k + D k j < D i j then upd D i j (D i k + D k j) else D) p q = D p q := by
        split
        · simp only [upd]; rw [if_neg e]
        · rfl
      rw [hv]; exact h.simple p q hp hq l hl hnd hpl hql
  · by_cases e : p = i ∧ q = j
    · obtain ⟨rfl, rfl⟩ := e
      rw [lev_here] at hl
      refine new_le l hl (fun hkl => h.le hN p q hp hq l (below_mono (below_succ hl hkl) hlij0)) ?_
      intro l1 l2 e
      subst e
      obtain ⟨hb1, _, hb2⟩ := below_append.mp hl
      -- the first `k` ends the first part; after the last `k` the rest; between them a closed walk
      obtain ⟨m1, m2, hm, hk1⟩ := split_first (show k ∈ l1 ++ k :: l2 by simp)
      rw [hm, wt_append]
      have hbm := hm ▸ hl
      obtain ⟨hbm1, _, hbm2⟩ := below_append.mp hbm
      have a1 := h.le hN p k hp hk m1 (below_mono (below_succ hbm1 hk1) hlik)
      by_cases hk2 : k ∈ m2
      · obtain ⟨m3, m4, rfl, hk4⟩ := split_last hk2
        obtain ⟨hb3, _, hb4⟩ := below_append.mp hbm2
        rw [wt_append]
        have a2 := h.le hN k q hk hq m4 (below_mono (below_succ hb4 hk4) hlkj)
        have a3 := hN k m3 hk (below_mono hb3 (by omega))
        omega
      · have a2 := h.le hN k q hk hq m2 (below_mono (below_succ hbm2 hk2) hlkj)
        omega
    · rw [lev_step _ _ _ _ _ e] at hl
      have hv : (if D i k + D k j < D i j then upd D i j (D i k + D k j) else D) p q = D p q := by
        split
        · simp only [upd]; rw [if_neg e]
        · rfl
      rw [hv]; exact h.le hN p q hp hq l hl

theorem step_D (k i j : Nat) (s : St) :
    (step k i j s).D = if s.D i k + s.D k j < s.D i j then upd s.D i j (s.D i k + s.D k j) else s.D := by
  unfold step; split <;> rfl

theorem vrow (W : Nat → Nat → Int) (n k i : Nat) (hk : k < n) (hi : i < n) (s : St) (h : VInv W n k i 0 s.D) :
    ∀ j, j ≤ n → VInv W n k i j (rowJ k i j s).D := by
  intro j
  induction j with
  | zero => intro _; exact h
  | succ j ih =>
    intro hj
    simp only [rowJ, step_D]
    exact vstep W n k i j hk hi (by omega) _ (ih (by omega))

theorem lev_row_end (k i n p q : Nat) (hq : q < n) : lev k i n p q = lev k (i + 1) 0 p q := by
  unfold lev done
  by_cases h1 : p < i ∨ p = i ∧ q < n
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

theorem vinv_row_end (W : Nat → Nat → Int) (n k i : Nat) (D : Nat → Nat → Int) (h : VInv W n k i n D) :
    VInv W n k (i + 1) 0 D :=
  ⟨fun p q hp hq => lev_row_end k i n p q hq ▸ h.walk p q hp hq,
   fun p q hp hq => lev_row_end k i n p q hq ▸ h.simple p q hp hq,
   fun hN p q hp hq => lev_row_end k i n p q hq ▸ h.le hN p q hp hq⟩

theorem vround (W : Nat → Nat → Int) (n k : Nat) (hk : k < n) (s : St) (h : VInv W n k 0 0 s.D) :
    ∀ i, i ≤ n → VInv W n k i 0 (roundI n k i s).D := by
  intro i
  induction i with
  | zero => intro _; exact h
  | succ i ih =>
    intro hi
    simp only [roundI]
    exact vinv_row_end W n k i _ (vrow W n k i hk (by omega) _ (ih (by omega)) n le_rfl)

theorem lev_round_end (k n p q : Nat) (hp : p < n) : lev k n 0 p q = lev (k + 1) 0 0 p q := by
  unfold lev done
  rw [if_pos (Or.inl hp), if_neg (by omega)]

theorem vinv_round_end (W : Nat → Nat → Int) (n k : Nat) (D : Nat → Nat → Int) (h : VInv W n k n 0 D) :
    VInv W n (k + 1) 0 0 D :=
  ⟨fun p q hp hq => lev_round_end k n p q hp ▸ h.walk p q hp hq,
   fun p q hp hq => lev_round_end k n p q hp ▸ h.simple p q hp hq,
   fun hN p q hp hq => lev_round_end k n p q hp ▸ h.le hN p q hp hq⟩

theorem lev_start (p q : Nat) : lev 0 0 0 p q = 0 := by unfold lev done; rw [if_neg (by omega)]

theorem below_zero {l : List Nat} (h : Below 0 l) : l = [] := by
  cases l with
  | nil => rfl
  | cons x l => exact absurd (h x (by simp)) (by omega)

theorem vinv_start (W : Nat → Nat → Int) (n : Nat) : VInv W n 0 0 0 W :=
  ⟨fun p q _ _ => ⟨[], by intro x hx; simp at hx, rfl⟩,
   fun p q _ _ l hl _ _ _ => by rw [lev_start] at hl; rw [below_zero hl]; exact le_rfl,
   fun _ p q _ _ l hl => by rw [lev_start] at hl; rw [below_zero hl]; exact le_rfl⟩

/-- The value invariant after `k` rounds. -/
theorem vfw (W : Nat → Nat → Int) (n : Nat) (P : Nat → Nat → Int) :
    ∀ k, k ≤ n → VInv W n k 0 0 (fwK n k ⟨W, P⟩).D := by
  intro k
  induction k with
  | zero => intro _; exact vinv_start W n
  | succ k ih =>
    intro hk
    simp only [fwK]
    exact vinv_round_end W n k _ (vround W n k (by omega) _ (ih (by omega)) n le_rfl)

theorem lev_final (n p q : Nat) : lev n 0 0 p q = n := by unfold lev done; rw [if_neg (by omega)]

theorem fw_walk (W : Nat → Nat → Int) (n : Nat) (P : Nat → Nat → Int) (p q : Nat) (hp : p < n) (hq : q < n) :
    ∃ l, Below n l ∧ (fwK n n ⟨W, P⟩).D p q = wt W p l q := by
  have := (vfw W n P n le_rfl).walk p q hp hq; rwa [lev_final] at this

theorem fw_le_simple (W : Nat → Nat → Int) (n : Nat) (P : Nat → Nat → Int) (p q : Nat) (hp : p < n) (hq : q < n)
    (l : List Nat) (hl : Below n l) (hnd : l.Nodup) (hpl : p ∉ l) (hql : q ∉ l) :
    (fwK n n ⟨W, P⟩).D p q ≤ wt W p l q :=
  (vfw W n P n le_rfl).simple p q hp hq l (by rwa [lev_final]) hnd hpl hql

theorem fw_le (W : Nat → Nat → Int) (n : Nat) (P : Nat → Nat → Int) (hN : NoNeg W n) (p q : Nat) (hp : p < n)
    (hq : q < n) (l : List Nat) (hl : Below n l) : (fwK n n ⟨W, P⟩).D p q ≤ wt W p l q :=
  (vfw W n P n le_rfl).le hN p q hp hq l (by rwa [lev_final])

/-! ## Negative closed walks -/

/-- A negative closed walk gives one whose vertices are distinct. -/
theorem simple_neg (W : Nat → Nat → Int) (n : Nat) :
    ∀ m v l, l.length ≤ m → v < n → Below n l → wt W v l v < 0 →
      ∃ v' l', v' < n ∧ Below n l' ∧ l'.Nodup ∧ v' ∉ l' ∧ wt W v' l' v' < 0 := by
  intro m
  induction m with
  | zero =>
    intro v l hlen hv hl hw
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨v, [], hv, hl, List.nodup_nil, by simp, hw⟩
  | succ m ih =>
    intro v l hlen hv hl hw
    by_cases hvl : v ∈ l
    · obtain ⟨l1, l2, rfl, _⟩ := List.append_of_mem hvl
      obtain ⟨hb1, _, hb2⟩ := below_append.mp hl
      rw [wt_append] at hw
      simp only [List.length_append, List.length_cons] at hlen
      by_cases h1 : wt W v l1 v < 0
      · exact ih v l1 (by omega) hv hb1 h1
      · exact ih v l2 (by omega) hv hb2 (by omega)
    · by_cases hnd : l.Nodup
      · exact ⟨v, l, hv, hl, hnd, hvl, hw⟩
      · obtain ⟨a, x, b, c, rfl⟩ := split_dup hnd
        obtain ⟨hba, hx, hbbc⟩ := below_append.mp hl
        obtain ⟨hbb, _, hbc⟩ := below_append.mp hbbc
        rw [wt_append, wt_append] at hw
        simp only [List.length_append, List.length_cons] at hlen
        by_cases h1 : wt W x b x < 0
        · exact ih x b (by omega) hx hbb h1
        · refine ih v (a ++ x :: c) (by simp; omega) hv (below_append.mpr ⟨hba, hx, hbc⟩) ?_
          rw [wt_append]; omega

/-- After the loop, some diagonal entry is negative iff some closed walk through vertices `< n` is negative. -/
theorem neg_iff (W : Nat → Nat → Int) (n : Nat) (P : Nat → Nat → Int) :
    (∃ v, v < n ∧ (fwK n n ⟨W, P⟩).D v v < 0) ↔ ¬ NoNeg W n := by
  constructor
  · rintro ⟨v, hv, hneg⟩ hN
    obtain ⟨l, hl, e⟩ := fw_walk W n P v v hv hv
    have := hN v l hv hl
    omega
  · intro hN
    simp only [NoNeg, not_forall, not_le] at hN
    obtain ⟨v, l, hv, hl, hw⟩ := hN
    obtain ⟨v', l', hv', hl', hnd, hvl, hw'⟩ := simple_neg W n l.length v l le_rfl hv hl hw
    exact ⟨v', hv', lt_of_le_of_lt (fw_le_simple W n P v' v' hv' hv' l' hl' hnd hvl hvl) hw'⟩

/-! ## Without negative closed walks: a round is a simultaneous update -/

/-- Relaxing every entry through `k` at once from the values at the start of the round. -/
def sim (k : Nat) (s : St) : St :=
  ⟨fun p q => if s.D p k + s.D k q < s.D p q then s.D p k + s.D k q else s.D p q,
   fun p q => if s.D p k + s.D k q < s.D p q then s.P k q else s.P p q⟩

/-- Mid-round, the relaxed entries hold the simultaneous values and the others the values at the start. -/
def Agree (n i j : Nat) (s0 s c : St) : Prop :=
  ∀ p q, p < n → q < n → c.D p q = (if done i j p q then s.D p q else s0.D p q) ∧
    c.P p q = (if done i j p q then s.P p q else s0.P p q)

theorem sim_col (k : Nat) (s : St) (hkk : 0 ≤ s.D k k) (p : Nat) :
    (sim k s).D p k = s.D p k ∧ (sim k s).P p k = s.P p k := by
  simp only [sim]; rw [if_neg (by omega), if_neg (by omega)]; exact ⟨rfl, rfl⟩

theorem sim_row (k : Nat) (s : St) (hkk : 0 ≤ s.D k k) (q : Nat) :
    (sim k s).D k q = s.D k q ∧ (sim k s).P k q = s.P k q := by
  simp only [sim]; rw [if_neg (by omega), if_neg (by omega)]; exact ⟨rfl, rfl⟩

theorem agree_step (n k i j : Nat) (hk : k < n) (hi : i < n) (hj : j < n) (s c : St) (hkk : 0 ≤ s.D k k)
    (h : Agree n i j s (sim k s) c) : Agree n i (j + 1) s (sim k s) (step k i j c) := by
  have rd : ∀ p q, p < n → q < n → (c.D p q = s.D p q ∧ c.P p q = s.P p q) ∨
      (c.D p q = (sim k s).D p q ∧ c.P p q = (sim k s).P p q) := by
    intro p q hp hq
    obtain ⟨h1, h2⟩ := h p q hp hq
    by_cases hd : done i j p q
    · rw [if_pos hd] at h1 h2; exact Or.inr ⟨h1, h2⟩
    · rw [if_neg hd] at h1 h2; exact Or.inl ⟨h1, h2⟩
  have cik : c.D i k = s.D i k := by
    rcases rd i k hi hk with ⟨e, _⟩ | ⟨e, _⟩
    · exact e
    · rw [e, (sim_col k s hkk i).1]
  have ckj : c.D k j = s.D k j ∧ c.P k j = s.P k j := by
    rcases rd k j hk hj with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1, e2⟩
    · rw [e1, e2]; exact sim_row k s hkk j
  have cij : c.D i j = s.D i j ∧ c.P i j = s.P i j := by
    obtain ⟨h1, h2⟩ := h i j hi hj
    rw [if_neg (by simp [done])] at h1 h2
    exact ⟨h1, h2⟩
  intro p q hp hq
  by_cases e : p = i ∧ q = j
  · obtain ⟨rfl, rfl⟩ := e
    have hd : done p (q + 1) p q := Or.inr ⟨rfl, by omega⟩
    rw [if_pos hd, if_pos hd]
    unfold step
    rw [cik, ckj.1, ckj.2, cij.1]
    simp only [sim]
    split
    · simp [upd]
    · exact ⟨cij.1.trans rfl, cij.2⟩
  · have hd : done i (j + 1) p q ↔ done i j p q := by simp only [done]; omega
    have hv : (step k i j c).D p q = c.D p q ∧ (step k i j c).P p q = c.P p q := by
      unfold step; split
      · simp only [upd]; rw [if_neg e, if_neg e]; exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    rw [hv.1, hv.2, if_congr hd rfl rfl, if_congr hd rfl rfl]
    exact h p q hp hq

theorem agree_row (n k i : Nat) (hk : k < n) (hi : i < n) (s c : St) (hkk : 0 ≤ s.D k k)
    (h : Agree n i 0 s (sim k s) c) : ∀ j, j ≤ n → Agree n i j s (sim k s) (rowJ k i j c) := by
  intro j
  induction j with
  | zero => intro _; exact h
  | succ j ih => intro hj; exact agree_step n k i j hk hi (by omega) s _ hkk (ih (by omega))

theorem agree_row_end (n i : Nat) (s0 s c : St) (h : Agree n i n s0 s c) : Agree n (i + 1) 0 s0 s c := by
  intro p q hp hq
  have hd : done (i + 1) 0 p q ↔ done i n p q := by simp only [done]; omega
  rw [if_congr hd rfl rfl, if_congr hd rfl rfl]
  exact h p q hp hq

theorem agree_round (n k : Nat) (hk : k < n) (s : St) (hkk : 0 ≤ s.D k k) :
    ∀ i, i ≤ n → Agree n i 0 s (sim k s) (roundI n k i s) := by
  intro i
  induction i with
  | zero =>
    intro _ p q _ _
    rw [if_neg (by simp [done]), if_neg (by simp [done])]; exact ⟨rfl, rfl⟩
  | succ i ih =>
    intro hi
    exact agree_row_end n i s _ _ (agree_row n k i hk (by omega) s _ hkk (ih (by omega)) n le_rfl)

/-- Without negative closed walks, round `k` is the simultaneous update (on the `n × n` entries). -/
theorem round_sim (n k : Nat) (hk : k < n) (s : St) (hkk : 0 ≤ s.D k k) (p q : Nat) (hp : p < n) (hq : q < n) :
    (roundI n k n s).D p q = (sim k s).D p q ∧ (roundI n k n s).P p q = (sim k s).P p q := by
  have := agree_round n k hk s hkk n le_rfl p q hp hq
  rw [if_pos (by simp [done]; omega), if_pos (by simp [done]; omega)] at this
  exact this

/-! ## The parents -/

/-- The parent invariant at the start of round `k`: `P i j` (for `j ≠ i`) is `-1` or a vertex `p`; if `p = i` the
edge `i → j` is at most the entry, otherwise `p < k` and the entry `(i, p)` plus the edge `p → j` is at most the
entry; in each row the parents decrease a rank. -/
structure PInv (W : Nat → Nat → Int) (n k : Nat) (s : St) : Prop where
  par : ∀ i j, i < n → j < n → j ≠ i → s.P i j = -1 ∨ ∃ p : Nat, s.P i j = p ∧ p < n ∧
    (p = i → W i j ≤ s.D i j) ∧ (p ≠ i → s.D i p + W p j ≤ s.D i j ∧ p < k)
  rank : ∀ i, i < n → ∃ r : Nat → Nat, ∀ j p : Nat, j < n → j ≠ i → s.P i j = p → p ≠ i → r p < r j

theorem pinv_congr (W : Nat → Nat → Int) (n k : Nat) (s t : St)
    (h : ∀ p q, p < n → q < n → t.D p q = s.D p q ∧ t.P p q = s.P p q) (hs : PInv W n k s) : PInv W n k t := by
  refine ⟨fun i j hi hj hji => ?_, fun i hi => ?_⟩
  · rw [(h i j hi hj).2]
    rcases hs.par i j hi hj hji with e | ⟨p, e, hp, h1, h2⟩
    · exact Or.inl e
    · refine Or.inr ⟨p, e, hp, fun e' => (h i j hi hj).1 ▸ h1 e', fun e' => ?_⟩
      rw [(h i j hi hj).1, (h i p hi hp).1]; exact h2 e'
  · obtain ⟨r, hr⟩ := hs.rank i hi
    exact ⟨r, fun j p hj hji e hpi => hr j p hj hji ((h i j hi hj).2 ▸ e) hpi⟩

theorem lev_zero (k p q : Nat) : lev k 0 0 p q = k := by unfold lev done; rw [if_neg (by omega)]

/-- One round keeps the parent invariant. -/
theorem pinv_sim (W : Nat → Nat → Int) (n k : Nat) (hk : k < n) (hN : NoNeg W n) (s : St)
    (hv : VInv W n k 0 0 s.D) (hs : PInv W n k s) : PInv W n (k + 1) (sim k s) := by
  have walk : ∀ p q, p < n → q < n → ∃ l, Below k l ∧ s.D p q = wt W p l q := by
    intro p q hp hq; have := hv.walk p q hp hq; rwa [lev_zero] at this
  have le : ∀ p q, p < n → q < n → ∀ l, Below k l → s.D p q ≤ wt W p l q := by
    intro p q hp hq l hl; exact hv.le hN p q hp hq l (by rwa [lev_zero])
  -- an entry plus an edge from a vertex `< k` bounds the entry
  have ext : ∀ p q j, p < n → q < n → j < n → q < k → s.D p j ≤ s.D p q + W q j := by
    intro p q j hp hq hj hqk
    obtain ⟨l, hl, e⟩ := walk p q hp hq
    have := le p j hp hj (l ++ q :: []) (below_append.mpr ⟨hl, hqk, fun x hx => by simp at hx⟩)
    rw [wt_append] at this; simp only [wt] at this; omega
  have closed : ∀ i, i < n → 0 ≤ s.D i k + s.D k i := by
    intro i hi
    obtain ⟨l1, hl1, e1⟩ := walk i k hi hk
    obtain ⟨l2, hl2, e2⟩ := walk k i hk hi
    have := hN i (l1 ++ k :: l2) hi (below_append.mpr ⟨below_mono hl1 (by omega), hk, below_mono hl2 (by omega)⟩)
    rw [wt_append] at this; omega
  have hkk : 0 ≤ s.D k k := by have := closed k hk; omega
  have colk := sim_col k s hkk
  have rowk := sim_row k s hkk
  have Dsim : ∀ p q, (sim k s).D p q = if s.D p k + s.D k q < s.D p q then s.D p k + s.D k q else s.D p q :=
    fun _ _ => rfl
  have Psim : ∀ p q, (sim k s).P p q = if s.D p k + s.D k q < s.D p q then s.P k q else s.P p q :=
    fun _ _ => rfl
  have Dle : ∀ p q, (sim k s).D p q ≤ s.D p q ∧ (sim k s).D p q ≤ s.D p k + s.D k q := by
    intro p q; rw [Dsim]; split <;> omega
  -- the parent of an entry relaxed through `k` (not `k` itself) is relaxed too
  have prop : ∀ i j p : Nat, i < n → j < n → p < n → p < k → s.D i k + s.D k j < s.D i j →
      s.D k p + W p j ≤ s.D k j → s.D i k + s.D k p < s.D i p := by
    intro i j p hi hj hp hpk hu hkp
    have := ext i p j hi hp hj hpk; omega
  -- the parent of an entry not relaxed is not relaxed
  have keep : ∀ i j q : Nat, i < n → j < n → q < n → q < k → ¬ s.D i k + s.D k j < s.D i j →
      s.D i q + W q j ≤ s.D i j → ¬ s.D i k + s.D k q < s.D i q := by
    intro i j q hi hj hq hqk hu hiq hu'
    have := ext k q j hk hq hj hqk; omega
  refine ⟨fun i j hi hj hji => ?_, fun i hi => ?_⟩
  · rw [Psim]
    by_cases hu : s.D i k + s.D k j < s.D i j
    · rw [if_pos hu]
      have hik : i ≠ k := fun e => by subst e; omega
      have hjk : j ≠ k := fun e => by subst e; omega
      rcases hs.par k j hk hj hjk with e | ⟨p, e, hp, h1, h2⟩
      · exact Or.inl e
      · refine Or.inr ⟨p, e, hp, fun hpi => ?_, fun hpi => ?_⟩
        · subst hpi
          have := (h2 hik).1
          have := closed p hi
          rw [Dsim, if_pos hu]; omega
        · rw [Dsim i j, if_pos hu]
          by_cases hpk : p = k
          · subst hpk
            have := h1 rfl
            rw [(colk i).1]; exact ⟨by omega, by omega⟩
          · obtain ⟨h3, h4⟩ := h2 hpk
            have := (Dle i p).2
            exact ⟨by omega, by omega⟩
    · rw [if_neg hu]
      rcases hs.par i j hi hj hji with e | ⟨q, e, hq, h1, h2⟩
      · exact Or.inl e
      · refine Or.inr ⟨q, e, hq, fun hqi => ?_, fun hqi => ?_⟩
        · rw [Dsim, if_neg hu]; exact h1 hqi
        · obtain ⟨h3, h4⟩ := h2 hqi
          rw [Dsim i j, if_neg hu]
          have := (Dle i q).1
          exact ⟨by omega, by omega⟩
  · obtain ⟨ri, hri⟩ := hs.rank i hi
    obtain ⟨rk, hrk⟩ := hs.rank k hk
    refine ⟨fun v => if s.D i k + s.D k v < s.D i v then rk v + ri k + 1 else ri v, fun j p hj hji e hpi => ?_⟩
    rw [Psim] at e
    beta_reduce
    by_cases hu : s.D i k + s.D k j < s.D i j
    · rw [if_pos hu] at e
      have hjk : j ≠ k := fun e' => by subst e'; omega
      rw [if_pos hu]
      have hp : p < n := by
        rcases hs.par k j hk hj hjk with e' | ⟨p', e', hp', _⟩
        · rw [e] at e'; omega
        · rw [e] at e'; have : p = p' := by exact_mod_cast e'
          omega
      by_cases hpk : p = k
      · subst hpk; rw [if_neg (by omega)]; omega
      · have hkp : s.D k p + W p j ≤ s.D k j ∧ p < k := by
          rcases hs.par k j hk hj hjk with e' | ⟨p', e', _, _, h2⟩
          · rw [e] at e'; omega
          · rw [e] at e'; have : p = p' := by exact_mod_cast e'
            subst this; exact h2 hpk
        rw [if_pos (prop i j p hi hj hp hkp.2 hu hkp.1)]
        have := hrk j p hj hjk e hpk
        omega
    · rw [if_neg hu] at e
      rw [if_neg hu]
      rcases hs.par i j hi hj hji with e' | ⟨q, e', hq, _, h2⟩
      · rw [e] at e'; omega
      · rw [e] at e'; have : p = q := by exact_mod_cast e'
        subst this
        obtain ⟨h3, h4⟩ := h2 hpi
        rw [if_neg (keep i j p hi hj hq h4 hu h3)]
        exact hri j p hj hji e hpi

/-- The parents at the start: `i` or `-1` off the diagonal. -/
theorem pinv_start (W : Nat → Nat → Int) (n : Nat) (P : Nat → Nat → Int)
    (hP : ∀ i j, i < n → j < n → j ≠ i → P i j = -1 ∨ P i j = i) : PInv W n 0 ⟨W, P⟩ := by
  refine ⟨fun i j hi hj hji => ?_, fun i _ => ⟨fun _ => 0, fun j p hj hji e hpi => ?_⟩⟩
  · rcases hP i j hi hj hji with e | e
    · exact Or.inl e
    · exact Or.inr ⟨i, e, hi, fun _ => le_rfl, fun h => absurd rfl h⟩
  · rcases hP i j (by omega) hj hji with e' | e'
    · simp only at e; rw [e] at e'; omega
    · simp only at e; rw [e] at e'; exact absurd (by exact_mod_cast e') hpi

/-- Without negative closed walks, the parent invariant after all rounds. -/
theorem pinv_fw (W : Nat → Nat → Int) (n : Nat) (P : Nat → Nat → Int) (hN : NoNeg W n)
    (hP : ∀ i j, i < n → j < n → j ≠ i → P i j = -1 ∨ P i j = i) :
    ∀ k, k ≤ n → PInv W n k (fwK n k ⟨W, P⟩) := by
  intro k
  induction k with
  | zero => intro _; exact pinv_start W n P hP
  | succ k ih =>
    intro hk
    have hv := vfw W n P k (by omega)
    have hs := ih (by omega)
    have hkk : 0 ≤ (fwK n k ⟨W, P⟩).D k k := by
      obtain ⟨l, hl, e⟩ := hv.walk k k (by omega) (by omega)
      have := hN k l (by omega) (below_mono hl (lev_le _ _ _ _ _ |>.trans (by omega)))
      omega
    simp only [fwK]
    exact pinv_congr W n (k + 1) _ _ (fun p q hp hq => round_sim n k (by omega) _ hkk p q hp hq)
      (pinv_sim W n k (by omega) hN _ hv hs)

/-! ## Following the parents -/

/-- The weight of the walk along the vertex list `l`. -/
def ww (W : Nat → Nat → Int) : List Nat → Int
  | [] => 0
  | [_] => 0
  | a :: b :: l => W a b + ww W (b :: l)

theorem ww_wt (W : Nat → Nat → Int) (a b : Nat) (l : List Nat) : ww W (a :: (l ++ [b])) = wt W a l b := by
  induction l generalizing a with
  | nil => simp [ww, wt]
  | cons v l ih => simp only [List.cons_append, ww, wt]; rw [← ih v]

theorem countP_lt {α : Type} (p q : α → Bool) (l : List α) (h : ∀ x ∈ l, p x → q x) (x : α) (hx : x ∈ l)
    (hq : q x) (hp : ¬p x) : l.countP p < l.countP q := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.countP_cons]
    have hm := List.countP_mono_left (l := l) (p := p) (q := q) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    rcases List.mem_cons.mp hx with e | e
    · subst e
      have : p x = false := by simpa using hp
      rw [this, hq]; simp only [Bool.false_eq_true, ite_false, ite_true]; omega
    · have ih' := ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) e
      by_cases hpy : p y = true
      · simp [hpy, h y (by simp) hpy]; omega
      · simp only [Bool.not_eq_true] at hpy
        rw [hpy]; simp only [Bool.false_eq_true, ite_false]; omega

/-- A rank bounded by `N`: the number of vertices `< N` of smaller rank. -/
def nrank (r : Nat → Nat) (N i : Nat) : Nat := (List.range N).countP (fun j => decide (r j < r i))

theorem nrank_le (r : Nat → Nat) (N i : Nat) : nrank r N i ≤ N := by
  unfold nrank
  exact Nat.le_trans (List.countP_le_length) (by simp)

theorem nrank_lt (r : Nat → Nat) (N i j : Nat) (hj : j < N) (h : r j < r i) : nrank r N j < nrank r N i :=
  countP_lt _ _ _ (fun x _ hx => by simp at hx ⊢; omega) j (by simpa using hj) (by simpa using h) (by simp)

end Proofs.GraphMatrixMath
