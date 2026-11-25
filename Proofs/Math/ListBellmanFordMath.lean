import Proofs.Cpp.Lib.Basic
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Tactic.Linarith
import Proofs.Math.ParentChain

/-! # The Bellman–Ford algorithm of `ListGraph::bellman_ford`

`E` is the list of the edges `(from, to, cost)` in the scan order (row by row). Phase 1 relaxes every edge
`n - 1` times (`step1`); phase 2 scans every edge `n` times and marks the target of an improvable edge with
`NEG` (`step2`). The ghost state of phase 1 is the time `T x` of the last update of each vertex and the clock `τ`. -/

namespace Proofs.ListBellmanFordMath

open Proofs.Cpp Proofs.ParentChain

abbrev Ed := Int × Int × Int

/-- Phase 1: relax `e = (u, w, c)` when `d[u]` is finite. -/
def step1 (U : Int) (st : Array Int × Array Int) (e : Ed) : Array Int × Array Int :=
  if (decide (Cpp.get st.1 e.1 ≠ U) && decide (Cpp.get st.1 e.1 + e.2.2 < Cpp.get st.1 e.2.1)) then
    (Cpp.set st.1 e.2.1 (Cpp.get st.1 e.1 + e.2.2), Cpp.set st.2 e.2.1 e.1)
  else st

/-- Phase 2: mark the target of an improvable edge. -/
def step2 (U NEG : Int) (st : Array Int × Array Int) (e : Ed) : Array Int × Array Int :=
  if (decide (Cpp.get st.1 e.1 ≠ U) && decide (Cpp.get st.1 e.1 + e.2.2 < Cpp.get st.1 e.2.1)) then
    (Cpp.set st.1 e.2.1 NEG, Cpp.set st.2 e.2.1 (-1))
  else st

/-- The edges are valid: endpoints in `[0, n)` and costs at most `C` in absolute value. -/
def Valid (n : Nat) (C : Int) (E : List Ed) : Prop :=
  ∀ e ∈ E, 0 ≤ e.1 ∧ e.1 < n ∧ 0 ≤ e.2.1 ∧ e.2.1 < n ∧ -C ≤ e.2.2 ∧ e.2.2 ≤ C

/-- A walk from `a` to `b` of cost `w` with `k` edges. -/
inductive Walk (E : List Ed) : Nat → Nat → Int → Nat → Prop
  | nil (a : Nat) : Walk E a a 0 0
  | snoc {a u : Nat} {w : Int} {k : Nat} (b : Nat) (c : Int) :
      Walk E a u w k → ((u : Int), (b : Int), c) ∈ E → Walk E a b (w + c) (k + 1)

/-- `v` is reachable from `s` through a vertex `x` on a closed walk of negative cost. -/
def NegReach (E : List Ed) (s v : Nat) : Prop :=
  ∃ x w k w' k' c k'', Walk E s x w k ∧ Walk E x x c k' ∧ c < 0 ∧ Walk E x v w' k''

theorem walk_append {E : List Ed} {a b c : Nat} {w w' : Int} {k k' : Nat} (h1 : Walk E a b w k)
    (h2 : Walk E b c w' k') : Walk E a c (w + w') (k + k') := by
  induction h2 with
  | nil => simpa using h1
  | snoc d cost _ he ih => rw [← Int.add_assoc, ← Nat.add_assoc]; exact Walk.snoc d cost ih he

theorem negReach_step {E : List Ed} {s v : Nat} (h : NegReach E s v) (y : Nat) (c : Int)
    (he : ((v : Int), (y : Int), c) ∈ E) : NegReach E s y := by
  obtain ⟨x, w, k, w', k', c', k'', h1, h2, h3, h4⟩ := h
  exact ⟨x, w, k, w' + c, k', c', k'' + 1, h1, h2, h3, Walk.snoc y c h4 he⟩

/-! ## Phase 1: monotonicity and completeness -/

/-- The arrays keep their size `n`. -/
theorem step1_size (U : Int) (st : Array Int × Array Int) (e : Ed) :
    (step1 U st e).1.size = st.1.size ∧ (step1 U st e).2.size = st.2.size := by
  unfold step1; split <;> simp

theorem fold1_size (U : Int) (E : List Ed) (st : Array Int × Array Int) :
    (E.foldl (step1 U) st).1.size = st.1.size ∧ (E.foldl (step1 U) st).2.size = st.2.size := by
  induction E generalizing st with
  | nil => simp
  | cons e E ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (step1 U st e)
    obtain ⟨h3, h4⟩ := step1_size U st e
    exact ⟨h1.trans h3, h2.trans h4⟩

/-- Relaxing never increases a distance. -/
theorem step1_le (U : Int) (st : Array Int × Array Int) (e : Ed) (x : Nat) :
    (step1 U st e).1[x]! ≤ st.1[x]! := by
  unfold step1
  split
  · rename_i h
    simp only [get_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hx : e.2.1.toNat < st.1.size
    · rw [getElemBang_set _ _ _ _ hx]; split
      · rename_i e'; rw [e']; simp only [get_eq]; exact le_of_lt (of_decide_eq_true h.2)
      · exact le_rfl
    · unfold Cpp.set; rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le (by omega)]
  · exact le_rfl

theorem fold1_le (U : Int) (E : List Ed) (st : Array Int × Array Int) (x : Nat) :
    (E.foldl (step1 U) st).1[x]! ≤ st.1[x]! := by
  induction E generalizing st with
  | nil => exact le_rfl
  | cons e E ih => exact le_trans (ih _) (step1_le U st e x)

/-- After relaxing `(u, v, c)` with `d[u]` finite, `d[v] ≤ d[u] + c`. -/
theorem step1_relaxed (U : Int) (st : Array Int × Array Int) (u v : Nat) (c : Int) (hv : v < st.1.size)
    (hu : st.1[u]! ≠ U) : (step1 U st ((u : Int), (v : Int), c)).1[v]! ≤ st.1[u]! + c := by
  unfold step1
  simp only [get_natCast]
  by_cases h : st.1[u]! + c < st.1[v]!
  · simp only [hu, h, ne_eq, not_false_eq_true, decide_true, Bool.and_self, ↓reduceIte]
    rw [getElemBang_set _ _ _ _ (by simpa using hv)]; simp
  · simp only [h, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]; omega

/-- One round of phase 1: every edge in order. -/
def round1 (U : Int) (E : List Ed) (st : Array Int × Array Int) : Array Int × Array Int := E.foldl (step1 U) st

/-- Scanning a list that contains the edge `(u, v, c)` from a state with `d[u] ≤ B < U` ends with `d[v] ≤ B + c`. -/
theorem fold_mem_relaxed (U : Int) (E : List Ed) (st : Array Int × Array Int) (u v : Nat) (c B : Int)
    (he : ((u : Int), (v : Int), c) ∈ E) (hv : v < st.1.size) (hu : st.1[u]! ≤ B) (hB : B < U) :
    (E.foldl (step1 U) st).1[v]! ≤ B + c := by
  induction E generalizing st with
  | nil => simp at he
  | cons e E ih =>
    simp only [List.foldl_cons]
    by_cases hee : e = ((u : Int), (v : Int), c)
    · subst hee
      have h1 := step1_relaxed U st u v c hv (by omega)
      have h2 := fold1_le U E (step1 U st ((u : Int), (v : Int), c)) v
      omega
    · have he' : ((u : Int), (v : Int), c) ∈ E := by
        simp at he; rcases he with h | h
        · exact absurd h.symm hee
        · exact h
      exact ih (step1 U st e) he' (by rw [(step1_size U st e).1]; exact hv)
        (le_trans (step1_le U st e u) hu)

theorem walk_lt {n : Nat} {C : Int} {E : List Ed} (hV : Valid n C E) {a b : Nat} {w : Int} {k : Nat}
    (ha : a < n) (h : Walk E a b w k) : b < n := by
  induction h with
  | nil => exact ha
  | snoc b c _ he _ => have := (hV _ he).2.2.2.1; simp only at this; omega

/-- Completeness of phase 1: after `r` rounds, `d[v]` is at most the cost of every walk from `s` with at most `r`
edges (when the costs of these walks are below `U`). -/
theorem round1_complete {n : Nat} {C : Int} {E : List Ed} (hV : Valid n C E) (U : Int) (s : Nat) (hs : s < n)
    (st : Array Int × Array Int) (hsz : st.1.size = n) (h0 : st.1[s]! ≤ 0) (r : Nat)
    (hU : ∀ a w k, k ≤ r → Walk E s a w k → w < U) :
    ∀ v w k, Walk E s v w k → k ≤ r → ((round1 U E)^[r] st).1[v]! ≤ w := by
  induction r with
  | zero =>
    intro v w k h hk
    have : k = 0 := by omega
    subst this
    cases h with
    | nil => simpa using h0
  | succ r ih =>
    intro v w k h hk
    have hsz' : ((round1 U E)^[r] st).1.size = n := by
      clear ih hU h hk
      induction r with
      | zero => simpa using hsz
      | succ r ih2 => rw [Function.iterate_succ_apply']; unfold round1; rw [(fold1_size U E _).1]; exact ih2
    rw [Function.iterate_succ_apply']
    by_cases hk' : k ≤ r
    · exact le_trans (fold1_le U E _ v) (ih (fun a w k hk h => hU a w k (by omega) h) v w k h hk')
    · cases h with
      | nil => omega
      | @snoc u wu ku _ c hw he =>
        have hu := ih (fun a w k hk h => hU a w k (by omega) h) u wu ku hw (by omega)
        have hvn := walk_lt hV hs (Walk.snoc v c hw he)
        exact fold_mem_relaxed U E _ u v c wu he (by rw [hsz']; exact hvn) hu
          (hU u wu ku (by omega) hw)

/-! ## Phase 1: soundness and the parents -/

/-- The invariant of phase 1 with the ghost times `T x` of the last updates and the clock `τ`. -/
structure Inv1 (n s : Nat) (U : Int) (E : List Ed) (d par : Array Int) (T : Nat → Nat) (τ : Nat) : Prop where
  sn : s < n
  dsz : d.size = n
  psz : par.size = n
  dle : ∀ x < n, d[x]! ≤ U
  sound : ∀ x < n, d[x]! ≠ U → ∃ k ≤ τ, Walk E s x d[x]! k
  parOk : ∀ x < n, par[x]! ≠ -1 → ∃ u < n, par[x]! = (u : Int) ∧ d[u]! ≠ U ∧ d[x]! ≠ U ∧
    ∃ c, ((u : Int), (x : Int), c) ∈ E ∧ d[u]! + c ≤ d[x]! ∧ (T x ≤ T u → d[u]! + c < d[x]!)
  parNone : ∀ x < n, par[x]! = -1 → d[x]! = U ∨ (x = s ∧ d[x]! = 0)
  Tlt : ∀ x, T x < τ

theorem inv1_init (n s : Nat) (U : Int) (E : List Ed) (hs : s < n) (hU : 0 < U) :
    Inv1 n s U E (Cpp.set (Array.replicate n U) (s : Int) 0) (Array.replicate n (-1)) (fun _ => 0) 1 := by
  have hsz : (s : Int).toNat < (Array.replicate n U).size := by simp; omega
  refine ⟨hs, by simp, by simp, ?_, ?_, ?_, ?_, fun _ => by omega⟩
  · intro x hx; rw [getElemBang_set _ _ _ _ hsz]; split
    · omega
    · simp [hx]
  · intro x hx h
    rw [getElemBang_set _ _ _ _ hsz] at h ⊢
    by_cases e : x = s
    · subst e; simp; exact ⟨0, by omega, Walk.nil x⟩
    · simp [hx] at h; exact absurd h.1 e
  · intro x hx h; simp [hx] at h
  · intro x hx _
    rw [getElemBang_set _ _ _ _ hsz]
    by_cases e : x = s
    · subst e; simp
    · simp [hx]; omega

theorem inv1_step {n s : Nat} {U C : Int} {E : List Ed} (hV : Valid n C E) {d par : Array Int} {T : Nat → Nat}
    {τ : Nat} (hI : Inv1 n s U E d par T τ) (e : Ed) (he : e ∈ E) :
    ∃ T' τ', Inv1 n s U E (step1 U (d, par) e).1 (step1 U (d, par) e).2 T' τ' ∧ τ' ≤ τ + 1 := by
  obtain ⟨u, w, c⟩ := e
  obtain ⟨hu0, hun, hw0, hwn, _, _⟩ := hV _ he
  simp only at hu0 hun hw0 hwn
  obtain ⟨u, rfl⟩ : ∃ u' : Nat, u = (u' : Int) := ⟨u.toNat, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w' : Nat, w = (w' : Int) := ⟨w.toNat, by omega⟩
  have hun' : u < n := by omega
  have hwn' : w < n := by omega
  unfold step1
  split
  · rename_i hb
    simp only [get_natCast, Bool.and_eq_true] at hb
    obtain ⟨hdu', hlt'⟩ := hb
    have hdu : d[u]! ≠ U := of_decide_eq_true hdu'
    have hlt : d[u]! + c < d[w]! := of_decide_eq_true hlt'
    simp only [get_natCast]
    have hdsz : (w : Int).toNat < d.size := by rw [hI.dsz]; simpa using hwn'
    have hpsz : (w : Int).toNat < par.size := by rw [hI.psz]; simpa using hwn'
    have hD : ∀ x, (Cpp.set d (w : Int) (d[u]! + c))[x]! = if x = w then d[u]! + c else d[x]! := by
      intro x; rw [getElemBang_set _ _ _ _ hdsz]; simp
    have hP : ∀ x, (Cpp.set par (w : Int) (u : Int))[x]! = if x = w then (u : Int) else par[x]! := by
      intro x; rw [getElemBang_set _ _ _ _ hpsz]; simp
    have hdw := hI.dle w hwn'
    refine ⟨fun x => if x = w then τ else T x, τ + 1, ⟨hI.sn, by simp [hI.dsz], by simp [hI.psz], ?_, ?_, ?_, ?_, ?_⟩,
      le_rfl⟩
    · intro x hx; rw [hD]; split
      · omega
      · exact hI.dle x hx
    · intro x hx hne
      rw [hD] at hne ⊢
      split
      · rename_i ex; subst ex
        obtain ⟨k, hk, hwk⟩ := hI.sound u hun' hdu
        exact ⟨k + 1, by omega, Walk.snoc x c hwk he⟩
      · rename_i ex; rw [if_neg ex] at hne
        obtain ⟨k, hk, hwk⟩ := hI.sound x hx hne
        exact ⟨k, by omega, hwk⟩
    · intro x hx hne
      rw [hP] at hne ⊢
      by_cases ex : x = w
      · subst ex
        simp only [↓reduceIte]
        refine ⟨u, hun', rfl, ?_, ?_, c, he, ?_, ?_⟩
        · rw [hD]; split <;> omega
        · rw [hD]; simp; omega
        · rw [hD, hD]; split
          · rename_i eu; subst eu; simp; omega
          · simp
        · intro hT
          rw [hD, hD]; split
          · rename_i eu; subst eu; simp; omega
          · rename_i eu; simp [eu] at hT; have := hI.Tlt u; omega
      · rw [if_neg ex] at hne
        obtain ⟨u0, hu0n, hpu, hdu0, hdx, c0, he0, hle, hstr⟩ := hI.parOk x hx hne
        refine ⟨u0, hu0n, by rw [if_neg ex]; exact hpu, ?_, ?_, c0, he0, ?_, ?_⟩
        · rw [hD]; split
          · omega
          · exact hdu0
        · rw [hD, if_neg ex]; exact hdx
        · rw [hD, hD, if_neg ex]; split
          · rename_i eu; subst eu; omega
          · exact hle
        · intro hT
          rw [hD, hD, if_neg ex]
          split
          · rename_i eu; subst eu; omega
          · rename_i eu; simp [ex, eu] at hT; exact hstr hT
    · intro x hx hp
      rw [hP] at hp
      split at hp
      · omega
      · rename_i ex; rw [hD, if_neg ex]; exact hI.parNone x hx hp
    · intro x; split
      · omega
      · have := hI.Tlt x; omega
  · exact ⟨T, τ, hI, by omega⟩

theorem inv1_fold {n s : Nat} {U C : Int} {E : List Ed} (hV : Valid n C E) (es : List Ed) (hes : ∀ e ∈ es, e ∈ E)
    (st : Array Int × Array Int) {T : Nat → Nat} {τ : Nat} (hI : Inv1 n s U E st.1 st.2 T τ) :
    ∃ T' τ', Inv1 n s U E (es.foldl (step1 U) st).1 (es.foldl (step1 U) st).2 T' τ' ∧ τ' ≤ τ + es.length := by
  induction es generalizing st T τ with
  | nil => exact ⟨T, τ, hI, by simp⟩
  | cons e es ih =>
    simp only [List.foldl_cons, List.length_cons]
    obtain ⟨T1, τ1, h1, hτ1⟩ := inv1_step hV hI e (hes e (by simp))
    obtain ⟨T2, τ2, h2, hτ2⟩ := ih (fun e' he' => hes e' (by simp [he'])) (step1 U st e) h1
    exact ⟨T2, τ2, h2, by omega⟩

theorem inv1_rounds {n s : Nat} {U C : Int} {E : List Ed} (hV : Valid n C E) (r : Nat)
    (st : Array Int × Array Int) {T : Nat → Nat} {τ : Nat} (hI : Inv1 n s U E st.1 st.2 T τ) :
    ∃ T' τ', Inv1 n s U E ((round1 U E)^[r] st).1 ((round1 U E)^[r] st).2 T' τ' ∧ τ' ≤ τ + r * E.length := by
  induction r with
  | zero => exact ⟨T, τ, hI, by simp⟩
  | succ r ih =>
    obtain ⟨T1, τ1, h1, hτ1⟩ := ih
    rw [Function.iterate_succ_apply']
    obtain ⟨T2, τ2, h2, hτ2⟩ := inv1_fold hV E (fun e he => he) _ h1
    exact ⟨T2, τ2, h2, by rw [Nat.succ_mul]; omega⟩

/-! ## Shortening walks around nonnegative cycles -/

/-- A walk with the list of its vertices. -/
inductive WalkL (E : List Ed) : Nat → Nat → Int → Nat → List Nat → Prop
  | nil (a : Nat) : WalkL E a a 0 0 [a]
  | snoc {a u : Nat} {w : Int} {k : Nat} {vs : List Nat} (b : Nat) (c : Int) :
      WalkL E a u w k vs → ((u : Int), (b : Int), c) ∈ E → WalkL E a b (w + c) (k + 1) (vs ++ [b])

theorem walkL_of_walk {E : List Ed} {a b : Nat} {w : Int} {k : Nat} (h : Walk E a b w k) :
    ∃ vs, WalkL E a b w k vs := by
  induction h with
  | nil => exact ⟨_, WalkL.nil _⟩
  | snoc b c _ he ih => obtain ⟨vs, h⟩ := ih; exact ⟨_, WalkL.snoc b c h he⟩

theorem walk_of_walkL {E : List Ed} {a b : Nat} {w : Int} {k : Nat} {vs : List Nat} (h : WalkL E a b w k vs) :
    Walk E a b w k := by
  induction h with
  | nil => exact Walk.nil _
  | snoc b c _ he ih => exact Walk.snoc b c ih he

theorem walkL_length {E : List Ed} {a b : Nat} {w : Int} {k : Nat} {vs : List Nat} (h : WalkL E a b w k vs) :
    vs.length = k + 1 := by
  induction h with
  | nil => rfl
  | snoc _ _ _ _ ih => simp [ih]

theorem walkL_mem {n : Nat} {C : Int} {E : List Ed} (hV : Valid n C E) {a b : Nat} {w : Int} {k : Nat}
    {vs : List Nat} (ha : a < n) (h : WalkL E a b w k vs) : ∀ x ∈ vs, x < n := by
  induction h with
  | nil => intro x hx; simp at hx; omega
  | snoc b c _ he ih =>
    intro x hx
    simp at hx
    rcases hx with hx | hx
    · exact ih x hx
    · have := (hV _ he).2.2.2.1; simp only at this; omega

/-- Splitting a walk at an occurrence of a vertex. -/
theorem walkL_split {E : List Ed} {a b : Nat} {w : Int} {k : Nat} {vs : List Nat} (h : WalkL E a b w k vs) :
    ∀ (A B : List Nat) (x : Nat), vs = A ++ x :: B →
      ∃ w1 k1 w2 k2, WalkL E a x w1 k1 (A ++ [x]) ∧ WalkL E x b w2 k2 (x :: B) ∧ w = w1 + w2 ∧ k = k1 + k2 := by
  induction h with
  | nil =>
    intro A B x e
    cases A with
    | nil => simp at e; obtain ⟨rfl, rfl⟩ := e; exact ⟨0, 0, 0, 0, WalkL.nil _, WalkL.nil _, by simp, by simp⟩
    | cons y A => simp at e
  | @snoc u w k vs b c hw he ih =>
    intro A B x e
    rcases List.eq_nil_or_concat B with rfl | ⟨B', b', rfl⟩
    · have h2 := List.append_inj' (s₁ := vs) (t₁ := [b]) (s₂ := A) (t₂ := [x]) (by simpa using e) (by simp)
      obtain ⟨rfl, hb⟩ := h2
      simp at hb; subst hb
      exact ⟨w + c, k + 1, 0, 0, WalkL.snoc _ c hw he, WalkL.nil _, by simp, by simp⟩
    · have e' : vs ++ [b] = (A ++ x :: B') ++ [b'] := by rw [e]; simp
      obtain ⟨hvs, hb⟩ := List.append_inj' e' (by simp)
      simp at hb; subst hb
      obtain ⟨w1, k1, w2, k2, h1, h2, hw', hk'⟩ := ih A B' x hvs
      refine ⟨w1, k1, w2 + c, k2 + 1, h1, ?_, by omega, by omega⟩
      have := WalkL.snoc b c h2 he
      simpa using this

/-- A list that is not duplicate-free has a vertex twice. -/
theorem exists_dup {l : List Nat} (h : ¬ l.Nodup) : ∃ A x M C, l = A ++ x :: (M ++ x :: C) := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    by_cases hy : y ∈ l
    · obtain ⟨M, C, rfl⟩ := List.append_of_mem hy
      exact ⟨[], y, M, C, by simp⟩
    · have : ¬ l.Nodup := fun hl => h (List.nodup_cons.mpr ⟨hy, hl⟩)
      obtain ⟨A, x, M, C, rfl⟩ := ih this
      exact ⟨y :: A, x, M, C, by simp⟩

theorem nodup_length {n : Nat} {l : List Nat} (hl : l.Nodup) (h : ∀ x ∈ l, x < n) : l.length ≤ n := by
  have := (List.Nodup.subperm hl (l₂ := List.range n) (fun x hx => List.mem_range.mpr (h x hx))).length_le
  simpa using this

/-- A walk to a vertex that no negative cycle reaches can be shortened to at most `n - 1` edges without
increasing its cost. -/
theorem shorten {n : Nat} {C : Int} {E : List Ed} (hV : Valid n C E) {s v : Nat} (hs : s < n)
    (hneg : ¬ NegReach E s v) : ∀ k w, Walk E s v w k → ∃ k' w', k' + 1 ≤ n ∧ w' ≤ w ∧ Walk E s v w' k' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w hw
    by_cases hk : k + 1 ≤ n
    · exact ⟨k, w, hk, le_rfl, hw⟩
    · obtain ⟨vs, hL⟩ := walkL_of_walk hw
      have hlen := walkL_length hL
      have hnd : ¬ vs.Nodup := fun hnd => by
        have := nodup_length hnd (walkL_mem hV hs hL); omega
      obtain ⟨A, x, M, Cs, hvs⟩ := exists_dup hnd
      obtain ⟨w1, k1, w2, k2, h1, h2, hw12, hk12⟩ := walkL_split hL A (M ++ x :: Cs) x hvs
      obtain ⟨w3, k3, w4, k4, h3, h4, hw34, hk34⟩ := walkL_split h2 (x :: M) Cs x (by simp)
      have hk3 : 1 ≤ k3 := by have := walkL_length h3; simp at this; omega
      by_cases hc : w3 < 0
      · exact absurd ⟨x, w1, k1, w4, k3, w3, k4, walk_of_walkL h1, walk_of_walkL h3, hc, walk_of_walkL h4⟩ hneg
      · obtain ⟨k', w', h5, h6, h7⟩ := ih (k1 + k4) (by omega) (w1 + w4)
          (walk_append (walk_of_walkL h1) (walk_of_walkL h4))
        exact ⟨k', w', h5, by omega, h7⟩

theorem walk_cost {n : Nat} {C : Int} {E : List Ed} (hV : Valid n C E) {a b : Nat} {w : Int} {k : Nat}
    (h : Walk E a b w k) : -((k : Int) * C) ≤ w ∧ w ≤ (k : Int) * C := by
  induction h with
  | nil => simp
  | snoc b c _ he ih =>
    have := (hV _ he).2.2.2.2; simp only at this
    push_cast; constructor <;> nlinarith [ih.1, ih.2, this.1, this.2]

/-- Every walk can be shortened to at most `n - 1` edges (the cost may change). -/
theorem shorten_any {n : Nat} {C : Int} {E : List Ed} (hV : Valid n C E) {s v : Nat} (hs : s < n) :
    ∀ k w, Walk E s v w k → ∃ k' w', k' + 1 ≤ n ∧ Walk E s v w' k' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w hw
    by_cases hk : k + 1 ≤ n
    · exact ⟨k, w, hk, hw⟩
    · obtain ⟨vs, hL⟩ := walkL_of_walk hw
      have hlen := walkL_length hL
      have hnd : ¬ vs.Nodup := fun hnd => by
        have := nodup_length hnd (walkL_mem hV hs hL); omega
      obtain ⟨A, x, M, Cs, hvs⟩ := exists_dup hnd
      obtain ⟨w1, k1, w2, k2, h1, h2, hw12, hk12⟩ := walkL_split hL A (M ++ x :: Cs) x hvs
      obtain ⟨w3, k3, w4, k4, h3, h4, hw34, hk34⟩ := walkL_split h2 (x :: M) Cs x (by simp)
      have hk3 : 1 ≤ k3 := by have := walkL_length h3; simp at this; omega
      exact ih (k1 + k4) (by omega) (w1 + w4) (walk_append (walk_of_walkL h1) (walk_of_walkL h4))

/-! ## The result of phase 1 -/

/-- The initial state: `d = U` except `d[s] = 0`, no parents. -/
abbrev st0 (n s : Nat) (U : Int) : Array Int × Array Int :=
  (Cpp.set (Array.replicate n U) (s : Int) 0, Array.replicate n (-1))

theorem st0_s (n s : Nat) (U : Int) (hs : s < n) : (st0 n s U).1[s]! = 0 := by
  rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp

theorem phase1_complete {n s : Nat} {U C : Int} {E : List Ed} (hV : Valid n C E) (hs : s < n) (hC : 0 ≤ C)
    (hU : (n : Int) * C < U) :
    ∀ v w k, Walk E s v w k → k + 1 ≤ n → ((round1 U E)^[n - 1] (st0 n s U)).1[v]! ≤ w := by
  intro v w k h hk
  refine round1_complete hV U s hs _ (by simp) (by rw [st0_s n s U hs]) (n - 1) ?_ v w k h (by omega)
  intro a w' k' hk' h'
  have := (walk_cost hV h').2
  have : (k' : Int) * C ≤ (n : Int) * C := Int.mul_le_mul_of_nonneg_right (by omega) hC
  omega

/-- A reachable vertex has a finite distance after phase 1. -/
theorem phase1_reach {n s : Nat} {U C : Int} {E : List Ed} (hV : Valid n C E) (hs : s < n) (hC : 0 ≤ C)
    (hU : (n : Int) * C < U) {v : Nat} {w : Int} {k : Nat} (h : Walk E s v w k) :
    ((round1 U E)^[n - 1] (st0 n s U)).1[v]! < U := by
  obtain ⟨k', w', hk', h'⟩ := shorten_any hV hs k w h
  have h1 := phase1_complete hV hs hC hU v w' k' h' hk'
  have h2 := (walk_cost hV h').2
  have : (k' : Int) * C ≤ (n : Int) * C := Int.mul_le_mul_of_nonneg_right (by omega) hC
  omega

/-- A vertex that no negative cycle reaches gets at most the cost of every walk to it. -/
theorem phase1_min {n s : Nat} {U C : Int} {E : List Ed} (hV : Valid n C E) (hs : s < n) (hC : 0 ≤ C)
    (hU : (n : Int) * C < U) {v : Nat} (hneg : ¬ NegReach E s v) {w : Int} {k : Nat} (h : Walk E s v w k) :
    ((round1 U E)^[n - 1] (st0 n s U)).1[v]! ≤ w := by
  obtain ⟨k', w', hk', hw', h'⟩ := shorten hV hs hneg k w h
  exact le_trans (phase1_complete hV hs hC hU v w' k' h' hk') hw'

/-- A walk given backwards (from its end to `s`), as `ListGraph::shortest_path` reads the parents. -/
inductive WalkB (E : List Ed) (s : Nat) : List Int → Int → Prop
  | one : WalkB E s [(s : Int)] 0
  | cons (x : Int) (u : Nat) (rest : List Int) (w c : Int) :
      WalkB E s ((u : Int) :: rest) w → ((u : Int), x, c) ∈ E → WalkB E s (x :: (u : Int) :: rest) (w + c)

/-- With the invariant of phase 1 and the minimality of the distances of the vertices that no negative cycle
reaches, the parent chain of such a vertex with a finite distance reaches `-1` through `s`, and it is a walk whose
cost is the distance. -/
theorem chain_of_min {n s : Nat} {U : Int} {E : List Ed} {d par : Array Int} {T : Nat → Nat} {τ : Nat}
    (hI : Inv1 n s U E d par T τ)
    (hmin : ∀ v, ¬ NegReach E s v → ∀ w k, Walk E s v w k → d[v]! ≤ w) :
    ∀ x, x < n → ¬ NegReach E s x → d[x]! ≠ U → ∃ Cl, Chain par x Cl ∧ WalkB E s Cl d[x]! ∧
      ∀ y ∈ Cl, ∃ y' : Nat, y = y' ∧ y' < n ∧ ¬ NegReach E s y' := by
  intro x
  induction hT : T x using Nat.strong_induction_on generalizing x with
  | _ t ih =>
    intro hx hneg hfin
    by_cases hp : par[x]! = -1
    · rcases hI.parNone x hx hp with h | ⟨rfl, h0⟩
      · exact absurd h hfin
      · refine ⟨[(x : Int)], Chain.step _ _ (by omega) ?_, by rw [h0]; exact WalkB.one, ?_⟩
        · have : Cpp.get par (x : Int) = -1 := hp
          rw [this]; exact Chain.stop
        · intro y hy; simp at hy; exact ⟨x, hy, hx, hneg⟩
    · obtain ⟨u, hun, hpu, hdu, _, c, he, hle, hstr⟩ := hI.parOk x hx hp
      obtain ⟨k, _, hwk⟩ := hI.sound u hun hdu
      have hmx := hmin x hneg _ _ (Walk.snoc x c hwk he)
      have hTu : T u < T x := by
        by_contra hge; have := hstr (by omega); omega
      have hnegu : ¬ NegReach E s u := fun h => hneg (negReach_step h x c he)
      obtain ⟨Cl, hC, hW, hmem⟩ := ih (T u) (by omega) u rfl hun hnegu hdu
      obtain ⟨rest, rfl, _⟩ := chain_cons hC (by omega)
      refine ⟨(x : Int) :: (u : Int) :: rest, Chain.step _ _ (by omega) ?_, ?_, ?_⟩
      · have : Cpp.get par (x : Int) = (u : Int) := hpu
        rw [this]; exact hC
      · have hdx : d[x]! = d[u]! + c := by omega
        rw [hdx]; exact WalkB.cons _ _ _ _ _ hW he
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact ⟨x, rfl, hx, hneg⟩
        · exact hmem y (by simp at hy ⊢; exact hy)

/-! ## Phase 2 -/

/-- One round of phase 2. -/
def round2 (U NEG : Int) (E : List Ed) (st : Array Int × Array Int) : Array Int × Array Int :=
  E.foldl (step2 U NEG) st

/-- During phase 2 every distance is its phase-1 value (with its parent) or `NEG`. -/
def Inv2 (n : Nat) (NEG : Int) (d1 p1 : Array Int) (st : Array Int × Array Int) : Prop :=
  st.1.size = n ∧ st.2.size = n ∧ ∀ x < n, (st.1[x]! = d1[x]! ∧ st.2[x]! = p1[x]!) ∨ st.1[x]! = NEG

theorem step2_spec (U NEG : Int) (st : Array Int × Array Int) (u w : Nat) (c : Int) (hw : w < st.1.size)
    (hwp : w < st.2.size) :
    let r := step2 U NEG st ((u : Int), (w : Int), c)
    (st.1[u]! ≠ U ∧ st.1[u]! + c < st.1[w]! → r.1[w]! = NEG) ∧
    (¬(st.1[u]! ≠ U ∧ st.1[u]! + c < st.1[w]!) → r = st) ∧
    (∀ x, x ≠ w → r.1[x]! = st.1[x]! ∧ r.2[x]! = st.2[x]!) ∧ r.1.size = st.1.size ∧ r.2.size = st.2.size := by
  intro r
  have hD : ∀ x, (Cpp.set st.1 (w : Int) NEG)[x]! = if x = w then NEG else st.1[x]! := by
    intro x; rw [getElemBang_set _ _ _ _ (by simpa using hw)]; simp
  have hP : ∀ x, (Cpp.set st.2 (w : Int) (-1))[x]! = if x = w then -1 else st.2[x]! := by
    intro x; rw [getElemBang_set _ _ _ _ (by simpa using hwp)]; simp
  by_cases hc : st.1[u]! ≠ U ∧ st.1[u]! + c < st.1[w]!
  · have hr : r = (Cpp.set st.1 (w : Int) NEG, Cpp.set st.2 (w : Int) (-1)) := by
      show step2 U NEG st _ = _
      unfold step2
      split
      · rfl
      · rename_i h; exfalso; apply h
        simp only [get_natCast, Bool.and_eq_true]; exact ⟨decide_eq_true hc.1, decide_eq_true hc.2⟩
    rw [hr]
    refine ⟨fun _ => by simp [hD], fun h => absurd hc h, fun x hx => by simp [hD, hP, hx], by simp, by simp⟩
  · have hr : r = st := by
      show step2 U NEG st _ = _
      unfold step2
      split
      · rename_i h; exfalso; simp only [get_natCast, Bool.and_eq_true] at h
        exact hc ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩
      · rfl
    rw [hr]
    exact ⟨fun h => absurd h hc, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩

theorem edge_nat {n : Nat} {C : Int} {E : List Ed} (hV : Valid n C E) {e : Ed} (he : e ∈ E) :
    ∃ (u w : Nat) (c : Int), u < n ∧ w < n ∧ e = ((u : Int), (w : Int), c) ∧ -C ≤ c ∧ c ≤ C := by
  obtain ⟨u, w, c⟩ := e
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hV _ he
  simp only at *
  exact ⟨u.toNat, w.toNat, c, by omega, by omega, by simp; omega, h5, h6⟩

theorem inv2_step {n : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) {d1 p1 : Array Int}
    {st : Array Int × Array Int} (h : Inv2 n NEG d1 p1 st) (e : Ed) (he : e ∈ E) :
    Inv2 n NEG d1 p1 (step2 U NEG st e) ∧ ∀ x < n, st.1[x]! = NEG → (step2 U NEG st e).1[x]! = NEG := by
  obtain ⟨u, w, c, hun, hwn, rfl, _, _⟩ := edge_nat hV he
  obtain ⟨hs1, hs2, hx⟩ := h
  obtain ⟨hfire, hno, hother, hsz1, hsz2⟩ := step2_spec U NEG st u w _ (by omega) (by omega)
  refine ⟨⟨by rw [hsz1, hs1], by rw [hsz2, hs2], fun x hx' => ?_⟩, fun x hx' hneg => ?_⟩
  · by_cases ex : x = w
    · subst ex
      by_cases hc : st.1[u]! ≠ U ∧ st.1[u]! + c < st.1[x]!
      · exact Or.inr (hfire hc)
      · rw [hno hc]; exact hx x hx'
    · rw [(hother x ex).1, (hother x ex).2]; exact hx x hx'
  · by_cases ex : x = w
    · subst ex
      by_cases hc : st.1[u]! ≠ U ∧ st.1[u]! + c < st.1[x]!
      · exact hfire hc
      · rw [hno hc]; exact hneg
    · rw [(hother x ex).1]; exact hneg

theorem inv2_fold {n : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) {d1 p1 : Array Int}
    (es : List Ed) (hes : ∀ e ∈ es, e ∈ E) (st : Array Int × Array Int) (h : Inv2 n NEG d1 p1 st) :
    Inv2 n NEG d1 p1 (es.foldl (step2 U NEG) st) ∧
      ∀ x < n, st.1[x]! = NEG → (es.foldl (step2 U NEG) st).1[x]! = NEG := by
  induction es generalizing st with
  | nil => exact ⟨h, fun _ _ h => h⟩
  | cons e es ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := inv2_step (U := U) hV h e (hes e (by simp))
    obtain ⟨h3, h4⟩ := ih (fun e' he' => hes e' (by simp [he'])) _ h1
    exact ⟨h3, fun x hx hn => h4 x hx (h2 x hx hn)⟩

theorem inv2_rounds {n : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) {d1 p1 : Array Int} (r : Nat)
    (st : Array Int × Array Int) (h : Inv2 n NEG d1 p1 st) :
    Inv2 n NEG d1 p1 ((round2 U NEG E)^[r] st) ∧
      ∀ x < n, st.1[x]! = NEG → ((round2 U NEG E)^[r] st).1[x]! = NEG := by
  induction r with
  | zero => exact ⟨h, fun _ _ h => h⟩
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := inv2_fold (U := U) hV E (fun e he => he) _ h1
    exact ⟨h3, fun x hx hn => h4 x hx (h2 x hx hn)⟩

/-- The vertices that no negative cycle reaches keep their phase-1 distances and parents during phase 2. -/
def Keep (n s : Nat) (E : List Ed) (d1 p1 : Array Int) (st : Array Int × Array Int) : Prop :=
  ∀ x < n, ¬ NegReach E s x → st.1[x]! = d1[x]! ∧ st.2[x]! = p1[x]!

theorem keep_step {n s : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) {d1 p1 : Array Int}
    (hsound : ∀ x < n, d1[x]! ≠ U → ∃ k, Walk E s x d1[x]! k)
    (hmin : ∀ v, ¬ NegReach E s v → ∀ w k, Walk E s v w k → d1[v]! ≤ w)
    {st : Array Int × Array Int} (h2 : Inv2 n NEG d1 p1 st) (h : Keep n s E d1 p1 st) (e : Ed) (he : e ∈ E) :
    Keep n s E d1 p1 (step2 U NEG st e) := by
  obtain ⟨u, w, c, hun, hwn, rfl, _, _⟩ := edge_nat hV he
  obtain ⟨hs1, hs2, _⟩ := h2
  obtain ⟨_, hno, hother, _, _⟩ := step2_spec U NEG st u w c (by omega) (by omega)
  intro x hx hneg
  by_cases ex : x = w
  · subst ex
    have hnegu : ¬ NegReach E s u := fun h' => hneg (negReach_step h' x c he)
    obtain ⟨hu1, _⟩ := h u hun hnegu
    obtain ⟨hx1, hx2⟩ := h x hx hneg
    have hc : ¬(st.1[u]! ≠ U ∧ st.1[u]! + c < st.1[x]!) := by
      rintro ⟨h1, h3⟩
      rw [hu1] at h1 h3; rw [hx1] at h3
      obtain ⟨k, hk⟩ := hsound u hun h1
      have := hmin x hneg _ _ (Walk.snoc x c hk he)
      omega
    rw [hno hc]; exact ⟨hx1, hx2⟩
  · rw [(hother x ex).1, (hother x ex).2]; exact h x hx hneg

theorem keep_rounds {n s : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) {d1 p1 : Array Int}
    (hsound : ∀ x < n, d1[x]! ≠ U → ∃ k, Walk E s x d1[x]! k)
    (hmin : ∀ v, ¬ NegReach E s v → ∀ w k, Walk E s v w k → d1[v]! ≤ w) (r : Nat)
    (st : Array Int × Array Int) (h2 : Inv2 n NEG d1 p1 st) (h : Keep n s E d1 p1 st) :
    Keep n s E d1 p1 ((round2 U NEG E)^[r] st) := by
  have hfold : ∀ (es : List Ed), (∀ e ∈ es, e ∈ E) → ∀ st, Inv2 n NEG d1 p1 st → Keep n s E d1 p1 st →
      Keep n s E d1 p1 (es.foldl (step2 U NEG) st) := by
    intro es hes
    induction es with
    | nil => intro st _ h; exact h
    | cons e es ih =>
      intro st h2 h
      simp only [List.foldl_cons]
      exact ih (fun e' he' => hes e' (by simp [he'])) _ (inv2_step hV h2 e (hes e (by simp))).1
        (keep_step hV hsound hmin h2 h e (hes e (by simp)))
  induction r with
  | zero => exact h
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact hfold E (fun e he => he) _ (inv2_rounds hV r st h2).1 ih

theorem walkL_last_mem {E : List Ed} {a b : Nat} {w : Int} {k : Nat} {vs : List Nat} (h : WalkL E a b w k vs) :
    b ∈ vs := by
  cases h with
  | nil => simp
  | snoc => simp

/-- Summing an inequality along the edges of a walk. -/
theorem walkL_sum (f : Nat → Int) {E : List Ed} {a b : Nat} {w : Int} {k : Nat} {vs : List Nat}
    (h : WalkL E a b w k vs)
    (H : ∀ (u b : Nat) (c : Int), ((u : Int), (b : Int), c) ∈ E → u ∈ vs → b ∈ vs → f b ≤ f u + c) :
    f b ≤ f a + w := by
  revert H
  induction h with
  | nil => intro _; simp
  | @snoc u w k vs b c hw he ih =>
    intro H
    have h1 := ih (fun u' b' c' he' hu hb => H u' b' c' he' (by simp [hu]) (by simp [hb]))
    have h2 := H u b c he (by simp [walkL_last_mem hw]) (by simp)
    omega

/-- `NEG` spreads along an edge in one round. -/
theorem fold_spread {n : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) {d1 p1 : Array Int}
    (hB : ∀ x < n, d1[x]! = U ∨ NEG + C < d1[x]!) (hNU : NEG + C < U) (hC : 0 ≤ C)
    {y z : Nat} {c : Int} (hyz : ((y : Int), (z : Int), c) ∈ E) :
    ∀ (es : List Ed), (∀ e ∈ es, e ∈ E) → ((y : Int), (z : Int), c) ∈ es → ∀ st, Inv2 n NEG d1 p1 st →
      st.1[y]! = NEG → (es.foldl (step2 U NEG) st).1[z]! = NEG := by
  obtain ⟨_, hyn, _, hzn, hc1, hc2⟩ := hV _ hyz
  simp only at hyn hzn hc1 hc2
  intro es hes hmem
  induction es with
  | nil => simp at hmem
  | cons e es ih =>
    intro st h2 hy
    simp only [List.foldl_cons]
    obtain ⟨h3, h4⟩ := inv2_step (U := U) hV h2 e (hes e (by simp))
    by_cases ee : e = ((y : Int), (z : Int), c)
    · subst ee
      obtain ⟨hs1, hs2, hx⟩ := h2
      obtain ⟨hfire, hno, _, _, _⟩ := step2_spec U NEG st y z c (by omega) (by omega)
      have hz : (step2 U NEG st ((y : Int), (z : Int), c)).1[z]! = NEG := by
        by_cases hzN : st.1[z]! = NEG
        · exact h4 z (by omega) hzN
        · apply hfire
          refine ⟨by rw [hy]; omega, ?_⟩
          rw [hy]
          rcases hx z (by omega) with ⟨hz1, _⟩ | hz1
          · rw [hz1]; rcases hB z (by omega) with h | h <;> omega
          · exact absurd hz1 hzN
      exact (inv2_fold (U := U) hV es (fun e' he' => hes e' (by simp [he'])) _ h3).2 z (by omega) hz
    · have hmem' : ((y : Int), (z : Int), c) ∈ es := by
        simp at hmem; rcases hmem with h | h
        · exact absurd h.symm ee
        · exact h
      exact ih (fun e' he' => hes e' (by simp [he'])) hmem' _ h3 (h4 y (by omega) hy)

/-- If no vertex of a closed walk is marked during a round, the inequalities hold along its edges. -/
theorem fold_nofire {n : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) {d1 p1 : Array Int}
    {u b : Nat} {c : Int} (hub : ((u : Int), (b : Int), c) ∈ E) (hu : d1[u]! ≠ U) :
    ∀ (es : List Ed), (∀ e ∈ es, e ∈ E) → ((u : Int), (b : Int), c) ∈ es → ∀ st, Inv2 n NEG d1 p1 st →
      (es.foldl (step2 U NEG) st).1[u]! ≠ NEG → (es.foldl (step2 U NEG) st).1[b]! ≠ NEG →
      d1[b]! ≤ d1[u]! + c := by
  obtain ⟨_, hun, _, hbn, _, _⟩ := hV _ hub
  simp only at hun hbn
  intro es hes hmem
  induction es with
  | nil => simp at hmem
  | cons e es ih =>
    intro st h2 hfu hfb
    simp only [List.foldl_cons] at hfu hfb
    obtain ⟨h3, h4⟩ := inv2_step (U := U) hV h2 e (hes e (by simp))
    have hpers := (inv2_fold (U := U) hV es (fun e' he' => hes e' (by simp [he'])) _ h3).2
    by_cases ee : e = ((u : Int), (b : Int), c)
    · subst ee
      obtain ⟨hs1, hs2, hx⟩ := h2
      obtain ⟨hfire, hno, _, _, _⟩ := step2_spec U NEG st u b c (by omega) (by omega)
      have hsu : st.1[u]! = d1[u]! := by
        rcases hx u (by omega) with ⟨h, _⟩ | h
        · exact h
        · exact absurd (hpers u (by omega) (h4 u (by omega) h)) hfu
      have hsb : st.1[b]! = d1[b]! := by
        rcases hx b (by omega) with ⟨h, _⟩ | h
        · exact h
        · exact absurd (hpers b (by omega) (h4 b (by omega) h)) hfb
      by_contra hlt
      have hf := hfire ⟨by rw [hsu]; exact hu, by rw [hsu, hsb]; omega⟩
      exact hfb (hpers b (by omega) hf)
    · have hmem' : ((u : Int), (b : Int), c) ∈ es := by
        simp at hmem; rcases hmem with h | h
        · exact absurd h.symm ee
        · exact h
      exact ih (fun e' he' => hes e' (by simp [he'])) hmem' _ h3 hfu hfb

theorem spread_walk {n : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) {d1 p1 : Array Int}
    (hB : ∀ x < n, d1[x]! = U ∨ NEG + C < d1[x]!) (hNU : NEG + C < U) (hC : 0 ≤ C)
    (st : Array Int × Array Int) (h2 : Inv2 n NEG d1 p1 st) {y z : Nat} {w : Int} {k : Nat}
    (hw : Walk E y z w k) :
    ∀ r, ((round2 U NEG E)^[r] st).1[y]! = NEG → ((round2 U NEG E)^[r + k] st).1[z]! = NEG := by
  induction hw with
  | nil => intro r h; simpa using h
  | @snoc u w k b c hw he ih =>
    intro r h
    have hu := ih r h
    rw [show r + (k + 1) = (r + k) + 1 by omega, Function.iterate_succ_apply']
    exact fold_spread hV hB hNU hC he E (fun e he => he) he _ (inv2_rounds hV (r + k) st h2).1 hu

/-- Phase 2 marks every vertex that a negative cycle reaches. -/
theorem phase2_neg {n s : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) (hs : s < n) {d1 p1 : Array Int}
    (h2 : Inv2 n NEG d1 p1 (d1, p1)) (hfin : ∀ v w k, Walk E s v w k → d1[v]! < U)
    (hB : ∀ x < n, d1[x]! = U ∨ NEG + C < d1[x]!) (hNU : NEG + C < U) (hC : 0 ≤ C)
    {v : Nat} (hneg : NegReach E s v) : ((round2 U NEG E)^[n] (d1, p1)).1[v]! = NEG := by
  obtain ⟨x, w0, k0, w', k', c0, k'', h1, hcyc, hc0, h3⟩ := hneg
  obtain ⟨vs, hL⟩ := walkL_of_walk hcyc
  have hxn : x < n := walk_lt hV hs h1
  -- every vertex of the cycle is reachable from s
  have hreach : ∀ u ∈ vs, (∃ w k, Walk E s u w k) ∧ ∃ w k, Walk E u v w k := by
    intro u hu
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hu
    obtain ⟨w1, k1, w2, k2, hA, hB', _, _⟩ := walkL_split hL A B u hAB
    exact ⟨⟨_, _, walk_append h1 (walk_of_walkL hA)⟩, ⟨_, _, walk_append (walk_of_walkL hB') h3⟩⟩
  -- after the first round some vertex of the cycle is marked
  have hfirst : ∃ y ∈ vs, ((round2 U NEG E)^[1] (d1, p1)).1[y]! = NEG := by
    by_contra hno
    push_neg at hno
    have hsum := walkL_sum (fun z => d1[z]!) hL (fun u b c he hu hb => by
      obtain ⟨⟨wu, ku, hwu⟩, _⟩ := hreach u hu
      have hfu := hfin u wu ku hwu
      exact fold_nofire hV he (ne_of_lt hfu) E (fun e he => he) he (d1, p1) h2
        (by simpa [round2] using hno u hu) (by simpa [round2] using hno b hb))
    simp at hsum; omega
  obtain ⟨y, hy, hyN⟩ := hfirst
  obtain ⟨_, ⟨wy, ky, hwy⟩⟩ := hreach y hy
  have hyn : y < n := walkL_mem hV hxn hL y hy
  obtain ⟨k, w, hk, hw⟩ := shorten_any hV hyn ky wy hwy
  have hv := spread_walk hV hB hNU hC (d1, p1) h2 hw 1 hyN
  have e : n = (n - (1 + k)) + (1 + k) := by omega
  rw [e, Function.iterate_add_apply]
  have hvn : v < n := walk_lt hV hyn hw
  exact (inv2_rounds hV _ _ (inv2_rounds hV (1 + k) (d1, p1) h2).1).2 v hvn hv

/-- A chain only reads the parents of its vertices. -/
theorem chain_transfer {P P' : Array Int} {c : Int} {L : List Int} (h : Chain P c L)
    (hP : ∀ y ∈ L, Cpp.get P' y = Cpp.get P y) : Chain P' c L := by
  induction h with
  | stop => exact Chain.stop
  | step cur L hne _ ih =>
    refine Chain.step cur L hne ?_
    rw [hP cur (by simp)]
    exact ih (fun y hy => hP y (by simp [hy]))

/-! ## The result -/

/-- `ListGraph::bellman_ford(s)`: phase 1 (`n - 1` rounds) from the initial state, then phase 2 (`n` rounds). For
every vertex `v`: unreachable from `s` gives `U`; reachable from a negative cycle gives `NEG`; otherwise the
distance is the least cost of a walk from `s` (it is at most every walk cost and below `U`), and the parents lead
from `v` back to `s` along a walk with this cost. -/
theorem bf_correct {n s : Nat} {U C NEG : Int} {E : List Ed} (hV : Valid n C E) (hs : s < n) (hC : 0 ≤ C)
    (hU : (n : Int) * C < U) (hNU : NEG + C < U)
    (hNEG : NEG + C < -(((1 + (n - 1) * E.length : Nat) : Int) * C)) (v : Nat) (hv : v < n) :
    let F := (round2 U NEG E)^[n] ((round1 U E)^[n - 1] (st0 n s U))
    ((¬ ∃ w k, Walk E s v w k) → F.1[v]! = U) ∧
    (NegReach E s v → F.1[v]! = NEG) ∧
    ((∃ w k, Walk E s v w k) → ¬ NegReach E s v →
      F.1[v]! < U ∧ (∀ w k, Walk E s v w k → F.1[v]! ≤ w) ∧
      ∃ Cl, Chain F.2 v Cl ∧ WalkB E s Cl F.1[v]!) := by
  intro F
  set P1 := (round1 U E)^[n - 1] (st0 n s U) with hP1
  have hU0 : 0 < U := by have : (0 : Int) ≤ (n : Int) * C := by positivity
                         omega
  obtain ⟨T, τ, hI, hτ⟩ := inv1_rounds hV (n - 1) (st0 n s U) (inv1_init n s U E hs hU0)
  rw [← hP1] at hI
  have hτ' : τ ≤ 1 + (n - 1) * E.length := by omega
  have hmin : ∀ v, ¬ NegReach E s v → ∀ w k, Walk E s v w k → P1.1[v]! ≤ w :=
    fun v hn w k h => phase1_min hV hs hC hU hn h
  have hsound : ∀ x < n, P1.1[x]! ≠ U → ∃ k, Walk E s x P1.1[x]! k := by
    intro x hx h; obtain ⟨k, _, hk⟩ := hI.sound x hx h; exact ⟨k, hk⟩
  have h2 : Inv2 n NEG P1.1 P1.2 (P1.1, P1.2) := ⟨hI.dsz, hI.psz, fun x _ => Or.inl ⟨rfl, rfl⟩⟩
  have hkeep := keep_rounds (U := U) hV hsound hmin n (P1.1, P1.2) h2 (fun x _ _ => ⟨rfl, rfl⟩)
  have hB : ∀ x < n, P1.1[x]! = U ∨ NEG + C < P1.1[x]! := by
    intro x hx
    by_cases h : P1.1[x]! = U
    · exact Or.inl h
    · right
      obtain ⟨k, hk, hw⟩ := hI.sound x hx h
      have := (walk_cost hV hw).1
      have : (k : Int) * C ≤ ((1 + (n - 1) * E.length : Nat) : Int) * C :=
        Int.mul_le_mul_of_nonneg_right (by omega) hC
      omega
  have hF : F = (round2 U NEG E)^[n] (P1.1, P1.2) := rfl
  refine ⟨fun hnr => ?_, fun hneg => ?_, fun hr hneg => ?_⟩
  · have hneg : ¬ NegReach E s v := fun ⟨x, w, k, w', k', c, k'', h1, _, _, h3⟩ =>
      hnr ⟨_, _, walk_append h1 h3⟩
    rw [hF, (hkeep v hv hneg).1]
    by_contra h
    obtain ⟨k, hk⟩ := hsound v hv h
    exact hnr ⟨_, _, hk⟩
  · rw [hF]
    exact phase2_neg hV hs h2 (fun v w k h => phase1_reach hV hs hC hU h) hB hNU hC hneg
  · obtain ⟨w0, k0, hw0⟩ := hr
    have hlt := phase1_reach hV hs hC hU hw0
    rw [hF, (hkeep v hv hneg).1]
    refine ⟨hlt, fun w k h => hmin v hneg w k h, ?_⟩
    obtain ⟨Cl, hC', hW, hmem⟩ := chain_of_min hI hmin v hv hneg (ne_of_lt hlt)
    refine ⟨Cl, chain_transfer hC' (fun y hy => ?_), hW⟩
    obtain ⟨y', rfl, hy', hny⟩ := hmem y hy
    exact (hkeep y' hy' hny).2

end Proofs.ListBellmanFordMath
