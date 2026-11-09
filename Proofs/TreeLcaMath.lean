import Proofs.TreeAncestorMath

namespace Proofs.TreeLcaMath
open Proofs.TreeAncestorMath (tab itr itr_add)

/-- The table is correct for the first levels `0 .. K`. -/
def TabAll (T : List (List Nat)) (f : Nat → Nat) (N K : Nat) : Prop :=
  ∀ k, k ≤ K → ∀ x, x < N → tab T k x = itr f (2 ^ k) x ∧ tab T k x < N ∧ x < (T.getD k []).length

/-- `f` is the parent map of a tree on `[0, N)` rooted at `root`, with depths `d`. -/
structure TreeF (f : Nat → Nat) (N root : Nat) (d : Nat → Nat) : Prop where
  rootN : root < N
  fN : ∀ x, x < N → f x < N
  fr : f root = root
  d0 : d root = 0
  step : ∀ x, x < N → x ≠ root → d (f x) + 1 = d x

theorem itr_lt (f : Nat → Nat) (N : Nat) (hf : ∀ x, x < N → f x < N) : ∀ t x, x < N → itr f t x < N := by
  intro t
  induction t with
  | zero => intro x hx; exact hx
  | succ t ih => intro x hx; exact ih (f x) (hf x hx)

theorem itr_succ (f : Nat → Nat) (t x : Nat) : itr f (t + 1) x = itr f t (f x) := rfl

theorem itr_dep {f : Nat → Nat} {N root : Nat} {d : Nat → Nat} (T : TreeF f N root d) :
    ∀ t x, x < N → t ≤ d x → d (itr f t x) + t = d x := by
  intro t
  induction t with
  | zero => intro x _ _; rfl
  | succ t ih =>
    intro x hx ht
    have hne : x ≠ root := by
      intro h; subst h; rw [T.d0] at ht; omega
    have h1 := T.step x hx hne
    have h2 := ih (f x) (T.fN x hx) (by omega)
    rw [itr_succ]
    omega

theorem dep_zero {f : Nat → Nat} {N root : Nat} {d : Nat → Nat} (T : TreeF f N root d) (y : Nat) (hy : y < N)
    (h0 : d y = 0) : y = root := by
  by_cases h : y = root
  · exact h
  · have := T.step y hy h
    omega

theorem itr_root {f : Nat → Nat} {N root : Nat} {d : Nat → Nat} (T : TreeF f N root d) (x : Nat) (hx : x < N) :
    itr f (d x) x = root := by
  have h := itr_dep T (d x) x hx (Nat.le_refl _)
  have hlt := itr_lt f N T.fN (d x) x hx
  exact dep_zero T _ hlt (by omega)

theorem itr_mono (f : Nat → Nat) (s t u v : Nat) (h : itr f s u = itr f s v) : itr f (s + t) u = itr f (s + t) v := by
  rw [Nat.add_comm s t, itr_add, itr_add, h]

/-- The first time two trajectories meet. -/
theorem first_meet (f : Nat → Nat) (u v : Nat) (P : ∃ t, itr f t u = itr f t v) :
    ∃ m, itr f m u = itr f m v ∧ ∀ s, s < m → itr f s u ≠ itr f s v := by
  obtain ⟨t, ht⟩ := P
  induction t using Nat.strongRecOn with
  | _ t ih =>
    by_cases h : ∃ s, s < t ∧ itr f s u = itr f s v
    · obtain ⟨s, hs, hs2⟩ := h
      exact ih s hs hs2
    · refine ⟨t, ht, ?_⟩
      intro s hs hs2
      exact h ⟨s, hs, hs2⟩

/-- The descent over the levels `c - 1, ..., 0`. -/
def descA (T : List (List Nat)) : Nat → Nat → Nat → Nat × Nat
  | 0, u, v => (u, v)
  | c + 1, u, v => if tab T c u ≠ tab T c v then descA T c (tab T c u) (tab T c v) else descA T c u v

theorem descA_zero (T : List (List Nat)) (u v : Nat) : descA T 0 u v = (u, v) := by
  unfold descA; rfl

theorem descA_succ (T : List (List Nat)) (c u v : Nat) :
    descA T (c + 1) u v = if tab T c u ≠ tab T c v then descA T c (tab T c u) (tab T c v) else descA T c u v := by
  rw [descA]

/-- The invariant of the descent: `u = f^a u0`, `v = f^a v0`, the trajectories have not met before `m`, and the remaining
distance `m - 1 - a` is below `2^c`. -/
theorem descA_spec (T : List (List Nat)) (f : Nat → Nat) (N : Nat) (hf : ∀ x, x < N → f x < N) (u0 v0 m : Nat)
    (hm : itr f m u0 = itr f m v0) (hmin : ∀ s, s < m → itr f s u0 ≠ itr f s v0) :
    ∀ c a, TabAll T f N (c - 1) → u0 < N → v0 < N → a < m → m - 1 - a < 2 ^ c →
      descA T c (itr f a u0) (itr f a v0) = (itr f (m - 1) u0, itr f (m - 1) v0) := by
  intro c
  induction c with
  | zero =>
    intro a _ _ _ ham hr
    have : m - 1 - a = 0 := by simpa using hr
    have ha : a = m - 1 := by omega
    rw [descA_zero, ha]
  | succ c ih =>
    intro a hT hu hv ham hr
    have hTc : ∀ x, x < N → tab T c x = itr f (2 ^ c) x ∧ tab T c x < N ∧ x < (T.getD c []).length :=
      fun x hx => hT c (by omega) x hx
    have hua := itr_lt f N hf a u0 hu
    have hva := itr_lt f N hf a v0 hv
    have e1 := (hTc _ hua).1
    have e2 := (hTc _ hva).1
    rw [descA_succ]
    have hpow : 2 ^ (c + 1) = 2 * 2 ^ c := by rw [Nat.pow_succ]; omega
    by_cases hr2 : 2 ^ c ≤ m - 1 - a
    · -- the trajectories do not meet after `2^c` more steps
      have hne : tab T c (itr f a u0) ≠ tab T c (itr f a v0) := by
        rw [e1, e2, ← itr_add, ← itr_add]
        exact hmin _ (by omega)
      rw [ite_eq_left hne]
      have n1 : tab T c (itr f a u0) = itr f (a + 2 ^ c) u0 := by rw [e1, ← itr_add, Nat.add_comm]
      have n2 : tab T c (itr f a v0) = itr f (a + 2 ^ c) v0 := by rw [e2, ← itr_add, Nat.add_comm]
      rw [n1, n2]
      exact ih (a + 2 ^ c) (fun k hk x hx => hT k (by omega) x hx) hu hv (by omega) (by omega)
    · have heq : tab T c (itr f a u0) = tab T c (itr f a v0) := by
        rw [e1, e2, ← itr_add, ← itr_add]
        have := itr_mono f m (a + 2 ^ c - m) u0 v0 hm
        have e : m + (a + 2 ^ c - m) = 2 ^ c + a := by omega
        rw [e] at this
        exact this
      rw [ite_eq_right (fun h => h heq)]
      exact ih a (fun k hk x hx => hT k (by omega) x hx) hu hv ham (by omega)

theorem descA_lt (T : List (List Nat)) (f : Nat → Nat) (N : Nat) :
    ∀ c u v, TabAll T f N (c - 1) → u < N → v < N → (descA T c u v).1 < N ∧ (descA T c u v).2 < N := by
  intro c
  induction c with
  | zero => intro u v _ hu hv; rw [descA_zero]; exact ⟨hu, hv⟩
  | succ c ih =>
    intro u v hT hu hv
    rw [descA_succ]
    have h1 := (hT c (by omega) u hu).2.1
    have h2 := (hT c (by omega) v hv).2.1
    by_cases h : tab T c u ≠ tab T c v
    · rw [ite_eq_left h]
      exact ih _ _ (fun k hk x hx => hT k (by omega) x hx) h1 h2
    · rw [ite_eq_right h]
      exact ih _ _ (fun k hk x hx => hT k (by omega) x hx) hu hv

/-- `tree_lca_same_depth`: for vertices of the same depth `d`, the result is the first common vertex `f^m u = f^m v`. -/
theorem lca_spec (T : List (List Nat)) (f : Nat → Nat) (N root : Nat) (d : Nat → Nat) (TF : TreeF f N root d)
    (u v top : Nat) (hu : u < N) (hv : v < N) (hd : d u = d v) (htop : d u < 2 ^ (top + 1)) (H : TabAll T f N top)
    (hne : u ≠ v) :
    ∃ m, itr f m u = itr f m v ∧ (∀ s, s < m → itr f s u ≠ itr f s v) ∧
      tab T 0 (descA T (top + 1) u v).1 = itr f m u := by
  obtain ⟨m, hm, hmin⟩ := first_meet f u v ⟨d u, by rw [itr_root TF u hu]; rw [hd]; exact (itr_root TF v hv).symm⟩
  have hm0 : m ≠ 0 := by
    intro h; subst h; exact hne hm
  have hmd : m ≤ d u := by
    refine Classical.byContradiction (fun hgt => ?_)
    have := hmin (d u) (by omega)
    exact this (by rw [itr_root TF u hu, hd, itr_root TF v hv])
  refine ⟨m, hm, hmin, ?_⟩
  have := descA_spec T f N TF.fN u v m hm hmin (top + 1) 0 (by simpa using H) hu hv (by omega) (by omega)
  simp only [itr] at this
  rw [this]
  simp only
  have hmm : m = (m - 1) + 1 := by omega
  have h0 := (H 0 (by omega) (itr f (m - 1) u) (itr_lt f N TF.fN _ u hu)).1
  rw [h0]
  rw [hmm]
  show itr f (2 ^ 0) (itr f (m - 1) u) = itr f (m - 1 + 1) u
  rw [← itr_add]
  congr 1
  omega

/-- The original Tree member now starts at the last existing row. All levels are
visited exactly once, in descending order; the first-meeting specification is
unchanged even when the table has more rows than the current depth needs. -/
theorem lca_all_rows_spec (T : List (List Nat)) (f : Nat → Nat) (N root : Nat)
    (d : Nat → Nat) (TF : TreeF f N root d) (u v : Nat)
    (hu : u < N) (hv : v < N) (hd : d u = d v)
    (nonempty : 0 < T.length) (enough : d u < 2 ^ T.length)
    (H : TabAll T f N (T.length - 1)) (different : u ≠ v) :
    ∃ m, itr f m u = itr f m v ∧ (∀ s, s < m → itr f s u ≠ itr f s v) ∧
      tab T 0 (descA T T.length u v).1 = itr f m u := by
  have rows : T.length - 1 + 1 = T.length := by omega
  simpa only [rows] using lca_spec T f N root d TF u v (T.length - 1)
    hu hv hd (by simpa only [rows] using enough) H different

/-- The signed C++ loop starts at row_count-1 and stops after row 0. -/
theorem all_rows_indices (T : List (List Nat)) (k : Nat) :
    k ∈ (List.range T.length).reverse ↔ k < T.length := by simp

/-- Same-depth part of the original member, including its equal-vertex return. -/
def allRowsLca (T : List (List Nat)) (u v : Nat) : Nat :=
  if u = v then u else tab T 0 (descA T T.length u v).1

theorem all_rows_lca_correct (T : List (List Nat)) (f : Nat → Nat) (N root : Nat)
    (d : Nat → Nat) (TF : TreeF f N root d) (u v : Nat)
    (hu : u < N) (hv : v < N) (hd : d u = d v)
    (nonempty : 0 < T.length) (enough : d u < 2 ^ T.length)
    (H : TabAll T f N (T.length - 1)) :
    allRowsLca T u v < N ∧
      ∃ m, itr f m u = allRowsLca T u v ∧ itr f m v = allRowsLca T u v ∧
        ∀ s, s < m → itr f s u ≠ itr f s v := by
  by_cases equal : u = v
  · subst v
    simp only [allRowsLca,ite_true]
    exact ⟨hu,0,rfl,rfl,by intro s hs; omega⟩
  · obtain ⟨m,meet,minimal,result⟩ := lca_all_rows_spec T f N root d TF u v hu hv hd nonempty enough H equal
    have value : allRowsLca T u v = itr f m u := by simp only [allRowsLca,ite_eq_right equal]; exact result
    rw [value]
    exact ⟨itr_lt f N TF.fN m u hu,m,rfl,meet.symm,minimal⟩

end Proofs.TreeLcaMath
