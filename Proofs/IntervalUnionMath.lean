namespace Proofs.IntervalUnionMath

/-- Strict lexicographic order on pairs: the condition `b < a || (a == b && d < c)` of the sort for `x = (b, d)`, `y = (a, c)`. -/
def PLt (x y : Int × Int) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)
def PLe (x y : Int × Int) : Prop := ¬ PLt y x

instance (x y : Int × Int) : Decidable (PLt x y) := by unfold PLt; infer_instance

theorem PLe_trans {a b c : Int × Int} (h1 : PLe a b) (h2 : PLe b c) : PLe a c := by
  unfold PLe PLt at *; omega

theorem PLe_of_PLt {a b : Int × Int} (h : PLt a b) : PLe a b := by
  unfold PLe PLt at *; omega

theorem PLe_refl (a : Int × Int) : PLe a a := by unfold PLe PLt; omega

/-- A list sorted in the lexicographic order. -/
def Sorted (S : List (Int × Int)) : Prop := S.Pairwise PLe

theorem sorted_append_cons {A B : List (Int × Int)} {x : Int × Int} (hAB : Sorted (A ++ B)) (hxB : Sorted (x :: B))
    (hAx : ∀ a ∈ A, PLe a x) : Sorted (A ++ x :: B) := by
  unfold Sorted at *
  rw [List.pairwise_append] at hAB ⊢
  obtain ⟨hA, hB, hAB'⟩ := hAB
  refine ⟨hA, hxB, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hAx a ha
  · exact hAB' a ha b hb

theorem sorted_cons_cons {x y : Int × Int} {B : List (Int × Int)} (hxy : PLt x y) (hxB : Sorted (x :: B))
    (hyB : Sorted (y :: B)) : Sorted (x :: y :: B) := by
  unfold Sorted at *
  rw [List.pairwise_cons] at hxB ⊢
  refine ⟨?_, hyB⟩
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact PLe_of_PLt hxy
  · exact hxB.1 b hb

theorem sorted_tail_of_append {A B : List (Int × Int)} {y : Int × Int} (h : Sorted (A ++ y :: B)) : Sorted (y :: B) := by
  unfold Sorted at *
  rw [List.pairwise_append] at h
  exact h.2.1

/-- The sinking stops: `x` is not below the last element `y` of `A`. -/
theorem sink_stop {A' B : List (Int × Int)} {x y : Int × Int} (hAB : Sorted (A' ++ y :: B)) (hxB : Sorted (x :: B))
    (hstop : ¬ PLt x y) : Sorted (A' ++ y :: x :: B) := by
  have hyx : PLe y x := hstop
  have hyB := sorted_tail_of_append hAB
  unfold Sorted at *
  rw [List.pairwise_append] at hAB ⊢
  obtain ⟨hA, hyB', hAB'⟩ := hAB
  refine ⟨hA, ?_, ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨?_, hxB⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hyx
    · exact (List.pairwise_cons.mp hyB').1 b hb
  · intro a ha c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hAB' a ha c (by simp)
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact PLe_trans (hAB' a ha y (by simp)) hyx
      · exact hAB' a ha c (List.mem_cons_of_mem _ hc)

/-- The sinking reaches the front: `A` is empty. -/
theorem sink_front {B : List (Int × Int)} {x : Int × Int} (hxB : Sorted (x :: B)) : Sorted ([] ++ x :: B) := hxB

/-! ### The merge pass -/

/-- A point is covered by a list of closed intervals `(l, r)`. -/
def Cov (M : List (Int × Int)) (x : Int) : Prop := ∃ p ∈ M, p.1 ≤ x ∧ x ≤ p.2

/-- The result list is valid: every interval is non-empty and the intervals are separated by gaps. -/
def Good (M : List (Int × Int)) : Prop := (∀ p ∈ M, p.1 ≤ p.2) ∧ M.Pairwise (fun p q => p.2 < q.1)

/-- One iteration of the merge pass: the new interval `p` (with `p.1 ≥` every left end so far) is appended, extends the last
interval, or is absorbed. -/
def mstep (M : List (Int × Int)) (p : Int × Int) : List (Int × Int) :=
  match M.getLast? with
  | none => [p]
  | some q => if q.2 < p.1 then M ++ [p] else if q.2 < p.2 then M.dropLast ++ [(q.1, p.2)] else M

theorem Cov_append (M N : List (Int × Int)) (x : Int) : Cov (M ++ N) x ↔ Cov M x ∨ Cov N x := by
  unfold Cov
  constructor
  · rintro ⟨p, hp, h⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact Or.inl ⟨p, hp, h⟩
    · exact Or.inr ⟨p, hp, h⟩
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, List.mem_append_left _ hp, h⟩
    · exact ⟨p, List.mem_append_right _ hp, h⟩

theorem Cov_single (p : Int × Int) (x : Int) : Cov [p] x ↔ p.1 ≤ x ∧ x ≤ p.2 := by
  unfold Cov; simp

theorem Cov_snoc (M : List (Int × Int)) (q : Int × Int) (x : Int) :
    Cov (M ++ [q]) x ↔ Cov M x ∨ (q.1 ≤ x ∧ x ≤ q.2) := by
  rw [Cov_append, Cov_single]

theorem Cov_nil (x : Int) : ¬ Cov [] x := by unfold Cov; simp

/-- The invariant of the merge pass after processing the sorted pairs `D`: `M` is valid, covers exactly `D`, and every left end
of `M` is a left end of `D`. -/
structure MInv (M D : List (Int × Int)) : Prop where
  good : Good M
  cov : ∀ x, Cov M x ↔ Cov D x
  ends : ∀ q ∈ M, ∃ r ∈ D, q.1 = r.1

theorem mstep_nil (p : Int × Int) (hp : p.1 ≤ p.2) : MInv (mstep [] p) [p] := by
  unfold mstep
  simp only [List.getLast?_nil]
  refine ⟨⟨?_, ?_⟩, fun x => Iff.rfl, ?_⟩
  · intro q hq; simp at hq; subst hq; exact hp
  · simp
  · intro q hq; simp at hq; exact ⟨q, by simp [hq], rfl⟩

theorem mstep_inv (M0 : List (Int × Int)) (q : Int × Int) (D : List (Int × Int)) (p : Int × Int)
    (hinv : MInv (M0 ++ [q]) D) (hmax : ∀ r ∈ D, r.1 ≤ p.1) (hp : p.1 ≤ p.2) :
    MInv (mstep (M0 ++ [q]) p) (D ++ [p]) := by
  obtain ⟨⟨hv, hg⟩, hcov, hend⟩ := hinv
  have hqv : q.1 ≤ q.2 := hv q (by simp)
  have hq1 : q.1 ≤ p.1 := by
    obtain ⟨r, hr, hr1⟩ := hend q (by simp)
    rw [hr1]; exact hmax r hr
  have hg' := List.pairwise_append.mp hg
  have hgap0 : ∀ r ∈ M0, r.2 < q.1 := fun r hr => hg'.2.2 r hr q (by simp)
  unfold mstep
  rw [List.getLast?_concat]
  by_cases h1 : q.2 < p.1
  · simp only [h1, if_true]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hv r hr
      · simp at hr; subst hr; exact hp
    · rw [List.pairwise_append]
      refine ⟨hg, by simp, ?_⟩
      intro r hr c hc
      simp at hc; subst hc
      rcases List.mem_append.mp hr with hr | hr
      · have := hgap0 r hr; omega
      · simp at hr; subst hr; exact h1
    · intro x
      rw [Cov_snoc, hcov, Cov_snoc]
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨t, ht, ht1⟩ := hend r hr
        exact ⟨t, List.mem_append_left _ ht, ht1⟩
      · simp at hr; exact ⟨p, by simp, by rw [hr]⟩
  · simp only [h1, ite_false]
    by_cases h2 : q.2 < p.2
    · simp only [h2, if_true]
      rw [List.dropLast_concat]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hv r (List.mem_append_left _ hr)
        · simp at hr; subst hr; simp; omega
      · rw [List.pairwise_append]
        refine ⟨hg'.1, by simp, ?_⟩
        intro r hr c hc
        simp at hc; subst hc
        exact hgap0 r hr
      · intro x
        have hc := hcov x
        rw [Cov_snoc] at hc
        rw [Cov_snoc, Cov_snoc, ← hc]
        by_cases hM0 : Cov M0 x
        · simp [hM0]
        · simp only [hM0, false_or]
          omega
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · obtain ⟨t, ht, ht1⟩ := hend r (List.mem_append_left _ hr)
          exact ⟨t, List.mem_append_left _ ht, ht1⟩
        · simp at hr; subst hr
          obtain ⟨t, ht, ht1⟩ := hend q (by simp)
          exact ⟨t, List.mem_append_left _ ht, ht1⟩
    · simp only [h2, ite_false]
      refine ⟨⟨hv, hg⟩, ?_, ?_⟩
      · intro x
        rw [Cov_snoc D p x, ← hcov x, Cov_snoc]
        by_cases hM0 : Cov M0 x
        · simp [hM0]
        · simp only [hM0, false_or]
          omega
      · intro r hr
        obtain ⟨t, ht, ht1⟩ := hend r hr
        exact ⟨t, List.mem_append_left _ ht, ht1⟩

theorem mfold_inv_aux : ∀ (k : Nat) (S : List (Int × Int)), S.length = k → Sorted S → (∀ p ∈ S, p.1 ≤ p.2) →
    MInv (S.foldl mstep []) S := by
  intro k
  induction k with
  | zero =>
    intro S hl _ _
    have : S = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    exact ⟨⟨by simp, by simp⟩, fun x => Iff.rfl, by simp⟩
  | succ k ih =>
    intro S hl hs hv
    rcases List.eq_nil_or_concat S with h | ⟨D, p, h⟩
    · subst h; simp at hl
    rw [List.concat_eq_append] at h
    subst h
    have hlD : D.length = k := by simp at hl; omega
    have hsD : Sorted D := by
      unfold Sorted at *
      exact (List.pairwise_append.mp hs).1
    have hvD : ∀ q ∈ D, q.1 ≤ q.2 := fun q hq => hv q (List.mem_append_left _ hq)
    have hp : p.1 ≤ p.2 := hv p (by simp)
    have hmax : ∀ r ∈ D, r.1 ≤ p.1 := by
      intro r hr
      have := (List.pairwise_append.mp hs).2.2 r hr p (by simp)
      unfold PLe PLt at this
      omega
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have hI := ih D hlD hsD hvD
    cases D with
    | nil => simpa [mstep] using mstep_nil p hp
    | cons d D' =>
      obtain ⟨M0, q, hM⟩ : ∃ M0 q, (d :: D').foldl mstep [] = M0 ++ [q] := by
        rcases List.eq_nil_or_concat ((d :: D').foldl mstep []) with h | ⟨M0, q, h⟩
        · exfalso
          have := (hI.cov d.1).mpr ⟨d, by simp, Int.le_refl _, hvD d (by simp)⟩
          rw [h] at this
          exact Cov_nil _ this
        · exact ⟨M0, q, by rw [h, List.concat_eq_append]⟩
      rw [hM] at hI ⊢
      exact mstep_inv M0 q (d :: D') p hI hmax hp

theorem mfold_inv (S : List (Int × Int)) (hs : Sorted S) (hv : ∀ p ∈ S, p.1 ≤ p.2) :
    MInv (S.foldl mstep []) S := mfold_inv_aux S.length S rfl hs hv

end Proofs.IntervalUnionMath
