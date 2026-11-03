namespace Proofs.BellmanFordMath

/-- An edge `(u, v, c)`: from `u` to `v` with cost `c`. -/
abbrev Edge := Nat × Nat × Int

/-- `d` with the entry `i` replaced by `x`. -/
def upd (d : Nat → Int) (i : Nat) (x : Int) : Nat → Int := fun j => if j = i then x else d j

/-- Relaxing one edge: `inf` marks a distance that is not known yet. -/
def relax (inf : Int) (d : Nat → Int) (e : Edge) : Nat → Int :=
  if d e.1 ≠ inf ∧ d e.1 + e.2.2 < d e.2.1 then upd d e.2.1 (d e.1 + e.2.2) else d

/-- One pass over the edges in order. -/
def pass (inf : Int) (E : List Edge) (d : Nat → Int) : Nat → Int := E.foldl (relax inf) d

/-- `r` passes. -/
def rounds (inf : Int) (E : List Edge) : Nat → (Nat → Int) → (Nat → Int)
  | 0, d => d
  | r + 1, d => rounds inf E r (pass inf E d)

/-- A walk from `a` to `b` of total cost `c` with `k` edges. -/
inductive Walk (E : List Edge) : Nat → Nat → Int → Nat → Prop
  | nil (a : Nat) : Walk E a a 0 0
  | step {a : Nat} {c : Int} {k : Nat} (e : Edge) : e ∈ E → Walk E a e.1 c k → Walk E a e.2.1 (c + e.2.2) (k + 1)


theorem upd_same (d : Nat → Int) (i : Nat) (x : Int) : upd d i x i = x := by simp [upd]
theorem upd_ne (d : Nat → Int) (i j : Nat) (x : Int) (h : j ≠ i) : upd d i x j = d j := by simp [upd, h]

theorem relax_le (inf : Int) (d : Nat → Int) (e : Edge) (j : Nat) : relax inf d e j ≤ d j := by
  unfold relax
  by_cases h : d e.1 ≠ inf ∧ d e.1 + e.2.2 < d e.2.1
  · rw [if_pos h]
    by_cases hj : j = e.2.1
    · subst hj; rw [upd_same]; exact Int.le_of_lt h.2
    · rw [upd_ne _ _ _ _ hj]; exact Int.le_refl _
  · rw [if_neg h]; exact Int.le_refl _

theorem foldl_le (inf : Int) : ∀ (es : List Edge) (d : Nat → Int) (j : Nat), es.foldl (relax inf) d j ≤ d j
  | [], d, j => Int.le_refl _
  | e :: t, d, j => by
    simp only [List.foldl_cons]
    exact Int.le_trans (foldl_le inf t (relax inf d e) j) (relax_le inf d e j)

theorem relax_ne (inf : Int) (d : Nat → Int) (e : Edge) (j : Nat) (h : j ≠ e.2.1) : relax inf d e j = d j := by
  unfold relax
  split
  · exact upd_ne _ _ _ _ h
  · rfl

/-- Soundness: every known distance is the cost of a walk from a source that was known at the start. -/
def Sound (inf : Int) (E : List Edge) (d0 d : Nat → Int) : Prop :=
  ∀ v, d v ≠ inf → ∃ w c k, d0 w ≠ inf ∧ Walk E w v c k ∧ d v = d0 w + c

theorem sound_relax (inf : Int) (E : List Edge) (d0 d : Nat → Int) (e : Edge) (he : e ∈ E) (h : Sound inf E d0 d) :
    Sound inf E d0 (relax inf d e) := by
  intro v hv
  by_cases hf : d e.1 ≠ inf ∧ d e.1 + e.2.2 < d e.2.1
  · have hr : relax inf d e = upd d e.2.1 (d e.1 + e.2.2) := by unfold relax; rw [if_pos hf]
    rw [hr] at hv ⊢
    by_cases hj : v = e.2.1
    · subst hj
      rw [upd_same]
      obtain ⟨w, c, k, h0, wk, hd⟩ := h e.1 hf.1
      exact ⟨w, c + e.2.2, k + 1, h0, Walk.step e he wk, by rw [hd]; omega⟩
    · rw [upd_ne _ _ _ _ hj] at hv ⊢
      exact h v hv
  · have hr : relax inf d e = d := by unfold relax; rw [if_neg hf]
    rw [hr] at hv ⊢
    exact h v hv

theorem sound_foldl (inf : Int) (E : List Edge) (d0 : Nat → Int) :
    ∀ (es : List Edge) (d : Nat → Int), (∀ e ∈ es, e ∈ E) → Sound inf E d0 d → Sound inf E d0 (es.foldl (relax inf) d)
  | [], d, _, h => h
  | e :: t, d, hs, h => by
    simp only [List.foldl_cons]
    exact sound_foldl inf E d0 t _ (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      (sound_relax inf E d0 d e (hs e (List.mem_cons_self ..)) h)

theorem sound_rounds (inf : Int) (E : List Edge) (d0 : Nat → Int) :
    ∀ (r : Nat) (d : Nat → Int), Sound inf E d0 d → Sound inf E d0 (rounds inf E r d)
  | 0, d, h => h
  | r + 1, d, h => sound_rounds inf E d0 r _ (sound_foldl inf E d0 E d (fun e he => he) h)

theorem sound_init (inf : Int) (E : List Edge) (d0 : Nat → Int) : Sound inf E d0 d0 :=
  fun v hv => ⟨v, 0, 0, hv, Walk.nil v, by omega⟩


theorem relax_edge (inf : Int) (d : Nat → Int) (e : Edge) (h : d e.1 < inf) :
    relax inf d e e.2.1 ≤ d e.1 + e.2.2 := by
  unfold relax
  by_cases hf : d e.1 ≠ inf ∧ d e.1 + e.2.2 < d e.2.1
  · rw [if_pos hf, upd_same]; exact Int.le_refl _
  · rw [if_neg hf]
    have : ¬ (d e.1 + e.2.2 < d e.2.1) := fun hh => hf ⟨by omega, hh⟩
    omega

theorem pass_edge (inf : Int) (E : List Edge) (d : Nat → Int) (e : Edge) (he : e ∈ E) (h : d e.1 < inf) :
    pass inf E d e.2.1 ≤ d e.1 + e.2.2 := by
  obtain ⟨A, B, hAB⟩ := List.append_of_mem he
  unfold pass
  rw [hAB, List.foldl_append, List.foldl_cons]
  have h1 : E.foldl (relax inf) d e.2.1 = _ := rfl
  have hA : A.foldl (relax inf) d e.1 ≤ d e.1 := foldl_le inf A d e.1
  have hE := relax_edge inf (A.foldl (relax inf) d) e (by omega)
  have hB := foldl_le inf B (relax inf (A.foldl (relax inf) d) e) e.2.1
  omega

/-- Completeness: after `r` passes every walk of at most `r` edges bounds the distance. -/
def Comp (inf : Int) (E : List Edge) (d0 : Nat → Int) (r : Nat) (d : Nat → Int) : Prop :=
  ∀ w v c k, k ≤ r → d0 w < inf → Walk E w v c k → d v ≤ d0 w + c

theorem comp_zero (inf : Int) (E : List Edge) (d0 : Nat → Int) : Comp inf E d0 0 d0 := by
  intro w v c k hk h0 wk
  cases wk with
  | nil => omega
  | step e he wk' => omega

theorem comp_pass (inf : Int) (E : List Edge) (d0 : Nat → Int) (R r : Nat) (hr : r + 1 ≤ R)
    (hS : ∀ w v c k, k ≤ R → Walk E w v c k → d0 w < inf → d0 w + c < inf)
    (d : Nat → Int) (h : Comp inf E d0 r d) : Comp inf E d0 (r + 1) (pass inf E d) := by
  intro w v c k hk h0 wk
  cases wk with
  | nil =>
    have := h w w 0 0 (by omega) h0 (Walk.nil w)
    have h2 : pass inf E d w ≤ d w := foldl_le inf E d w
    omega
  | @step c0 k0 e he wk' =>
    have hu := h w e.1 c0 k0 (by omega) h0 wk'
    have hlt := hS w e.1 c0 k0 (by omega) wk' h0
    have := pass_edge inf E d e he (by omega)
    omega

theorem comp_rounds (inf : Int) (E : List Edge) (d0 : Nat → Int) (R : Nat)
    (hS : ∀ w v c k, k ≤ R → Walk E w v c k → d0 w < inf → d0 w + c < inf) :
    ∀ (r : Nat), r ≤ R → Comp inf E d0 r (rounds inf E r d0) := by
  have key : ∀ (r : Nat) (d : Nat → Int) (s : Nat), s + r ≤ R → Comp inf E d0 s d →
      Comp inf E d0 (s + r) (rounds inf E r d) := by
    intro r
    induction r with
    | zero => intro d s _ h; simpa [rounds] using h
    | succ r ih =>
      intro d s hsr h
      have := ih (pass inf E d) (s + 1) (by omega) (comp_pass inf E d0 R s (by omega) hS d h)
      rw [show s + (r + 1) = s + 1 + r by omega]
      exact this
  intro r hr
  have := key r d0 0 (by omega) (comp_zero inf E d0)
  simpa using this


/-- Overflow bounds: every relaxation lowers the smallest entry by at most `C`. -/
theorem relax_lower (inf C lo : Int) (d : Nat → Int) (e : Edge) (hc : -C ≤ e.2.2) (hC : 0 ≤ C) (hd : ∀ j, lo ≤ d j) :
    ∀ j, lo - C ≤ relax inf d e j := by
  intro j
  unfold relax
  by_cases hf : d e.1 ≠ inf ∧ d e.1 + e.2.2 < d e.2.1
  · rw [if_pos hf]
    by_cases hj : j = e.2.1
    · subst hj; rw [upd_same]; have := hd e.1; omega
    · rw [upd_ne _ _ _ _ hj]; have := hd j; omega
  · rw [if_neg hf]; have := hd j; omega

theorem foldl_lower (inf C : Int) (hC : 0 ≤ C) : ∀ (es : List Edge) (d : Nat → Int) (lo : Int),
    (∀ e ∈ es, -C ≤ e.2.2) → (∀ j, lo ≤ d j) → ∀ j, lo - (es.length : Int) * C ≤ es.foldl (relax inf) d j
  | [], d, lo, _, hd, j => by simpa using hd j
  | e :: t, d, lo, hc, hd, j => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := relax_lower inf C lo d e (hc e (List.mem_cons_self ..)) hC hd
    have h2 := foldl_lower inf C hC t (relax inf d e) (lo - C) (fun x hx => hc x (List.mem_cons_of_mem _ hx)) h1 j
    rw [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
    omega

end Proofs.BellmanFordMath
