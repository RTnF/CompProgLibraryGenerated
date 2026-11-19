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

end Proofs.BellmanFordMath
