namespace Proofs.PrimRelax

abbrev Edge := Nat × Nat × Int

/-- Relax one arc: `if (done[w] == 0 && c < dist[w]) dist[w] = c` for the arc `(_, w, c)`. -/
def relaxL (Dn : List Nat) (Dd : List Int) (e : Edge) : List Int :=
  if Dn.getD e.2.1 0 = 0 ∧ e.2.2 < Dd.getD e.2.1 0 then Dd.set e.2.1 e.2.2 else Dd

theorem relaxL_length (Dn : List Nat) (Dd : List Int) (e : Edge) : (relaxL Dn Dd e).length = Dd.length := by
  unfold relaxL
  split <;> simp

theorem getD_set_same (Dd : List Int) (i : Nat) (a : Int) (h : i < Dd.length) : (Dd.set i a).getD i 0 = a := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_ne (Dd : List Int) (i x : Nat) (a : Int) (h : x ≠ i) : (Dd.set i a).getD x 0 = Dd.getD x 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne, Ne.symm h]

theorem getD_set_oob (Dd : List Int) (i : Nat) (a : Int) (h : ¬ i < Dd.length) : (Dd.set i a).getD i 0 = Dd.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem relaxL_getD (Dn : List Nat) (Dd : List Int) (e : Edge) (x : Nat) :
    (relaxL Dn Dd e).getD x 0 =
      if Dn.getD e.2.1 0 = 0 ∧ e.2.2 < Dd.getD e.2.1 0 ∧ x = e.2.1 ∧ x < Dd.length then e.2.2 else Dd.getD x 0 := by
  unfold relaxL
  by_cases h : Dn.getD e.2.1 0 = 0 ∧ e.2.2 < Dd.getD e.2.1 0
  · rw [if_pos h]
    by_cases hxe : x = e.2.1
    · by_cases hl : x < Dd.length
      · rw [if_pos ⟨h.1, h.2, hxe, hl⟩, hxe, getD_set_same _ _ _ (hxe ▸ hl)]
      · rw [if_neg (fun hh => hl hh.2.2.2), hxe, getD_set_oob _ _ _ (hxe ▸ hl)]
    · rw [if_neg (fun hh => hxe hh.2.2.1), getD_set_ne _ _ _ _ hxe]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.1, hh.2.1⟩)]

theorem foldl_length (Dn : List Nat) (L : List Edge) : ∀ Dd : List Int, (L.foldl (relaxL Dn) Dd).length = Dd.length := by
  induction L with
  | nil => intro Dd; rfl
  | cons e L ih => intro Dd; simp only [List.foldl_cons]; rw [ih, relaxL_length]

theorem relaxL_le (Dn : List Nat) (Dd : List Int) (e : Edge) (x : Nat) : (relaxL Dn Dd e).getD x 0 ≤ Dd.getD x 0 := by
  rw [relaxL_getD]
  by_cases h : Dn.getD e.2.1 0 = 0 ∧ e.2.2 < Dd.getD e.2.1 0 ∧ x = e.2.1 ∧ x < Dd.length
  · rw [if_pos h]; obtain ⟨_, h2, h3, _⟩ := h; subst h3; omega
  · rw [if_neg h]; exact Int.le_refl _

theorem foldl_le (Dn : List Nat) (L : List Edge) (x : Nat) : ∀ Dd : List Int, (L.foldl (relaxL Dn) Dd).getD x 0 ≤ Dd.getD x 0 := by
  induction L with
  | nil => intro Dd; exact Int.le_refl _
  | cons e L ih =>
    intro Dd
    simp only [List.foldl_cons]
    have h1 := ih (relaxL Dn Dd e)
    have h2 := relaxL_le Dn Dd e x
    omega

theorem foldl_done (Dn : List Nat) (L : List Edge) (x : Nat) (hx : Dn.getD x 0 ≠ 0) :
    ∀ Dd : List Int, (L.foldl (relaxL Dn) Dd).getD x 0 = Dd.getD x 0 := by
  induction L with
  | nil => intro Dd; rfl
  | cons e L ih =>
    intro Dd
    simp only [List.foldl_cons]
    rw [ih]
    rw [relaxL_getD]
    have : ¬ (Dn.getD e.2.1 0 = 0 ∧ e.2.2 < Dd.getD e.2.1 0 ∧ x = e.2.1 ∧ x < Dd.length) := by
      intro ⟨h1, _, h3, _⟩
      subst h3
      exact hx h1
    rw [if_neg this]

theorem foldl_cases (Dn : List Nat) (L : List Edge) (x : Nat) :
    ∀ Dd : List Int, x < Dd.length → (L.foldl (relaxL Dn) Dd).getD x 0 = Dd.getD x 0 ∨
      ∃ e ∈ L, e.2.1 = x ∧ Dn.getD x 0 = 0 ∧ (L.foldl (relaxL Dn) Dd).getD x 0 = e.2.2 := by
  induction L with
  | nil => intro Dd _; exact Or.inl rfl
  | cons e L ih =>
    intro Dd hx
    simp only [List.foldl_cons]
    have hl : x < (relaxL Dn Dd e).length := by rw [relaxL_length]; exact hx
    rcases ih (relaxL Dn Dd e) hl with h | ⟨e', he', h1, h2, h3⟩
    · rw [h, relaxL_getD]
      by_cases hc : Dn.getD e.2.1 0 = 0 ∧ e.2.2 < Dd.getD e.2.1 0 ∧ x = e.2.1 ∧ x < Dd.length
      · rw [if_pos hc]
        right
        exact ⟨e, List.mem_cons_self .., hc.2.2.1.symm, by rw [hc.2.2.1]; exact hc.1, rfl⟩
      · rw [if_neg hc]; left; rfl
    · right
      exact ⟨e', List.mem_cons_of_mem _ he', h1, h2, h3⟩

theorem foldl_cover (Dn : List Nat) (L : List Edge) :
    ∀ Dd : List Int, ∀ e ∈ L, e.2.1 < Dd.length → Dn.getD e.2.1 0 = 0 → (L.foldl (relaxL Dn) Dd).getD e.2.1 0 ≤ e.2.2 := by
  induction L with
  | nil => intro Dd e he; simp at he
  | cons e0 L ih =>
    intro Dd e he hlt hdn
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp he with rfl | he'
    · -- the arc `e` is relaxed first and later steps only decrease
      have h1 := foldl_le Dn L e.2.1 (relaxL Dn Dd e)
      have h2 : (relaxL Dn Dd e).getD e.2.1 0 ≤ e.2.2 := by
        rw [relaxL_getD]
        by_cases hc : Dn.getD e.2.1 0 = 0 ∧ e.2.2 < Dd.getD e.2.1 0 ∧ e.2.1 = e.2.1 ∧ e.2.1 < Dd.length
        · rw [if_pos hc]; exact Int.le_refl _
        · rw [if_neg hc]
          have : ¬ e.2.2 < Dd.getD e.2.1 0 := fun hh => hc ⟨hdn, hh, rfl, hlt⟩
          omega
      omega
    · exact ih (relaxL Dn Dd e0) e he' (by rw [relaxL_length]; exact hlt) hdn

end Proofs.PrimRelax
