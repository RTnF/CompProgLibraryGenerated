namespace Proofs.RunLengthMath

/-- Appending one element to a run-length encoding. -/
def rleAdd (acc : List (Int × Nat)) (x : Int) : List (Int × Nat) :=
  match acc.getLast? with
  | some (a, c) => if a = x then acc.dropLast ++ [(a, c + 1)] else acc ++ [(x, 1)]
  | none => [(x, 1)]

/-- The maximal runs of equal values of `l`, as pairs (value, length). -/
def rle (l : List Int) : List (Int × Nat) := l.foldl rleAdd []

/-- The encoding of the first `t` elements, where the empty prefix is represented as the pending run `(v[0], 0)`. -/
def rleExt (v : List Int) (t : Nat) : List (Int × Nat) := if t = 0 then [(v.getD 0 0, 0)] else rle (v.take t)

theorem rleAdd_length (acc : List (Int × Nat)) (x : Int) : (rleAdd acc x).length ≤ acc.length + 1 := by
  unfold rleAdd
  cases h : acc.getLast? with
  | none => simp
  | some p =>
    obtain ⟨a, c⟩ := p
    by_cases e : a = x
    · simp [e]
    · simp [e]

theorem rle_length_le_aux (l : List Int) : ∀ (acc : List (Int × Nat)), (l.foldl rleAdd acc).length ≤ acc.length + l.length := by
  induction l with
  | nil => intro acc; simp
  | cons x t ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    have := ih (rleAdd acc x)
    have := rleAdd_length acc x
    omega

theorem rle_length_le (l : List Int) : (rle l).length ≤ l.length := by
  have := rle_length_le_aux l []
  simpa [rle] using this

theorem rleExt_succ (v : List Int) (t : Nat) (ht : t < v.length) : rleExt v (t + 1) = rleAdd (rleExt v t) (v.getD t 0) := by
  have htk : v.take (t + 1) = v.take t ++ [v.getD t 0] := by
    rw [List.take_succ]
    simp [List.getD_eq_getElem?_getD, ht]
  by_cases h0 : t = 0
  · subst h0
    have hv : v.take 1 = [v.getD 0 0] := by simpa using htk
    simp only [rleExt, if_neg (show 0 + 1 ≠ 0 by omega), if_pos rfl, hv, rle, List.foldl_cons, List.foldl_nil]
    simp [rleAdd]
  · simp only [rleExt, if_neg h0, if_neg (show t + 1 ≠ 0 by omega), htk, rle, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

/-- The values a run-length encoding stands for. -/
def rleFlat (r : List (Int × Nat)) : List Int := r.flatMap (fun p => List.replicate p.2 p.1)

/-- Adjacent runs have different values. -/
def AdjOK : List (Int × Nat) → Prop
  | [] => True
  | [_] => True
  | p :: q :: t => p.1 ≠ q.1 ∧ AdjOK (q :: t)

theorem snoc_cases (acc : List (Int × Nat)) : acc = [] ∨ ∃ (L : List (Int × Nat)) (b : Int × Nat), acc = L ++ [b] := by
  rcases List.eq_nil_or_concat acc with h | ⟨L, b, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨L, b, by simpa using h⟩

theorem adjOK_snoc : ∀ (L : List (Int × Nat)) (p : Int × Nat),
    AdjOK (L ++ [p]) ↔ AdjOK L ∧ ∀ q, L.getLast? = some q → q.1 ≠ p.1 := by
  intro L
  induction L with
  | nil => intro p; simp [AdjOK]
  | cons a t ih =>
    intro p
    cases t with
    | nil => simp [AdjOK]
    | cons b t' =>
      have ih' := ih p
      simp only [List.cons_append] at ih'
      simp only [List.cons_append, AdjOK, List.getLast?_cons_cons] at ih' ⊢
      rw [ih']
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

theorem rleAdd_flat (acc : List (Int × Nat)) (x : Int) : rleFlat (rleAdd acc x) = rleFlat acc ++ [x] := by
  rcases snoc_cases acc with h | ⟨L, b, h⟩
  · subst h; simp [rleAdd, rleFlat]
  · subst h
    obtain ⟨a, c⟩ := b
    by_cases e : a = x
    · subst e
      simp [rleAdd, rleFlat, List.replicate_succ']
    · simp [rleAdd, rleFlat, e]

theorem rleAdd_pos (acc : List (Int × Nat)) (x : Int) (h : ∀ p ∈ acc, 0 < p.2) : ∀ p ∈ rleAdd acc x, 0 < p.2 := by
  rcases snoc_cases acc with h0 | ⟨L, b, h0⟩
  · subst h0; simp [rleAdd]
  · subst h0
    obtain ⟨a, c⟩ := b
    by_cases e : a = x
    · subst e
      intro p hp
      simp [rleAdd] at hp
      rcases hp with hp | hp
      · exact h p (by simp [hp])
      · rw [hp]; simp
    · intro p hp
      simp [rleAdd, e] at hp
      rcases hp with hp | hp | hp
      · exact h p (by simp [hp])
      · exact h p (by simp [hp])
      · rw [hp]; simp

theorem rleAdd_adj (acc : List (Int × Nat)) (x : Int) (h : AdjOK acc) : AdjOK (rleAdd acc x) := by
  rcases snoc_cases acc with h0 | ⟨L, b, h0⟩
  · subst h0; simp [rleAdd, AdjOK]
  · subst h0
    obtain ⟨a, c⟩ := b
    rw [adjOK_snoc] at h
    by_cases e : a = x
    · subst e
      have hl : (L ++ [(a, c)]).getLast? = some (a, c) := by simp
      have hd : (L ++ [(a, c)]).dropLast = L := by simp
      simp only [rleAdd, hl, if_true, hd]
      rw [adjOK_snoc]
      exact h
    · have hl : (L ++ [(a, c)]).getLast? = some (a, c) := by simp
      simp only [rleAdd, hl, if_neg e]
      rw [List.append_assoc]
      have hA : AdjOK (L ++ [(a, c)]) := (adjOK_snoc L (a, c)).mpr h
      have h2 := (adjOK_snoc (L ++ [(a, c)]) (x, 1)).mpr ⟨hA, by
        intro q hq
        simp at hq
        subst hq
        exact e⟩
      simpa using h2

theorem rle_foldl_spec (l : List Int) : ∀ (acc : List (Int × Nat)), (∀ p ∈ acc, 0 < p.2) → AdjOK acc →
    rleFlat (l.foldl rleAdd acc) = rleFlat acc ++ l ∧ (∀ p ∈ l.foldl rleAdd acc, 0 < p.2) ∧ AdjOK (l.foldl rleAdd acc) := by
  induction l with
  | nil => intro acc hp ha; exact ⟨by simp, hp, ha⟩
  | cons x t ih =>
    intro acc hp ha
    obtain ⟨h1, h2, h3⟩ := ih (rleAdd acc x) (rleAdd_pos acc x hp) (rleAdd_adj acc x ha)
    simp only [List.foldl_cons]
    refine ⟨?_, h2, h3⟩
    rw [h1, rleAdd_flat]
    simp

/-- The run-length encoding decodes to the input, has positive counts and maximal runs. -/
theorem rle_spec (l : List Int) : rleFlat (rle l) = l ∧ (∀ p ∈ rle l, 0 < p.2) ∧ AdjOK (rle l) := by
  have := rle_foldl_spec l [] (by simp) (by simp [AdjOK])
  simpa [rle, rleFlat] using this

end Proofs.RunLengthMath
