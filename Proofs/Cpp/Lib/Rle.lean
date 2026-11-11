import Proofs.Cpp.Lib.Basic

/-! Run-length encoding: the runs of equal consecutive values of a list with their lengths.

The runs are built in reverse order (`rrle`, the last run first) because the C++ loops change the last run;
`rle xs = (rrle xs).reverse`. -/

namespace Proofs.Cpp

variable {T : Type} [DecidableEq T]

/-- Add one value to the runs so far (last run first). -/
def rrStep (acc : List (T × Int)) (y : T) : List (T × Int) :=
  match acc with
  | p :: rest => if p.1 = y then (p.1, p.2 + 1) :: rest else (y, 1) :: p :: rest
  | [] => [(y, 1)]

/-- The runs of `xs`, last run first. -/
def rrle (xs : List T) : List (T × Int) := xs.foldl rrStep []

/-- The runs of `xs`. -/
def rle (xs : List T) : List (T × Int) := (rrle xs).reverse

/-- The values that the runs stand for. -/
def unrle (r : List (T × Int)) : List T := r.flatMap (fun p => List.replicate p.2.toNat p.1)

/-- Every run is nonempty and adjacent runs have different values. -/
def RunsOk (r : List (T × Int)) : Prop :=
  (∀ p ∈ r, 0 < p.2) ∧ ∀ i (h : i + 1 < r.length), (r[i]'(by omega)).1 ≠ (r[i + 1]'h).1

theorem unrle_reverse (r : List (T × Int)) : unrle r.reverse = (unrle r).reverse := by
  induction r with
  | nil => simp [unrle]
  | cons p r ih =>
    simp only [unrle] at *
    simp [List.flatMap_append, ih, List.reverse_replicate]

theorem runsOk_reverse (r : List (T × Int)) (h : RunsOk r) : RunsOk r.reverse := by
  refine ⟨fun p hp => h.1 p (List.mem_reverse.mp hp), fun i hi => ?_⟩
  simp only [List.length_reverse] at hi
  rw [List.getElem_reverse, List.getElem_reverse]
  have := h.2 (r.length - 1 - (i + 1)) (by omega)
  have e : r.length - 1 - (i + 1) + 1 = r.length - 1 - i := by omega
  simp only [e] at this
  exact fun h' => this h'.symm

theorem rrStep_ok (acc : List (T × Int)) (y : T) (h : RunsOk acc) :
    RunsOk (rrStep acc y) ∧ unrle (rrStep acc y) = y :: unrle acc := by
  cases acc with
  | nil => simp [rrStep, RunsOk, unrle]
  | cons p rest =>
    by_cases hp : p.1 = y
    · simp only [rrStep, hp, ite_true]
      have hpos := h.1 p (by simp)
      refine ⟨⟨fun q hq => ?_, fun i hi => ?_⟩, ?_⟩
      · simp at hq
        rcases hq with rfl | hq
        · simp; omega
        · exact h.1 q (by simp [hq])
      · have := h.2 i (by simpa using hi)
        cases i with
        | zero => simpa [hp] using this
        | succ i => simpa using this
      · simp [unrle, show (p.2 + 1).toNat = p.2.toNat + 1 by omega, List.replicate_succ, ← hp]
    · simp only [rrStep, hp, ite_false]
      refine ⟨⟨fun q hq => ?_, fun i hi => ?_⟩, ?_⟩
      · simp at hq
        rcases hq with rfl | hq
        · simp
        · exact h.1 q (by simpa using hq)
      · cases i with
        | zero => simpa using Ne.symm hp
        | succ i =>
          have := h.2 i (by simpa using hi)
          simp only [List.getElem_cons_succ] at this ⊢
          exact this
      · simp [unrle]

theorem foldl_rrStep_ok (xs : List T) (acc : List (T × Int)) (h : RunsOk acc) :
    RunsOk (xs.foldl rrStep acc) ∧ unrle (xs.foldl rrStep acc) = xs.reverse ++ unrle acc := by
  induction xs generalizing acc with
  | nil => simp [h]
  | cons y xs ih =>
    obtain ⟨h1, h2⟩ := rrStep_ok acc y h
    obtain ⟨h3, h4⟩ := ih _ h1
    exact ⟨h3, by simp [h4, h2]⟩

/-- The runs of `xs` give back `xs`. -/
theorem unrle_rle (xs : List T) : unrle (rle xs) = xs := by
  have := (foldl_rrStep_ok xs [] (by simp [RunsOk])).2
  rw [rle, unrle_reverse, rrle, this]
  simp [unrle]

/-- Every run is nonempty and adjacent runs have different values. -/
theorem rle_ok (xs : List T) : RunsOk (rle xs) :=
  runsOk_reverse _ (foldl_rrStep_ok xs [] (by simp [RunsOk])).1

/-- Adding a value to a list whose runs end with `p`. -/
theorem rle_snoc_last (l : List T) (y : T) (R : List (T × Int)) (p : T × Int) (h : rle l = R ++ [p]) :
    rle (l ++ [y]) = if p.1 = y then R ++ [(p.1, p.2 + 1)] else R ++ [p, (y, 1)] := by
  have hr : rrle l = p :: R.reverse := by
    have := congrArg List.reverse h
    simpa [rle] using this
  simp only [rle, rrle, List.foldl_append, List.foldl_cons, List.foldl_nil] at hr ⊢
  rw [hr]
  simp only [rrStep]
  by_cases hp : p.1 = y <;> simp [hp]

/-! ## The C++ loops that extend the last run of a vector of pairs -/

section
variable [Inhabited T]

theorem rrle_snoc (l : List T) (y : T) : rrle (l ++ [y]) = rrStep (rrle l) y := by
  simp [rrle, List.foldl_append]

theorem rrle_ne_nil (l : List T) (h : l ≠ []) : rrle l ≠ [] := by
  obtain ⟨l', z, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left h
  rw [List.concat_eq_append, rrle_snoc]
  unfold rrStep
  split
  · split <;> simp
  · simp

theorem counts_step (l : List T) (y : T) (ret : Array (T × Int)) (h : ret.toList = rle l) (hl : l ≠ []) :
    ((back ret).1 ≠ y → (ret.push (y, 1)).toList = rle (l ++ [y])) ∧
    (¬ (back ret).1 ≠ y → (set ret (size ret - 1)
        ((get ret (size ret - 1)).1, (get ret (size ret - 1)).2 + 1)).toList = rle (l ++ [y])) := by
  obtain ⟨p, rest, hpr⟩ : ∃ p rest, rrle l = p :: rest := by
    cases e : rrle l with
    | nil => exact absurd e (rrle_ne_nil l hl)
    | cons p rest => exact ⟨p, rest, rfl⟩
  have ht : ret.toList = rest.reverse ++ [p] := by rw [h, rle, hpr]; simp
  have hsz : ret.size = rest.length + 1 := by rw [← Array.length_toList, ht]; simp
  have hlast : ret[rest.length]! = p := by
    rw [getElem!_pos ret rest.length (by omega), ← Array.getElem_toList]
    simp [ht]
  have hback : back ret = p := by
    simp only [back, Array.back!, hsz]
    simpa using hlast
  have hget : get ret (size ret - 1) = p := by
    simp only [get_eq, size, hsz]
    rw [show ((rest.length + 1 : Nat) : Int) - 1 = (rest.length : Int) by omega, Int.toNat_natCast]
    exact hlast
  rw [hback, hget]
  constructor
  · intro hne
    rw [Array.toList_push, ht, rle, rrle_snoc, hpr]
    simp [rrStep, hne]
  · intro heq
    have heq' : p.1 = y := by simpa using heq
    rw [show size ret - 1 = (rest.length : Int) by simp [size, hsz]]
    unfold Proofs.Cpp.set
    rw [Int.toNat_natCast, rle, rrle_snoc, hpr]
    simp only [rrStep, heq', ite_true]
    rw [Array.set!, Array.toList_setIfInBounds, ht, List.set_append_right _ _ (by simp)]
    simp

theorem counts_push (l : List T) (y : T) (ret : Array (T × Int)) (h : ret.toList = rle l)
    (hc : l = [] ∨ (back ret).1 ≠ y) : (ret.push (y, 1)).toList = rle (l ++ [y]) := by
  rcases hc with rfl | hne
  · simp [rle, rrle, rrStep] at h ⊢; simp [h]
  · by_cases hl : l = []
    · subst hl; simp [rle, rrle, rrStep] at h ⊢; simp [h]
    · exact (counts_step l y ret h hl).1 hne

theorem counts_bump (l : List T) (y : T) (ret : Array (T × Int)) (h : ret.toList = rle l)
    (hl : l ≠ []) (he : (back ret).1 = y) :
    (set ret (size ret - 1) ((get ret (size ret - 1)).1, (get ret (size ret - 1)).2 + 1)).toList =
      rle (l ++ [y]) :=
  (counts_step l y ret h hl).2 (by simpa using he)

end

end Proofs.Cpp
