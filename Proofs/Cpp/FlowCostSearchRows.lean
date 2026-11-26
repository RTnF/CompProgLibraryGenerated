import Proofs.Cpp.FlowCostSearchProgram

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.FlowCostSearch

variable {Cost E : Type} [Inhabited Cost] [Inhabited E] [Zero Cost] [Add Cost] [LT Cost] [DecidableLT Cost]
  [Field "cap" E Cost] [Field "cost" E Cost] [Field "to" E Int]

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

def edgeFold (row : Array E) (v : Int) (s : Pass Cost) (i : Int) : Pass Cost :=
  if relaxes (get row i) v s then relaxEdge (get row i) v i s else s

def rowFold (adj : Array (Array E)) (s : Pass Cost) (v : Int) : Pass Cost :=
  if get s.2.1 v = -1 then s
  else (range 0 (size (get adj v))).foldl (edgeFold (get adj v) v) s

@[simp] theorem edgeStep_run (row : Array E) (v i : Int) (s : Pass Cost) (t : Nat) :
    (edgeStep row v i s).run t = some (.yield (edgeFold row v s i), t + 1) := by
  unfold edgeStep edgeFold
  dsimp only
  split <;> rfl

theorem edgeScan_run (row : Array E) (v : Int) (items : List Int) (s : Pass Cost) (t : Nat) :
    (forIn items s (edgeStep row v)).run t = some (items.foldl (edgeFold row v) s, t + items.length) := by
  induction items generalizing s t with
  | nil => rfl
  | cons i items ih =>
    rw [List.forIn_cons, StateT.run_bind, edgeStep_run]
    change (forIn items _ (edgeStep row v)).run (t + 1) = _
    rw [ih, List.foldl_cons, List.length_cons]
    congr 2
    omega

theorem rowStep_run (adj : Array (Array E)) (v : Int) (s : Pass Cost) (t : Nat) :
    ∃ t', (rowStep adj v s).run t = some (.yield (rowFold adj s v), t') ∧
      t' ≤ t + 1 + (get adj v).size := by
  by_cases h : get s.2.1 v = -1
  · refine ⟨t + 1, ?_, by omega⟩
    unfold rowStep rowFold
    simp [h, tick_run]
  · let row := get adj v
    have len : (range 0 (size row)).length = row.size := by simp [range, size]
    refine ⟨t + 1 + row.size, ?_, Nat.le_refl _⟩
    unfold rowStep rowFold
    simp only [h, decide_false, Bool.false_eq_true, ite_false, StateT.run_bind, tick_run, some_bind]
    rw [edgeScan_run, len]
    rfl

def scanCharge (adj : Array (Array E)) (items : List Int) : Nat :=
  (items.map (fun v => 1 + (get adj v).size)).sum

theorem rowScan_run (adj : Array (Array E)) (items : List Int) (s : Pass Cost) (t : Nat) :
    ∃ t', (forIn items s (rowStep adj)).run t = some (items.foldl (rowFold adj) s, t') ∧
      t' ≤ t + scanCharge adj items := by
  induction items generalizing s t with
  | nil => exact ⟨t, rfl, le_rfl⟩
  | cons v items ih =>
    obtain ⟨tm, hm, hmt⟩ := rowStep_run adj v s t
    obtain ⟨tf, hf, hft⟩ := ih (rowFold adj s v) tm
    refine ⟨tf, ?_, ?_⟩
    · rw [List.forIn_cons, StateT.run_bind, hm, List.foldl_cons]
      exact hf
    · simp only [scanCharge, List.map_cons, List.sum_cons] at hft ⊢
      omega

private theorem edgeScan_false (row : Array E) (v : Int) (items : List Int) (s : Pass Cost)
    (h : ((items.foldl (edgeFold row v) s).2.2.2) = false) :
    items.foldl (edgeFold row v) s = s ∧ s.2.2.2 = false ∧
      ∀ i ∈ items, relaxes (get row i) v s = false := by
  induction items generalizing s with
  | nil => exact ⟨rfl, h, by simp⟩
  | cons i items ih =>
    obtain ⟨tail, flag, noRelax⟩ := ih (edgeFold row v s i) h
    have noHead : relaxes (get row i) v s = false := by
      by_contra hn
      have ht : relaxes (get row i) v s = true := by cases h : relaxes (get row i) v s <;> simp_all
      simp [edgeFold, ht, relaxEdge] at flag
    have eh : edgeFold row v s i = s := by simp [edgeFold, noHead]
    rw [eh] at tail flag noRelax
    refine ⟨by simpa only [List.foldl_cons, eh] using tail, flag, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact noHead
    · exact noRelax j hj

private theorem rowFold_false (adj : Array (Array E)) (v : Int) (s : Pass Cost)
    (h : (rowFold adj s v).2.2.2 = false) :
    rowFold adj s v = s ∧ s.2.2.2 = false ∧
      (get s.2.1 v ≠ -1 → ∀ i ∈ range 0 (size (get adj v)), relaxes (get (get adj v) i) v s = false) := by
  by_cases hv : get s.2.1 v = -1
  · simp only [rowFold, hv, ite_true] at h ⊢
    exact ⟨True.intro, h, fun notClosed => False.elim (notClosed rfl)⟩
  · unfold rowFold at h ⊢
    rw [ite_eq_right hv] at h ⊢
    obtain ⟨eq, flag, noRelax⟩ := edgeScan_false _ _ _ _ h
    exact ⟨eq, flag, fun _ => noRelax⟩

/-- A pass which leaves the flag false preserves its input and leaves no remaining relaxable edge. -/
theorem pass_no_update (adj : Array (Array E)) (items : List Int) (s : Pass Cost)
    (h : ((items.foldl (rowFold adj) s).2.2.2) = false) :
    items.foldl (rowFold adj) s = s ∧ s.2.2.2 = false ∧
      ∀ v ∈ items, get s.2.1 v ≠ -1 →
        ∀ i ∈ range 0 (size (get adj v)), relaxes (get (get adj v) i) v s = false := by
  induction items generalizing s with
  | nil => exact ⟨rfl, h, by simp⟩
  | cons v items ih =>
    obtain ⟨tail, flag, noRelax⟩ := ih (rowFold adj s v) h
    obtain ⟨row, initial, noRow⟩ := rowFold_false adj v s flag
    rw [row] at tail noRelax
    refine ⟨by simpa only [List.foldl_cons, row] using tail, initial, ?_⟩
    intro u hu openRow
    rcases List.mem_cons.mp hu with rfl | hu
    · exact noRow openRow
    · exact noRelax u hu openRow

end Proofs.Cpp.FlowCostSearch
