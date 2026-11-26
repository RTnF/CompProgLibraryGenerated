import Proofs.Cpp.FlowCostSearchRows

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.FlowCostSearch

variable {Cost E : Type} [Inhabited Cost] [Inhabited E] [Zero Cost] [Add Cost] [LT Cost] [DecidableLT Cost]
  [Field "cap" E Cost] [Field "cost" E Cost] [Field "to" E Int]

def sweep (g : cp.FlowGraph Cost E) (b : Labels Cost) : Pass Cost :=
  (range 0 g.n_).foldl (rowFold g.adj) (b.1, b.2.1, b.2.2, false)

def labelPart (b : Pass Cost) : Labels Cost := (b.1, b.2.1, b.2.2.1)

def passCharge (g : cp.FlowGraph Cost E) : Nat := 1 + scanCharge g.adj (range 0 g.n_)

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

theorem passStep_run (g : cp.FlowGraph Cost E) (b : Labels Cost) (t : Nat) :
    ∃ finish, (passStep g () b).run t =
      some ((if (sweep g b).2.2.2 then .yield (labelPart (sweep g b)) else .done (labelPart (sweep g b))), finish) ∧
      finish ≤ t + passCharge g := by
  obtain ⟨finish, run, work⟩ := rowScan_run g.adj (range 0 g.n_) (b.1, b.2.1, b.2.2, false) (t + 1)
  refine ⟨finish, ?_, ?_⟩
  · unfold passStep
    simp only [StateT.run_bind, tick_run, some_bind, run]
    by_cases h : (sweep g b).2.2.2 = true
    · simp only [sweep] at h
      simp only [sweep, labelPart, h, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      rfl
    · have hn : (sweep g b).2.2.2 = false := by cases h' : (sweep g b).2.2.2 <;> simp_all
      simp only [sweep] at hn
      simp only [sweep, labelPart, hn, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
      rfl
  · unfold passCharge
    omega

def Stable (g : cp.FlowGraph Cost E) (b : Labels Cost) : Prop :=
  ∀ v ∈ range 0 g.n_, get b.2.1 v ≠ -1 →
    ∀ i ∈ range 0 (size (get g.adj v)), relaxes (get (get g.adj v) i) v (b.1, b.2.1, b.2.2, false) = false

theorem pass_stable (g : cp.FlowGraph Cost E) (b : Labels Cost) (h : (sweep g b).2.2.2 = false) :
    labelPart (sweep g b) = b ∧ Stable g b := by
  obtain ⟨eq, _, noRelax⟩ := pass_no_update g.adj (range 0 g.n_) (b.1, b.2.1, b.2.2, false) h
  refine ⟨?_, noRelax⟩
  unfold sweep
  rw [eq]
  rfl

def StopsBy (g : cp.FlowGraph Cost E) : Nat → Labels Cost → Prop
  | 0, _ => False
  | k + 1, b => (sweep g b).2.2.2 = false ∨ StopsBy g k (labelPart (sweep g b))

theorem pass_loop (g : cp.FlowGraph Cost E) (lim budget : Nat) (hlim : budget ≤ lim)
    (b : Labels Cost) (hstop : StopsBy g budget b) (t : Nat) (inv : Labels Cost → Prop)
    (preserves : ∀ s, inv s → inv (labelPart (sweep g s))) (start : inv b) :
    ∃ out finish, (loopFuel lim b (passStep g)).run t = some (out, finish) ∧ Stable g out ∧ inv out ∧
      finish ≤ t + budget * passCharge g := by
  induction budget generalizing lim b t with
  | zero => exact False.elim hstop
  | succ k ih =>
    cases lim with
    | zero => omega
    | succ len =>
      obtain ⟨stepTime, runStep, localCost⟩ := passStep_run g b t
      by_cases still : (sweep g b).2.2.2 = false
      · obtain ⟨same, stable⟩ := pass_stable g b still
        refine ⟨b, stepTime, ?_, stable, start, ?_⟩
        · rw [loopFuel, StateT.run_bind, runStep]
          simp only [still, ite_false, Bool.false_eq_true, same]
          rfl
        · rw [Nat.succ_mul]
          omega
      · have more : StopsBy g k (labelPart (sweep g b)) := by
          rcases hstop with h | h
          · exact False.elim (still h)
          · exact h
        have go : (sweep g b).2.2.2 = true := by cases h : (sweep g b).2.2.2 <;> simp_all
        obtain ⟨out, finish, runTail, stable, invOut, tailCost⟩ := ih len (by omega)
          (labelPart (sweep g b)) more stepTime (preserves b start)
        refine ⟨out, finish, ?_, stable, invOut, ?_⟩
        · rw [loopFuel, StateT.run_bind, runStep]
          simp only [go, ite_true]
          exact runTail
        · rw [Nat.succ_mul]
          omega

end Proofs.Cpp.FlowCostSearch
