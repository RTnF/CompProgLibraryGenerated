import Proofs.Cpp.FlowBfsProjection

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowBfs

namespace Proofs.Cpp.FlowBfs

variable {Cost E : Type} [Inhabited E] [Zero Cost] [LT Cost] [DecidableLT Cost]
  [Field "cap" E Cost] [Field "to" E Int]

/-- The queue and the completed prefix together contain at most one occurrence of each reachable vertex. -/
theorem scan_width {g : cp.FlowGraph Cost E} {source active : Nat} {done : List Nat}
    {b : BfsState} {d : Nat} (state : ScanState g source active done b d) :
    done.length + 1 + b.2.length ≤ g.adj.size := by
  have hall : done ++ active :: b.2.map Int.toNat ⊆ List.range g.adj.size := by
    intro u hu
    apply List.mem_range.mpr
    obtain ⟨j, hj⟩ := (state.scan.seen u).mpr hu
    by_contra h
    have hh : ¬u < b.1.size := by simpa only [state.size] using h
    simp [levelsView, hh] at hj
  have h := state.scan.unique.length_le_of_subset hall
  simp only [List.length_append, List.length_cons, List.length_map, List.length_range] at h
  omega

theorem scan_vertices {g : cp.FlowGraph Cost E} {source active : Nat} {done : List Nat}
    {b : BfsState} {d : Nat} (state : ScanState g source active done b d)
    (v : Nat) (hv : v ∈ done ++ active :: b.2.map Int.toNat) : v < g.adj.size := by
  obtain ⟨j, hj⟩ := (state.scan.seen v).mpr hv
  by_contra h
  have hh : ¬v < b.1.size := by simpa only [state.size] using h
  simp [levelsView, hh] at hj

/-- All positive-capacity arcs in the row establish the distance inequality. Existing distances survive the scan. -/
theorem scan_row (g : cp.FlowGraph Cost E) (valid : Valid g) (source active d : Nat) (done : List Nat)
    (row : List E) (subset : row ⊆ edgesAt g active) :
    ∀ b t, ScanState g source active done b d →
      ∃ (out : BfsState) (t' : Nat),
        (forIn row b (edgeStep (Cost := Cost) (active : Int))).run t = some (out, t') ∧
        ScanState g source active done out d ∧ KeepsLevels (levelsView b.1) (levelsView out.1) ∧
        (∀ e ∈ row, positive (Cost := Cost) e → lowerAtMost (levelsView out.1) (target e).toNat (d + 1)) ∧
        t' ≤ t + 2 * row.length := by
  induction row with
  | nil =>
    intro b t st
    exact ⟨b, t, rfl, st, fun _ _ h => h, by simp, by simp⟩
  | cons edge row ih =>
    intro b t st
    have hrow : row ⊆ edgesAt g active := fun _ he => subset (List.mem_cons_of_mem _ he)
    obtain ⟨mid, tm, hr, hm, keep, hit, time⟩ := scan_edge g valid source active d done b st edge
      (subset (by simp)) t
    obtain ⟨out, t', hrun, hf, keep', lower, bound⟩ := ih hrow mid tm hm
    refine ⟨out, t', ?_, hf, keep.trans keep', ?_, ?_⟩
    · rw [List.forIn_cons, StateT.run_bind, hr]
      exact hrun
    · intro e he hp
      rcases List.mem_cons.mp he with rfl | h
      · exact keep'.keeps_bound (hit hp)
      · exact lower e h hp
    · simp only [List.length_cons]
      omega

end Proofs.Cpp.FlowBfs
