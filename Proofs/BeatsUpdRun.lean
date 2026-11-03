import Proofs.BeatsUpdIter
import Proofs.BeatsSums
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec
set_option maxRecDepth 100000

/-- The update loop of `apply_op`. -/
abbrev ULoop (o : Nat) : Command :=
  .whileLoop (.binary bT .gt (.variable i32 (o + 7)) (.literal i32 (0))) (.sequence (.scope (UpdLoopBody o)) Sk)

theorem loop_condU (mv : MV) (hnv : mv.nv = 15) (P pre : List Cell) (vv : Nat → List Int) (inf : Int) (n op qa qb : Nat) (x : Int)
    (sp ne : Nat) (hne : ne < M31) :
    vdenM mv vv (penvN mv.nv (gS P (pre ++ LCells inf n op qa qb x sp ne)))
      (.binary bT .gt (.variable i32 (mv.nv + pre.length + 7)) (.literal i32 (0))) = some (if (ne : Int) > 0 then 1 else 0) := by
  have h7 : (pre ++ LCells inf n op qa qb x sp ne)[pre.length + 7]? = some (ci ne) :=
    cell_at0 pre (LCells inf n op qa qb x sp ne) 7 (ci ne) rfl
  refine den_cmpw mv vv _ .gt _ _ (ne : Int) 0 ((ne : Int) > 0) (gt_conv _ _) ?_ ?_ rfl rfl
  · exact den_cellvar_t mv P _ i32 (pre.length + 7) _ (by omega) (ne : Int) h7 (Proofs.BellmanFordExec.i32_valid_nat ne hne) vv
  · exact den_lit32 mv vv _ 0 (by decide)

def RunsU (mv : MV) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) (sp ne : Nat)
    (ps' : PS) (vv' : Nat → List Int) (C W : Nat) : Prop :=
  ∃ r : PRM, pexecM mv fu (ULoop (mv.nv + pre.length)) (gS P (pre ++ LCells inf n op qa qb x sp ne)) (VVB b) = some r ∧
    r.ret = none ∧ r.ps = ps' ∧ r.vv = vv' ∧ r.cost ≤ C ∧ r.wk ≤ W

theorem runsU_exit (mv : MV) (hnv : mv.nv = 15) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) (sp : Nat) :
    RunsU mv (fu + 1) P pre inf n op qa qb x b sp 0 (gS P (pre ++ LCells inf n op qa qb x sp 0)) (VVB b) 4 0 := by
  have hc := loop_condU mv hnv P pre (VVB b) inf n op qa qb x sp 0 (by decide)
  simp only [Nat.cast_zero, gt_iff_lt, lt_self_iff_false, if_false] at hc
  refine ⟨_, while_exit_p mv fu _ _ _ _ hc, rfl, rfl, rfl, ?_, ?_⟩
  · simp [vwp, NExpr.nodes]
  · simp

theorem runsU_step (mv : MV) (hnv : mv.nv = 15) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b b' : BS)
    (sp ne ne' : Nat) (hneM : ne < M31) (hne : 0 < ne) (r1 : PRM)
    (h1 : pexecM mv (fu + 1) (.sequence (.scope (UpdLoopBody (mv.nv + pre.length))) Sk)
      (gS P (pre ++ LCells inf n op qa qb x sp ne)) (VVB b) = some r1)
    (hret : r1.ret = none) (hps : r1.ps = gS P (pre ++ LCells inf n op qa qb x sp ne')) (hvv : r1.vv = VVB b')
    (c1 w1 : Nat) (hc1 : r1.cost ≤ c1) (hw1 : r1.wk ≤ w1) (ps'' : PS) (vv'' : Nat → List Int) (C W : Nat)
    (hrest : RunsU mv fu P pre inf n op qa qb x b' sp ne' ps'' vv'' C W) :
    RunsU mv (fu + 1) P pre inf n op qa qb x b sp ne ps'' vv'' (4 + c1 + C) (w1 + W) := by
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hw2⟩ := hrest
  have hc := loop_condU mv hnv P pre (VVB b) inf n op qa qb x sp ne hneM
  have hne' : (ne : Int) > 0 := by omega
  simp only [hne', if_true] at hc
  have h2' : pexecM mv fu (ULoop (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hps, hvv]; exact h2
  refine ⟨_, while_step_p mv fu _ _ _ _ hc r1 r2 h1 hret h2', hr2, hp2, hv2, ?_, ?_⟩
  · simp [vwp, NExpr.nodes]; omega
  · simp; omega

theorem runsU_weaken_p {mv : MV} {fu : Nat} {P pre : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {b : BS} {sp ne : Nat}
    {ps' : PS} {vv' : Nat → List Int} {C W C' W' : Nat} (h : RunsU mv fu P pre inf n op qa qb x b sp ne ps' vv' C W) (hc : C ≤ C') (hw : W ≤ W') :
    RunsU mv fu P pre inf n op qa qb x b sp ne ps' vv' C' W' := by
  obtain ⟨r, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨r, h1, h2, h3, h4, le_trans h5 hc, le_trans h6 hw⟩

/-- The whole update loop: the entered nodes are processed in reverse order of entry. -/
theorem upd_all (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32)
    (P : List Cell) (inf : Int) (n op qa qb sp : Nat) (x : Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hopM : op < M31) (hqaM : qa < M31) (hqbM : qb < M31) (hspM : sp < M31) (hx : s64.valid x = true)
    (L : Nat) (hLM : L < M31) :
    ∀ (E : List Nat) (b : BS) (ne : Nat) (H : Heap), EntRep b ne E → ValidOK b → Lens b L → (∀ e ∈ E, 2 * e + 2 < L) → ne ≤ L →
      SumsOK E H → HRel inf b H →
      ∃ b' : BS, ∃ F, F ≤ E.length + 1 ∧
        RunsU mv F P pre inf n op qa qb x b sp ne (gS P (pre ++ LCells inf n op qa qb x sp 0)) (VVB b') (E.length * 24794 + 4) (E.length * 6) ∧
        HRel inf b' (upPhase E H) ∧ ValidOK b' ∧ SameLen b b' ∧ b'.sk = b.sk ∧ b'.sl = b.sl ∧ b'.sr = b.sr := by
  intro E
  induction E with
  | nil =>
    intro b ne H hent hV hLens hE hne hS hH
    have h0 : ne = 0 := by have := hent.1; simp at this; omega
    subst h0
    refine ⟨b, 0 + 1, by simp, ?_, hH, hV, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
    simpa using runsU_exit mv hnv 0 P pre inf n op qa qb x b sp
  | cons e E ih =>
    intro b ne H hent hV hLens hE hne hS hH
    have hne0 : 0 < ne := by have := hent.1; simp at this; omega
    have hS1 : SumOK H e := hS.1
    have hmc : s64.valid (b.mxc.getD (2 * e + 1) 0 + b.mxc.getD (2 * e + 2) 0) = true := by
      have a := (hH (2 * e + 1)).1; have c := (hH (2 * e + 2)).1
      have h1 := hS1.1; rw [← a, ← c] at h1; exact h1
    have hnc : s64.valid (b.mnc.getD (2 * e + 1) 0 + b.mnc.getD (2 * e + 2) 0) = true := by
      have a := (hH (2 * e + 1)).1; have c := (hH (2 * e + 2)).1
      have h1 := hS1.2; rw [← a, ← c] at h1; exact h1
    obtain ⟨b1, hH1, hent1, hV1, hSL1, hsk1, hsl1, hsr1, hit⟩ :=
      iter_upd mv hnv pre hty hty32 b P inf n op qa qb sp ne x hinf hnM hopM hqaM hqbM hspM (by omega) hx L hV hLens hLM e E hent
        (hE e (by simp)) hne hmc hnc H hH
    obtain ⟨b2, F, hF, hrun, hH2, hV2, hSL2, hsk2, hsl2, hsr2⟩ :=
      ih b1 (ne - 1) (updateH H e) hent1 hV1 (Lens_of_same hLens hSL1) (fun e' he' => hE e' (by simp [he'])) (by omega) hS.2 hH1
    refine ⟨b2, F + 1, by simp at hF ⊢; omega, ?_, ?_, hV2, ?_, ?_, ?_, ?_⟩
    · obtain ⟨r1, h1, hret, hps, hvv, hc, hw⟩ := hit (F + 1)
      have := runsU_step mv hnv F P pre inf n op qa qb x b b1 sp ne (ne - 1) (by omega) hne0 r1 h1 hret hps hvv 24790 6 hc hw _ _ _ _ hrun
      refine runsU_weaken_p this ?_ ?_ <;> simp <;> omega
    · rw [upPhase_cons]; exact hH2
    · exact ⟨by rw [hSL2.l0, hSL1.l0], by rw [hSL2.l1, hSL1.l1], by rw [hSL2.l2, hSL1.l2], by rw [hSL2.l3, hSL1.l3],
        by rw [hSL2.l4, hSL1.l4], by rw [hSL2.l5, hSL1.l5], by rw [hSL2.l6, hSL1.l6], by rw [hSL2.l7, hSL1.l7],
        by rw [hSL2.l8, hSL1.l8], by rw [hSL2.l9, hSL1.l9], by rw [hSL2.l10, hSL1.l10], by rw [hSL2.l11, hSL1.l11],
        by rw [hSL2.l12, hSL1.l12], by rw [hSL2.l13, hSL1.l13], by rw [hSL2.l14, hSL1.l14], by rw [hSL2.leneq, hSL1.leneq]⟩
    · rw [hsk2, hsk1]
    · rw [hsl2, hsl1]
    · rw [hsr2, hsr1]

end Proofs.BeatsRep
