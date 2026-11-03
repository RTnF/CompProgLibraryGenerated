import Proofs.BeatsStep
import Proofs.BeatsExec_CalcLoopIterS
import Proofs.BeatsExec_CalcLoopIterW0
import Proofs.BeatsExec_CalcLoopIterW1
import Proofs.BeatsExec_CalcLoopIterDset
import Proofs.BeatsExec_CalcLoopIterDadd
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

/-- The explicit-stack loop of `calc_op`. -/
abbrev CLoop (o : Nat) : Command :=
  .whileLoop (.binary bT .gt (.variable i32 (o + 6)) (.literal i32 (0))) (.sequence (.scope (CalcLoopBody o)) Sk)

abbrev CCells (inf : Int) (n op qa qb : Nat) (x : Int) (sp : Nat) : List Cell :=
  [cs inf, ci n, ci op, ci qa, ci qb, cs x, ci sp]

theorem loop_condC (mv : MV) (hnv : mv.nv = 15) (P pre : List Cell) (vv : Nat → List Int) (inf : Int) (n op qa qb : Nat) (x : Int)
    (sp : Nat) (hsp : sp < M31) :
    vdenM mv vv (penvN mv.nv (gS P (pre ++ CCells inf n op qa qb x sp)))
      (.binary bT .gt (.variable i32 (mv.nv + pre.length + 6)) (.literal i32 (0))) = some (if (sp : Int) > 0 then 1 else 0) := by
  have h6 : (pre ++ CCells inf n op qa qb x sp)[pre.length + 6]? = some (ci sp) :=
    cell_at0 pre (CCells inf n op qa qb x sp) 6 (ci sp) rfl
  refine den_cmpw mv vv _ .gt _ _ (sp : Int) 0 ((sp : Int) > 0) (gt_conv _ _) ?_ ?_ rfl rfl
  · exact den_cellvar_t mv P _ i32 (pre.length + 6) _ (by omega) (sp : Int) h6 (Proofs.BellmanFordExec.i32_valid_nat sp hsp) vv
  · exact den_lit32 mv vv _ 0 (by decide)

def RunsC (mv : MV) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) (sp : Nat)
    (ps' : PS) (vv' : Nat → List Int) (C W : Nat) : Prop :=
  ∃ r : PRM, pexecM mv fu (CLoop (mv.nv + pre.length)) (gS P (pre ++ CCells inf n op qa qb x sp)) (VVB b) = some r ∧
    r.ret = none ∧ r.ps = ps' ∧ r.vv = vv' ∧ r.cost ≤ C ∧ r.wk ≤ W

theorem runsC_exit (mv : MV) (hnv : mv.nv = 15) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) :
    RunsC mv (fu + 1) P pre inf n op qa qb x b 0 (gS P (pre ++ CCells inf n op qa qb x 0)) (VVB b) 4 0 := by
  have hc := loop_condC mv hnv P pre (VVB b) inf n op qa qb x 0 (by decide)
  simp only [Nat.cast_zero, gt_iff_lt, lt_self_iff_false, if_false] at hc
  refine ⟨_, while_exit_p mv fu _ _ _ _ hc, rfl, rfl, rfl, ?_, ?_⟩
  · simp [vwp, NExpr.nodes]
  · simp

/-- One iteration of the loop of `calc_op`. -/
def IterC (mv : MV) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) (sp : Nat) (x' : Int) (b' : BS) (sp' : Nat) : Prop :=
  ∀ fu : Nat, ∃ r : PRM, pexecM mv fu (.sequence (.scope (CalcLoopBody (mv.nv + pre.length))) Sk)
      (gS P (pre ++ CCells inf n op qa qb x sp)) (VVB b) = some r ∧ r.ret = none ∧
    r.ps = gS P (pre ++ CCells inf n op qa qb x' sp') ∧ r.vv = VVB b' ∧ r.cost ≤ 72250 ∧ r.wk ≤ 24

theorem runsC_step (mv : MV) (hnv : mv.nv = 15) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x x' : Int) (b b' : BS)
    (sp sp' : Nat) (hspM : sp < M31) (hsp : 0 < sp) (r1 : PRM)
    (h1 : pexecM mv (fu + 1) (.sequence (.scope (CalcLoopBody (mv.nv + pre.length))) Sk)
      (gS P (pre ++ CCells inf n op qa qb x sp)) (VVB b) = some r1)
    (hret : r1.ret = none) (hps : r1.ps = gS P (pre ++ CCells inf n op qa qb x' sp')) (hvv : r1.vv = VVB b')
    (c1 w1 : Nat) (hc1 : r1.cost ≤ c1) (hw1 : r1.wk ≤ w1) (ps'' : PS) (vv'' : Nat → List Int) (C W : Nat)
    (hrest : RunsC mv fu P pre inf n op qa qb x' b' sp' ps'' vv'' C W) :
    RunsC mv (fu + 1) P pre inf n op qa qb x b sp ps'' vv'' (4 + c1 + C) (w1 + W) := by
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hw2⟩ := hrest
  have hc := loop_condC mv hnv P pre (VVB b) inf n op qa qb x sp hspM
  have hsp' : (sp : Int) > 0 := by omega
  simp only [hsp', if_true] at hc
  have h2' : pexecM mv fu (CLoop (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hps, hvv]; exact h2
  refine ⟨_, while_step_p mv fu _ _ _ _ hc r1 r2 h1 hret h2', hr2, hp2, hv2, ?_, ?_⟩
  · simp [vwp, NExpr.nodes]; omega
  · simp; omega

/-- The loop run from `(b, sp, x)` ends in `(bf, xf)`. -/
def RunsCE (mv : MV) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) (sp : Nat) (bf : BS) (xf : Int) (C W : Nat) : Prop :=
  RunsC mv fu P pre inf n op qa qb x b sp (gS P (pre ++ CCells inf n op qa qb xf 0)) (VVB bf) C W

theorem runsC_of_iter (mv : MV) (hnv : mv.nv = 15) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x x' : Int) (b b' : BS)
    (sp sp' : Nat) (hspM : sp < M31) (hsp : 0 < sp) (hit : IterC mv P pre inf n op qa qb x b sp x' b' sp')
    (F : Nat) (bf : BS) (xf : Int) (C W : Nat) (hrest : RunsCE mv F P pre inf n op qa qb x' b' sp' bf xf C W) :
    RunsCE mv (F + 1) P pre inf n op qa qb x b sp bf xf (72254 + C) (24 + W) := by
  obtain ⟨r1, h1, hret, hps, hvv, hc, hw⟩ := hit (F + 1)
  have := runsC_step mv hnv F P pre inf n op qa qb x x' b b' sp sp' hspM hsp r1 h1 hret hps hvv 72250 24 hc hw _ _ C W hrest
  unfold RunsCE
  have e : 4 + 72250 + C = 72254 + C := by omega
  rw [e] at this
  exact this

theorem runsC_weaken {mv : MV} {fu : Nat} {P pre : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {b : BS} {sp : Nat} {bf : BS} {xf : Int}
    {C W C' W' : Nat} (h : RunsCE mv fu P pre inf n op qa qb x b sp bf xf C W) (hc : C ≤ C') (hw : W ≤ W') :
    RunsCE mv fu P pre inf n op qa qb x b sp bf xf C' W' := by
  obtain ⟨r, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨r, h1, h2, h3, h4, le_trans h5 hc, le_trans h6 hw⟩

theorem Env_withX {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n op qa qb x L) (x' : Int) (hx' : s64.valid x' = true) : Env mv pre P inf n op qa qb x' L :=
  { Ev with hx := hx' }

end Proofs.BeatsRep
