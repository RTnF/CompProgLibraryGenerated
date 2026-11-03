import Proofs.BeatsExec_ApplyLoopIterW0
import Proofs.BeatsExec_ApplyLoopIterDset
import Proofs.BeatsExec_ApplyLoopIterDadd
import Proofs.BeatsExec_ApplyLoopIterS
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

/-- The explicit-stack loop of `apply_op`. -/
abbrev ALoop (o : Nat) : Command :=
  .whileLoop (.binary bT .gt (.variable i32 (o + 6)) (.literal i32 (0))) (.sequence (.scope (ApplyLoopBody o)) Sk)

/-- The cells at the loop head. -/
abbrev LCells (inf : Int) (n op qa qb : Nat) (x : Int) (sp ne : Nat) : List Cell :=
  [cs inf, ci n, ci op, ci qa, ci qb, cs x, ci sp, ci ne]

theorem loop_cond (mv : MV) (hnv : mv.nv = 15) (P pre : List Cell) (vv : Nat → List Int) (inf : Int) (n op qa qb : Nat) (x : Int)
    (sp ne : Nat) (hsp : sp < M31) :
    vdenM mv vv (penvN mv.nv (gS P (pre ++ LCells inf n op qa qb x sp ne)))
      (.binary bT .gt (.variable i32 (mv.nv + pre.length + 6)) (.literal i32 (0))) = some (if (sp : Int) > 0 then 1 else 0) := by
  have h6 : (pre ++ LCells inf n op qa qb x sp ne)[pre.length + 6]? = some (ci sp) :=
    cell_at0 pre (LCells inf n op qa qb x sp ne) 6 (ci sp) rfl
  refine den_cmpw mv vv _ .gt _ _ (sp : Int) 0 ((sp : Int) > 0) (gt_conv _ _) ?_ ?_ rfl rfl
  · exact den_cellvar_t mv P _ i32 (pre.length + 6) _ (by omega) (sp : Int) h6 (Proofs.BellmanFordExec.i32_valid_nat sp hsp) vv
  · exact den_lit32 mv vv _ 0 (by decide)

theorem while_exit_p (mv : MV) (fu : Nat) (c : NExpr) (b : Command) (ps : PS) (vv : Nat → List Int)
    (hc : vdenM mv vv (penvN mv.nv ps) c = some 0) :
    pexecM mv (fu + 1) (.whileLoop c b) ps vv =
      some ⟨ps, vv, none, (vwp c).1 + 1, ps.mem.length + ps.bs.length + (vwp c).2 + 2, 0⟩ := by
  rw [pexecM_while, hc]
  simp [Bind.bind, Option.bind]

theorem while_step_p (mv : MV) (fu : Nat) (c : NExpr) (b : Command) (ps : PS) (vv : Nat → List Int)
    (hc : vdenM mv vv (penvN mv.nv ps) c = some 1) (r1 r2 : PRM) (h1 : pexecM mv (fu + 1) b ps vv = some r1)
    (hret : r1.ret = none) (h2 : pexecM mv fu (.whileLoop c b) r1.ps r1.vv = some r2) :
    pexecM mv (fu + 1) (.whileLoop c b) ps vv =
      some ⟨r2.ps, r2.vv, r2.ret, (vwp c).1 + 1 + r1.cost + r2.cost,
        max (ps.mem.length + ps.bs.length + (vwp c).2 + 2) (max r1.need r2.need), r1.wk + r2.wk⟩ := by
  rw [pexecM_while, hc]
  simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, hret, h2]

/-- The loop started at `(b, sp, ne)` finishes with the given final state within the given cost and write bounds. -/
def RunsF (mv : MV) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) (sp ne : Nat)
    (ps' : PS) (vv' : Nat → List Int) (C W : Nat) : Prop :=
  ∃ r : PRM, pexecM mv fu (ALoop (mv.nv + pre.length)) (gS P (pre ++ LCells inf n op qa qb x sp ne)) (VVB b) = some r ∧
    r.ret = none ∧ r.ps = ps' ∧ r.vv = vv' ∧ r.cost ≤ C ∧ r.wk ≤ W

theorem runs_exit (mv : MV) (hnv : mv.nv = 15) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b : BS) (ne : Nat) :
    RunsF mv (fu + 1) P pre inf n op qa qb x b 0 ne (gS P (pre ++ LCells inf n op qa qb x 0 ne)) (VVB b) 4 0 := by
  have hc := loop_cond mv hnv P pre (VVB b) inf n op qa qb x 0 ne (by decide)
  simp only [Nat.cast_zero, gt_iff_lt, lt_self_iff_false, if_false] at hc
  refine ⟨_, while_exit_p mv fu _ _ _ _ hc, rfl, rfl, rfl, ?_, ?_⟩
  · simp [vwp, NExpr.nodes]
  · simp

theorem runs_step (mv : MV) (hnv : mv.nv = 15) (fu : Nat) (P pre : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (b b' : BS)
    (sp ne sp' ne' : Nat) (hspM : sp < M31) (hsp : 0 < sp) (r1 : PRM)
    (h1 : pexecM mv (fu + 1) (.sequence (.scope (ApplyLoopBody (mv.nv + pre.length))) Sk)
      (gS P (pre ++ LCells inf n op qa qb x sp ne)) (VVB b) = some r1)
    (hret : r1.ret = none) (hps : r1.ps = gS P (pre ++ LCells inf n op qa qb x sp' ne')) (hvv : r1.vv = VVB b')
    (c1 w1 : Nat) (hc1 : r1.cost ≤ c1) (hw1 : r1.wk ≤ w1) (ps'' : PS) (vv'' : Nat → List Int) (C W : Nat)
    (hrest : RunsF mv fu P pre inf n op qa qb x b' sp' ne' ps'' vv'' C W) :
    RunsF mv (fu + 1) P pre inf n op qa qb x b sp ne ps'' vv'' (4 + c1 + C) (w1 + W) := by
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hw2⟩ := hrest
  have hc := loop_cond mv hnv P pre (VVB b) inf n op qa qb x sp ne hspM
  have hsp' : (sp : Int) > 0 := by omega
  simp only [hsp', if_true] at hc
  have h2' : pexecM mv fu (ALoop (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hps, hvv]; exact h2
  refine ⟨_, while_step_p mv fu _ _ _ _ hc r1 r2 h1 hret h2', hr2, hp2, hv2, ?_, ?_⟩
  · simp [vwp, NExpr.nodes]; omega
  · simp; omega

end Proofs.BeatsRep
