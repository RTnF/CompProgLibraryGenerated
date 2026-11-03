import Proofs.BeatsExecUA
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec

/-- `v[k] + x` where both sides are known. -/
theorem den_rdadd (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (v : Nat) (hv : v < mv.nv)
    (hty : mv.ty v = s64) (a x : Int) (iE vE : NExpr) (hiS : iE.scalarOnly = true) (k : Nat) (hk : k < (vv v).length) (hvk : (vv v).getD k 0 = a)
    (hvlist : ∀ w ∈ vv v, s64.valid w = true) (hd : iE.denote env = some (k : Int)) (hk31 : k < M31)
    (hx : vdenM mv vv env vE = some x) (hsum : s64.valid (a + x) = true) (hvs : vE.scalarOnly = true) :
    vdenM mv vv env (.binary s64 .add (.read s64 (.local v) iE) vE) = some (a + x) := by
  have hrd : vdenM mv vv env (.read s64 (.local v) iE) = some a := by
    apply rdM_val mv vv env v hv s64 hty.symm iE hiS (by simp [NExpr.scalarOnly]) k hd a
    · rw [← hvk]; exact vec_getI (vv v) k hk
    · rw [hty]; rw [← hvk]; exact hvlist _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _)
  rw [vdenM_binary _ _ _ _ _ _ _ (by simp [NExpr.scalarOnly, hvs]), hrd, hx, Option.bind_some, Option.bind_some]
  exact conv_signed s64 rfl rfl _ hsum

end Proofs.BeatsExec
