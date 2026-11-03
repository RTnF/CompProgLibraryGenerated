import Proofs.BeatsExecP0
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.BellmanFordExec

/-- `(long long)e` of a scalar expression whose value is representable. -/
theorem den_castw (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (e : NExpr) (a : Int)
    (he : vdenM mv vv env e = some a) (hes : e.scalarOnly = true) (hv : s64.valid a = true) :
    vdenM mv vv env (.cast s64 e) = some a := by
  have hs : (NExpr.cast s64 e).scalarOnly = true := by simp [NExpr.scalarOnly, hes]
  rw [vdenM_scalar _ _ _ _ hs, den_cast, ← vdenM_scalar mv vv env e hes, he]
  simp
  exact conv_s64 _ hv

end Proofs.BeatsExec
