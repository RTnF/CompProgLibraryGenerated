import Proofs.BeatsExecU0
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.IntSim Proofs.QuotientSearch
open Proofs.VectorSumCall (conv_signed)
open Proofs.BellmanFordExec

/-- `l && r` of two comparisons, as a 0/1 value. -/
theorem den_andw (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (l r : NExpr) (P Q : Prop) [Decidable P] [Decidable Q]
    (hl : vdenM mv vv env l = some (if P then 1 else 0)) (hr : vdenM mv vv env r = some (if Q then 1 else 0))
    (hls : l.scalarOnly = true) (hrs : r.scalarOnly = true) :
    vdenM mv vv env (.logical true l r) = some (if P ∧ Q then 1 else 0) := by
  have hs : (NExpr.logical true l r).scalarOnly = true := by simp [NExpr.scalarOnly, hls, hrs]
  rw [vdenM_scalar _ _ _ _ hs, Proofs.CountrZeroExec.den_and, ← vdenM_scalar mv vv env l hls, hl]
  by_cases hp : P
  · by_cases hq : Q
    · simp [hp, hq, ← vdenM_scalar mv vv env r hrs, hr]
    · simp [hp, hq, ← vdenM_scalar mv vv env r hrs, hr]
  · simp [hp]

/-- `-e` for `long long`. -/
theorem den_negw (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (e : NExpr) (a : Int)
    (he : vdenM mv vv env e = some a) (hes : e.scalarOnly = true) (hv : s64.valid (-a) = true) :
    vdenM mv vv env (.unary s64 .neg e) = some (-a) := by
  have hs : (NExpr.unary s64 .neg e).scalarOnly = true := by simp [NExpr.scalarOnly, hes]
  rw [vdenM_scalar _ _ _ _ hs, Proofs.BellmanFordPExec.den_unaryP, ← vdenM_scalar mv vv env e hes, he]
  simp [unaryValue]
  exact conv_s64 _ hv

/-- `(long long)(literal int)`. -/
theorem den_castlit (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (n : Int)
    (h1 : i32.valid n = true) (h2 : s64.valid n = true) :
    vdenM mv vv env (.cast s64 (.literal i32 n)) = some n := by
  have hs : (NExpr.cast s64 (.literal i32 n)).scalarOnly = true := by simp [NExpr.scalarOnly]
  rw [vdenM_scalar _ _ _ _ hs, den_cast]
  simp only [den_literal, if_pos h1]
  simp
  exact conv_s64 _ h2

end Proofs.BeatsExec
