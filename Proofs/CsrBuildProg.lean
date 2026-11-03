import Proofs.DijkstraOldExec
import Proofs.Generated.CsrBuild

namespace Proofs.CsrBuildProg
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.DijkstraOldScan
open Proofs.DijkstraOldExec

/-! The program of `csr_build`: vectors `0 = from`, `1 = to`, `2 = head`, `3 = target`, `4 = pos` (`nv = 5`); cells
(variable `nv + c`): `0 = n`, `1 = m`, `2 = i` (or `v`), `3 = f`, `4 = p`. -/

abbrev one : NExpr := .literal i32 1
abbrev vr (nv j : Nat) : NExpr := .variable i32 (nv + j)
abbrev ixc (nv j : Nat) : NExpr := .cast u64 (.variable i32 (nv + j))
abbrev rdv (nv k j : Nat) : NExpr := .read i32 (.local k) (ixc nv j)
abbrev idxF1 (nv : Nat) : NExpr := .cast u64 (.binary i32 .add (vr nv 3) one)
abbrev idxV1 (nv : Nat) : NExpr := .cast u64 (.binary i32 .add (vr nv 2) one)
abbrev dM (nv : Nat) : NStmt := .declare i32 true (.cast i32 (.size (.integer i32) (.local 0)))
abbrev dF (nv : Nat) : NStmt := .declare i32 true (rdv nv 0 2)
abbrev wH1 (nv : Nat) : NStmt :=
  .write (.local 2) i32 (idxF1 nv) (.binary i32 .add (.read i32 (.local 2) (idxF1 nv)) one)
abbrev B1 (nv : Nat) : Command := .sequence (.primitive (dF nv)) (.sequence (.primitive (wH1 nv)) Sk)
abbrev wH2 (nv : Nat) : NStmt :=
  .write (.local 2) i32 (idxV1 nv) (.binary i32 .add (.read i32 (.local 2) (idxV1 nv)) (rdv nv 2 2))
abbrev B2 (nv : Nat) : Command := .sequence (.primitive (wH2 nv)) Sk
abbrev wP3 (nv : Nat) : NStmt := .write (.local 4) i32 (ixc nv 2) (rdv nv 2 2)
abbrev B3 (nv : Nat) : Command := .sequence (.primitive (wP3 nv)) Sk
abbrev dP (nv : Nat) : NStmt := .declare i32 true (rdv nv 4 3)
abbrev wT (nv : Nat) : NStmt := .write (.local 3) i32 (ixc nv 4) (rdv nv 1 2)
abbrev wP4 (nv : Nat) : NStmt := .write (.local 4) i32 (ixc nv 3) (.binary i32 .add (vr nv 4) one)
abbrev B4 (nv : Nat) : Command := .sequence (.primitive (dF nv)) (.sequence (.primitive (dP nv))
  (.sequence (.primitive (wT nv)) (.sequence (.primitive (wP4 nv)) Sk)))
abbrev progCB (nv : Nat) : Command :=
  .sequence (.primitive (dM nv)) (.sequence (forStmtB nv 2 1 (B1 nv)) (.sequence (forStmtB nv 2 0 (B2 nv))
    (.sequence (forStmtB nv 2 0 (B3 nv)) (.sequence (forStmtB nv 2 1 (B4 nv)) Sk))))

theorem body_eqCB : Proofs.CsrBuildInstance.csr_build.body = progCB 5 := rfl

end Proofs.CsrBuildProg
