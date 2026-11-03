import Proofs.DijkstraExec
import Proofs.Generated.FindCycle

namespace Proofs.FindCycleProg
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getM vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false cs)
open Proofs.DijkstraScan
open Proofs.DijkstraExec

/-! The program of `find_cycle`: vectors `0 = head`, `1 = target`, `2 = state`, `3 = it`, `4 = stk`, `5 = cyc` (`nv = 6`);
scalar cells (variable `nv + c`): `0 = n`, `1 = fsp`, `2 = fw`, `3 = r` (later `k`), `4 = sp` (later `j`), `5 = v` (later `t`),
`6 = e`, `7 = w`. -/

abbrev one : NExpr := .literal i32 1
abbrev two : NExpr := .literal i32 2
abbrev vr (nv j : Nat) : NExpr := .variable i32 (nv + j)
abbrev ixc (nv j : Nat) : NExpr := .cast u64 (.variable i32 (nv + j))
abbrev rdv (nv k j : Nat) : NExpr := .read i32 (.local k) (ixc nv j)
abbrev wrv (nv k j : Nat) (e : NExpr) : NStmt := .write (.local k) i32 (ixc nv j) e
abbrev eqE (a b : NExpr) : NExpr := .binary bT .eq a b
abbrev ltE (a b : NExpr) : NExpr := .binary bT .lt a b
abbrev gtE (a b : NExpr) : NExpr := .binary bT .gt a b

abbrev cF0 (nv : Nat) : NExpr := eqE (vr nv 1) lit0
abbrev cSt0 (nv : Nat) : NExpr := eqE (rdv nv 2 3) lit0
abbrev sSt1R (nv : Nat) : NStmt := wrv nv 2 3 one
abbrev sItR (nv : Nat) : NStmt := wrv nv 3 3 (rdv nv 0 3)
abbrev sStk0 (nv : Nat) : NStmt := .write (.local 4) i32 (.cast u64 lit0) (vr nv 3)
abbrev dSp : NStmt := .declare i32 true one
abbrev cSp (nv : Nat) : NExpr := gtE (vr nv 4) lit0
abbrev idxTop (nv : Nat) : NExpr := .cast u64 (.binary i32 .sub (vr nv 4) one)
abbrev dV (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 4) (idxTop nv))
abbrev idxV1 (nv : Nat) : NExpr := .cast u64 (.binary i32 .add (vr nv 5) one)
abbrev cIt (nv : Nat) : NExpr := ltE (rdv nv 3 5) (.read i32 (.local 0) (idxV1 nv))
abbrev dE (nv : Nat) : NStmt := .declare i32 true (rdv nv 3 5)
abbrev dW (nv : Nat) : NStmt := .declare i32 true (rdv nv 1 6)
abbrev sIt1 (nv : Nat) : NStmt := wrv nv 3 5 (.binary i32 .add (vr nv 6) one)
abbrev cWh (nv : Nat) : NExpr := eqE (rdv nv 2 7) lit0
abbrev wSt1 (nv : Nat) : NStmt := wrv nv 2 7 one
abbrev wItW (nv : Nat) : NStmt := wrv nv 3 7 (rdv nv 0 7)
abbrev wStkW (nv : Nat) : NStmt := .write (.local 4) i32 (ixc nv 4) (vr nv 7)
abbrev aSp1 (nv : Nat) : NStmt := .assign (nv + 4) i32 (.binary i32 .add (vr nv 4) one)
abbrev cGr (nv : Nat) : NExpr := eqE (rdv nv 2 7) one
abbrev aFsp (nv : Nat) : NStmt := .assign (nv + 1) i32 (vr nv 4)
abbrev aFw (nv : Nat) : NStmt := .assign (nv + 2) i32 (vr nv 7)
abbrev aSp0 (nv : Nat) : NStmt := .assign (nv + 4) i32 lit0
abbrev wSt2 (nv : Nat) : NStmt := wrv nv 2 5 two
abbrev aSpD (nv : Nat) : NStmt := .assign (nv + 4) i32 (.binary i32 .sub (vr nv 4) one)

abbrev PUSHB (nv : Nat) : Command := .sequence (.primitive (wSt1 nv)) (.sequence (.primitive (wItW nv))
  (.sequence (.primitive (wStkW nv)) (.sequence (.primitive (aSp1 nv)) Sk)))
abbrev PUSHT (nv : Nat) : Command := .sequence (.scope (PUSHB nv)) Sk
abbrev FNB (nv : Nat) : Command := .sequence (.primitive (aFsp nv)) (.sequence (.primitive (aFw nv))
  (.sequence (.primitive (aSp0 nv)) Sk))
abbrev FND (nv : Nat) : Command := .sequence (.scope (FNB nv)) Sk
abbrev ELB (nv : Nat) : Command := .sequence (.branch (cGr nv) (FND nv) Sk) Sk
abbrev ELS (nv : Nat) : Command := .sequence (.scope (ELB nv)) Sk
abbrev THENS (nv : Nat) : Command := .sequence (.primitive (dE nv)) (.sequence (.primitive (dW nv))
  (.sequence (.primitive (sIt1 nv)) (.sequence (.branch (cWh nv) (PUSHT nv) (ELS nv)) Sk)))
abbrev THENB (nv : Nat) : Command := .sequence (.scope (THENS nv)) Sk
abbrev POPS (nv : Nat) : Command := .sequence (.primitive (wSt2 nv)) (.sequence (.primitive (aSpD nv)) Sk)
abbrev POPB (nv : Nat) : Command := .sequence (.scope (POPS nv)) Sk
abbrev WSC (nv : Nat) : Command := .sequence (.primitive (dV nv)) (.sequence (.branch (cIt nv) (THENB nv) (POPB nv)) Sk)
abbrev WBODY (nv : Nat) : Command := .sequence (.scope (WSC nv)) Sk
abbrev WH (nv : Nat) : Command := .whileLoop (cSp nv) (WBODY nv)
abbrev R2B (nv : Nat) : Command := .sequence (.primitive (sSt1R nv)) (.sequence (.primitive (sItR nv))
  (.sequence (.primitive (sStk0 nv)) (.sequence (.primitive dSp) (.sequence (WH nv) Sk))))
abbrev R2 (nv : Nat) : Command := .sequence (.scope (R2B nv)) Sk
abbrev R1B (nv : Nat) : Command := .sequence (.branch (cSt0 nv) (R2 nv) Sk) Sk
abbrev R1 (nv : Nat) : Command := .sequence (.scope (R1B nv)) Sk
abbrev BO (nv : Nat) : Command := .sequence (.branch (cF0 nv) (R1 nv) Sk) Sk

abbrev dJ (nv : Nat) : NStmt := .declare i32 true (.binary i32 .sub (vr nv 1) one)
abbrev cJ (nv : Nat) : NExpr := .binary bT .ne (rdv nv 4 4) (vr nv 2)
abbrev aJd (nv : Nat) : NStmt := .assign (nv + 4) i32 (.binary i32 .sub (vr nv 4) one)
abbrev WJ (nv : Nat) : Command := .whileLoop (cJ nv) (.sequence (.scope (.sequence (.primitive (aJd nv)) Sk)) Sk)
abbrev aK (nv : Nat) : NStmt := .assign (nv + 3) i32 (.binary i32 .sub (vr nv 1) (vr nv 4))
abbrev dT : NStmt := .declare i32 true lit0
abbrev cT (nv : Nat) : NExpr := ltE (vr nv 5) (vr nv 3)
abbrev wCyc (nv : Nat) : NStmt := wrv nv 5 5 (.read i32 (.local 4) (.cast u64 (.binary i32 .add (vr nv 4) (vr nv 5))))
abbrev aT1 (nv : Nat) : NStmt := .assign (nv + 5) i32 (.binary i32 .add (vr nv 5) one)
abbrev WC (nv : Nat) : Command :=
  .whileLoop (cT nv) (.sequence (.scope (.sequence (.primitive (wCyc nv)) Sk)) (.sequence (.primitive (aT1 nv)) Sk))
abbrev CPB (nv : Nat) : Command := .sequence (.primitive dT) (.sequence (WC nv) Sk)
abbrev EXB (nv : Nat) : Command := .sequence (.primitive (dJ nv)) (.sequence (WJ nv)
  (.sequence (.primitive (aK nv)) (.sequence (.scope (CPB nv)) Sk)))
abbrev EXT (nv : Nat) : Command := .sequence (.scope (EXB nv)) Sk
abbrev progFC (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true lit0)) (.sequence (.primitive (.declare i32 true lit0))
    (.sequence (forStmtB nv 3 0 (BO nv)) (.sequence (.primitive (.declare i32 true lit0))
      (.sequence (.branch (gtE (vr nv 1) lit0) (EXT nv) Sk) (.sequence (.primitive (.ret (vr nv 3))) Sk)))))

theorem body_eqFC : Proofs.FindCycleInstance.find_cycle.body = progFC 6 := rfl

end Proofs.FindCycleProg
