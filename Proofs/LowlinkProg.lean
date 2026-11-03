import Proofs.DijkstraExec
import Proofs.Generated.Lowlink

namespace Proofs.LowlinkProg
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

/-! The program of `lowlink`: vectors `0 = head`, `1 = target`, `2 = ord`, `3 = low`, `4 = par`, `5 = sep`, `6 = it`,
`7 = stk` (so `nv = 8`); scalar cells (variable `nv + c`): `0 = n`, `1 = cnt`, `2 = r`, `3 = sp`, `4 = v`, `5 = e` (or `p`),
`6 = w`. -/

abbrev one : NExpr := .literal i32 1
abbrev vr (nv j : Nat) : NExpr := .variable i32 (nv + j)
abbrev ixc (nv j : Nat) : NExpr := .cast u64 (.variable i32 (nv + j))
abbrev rdv (nv k j : Nat) : NExpr := .read i32 (.local k) (ixc nv j)
abbrev wrv (nv k j : Nat) (e : NExpr) : NStmt := .write (.local k) i32 (ixc nv j) e
abbrev ltE (a b : NExpr) : NExpr := .binary bT .lt a b

abbrev cRoot (nv : Nat) : NExpr := ltE (rdv nv 2 2) lit0
abbrev sOrdR (nv : Nat) : NStmt := wrv nv 2 2 (vr nv 1)
abbrev sLowR (nv : Nat) : NStmt := wrv nv 3 2 (vr nv 1)
abbrev aCnt (nv : Nat) : NStmt := .assign (nv + 1) i32 (.binary i32 .add (vr nv 1) one)
abbrev sItR (nv : Nat) : NStmt := wrv nv 6 2 (rdv nv 0 2)
abbrev sStk0 (nv : Nat) : NStmt := .write (.local 7) i32 (.cast u64 lit0) (vr nv 2)
abbrev dSp : NStmt := .declare i32 true one
abbrev cSp (nv : Nat) : NExpr := .binary bT .gt (vr nv 3) lit0
abbrev idxTop (nv : Nat) : NExpr := .cast u64 (.binary i32 .sub (vr nv 3) one)
abbrev dV (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 7) (idxTop nv))
abbrev idxV1 (nv : Nat) : NExpr := .cast u64 (.binary i32 .add (vr nv 4) one)
abbrev cIt (nv : Nat) : NExpr := ltE (rdv nv 6 4) (.read i32 (.local 0) (idxV1 nv))
abbrev dE (nv : Nat) : NStmt := .declare i32 true (rdv nv 6 4)
abbrev dW (nv : Nat) : NStmt := .declare i32 true (rdv nv 1 5)
abbrev sIt1 (nv : Nat) : NStmt := wrv nv 6 4 (.binary i32 .add (vr nv 5) one)
abbrev cNew (nv : Nat) : NExpr := ltE (rdv nv 2 6) lit0
abbrev wPar (nv : Nat) : NStmt := wrv nv 4 6 (vr nv 4)
abbrev wOrdW (nv : Nat) : NStmt := wrv nv 2 6 (vr nv 1)
abbrev wLowW (nv : Nat) : NStmt := wrv nv 3 6 (vr nv 1)
abbrev wItW (nv : Nat) : NStmt := wrv nv 6 6 (rdv nv 0 6)
abbrev wStkW (nv : Nat) : NStmt := .write (.local 7) i32 (ixc nv 3) (vr nv 6)
abbrev aSp1 (nv : Nat) : NStmt := .assign (nv + 3) i32 (.binary i32 .add (vr nv 3) one)
abbrev cPar (nv : Nat) : NExpr := .binary bT .ne (vr nv 6) (rdv nv 4 4)
abbrev cLow (nv : Nat) : NExpr := ltE (rdv nv 2 6) (rdv nv 3 4)
abbrev sLowU (nv : Nat) : NStmt := wrv nv 3 4 (rdv nv 2 6)
abbrev aSp0 (nv : Nat) : NStmt := .assign (nv + 3) i32 (.binary i32 .sub (vr nv 3) one)
abbrev cLP (nv : Nat) : NExpr := ltE (rdv nv 3 4) (rdv nv 3 5)
abbrev sLowP (nv : Nat) : NStmt := wrv nv 3 5 (rdv nv 3 4)
abbrev cSep (nv : Nat) : NExpr := .binary bT .le (rdv nv 2 5) (rdv nv 3 4)
abbrev sSep (nv : Nat) : NStmt := wrv nv 5 5 (.binary i32 .add (rdv nv 5 5) one)

/-- `if (c) { s; }` -/
abbrev CWb (c : NExpr) (s : NStmt) : Command := .branch c (.sequence (.scope (.sequence (.primitive s) Sk)) Sk) Sk

abbrev PUSHB (nv : Nat) : Command := .sequence (.primitive (wPar nv)) (.sequence (.primitive (wOrdW nv))
  (.sequence (.primitive (wLowW nv)) (.sequence (.primitive (aCnt nv)) (.sequence (.primitive (wItW nv))
  (.sequence (.primitive (wStkW nv)) (.sequence (.primitive (aSp1 nv)) Sk))))))
abbrev PUSHT (nv : Nat) : Command := .sequence (.scope (PUSHB nv)) Sk
abbrev BK2 (nv : Nat) : Command := .sequence (.scope (.sequence (CWb (cLow nv) (sLowU nv)) Sk)) Sk
abbrev BACKE (nv : Nat) : Command := .sequence (.scope (.sequence (.branch (cPar nv) (BK2 nv) Sk) Sk)) Sk
abbrev THENS (nv : Nat) : Command := .sequence (.primitive (dE nv)) (.sequence (.primitive (dW nv))
  (.sequence (.primitive (sIt1 nv)) (.sequence (.branch (cNew nv) (PUSHT nv) (BACKE nv)) Sk)))
abbrev THENB (nv : Nat) : Command := .sequence (.scope (THENS nv)) Sk
abbrev PCS (nv : Nat) : Command := .sequence (.primitive (dV nv)) (.sequence (CWb (cLP nv) (sLowP nv))
  (.sequence (CWb (cSep nv) (sSep nv)) Sk))
abbrev POPC (nv : Nat) : Command := .sequence (.scope (PCS nv)) Sk
abbrev POPS (nv : Nat) : Command := .sequence (.primitive (aSp0 nv)) (.sequence (.branch (cSp nv) (POPC nv) Sk) Sk)
abbrev POPB (nv : Nat) : Command := .sequence (.scope (POPS nv)) Sk
abbrev WSC (nv : Nat) : Command := .sequence (.primitive (dV nv)) (.sequence (.branch (cIt nv) (THENB nv) (POPB nv)) Sk)
abbrev WBODY (nv : Nat) : Command := .sequence (.scope (WSC nv)) Sk
abbrev WH (nv : Nat) : Command := .whileLoop (cSp nv) (WBODY nv)
abbrev ROOTB (nv : Nat) : Command := .sequence (.primitive (sOrdR nv)) (.sequence (.primitive (sLowR nv))
  (.sequence (.primitive (aCnt nv)) (.sequence (.primitive (sItR nv)) (.sequence (.primitive (sStk0 nv))
  (.sequence (.primitive dSp) (.sequence (WH nv) Sk))))))
abbrev ROOTT (nv : Nat) : Command := .sequence (.scope (ROOTB nv)) Sk
abbrev BOUT (nv : Nat) : Command := .sequence (.branch (cRoot nv) (ROOTT nv) Sk) Sk
abbrev progLL (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true lit0)) (.sequence (forStmtB nv 2 0 (BOUT nv)) Sk)

theorem body_eqLL : Proofs.LowlinkInstance.lowlink.body = progLL 8 := rfl

end Proofs.LowlinkProg
