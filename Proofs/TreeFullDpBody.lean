import Proofs.SegmentTreeExec
import Proofs.Generated.TreeFullDp

namespace Proofs.TreeFullDpBody
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.ForLoopC (gS_takeC)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.InvGcdExec (vS)
open Proofs.SegmentTreeExec (AppBlk)

/-! ### `tree_full_dp` (nv = 9: head, target, parent, ord, dp, pre, suf, up, full).
Cells: 0 = root, 1 = n. -/

abbrev vI (nv k : Nat) : NExpr := .variable i32 (nv + k)
abbrev rdI (j : Nat) (e : NExpr) : NExpr := .read i32 (.local j) (.cast u64 e)
abbrev rdS (j : Nat) (e : NExpr) : NExpr := .read s64 (.local j) (.cast u64 e)
abbrev wrS (j : Nat) (i v : NExpr) : NStmt := .write (.local j) s64 (.cast u64 i) v
abbrev lit1 : NExpr := .literal i32 1
abbrev zeroS : NExpr := .cast s64 (.literal i32 0)
abbrev succS (nv k : Nat) : NExpr := .binary s64 .add (vS nv k) (.cast s64 (.literal i32 1))
abbrev incI (nv k : Nat) : NStmt := .assign (nv + k) i32 (.binary i32 .add (vI nv k) lit1)
abbrev decI (nv k : Nat) : NStmt := .assign (nv + k) i32 (.binary i32 .sub (vI nv k) lit1)
abbrev isChild (nv v w : Nat) : NExpr := .binary bT .eq (rdI 2 (vI nv w)) (vI nv v)

-- bottom-up: the forward arc loop (`pre`)
abbrev I1act (nv : Nat) : Command :=
  .sequence (.primitive (wrS 5 (vI nv 6) (vS nv 5)))
    (AppBlk nv 8 (vS nv 5) (rdS 4 (vI nv 7)) (.sequence (.primitive (.assign (nv + 5) s64 (vS nv 11))) Sk))
abbrev I1iter (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 1 (vI nv 6))))
    (.sequence (.branch (isChild nv 3 7) (.sequence (.scope (I1act nv)) Sk) Sk) Sk)
abbrev I1body (nv : Nat) : Command := .sequence (.scope (I1iter nv)) (.sequence (.primitive (incI nv 6)) Sk)
abbrev I1cond (nv : Nat) : NExpr := .binary bT .lt (vI nv 6) (rdI 0 (.binary i32 .add (vI nv 3) lit1))
abbrev Inner1 (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 0 (vI nv 3)))) (.sequence (.whileLoop (I1cond nv) (I1body nv)) Sk)

-- bottom-up: the backward arc loop (`suf`)
abbrev I2act (nv : Nat) : Command :=
  .sequence (.primitive (wrS 6 (vI nv 10) (vS nv 9)))
    (AppBlk nv 12 (vS nv 9) (rdS 4 (vI nv 11)) (.sequence (.primitive (.assign (nv + 9) s64 (vS nv 15))) Sk))
abbrev I2iter (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 1 (vI nv 10))))
    (.sequence (.branch (isChild nv 3 11) (.sequence (.scope (I2act nv)) Sk) Sk) Sk)
abbrev I2body (nv : Nat) : Command := .sequence (.scope (I2iter nv)) (.sequence (.primitive (decI nv 10)) Sk)
abbrev I2cond (nv : Nat) : NExpr := .binary bT .ge (vI nv 10) (rdI 0 (vI nv 3))
abbrev Inner2 (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.binary i32 .sub (rdI 0 (.binary i32 .add (vI nv 3) lit1)) lit1)))
    (.sequence (.whileLoop (I2cond nv) (I2body nv)) Sk)

abbrev BUiter (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 3 (vI nv 2))))
    (.sequence (.primitive (.declare s64 true zeroS))
      (.sequence (.primitive (.declare s64 true (vS nv 4)))
        (.sequence (.scope (Inner1 nv))
          (.sequence (.primitive (wrS 8 (vI nv 3) (vS nv 5)))
            (.sequence (.primitive (.declare s64 true (vS nv 5)))
              (.sequence (.primitive (.declare s64 true (succS nv 6)))
                (.sequence (.primitive (wrS 4 (vI nv 3) (vS nv 7)))
                  (.sequence (.primitive (.declare s64 true zeroS))
                    (.sequence (.primitive (.declare s64 true (vS nv 8)))
                      (.sequence (.scope (Inner2 nv)) Sk))))))))))
abbrev BUbody (nv : Nat) : Command := .sequence (.scope (BUiter nv)) (.sequence (.primitive (decI nv 2)) Sk)
abbrev BUouter (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.binary i32 .sub (vI nv 1) lit1)))
    (.sequence (.whileLoop (.binary bT .ge (vI nv 2) (.literal i32 0)) (BUbody nv)) Sk)

-- top-down
abbrev TD2act (nv : Nat) : Command :=
  AppBlk nv 14 (rdS 7 (vI nv 4)) (rdS 5 (vI nv 12))
    (AppBlk nv 18 (vS nv 17) (rdS 6 (vI nv 12))
      (.sequence (.primitive (.declare s64 true (vS nv 21)))
        (.sequence (.primitive (.declare s64 true (succS nv 22)))
          (.sequence (.primitive (wrS 7 (vI nv 13) (vS nv 23))) Sk))))
abbrev TD2iter (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 1 (vI nv 12))))
    (.sequence (.branch (isChild nv 4 13) (.sequence (.scope (TD2act nv)) Sk) Sk) Sk)
abbrev TD2body (nv : Nat) : Command := .sequence (.scope (TD2iter nv)) (.sequence (.primitive (incI nv 12)) Sk)
abbrev TD2cond (nv : Nat) : NExpr := .binary bT .lt (vI nv 12) (rdI 0 (.binary i32 .add (vI nv 4) lit1))
abbrev TD2 (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 0 (vI nv 4)))) (.sequence (.whileLoop (TD2cond nv) (TD2body nv)) Sk)
abbrev TDiter (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (rdI 3 (vI nv 3))))
    (.sequence (.primitive (.declare s64 true (rdS 8 (vI nv 4))))
      (AppBlk nv 6 (rdS 7 (vI nv 4)) (vS nv 5)
        (.sequence (.primitive (.declare s64 true (vS nv 9)))
          (.sequence (.primitive (.declare s64 true (succS nv 10)))
            (.sequence (.primitive (wrS 8 (vI nv 4) (vS nv 11)))
              (.sequence (.scope (TD2 nv)) Sk))))))
abbrev TDbody (nv : Nat) : Command := .sequence (.scope (TDiter nv)) (.sequence (.primitive (incI nv 3)) Sk)
abbrev TDouter (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.literal i32 0))) (.sequence (.whileLoop (.binary bT .lt (vI nv 3) (vI nv 1)) (TDbody nv)) Sk)

abbrev bodyFD (nv : Nat) : Command :=
  .sequence (.scope (BUouter nv))
    (.sequence (.primitive (.declare s64 true zeroS))
      (.sequence (.primitive (wrS 7 (vI nv 0) (vS nv 2)))
        (.sequence (.scope (TDouter nv)) Sk)))

theorem body_eqFD : Proofs.TreeFullDpInstance.tree_full_dp_std_vector_int.body = bodyFD 9 := rfl

end Proofs.TreeFullDpBody
