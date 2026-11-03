import Proofs.BeatsExec_CalcLoopCh0
import Proofs.BeatsExec_CalcLoopCh1
import Proofs.BeatsExec_CalcLoopCh2
import Proofs.BeatsExec_CalcLoopCh3
import Proofs.BeatsExec_CalcLoopCh4
import Proofs.BeatsExec_CalcLoopCh5
import Proofs.BeatsExec_CalcLoopCh6
import Proofs.BeatsExec_CalcLoopCh7
import Proofs.BeatsExec_CalcLoopCh8
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
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem CalcLoop_body (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (b : BS) (P : List Cell)
    (inf : Int) (n op qa qb sp : Nat) (x : Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hopM : op < M31) (hqaM : qa < M31) (hqbM : qb < M31) (hspM : sp < M31) (hpos : 0 < sp) (hx : s64.valid x = true) (hvl0 : ∀ w ∈ b.mxv, s64.valid w = true) (hvl1 : ∀ w ∈ b.smx, s64.valid w = true) (hvl2 : ∀ w ∈ b.mxc, s64.valid w = true) (hvl3 : ∀ w ∈ b.mnv, s64.valid w = true) (hvl4 : ∀ w ∈ b.smn, s64.valid w = true) (hvl5 : ∀ w ∈ b.mnc, s64.valid w = true) (hvl6 : ∀ w ∈ b.len, s64.valid w = true) (hvl7 : ∀ w ∈ b.ladd, s64.valid w = true) (hvl8 : ∀ w ∈ b.lval, s64.valid w = true) (hvl11 : ∀ w ∈ b.sk, i32.valid w = true) (hvl12 : ∀ w ∈ b.sl, i32.valid w = true) (hvl13 : ∀ w ∈ b.sr, i32.valid w = true) (W0 : Nat) (hNW0 : W0 < M31) (hD_W0 : b.sk.getD (sp - 1) 0 = (W0 : Int)) (W1 : Nat) (hNW1 : W1 < M31) (hD_W1 : b.sl.getD (sp - 1) 0 = (W1 : Int)) (W2 : Nat) (hNW2 : W2 < M31) (hD_W2 : b.sr.getD (sp - 1) 0 = (W2 : Int)) (Z3 : Int) (hD_Z3 : b.mxv.getD W0 0 = Z3) (Z4 : Int) (hD_Z4 : b.mnv.getD W0 0 = Z4) (Z5 : Int) (hD_Z5 : b.lval.getD W0 0 = Z5) (Z6 : Int) (hD_Z6 : b.ladd.getD W0 0 = Z6) (Z7 : Int) (hD_Z7 : b.mxv.getD (2 * W0 + 1) 0 = Z7) (Z8 : Int) (hD_Z8 : b.smx.getD (2 * W0 + 1) 0 = Z8) (Z9 : Int) (hD_Z9 : b.mxc.getD (2 * W0 + 1) 0 = Z9) (Z10 : Int) (hD_Z10 : b.mnv.getD (2 * W0 + 1) 0 = Z10) (Z11 : Int) (hD_Z11 : b.smn.getD (2 * W0 + 1) 0 = Z11) (Z12 : Int) (hD_Z12 : b.mnc.getD (2 * W0 + 1) 0 = Z12) (Z13 : Int) (hD_Z13 : b.ladd.getD (2 * W0 + 1) 0 = Z13) (Z14 : Int) (hD_Z14 : b.lval.getD (2 * W0 + 1) 0 = Z14) (Z15 : Int) (hD_Z15 : b.len.getD (2 * W0 + 1) 0 = Z15) (Z16 : Int) (hD_Z16 : b.mxv.getD (2 * W0 + 2) 0 = Z16) (Z17 : Int) (hD_Z17 : b.smx.getD (2 * W0 + 2) 0 = Z17) (Z18 : Int) (hD_Z18 : b.mxc.getD (2 * W0 + 2) 0 = Z18) (Z19 : Int) (hD_Z19 : b.mnv.getD (2 * W0 + 2) 0 = Z19) (Z20 : Int) (hD_Z20 : b.smn.getD (2 * W0 + 2) 0 = Z20) (Z21 : Int) (hD_Z21 : b.mnc.getD (2 * W0 + 2) 0 = Z21) (Z22 : Int) (hD_Z22 : b.ladd.getD (2 * W0 + 2) 0 = Z22) (Z23 : Int) (hD_Z23 : b.lval.getD (2 * W0 + 2) 0 = Z23) (Z24 : Int) (hD_Z24 : b.len.getD (2 * W0 + 2) 0 = Z24) (hl11_0 : (sp - 1) < (b.sk).length) (hl12_1 : (sp - 1) < (b.sl).length) (hl13_2 : (sp - 1) < (b.sr).length) (hl0_3 : W0 < (b.mxv).length) (hl3_4 : W0 < (b.mnv).length) (hl8_5 : W0 < (b.lval).length) (hl7_6 : W0 < (b.ladd).length) (hl0_7 : (2 * W0 + 1) < (b.mxv).length) (hl1_8 : (2 * W0 + 1) < (b.smx).length) (hl2_9 : (2 * W0 + 1) < (b.mxc).length) (hl3_10 : (2 * W0 + 1) < (b.mnv).length) (hl4_11 : (2 * W0 + 1) < (b.smn).length) (hl5_12 : (2 * W0 + 1) < (b.mnc).length) (hl7_13 : (2 * W0 + 1) < (b.ladd).length) (hl8_14 : (2 * W0 + 1) < (b.lval).length) (hl6_15 : (2 * W0 + 1) < (b.len).length) (hl0_16 : (2 * W0 + 2) < (b.mxv).length) (hl1_17 : (2 * W0 + 2) < (b.smx).length) (hl2_18 : (2 * W0 + 2) < (b.mxc).length) (hl3_19 : (2 * W0 + 2) < (b.mnv).length) (hl4_20 : (2 * W0 + 2) < (b.smn).length) (hl5_21 : (2 * W0 + 2) < (b.mnc).length) (hl7_22 : (2 * W0 + 2) < (b.ladd).length) (hl8_23 : (2 * W0 + 2) < (b.lval).length) (hl6_24 : (2 * W0 + 2) < (b.len).length) (hl11_25 : ((sp - 1) + 1) < (b.sk).length) (hl12_26 : ((sp - 1) + 1) < (b.sl).length) (hl13_27 : ((sp - 1) + 1) < (b.sr).length) (hk1_W0 : (2 * W0 + 1) < M31) (hk2_W0 : (2 * W0 + 2) < M31) (hix2 : ((sp - 1) + 1) < M31) (hix3 : ((sp - 1) + 1) < M31) (hix4 : ((sp - 1) + 1) < M31) (X0 : Int) (hX0 : X0 = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0)) (X1 : Int) (hX1 : X1 = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0)) (X2 : Int) (hX2 : X2 = (if ((X0 = 0) ∧ (X1 = 1)) then 1 else 0)) (X3 : Int) (hX3 : X3 = (if ((X0 = 0) ∧ (X2 = 0)) then 1 else 0)) (X4 : Int) (hX4 : X4 = (if (((X2 = 1) ∧ ((op : Int) = 0)) ∧ (x < Z3)) then Z3 else x)) (X5 : Int) (hX5 : X5 = (if (((X2 = 1) ∧ ((op : Int) = 1)) ∧ (Z4 < X4)) then Z4 else X4)) (X6 : Int) (hX6 : X6 = (if ((X3 = 1) ∧ (Z5 ≠ inf)) then 1 else 0)) (X7 : Int) (hX7 : X7 = (if ((X3 = 1) ∧ (X6 = 0)) then Z6 else 0)) (X8 : Int) (hX8 : X8 = (if ((X3 = 1) ∧ (X6 = 0)) then 1 else 0)) (X9 : Int) (hX9 : X9 = (if (X6 = 1) then Z5 else Z7)) (X10 : Int) (hX10 : X10 = (if (X6 = 1) then (-inf) else Z8)) (X11 : Int) (hX11 : X11 = (if (X6 = 1) then Z15 else Z9)) (X12 : Int) (hX12 : X12 = (if (X6 = 1) then Z5 else Z10)) (X13 : Int) (hX13 : X13 = (if (X6 = 1) then inf else Z11)) (X14 : Int) (hX14 : X14 = (if (X6 = 1) then Z15 else Z12)) (X15 : Int) (hX15 : X15 = (if (X6 = 1) then 0 else Z13)) (X16 : Int) (hX16 : X16 = (if ((X6 = 1) ∧ (Z15 ≠ 1)) then Z5 else Z14)) (X17 : Int) (hX17 : X17 = (if (X10 ≠ (-inf)) then (X10 + X7) else X10)) (X18 : Int) (hX18 : X18 = (if (X13 ≠ inf) then (X13 + X7) else X13)) (X19 : Int) (hX19 : X19 = (if ((X16 = inf) ∧ (Z15 ≠ 1)) then (X15 + X7) else X15)) (X20 : Int) (hX20 : X20 = (if (X16 ≠ inf) then (X16 + X7) else X16)) (X21 : Int) (hX21 : X21 = (if ((X8 = 1) ∧ (Z3 < (X9 + X7))) then 1 else 0)) (X22 : Int) (hX22 : X22 = (if (X21 = 1) then Z3 else (X9 + X7))) (X23 : Int) (hX23 : X23 = (if ((X21 = 1) ∧ ((X9 + X7) = (X12 + X7))) then Z3 else (X12 + X7))) (X24 : Int) (hX24 : X24 = (if (((X21 = 1) ∧ ((X9 + X7) ≠ (X12 + X7))) ∧ ((X9 + X7) = X18)) then Z3 else X18)) (X25 : Int) (hX25 : X25 = (if (((X21 = 1) ∧ (X20 ≠ inf)) ∧ (Z3 < X20)) then Z3 else X20)) (X26 : Int) (hX26 : X26 = (if ((X8 = 1) ∧ (X23 < Z4)) then 1 else 0)) (X27 : Int) (hX27 : X27 = (if (X26 = 1) then Z4 else X23)) (X28 : Int) (hX28 : X28 = (if ((X26 = 1) ∧ (X22 = X23)) then Z4 else X22)) (X29 : Int) (hX29 : X29 = (if (((X26 = 1) ∧ (X22 ≠ X23)) ∧ (X17 = X23)) then Z4 else X17)) (X30 : Int) (hX30 : X30 = (if (((X26 = 1) ∧ (X25 ≠ inf)) ∧ (X25 < Z4)) then Z4 else X25)) (X31 : Int) (hX31 : X31 = (if (X6 = 1) then Z5 else Z16)) (X32 : Int) (hX32 : X32 = (if (X6 = 1) then (-inf) else Z17)) (X33 : Int) (hX33 : X33 = (if (X6 = 1) then Z24 else Z18)) (X34 : Int) (hX34 : X34 = (if (X6 = 1) then Z5 else Z19)) (X35 : Int) (hX35 : X35 = (if (X6 = 1) then inf else Z20)) (X36 : Int) (hX36 : X36 = (if (X6 = 1) then Z24 else Z21)) (X37 : Int) (hX37 : X37 = (if (X6 = 1) then 0 else Z22)) (X38 : Int) (hX38 : X38 = (if ((X6 = 1) ∧ (Z24 ≠ 1)) then Z5 else Z23)) (X39 : Int) (hX39 : X39 = (if (X32 ≠ (-inf)) then (X32 + X7) else X32)) (X40 : Int) (hX40 : X40 = (if (X35 ≠ inf) then (X35 + X7) else X35)) (X41 : Int) (hX41 : X41 = (if ((X38 = inf) ∧ (Z24 ≠ 1)) then (X37 + X7) else X37)) (X42 : Int) (hX42 : X42 = (if (X38 ≠ inf) then (X38 + X7) else X38)) (X43 : Int) (hX43 : X43 = (if ((X8 = 1) ∧ (Z3 < (X31 + X7))) then 1 else 0)) (X44 : Int) (hX44 : X44 = (if (X43 = 1) then Z3 else (X31 + X7))) (X45 : Int) (hX45 : X45 = (if ((X43 = 1) ∧ ((X31 + X7) = (X34 + X7))) then Z3 else (X34 + X7))) (X46 : Int) (hX46 : X46 = (if (((X43 = 1) ∧ ((X31 + X7) ≠ (X34 + X7))) ∧ ((X31 + X7) = X40)) then Z3 else X40)) (X47 : Int) (hX47 : X47 = (if (((X43 = 1) ∧ (X42 ≠ inf)) ∧ (Z3 < X42)) then Z3 else X42)) (X48 : Int) (hX48 : X48 = (if ((X8 = 1) ∧ (X45 < Z4)) then 1 else 0)) (X49 : Int) (hX49 : X49 = (if (X48 = 1) then Z4 else X45)) (X50 : Int) (hX50 : X50 = (if ((X48 = 1) ∧ (X44 = X45)) then Z4 else X44)) (X51 : Int) (hX51 : X51 = (if (((X48 = 1) ∧ (X44 ≠ X45)) ∧ (X39 = X45)) then Z4 else X39)) (X52 : Int) (hX52 : X52 = (if (((X48 = 1) ∧ (X47 ≠ inf)) ∧ (X47 < Z4)) then Z4 else X47)) (X53 : Int) (hX53 : X53 = (if (X3 = 1) then inf else Z5)) (X54 : Int) (hX54 : X54 = (if (X3 = 1) then 0 else Z6)) (X55 : Int) (hX55 : X55 = (((sp - 1 : Nat) : Int) + (2 * X3))) (hsc0 : i32.valid ((sp : Int) - 1) = true) (hsc1 : ((X6 = 1)) → s64.valid (-inf) = true) (hsc2 : s64.valid (X9 + X7) = true) (hsc3 : s64.valid (-inf) = true) (hsc4 : ((X10 ≠ (-inf))) → s64.valid (X10 + X7) = true) (hsc5 : s64.valid (X12 + X7) = true) (hsc6 : ((X13 ≠ inf)) → s64.valid (X13 + X7) = true) (hsc7 : (((X16 = inf) ∧ (Z15 ≠ 1))) → s64.valid (X15 + X7) = true) (hsc8 : ((X16 ≠ inf)) → s64.valid (X16 + X7) = true) (hsc9 : s64.valid (X31 + X7) = true) (hsc10 : ((X32 ≠ (-inf))) → s64.valid (X32 + X7) = true) (hsc11 : s64.valid (X34 + X7) = true) (hsc12 : ((X35 ≠ inf)) → s64.valid (X35 + X7) = true) (hsc13 : (((X38 = inf) ∧ (Z24 ≠ 1))) → s64.valid (X37 + X7) = true) (hsc14 : ((X38 ≠ inf)) → s64.valid (X38 + X7) = true) (hsc15 : i32.valid ((W1 : Int) + (W2 : Int)) = true) (hsc17 : i32.valid (2 * (W0 : Int)) = true) (hsc18 : i32.valid ((2 * (W0 : Int)) + 2) = true) (hsc19 : i32.valid ((2 * (W0 : Int)) + 1) = true) (hsc20 : i32.valid (2 * X3) = true) (hsc21 : i32.valid (((sp - 1 : Nat) : Int) + (2 * X3)) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (CalcLoopBody (mv.nv + pre.length)) (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell)] : List Cell))) (VVB b) = some r ∧ r.ret = none ∧
      r.ps = gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, X55⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, (((2 * W0 + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, Z10⟩ : Cell), (⟨s64, Z11⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨s64, Z13⟩ : Cell), (⟨s64, Z14⟩ : Cell), (⟨s64, Z15⟩ : Cell), (⟨s64, Z16⟩ : Cell), (⟨s64, Z17⟩ : Cell), (⟨s64, Z18⟩ : Cell), (⟨s64, Z19⟩ : Cell), (⟨s64, Z20⟩ : Cell), (⟨s64, Z21⟩ : Cell), (⟨s64, Z22⟩ : Cell), (⟨s64, Z23⟩ : Cell), (⟨s64, Z24⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨s64, X10⟩ : Cell), (⟨s64, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X14⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X16⟩ : Cell), (⟨s64, (X9 + X7)⟩ : Cell), (⟨s64, X17⟩ : Cell), (⟨s64, (X12 + X7)⟩ : Cell), (⟨s64, X18⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X20⟩ : Cell), (⟨i32, X21⟩ : Cell), (⟨s64, X22⟩ : Cell), (⟨s64, X23⟩ : Cell), (⟨s64, X24⟩ : Cell), (⟨s64, X25⟩ : Cell), (⟨i32, X26⟩ : Cell), (⟨s64, X27⟩ : Cell), (⟨s64, X28⟩ : Cell), (⟨s64, X29⟩ : Cell), (⟨s64, X30⟩ : Cell), (⟨s64, X31⟩ : Cell), (⟨s64, X32⟩ : Cell), (⟨s64, X33⟩ : Cell), (⟨s64, X34⟩ : Cell), (⟨s64, X35⟩ : Cell), (⟨s64, X36⟩ : Cell), (⟨s64, X37⟩ : Cell), (⟨s64, X38⟩ : Cell), (⟨s64, (X31 + X7)⟩ : Cell), (⟨s64, X39⟩ : Cell), (⟨s64, (X34 + X7)⟩ : Cell), (⟨s64, X40⟩ : Cell), (⟨s64, X41⟩ : Cell), (⟨s64, X42⟩ : Cell), (⟨i32, X43⟩ : Cell), (⟨s64, X44⟩ : Cell), (⟨s64, X45⟩ : Cell), (⟨s64, X46⟩ : Cell), (⟨s64, X47⟩ : Cell), (⟨i32, X48⟩ : Cell), (⟨s64, X49⟩ : Cell), (⟨s64, X50⟩ : Cell), (⟨s64, X51⟩ : Cell), (⟨s64, X52⟩ : Cell), (⟨s64, X53⟩ : Cell), (⟨s64, X54⟩ : Cell), (⟨i32, (((W1 : Int) + (W2 : Int)) / 2)⟩ : Cell)] : List Cell)) ∧ r.vv = VVB (uc24 (uc23 (uc22 (uc21 (uc20 (uc19 (uc18 (uc17 (uc16 (uc15 (uc14 (uc13 (uc12 (uc11 (uc10 (uc9 (uc8 (uc7 (uc6 (uc5 (uc4 (uc3 (uc2 (uc1 b (2 * W0 + 1) X28) (2 * W0 + 1) X29) (2 * W0 + 1) X11) (2 * W0 + 1) X27) (2 * W0 + 1) X24) (2 * W0 + 1) X14) (2 * W0 + 1) X19) (2 * W0 + 1) X30) (2 * W0 + 2) X50) (2 * W0 + 2) X51) (2 * W0 + 2) X33) (2 * W0 + 2) X49) (2 * W0 + 2) X46) (2 * W0 + 2) X36) (2 * W0 + 2) X41) (2 * W0 + 2) X52) W0 X53) W0 X54) (sp - 1) ((2 * (W0 : Int)) + 2)) (sp - 1) (((W1 : Int) + (W2 : Int)) / 2)) (sp - 1) (W2 : Int)) ((sp - 1) + 1) ((2 * (W0 : Int)) + 1)) ((sp - 1) + 1) (W1 : Int)) ((sp - 1) + 1) (((W1 : Int) + (W2 : Int)) / 2)) ∧ r.cost ≤ 72240 ∧ r.wk ≤ 24 := by
  classical
  have vW0 : i32.valid (W0 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW0
  have vW1 : i32.valid (W1 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW1
  have vW2 : i32.valid (W2 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW2
  have vZ3 : s64.valid Z3 = true := by rw [← hD_Z3]; exact getD_mem_valid b.mxv W0 hl0_3 hvl0
  have vZ4 : s64.valid Z4 = true := by rw [← hD_Z4]; exact getD_mem_valid b.mnv W0 hl3_4 hvl3
  have vZ5 : s64.valid Z5 = true := by rw [← hD_Z5]; exact getD_mem_valid b.lval W0 hl8_5 hvl8
  have vZ6 : s64.valid Z6 = true := by rw [← hD_Z6]; exact getD_mem_valid b.ladd W0 hl7_6 hvl7
  have vZ7 : s64.valid Z7 = true := by rw [← hD_Z7]; exact getD_mem_valid b.mxv (2 * W0 + 1) hl0_7 hvl0
  have vZ8 : s64.valid Z8 = true := by rw [← hD_Z8]; exact getD_mem_valid b.smx (2 * W0 + 1) hl1_8 hvl1
  have vZ9 : s64.valid Z9 = true := by rw [← hD_Z9]; exact getD_mem_valid b.mxc (2 * W0 + 1) hl2_9 hvl2
  have vZ10 : s64.valid Z10 = true := by rw [← hD_Z10]; exact getD_mem_valid b.mnv (2 * W0 + 1) hl3_10 hvl3
  have vZ11 : s64.valid Z11 = true := by rw [← hD_Z11]; exact getD_mem_valid b.smn (2 * W0 + 1) hl4_11 hvl4
  have vZ12 : s64.valid Z12 = true := by rw [← hD_Z12]; exact getD_mem_valid b.mnc (2 * W0 + 1) hl5_12 hvl5
  have vZ13 : s64.valid Z13 = true := by rw [← hD_Z13]; exact getD_mem_valid b.ladd (2 * W0 + 1) hl7_13 hvl7
  have vZ14 : s64.valid Z14 = true := by rw [← hD_Z14]; exact getD_mem_valid b.lval (2 * W0 + 1) hl8_14 hvl8
  have vZ15 : s64.valid Z15 = true := by rw [← hD_Z15]; exact getD_mem_valid b.len (2 * W0 + 1) hl6_15 hvl6
  have vZ16 : s64.valid Z16 = true := by rw [← hD_Z16]; exact getD_mem_valid b.mxv (2 * W0 + 2) hl0_16 hvl0
  have vZ17 : s64.valid Z17 = true := by rw [← hD_Z17]; exact getD_mem_valid b.smx (2 * W0 + 2) hl1_17 hvl1
  have vZ18 : s64.valid Z18 = true := by rw [← hD_Z18]; exact getD_mem_valid b.mxc (2 * W0 + 2) hl2_18 hvl2
  have vZ19 : s64.valid Z19 = true := by rw [← hD_Z19]; exact getD_mem_valid b.mnv (2 * W0 + 2) hl3_19 hvl3
  have vZ20 : s64.valid Z20 = true := by rw [← hD_Z20]; exact getD_mem_valid b.smn (2 * W0 + 2) hl4_20 hvl4
  have vZ21 : s64.valid Z21 = true := by rw [← hD_Z21]; exact getD_mem_valid b.mnc (2 * W0 + 2) hl5_21 hvl5
  have vZ22 : s64.valid Z22 = true := by rw [← hD_Z22]; exact getD_mem_valid b.ladd (2 * W0 + 2) hl7_22 hvl7
  have vZ23 : s64.valid Z23 = true := by rw [← hD_Z23]; exact getD_mem_valid b.lval (2 * W0 + 2) hl8_23 hvl8
  have vZ24 : s64.valid Z24 = true := by rw [← hD_Z24]; exact getD_mem_valid b.len (2 * W0 + 2) hl6_24 hvl6
  have vX0 : i32.valid X0 = true := by
    rw [hX0]
    by_cases hC : (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX1 : i32.valid X1 = true := by
    rw [hX1]
    by_cases hC : (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX2 : i32.valid X2 = true := by
    rw [hX2]
    by_cases hC : ((X0 = 0) ∧ (X1 = 1))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX3 : i32.valid X3 = true := by
    rw [hX3]
    by_cases hC : ((X0 = 0) ∧ (X2 = 0))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX4 : s64.valid X4 = true := by
    rw [hX4]
    by_cases hC : (((X2 = 1) ∧ ((op : Int) = 0)) ∧ (x < Z3))
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact hx
  have vX5 : s64.valid X5 = true := by
    rw [hX5]
    by_cases hC : (((X2 = 1) ∧ ((op : Int) = 1)) ∧ (Z4 < X4))
    · rw [if_pos hC]; exact vZ4
    · rw [if_neg hC]; exact vX4
  have vX6 : i32.valid X6 = true := by
    rw [hX6]
    by_cases hC : ((X3 = 1) ∧ (Z5 ≠ inf))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX7 : s64.valid X7 = true := by
    rw [hX7]
    by_cases hC : ((X3 = 1) ∧ (X6 = 0))
    · rw [if_pos hC]; exact vZ6
    · rw [if_neg hC]; exact (by decide)
  have vX8 : i32.valid X8 = true := by
    rw [hX8]
    by_cases hC : ((X3 = 1) ∧ (X6 = 0))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX9 : s64.valid X9 = true := by
    rw [hX9]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact vZ5
    · rw [if_neg hC]; exact vZ7
  have vX10 : s64.valid X10 = true := by
    rw [hX10]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact (hsc1 hC)
    · rw [if_neg hC]; exact vZ8
  have vX11 : s64.valid X11 = true := by
    rw [hX11]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact vZ15
    · rw [if_neg hC]; exact vZ9
  have vX12 : s64.valid X12 = true := by
    rw [hX12]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact vZ5
    · rw [if_neg hC]; exact vZ10
  have vX13 : s64.valid X13 = true := by
    rw [hX13]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact hinf
    · rw [if_neg hC]; exact vZ11
  have vX14 : s64.valid X14 = true := by
    rw [hX14]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact vZ15
    · rw [if_neg hC]; exact vZ12
  have vX15 : s64.valid X15 = true := by
    rw [hX15]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vZ13
  have vX16 : s64.valid X16 = true := by
    rw [hX16]
    by_cases hC : ((X6 = 1) ∧ (Z15 ≠ 1))
    · rw [if_pos hC]; exact vZ5
    · rw [if_neg hC]; exact vZ14
  have vX17 : s64.valid X17 = true := by
    rw [hX17]
    by_cases hC : (X10 ≠ (-inf))
    · rw [if_pos hC]; exact (hsc4 hC)
    · rw [if_neg hC]; exact vX10
  have vX18 : s64.valid X18 = true := by
    rw [hX18]
    by_cases hC : (X13 ≠ inf)
    · rw [if_pos hC]; exact (hsc6 hC)
    · rw [if_neg hC]; exact vX13
  have vX19 : s64.valid X19 = true := by
    rw [hX19]
    by_cases hC : ((X16 = inf) ∧ (Z15 ≠ 1))
    · rw [if_pos hC]; exact (hsc7 hC)
    · rw [if_neg hC]; exact vX15
  have vX20 : s64.valid X20 = true := by
    rw [hX20]
    by_cases hC : (X16 ≠ inf)
    · rw [if_pos hC]; exact (hsc8 hC)
    · rw [if_neg hC]; exact vX16
  have vX21 : i32.valid X21 = true := by
    rw [hX21]
    by_cases hC : ((X8 = 1) ∧ (Z3 < (X9 + X7)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX22 : s64.valid X22 = true := by
    rw [hX22]
    by_cases hC : (X21 = 1)
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact hsc2
  have vX23 : s64.valid X23 = true := by
    rw [hX23]
    by_cases hC : ((X21 = 1) ∧ ((X9 + X7) = (X12 + X7)))
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact hsc5
  have vX24 : s64.valid X24 = true := by
    rw [hX24]
    by_cases hC : (((X21 = 1) ∧ ((X9 + X7) ≠ (X12 + X7))) ∧ ((X9 + X7) = X18))
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact vX18
  have vX25 : s64.valid X25 = true := by
    rw [hX25]
    by_cases hC : (((X21 = 1) ∧ (X20 ≠ inf)) ∧ (Z3 < X20))
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact vX20
  have vX26 : i32.valid X26 = true := by
    rw [hX26]
    by_cases hC : ((X8 = 1) ∧ (X23 < Z4))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX27 : s64.valid X27 = true := by
    rw [hX27]
    by_cases hC : (X26 = 1)
    · rw [if_pos hC]; exact vZ4
    · rw [if_neg hC]; exact vX23
  have vX28 : s64.valid X28 = true := by
    rw [hX28]
    by_cases hC : ((X26 = 1) ∧ (X22 = X23))
    · rw [if_pos hC]; exact vZ4
    · rw [if_neg hC]; exact vX22
  have vX29 : s64.valid X29 = true := by
    rw [hX29]
    by_cases hC : (((X26 = 1) ∧ (X22 ≠ X23)) ∧ (X17 = X23))
    · rw [if_pos hC]; exact vZ4
    · rw [if_neg hC]; exact vX17
  have vX30 : s64.valid X30 = true := by
    rw [hX30]
    by_cases hC : (((X26 = 1) ∧ (X25 ≠ inf)) ∧ (X25 < Z4))
    · rw [if_pos hC]; exact vZ4
    · rw [if_neg hC]; exact vX25
  have vX31 : s64.valid X31 = true := by
    rw [hX31]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact vZ5
    · rw [if_neg hC]; exact vZ16
  have vX32 : s64.valid X32 = true := by
    rw [hX32]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact (hsc1 hC)
    · rw [if_neg hC]; exact vZ17
  have vX33 : s64.valid X33 = true := by
    rw [hX33]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact vZ24
    · rw [if_neg hC]; exact vZ18
  have vX34 : s64.valid X34 = true := by
    rw [hX34]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact vZ5
    · rw [if_neg hC]; exact vZ19
  have vX35 : s64.valid X35 = true := by
    rw [hX35]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact hinf
    · rw [if_neg hC]; exact vZ20
  have vX36 : s64.valid X36 = true := by
    rw [hX36]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact vZ24
    · rw [if_neg hC]; exact vZ21
  have vX37 : s64.valid X37 = true := by
    rw [hX37]
    by_cases hC : (X6 = 1)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vZ22
  have vX38 : s64.valid X38 = true := by
    rw [hX38]
    by_cases hC : ((X6 = 1) ∧ (Z24 ≠ 1))
    · rw [if_pos hC]; exact vZ5
    · rw [if_neg hC]; exact vZ23
  have vX39 : s64.valid X39 = true := by
    rw [hX39]
    by_cases hC : (X32 ≠ (-inf))
    · rw [if_pos hC]; exact (hsc10 hC)
    · rw [if_neg hC]; exact vX32
  have vX40 : s64.valid X40 = true := by
    rw [hX40]
    by_cases hC : (X35 ≠ inf)
    · rw [if_pos hC]; exact (hsc12 hC)
    · rw [if_neg hC]; exact vX35
  have vX41 : s64.valid X41 = true := by
    rw [hX41]
    by_cases hC : ((X38 = inf) ∧ (Z24 ≠ 1))
    · rw [if_pos hC]; exact (hsc13 hC)
    · rw [if_neg hC]; exact vX37
  have vX42 : s64.valid X42 = true := by
    rw [hX42]
    by_cases hC : (X38 ≠ inf)
    · rw [if_pos hC]; exact (hsc14 hC)
    · rw [if_neg hC]; exact vX38
  have vX43 : i32.valid X43 = true := by
    rw [hX43]
    by_cases hC : ((X8 = 1) ∧ (Z3 < (X31 + X7)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX44 : s64.valid X44 = true := by
    rw [hX44]
    by_cases hC : (X43 = 1)
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact hsc9
  have vX45 : s64.valid X45 = true := by
    rw [hX45]
    by_cases hC : ((X43 = 1) ∧ ((X31 + X7) = (X34 + X7)))
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact hsc11
  have vX46 : s64.valid X46 = true := by
    rw [hX46]
    by_cases hC : (((X43 = 1) ∧ ((X31 + X7) ≠ (X34 + X7))) ∧ ((X31 + X7) = X40))
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact vX40
  have vX47 : s64.valid X47 = true := by
    rw [hX47]
    by_cases hC : (((X43 = 1) ∧ (X42 ≠ inf)) ∧ (Z3 < X42))
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact vX42
  have vX48 : i32.valid X48 = true := by
    rw [hX48]
    by_cases hC : ((X8 = 1) ∧ (X45 < Z4))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX49 : s64.valid X49 = true := by
    rw [hX49]
    by_cases hC : (X48 = 1)
    · rw [if_pos hC]; exact vZ4
    · rw [if_neg hC]; exact vX45
  have vX50 : s64.valid X50 = true := by
    rw [hX50]
    by_cases hC : ((X48 = 1) ∧ (X44 = X45))
    · rw [if_pos hC]; exact vZ4
    · rw [if_neg hC]; exact vX44
  have vX51 : s64.valid X51 = true := by
    rw [hX51]
    by_cases hC : (((X48 = 1) ∧ (X44 ≠ X45)) ∧ (X39 = X45))
    · rw [if_pos hC]; exact vZ4
    · rw [if_neg hC]; exact vX39
  have vX52 : s64.valid X52 = true := by
    rw [hX52]
    by_cases hC : (((X48 = 1) ∧ (X47 ≠ inf)) ∧ (X47 < Z4))
    · rw [if_pos hC]; exact vZ4
    · rw [if_neg hC]; exact vX47
  have vX53 : s64.valid X53 = true := by
    rw [hX53]
    by_cases hC : (X3 = 1)
    · rw [if_pos hC]; exact hinf
    · rw [if_neg hC]; exact vZ5
  have vX54 : s64.valid X54 = true := by
    rw [hX54]
    by_cases hC : (X3 = 1)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vZ6
  have vX55 : i32.valid X55 = true := by rw [hX55]; exact hsc21
  obtain ⟨rE, hE, hrE, hpE, hvE, hcE, hwE⟩ : ∃ rE : PRM, pexecM mv fu Sk (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, X55⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, (((2 * W0 + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, Z10⟩ : Cell), (⟨s64, Z11⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨s64, Z13⟩ : Cell), (⟨s64, Z14⟩ : Cell), (⟨s64, Z15⟩ : Cell), (⟨s64, Z16⟩ : Cell), (⟨s64, Z17⟩ : Cell), (⟨s64, Z18⟩ : Cell), (⟨s64, Z19⟩ : Cell), (⟨s64, Z20⟩ : Cell), (⟨s64, Z21⟩ : Cell), (⟨s64, Z22⟩ : Cell), (⟨s64, Z23⟩ : Cell), (⟨s64, Z24⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨s64, X10⟩ : Cell), (⟨s64, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X14⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X16⟩ : Cell), (⟨s64, (X9 + X7)⟩ : Cell), (⟨s64, X17⟩ : Cell), (⟨s64, (X12 + X7)⟩ : Cell), (⟨s64, X18⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X20⟩ : Cell), (⟨i32, X21⟩ : Cell), (⟨s64, X22⟩ : Cell), (⟨s64, X23⟩ : Cell), (⟨s64, X24⟩ : Cell), (⟨s64, X25⟩ : Cell), (⟨i32, X26⟩ : Cell), (⟨s64, X27⟩ : Cell), (⟨s64, X28⟩ : Cell), (⟨s64, X29⟩ : Cell), (⟨s64, X30⟩ : Cell), (⟨s64, X31⟩ : Cell), (⟨s64, X32⟩ : Cell), (⟨s64, X33⟩ : Cell), (⟨s64, X34⟩ : Cell), (⟨s64, X35⟩ : Cell), (⟨s64, X36⟩ : Cell), (⟨s64, X37⟩ : Cell), (⟨s64, X38⟩ : Cell), (⟨s64, (X31 + X7)⟩ : Cell), (⟨s64, X39⟩ : Cell), (⟨s64, (X34 + X7)⟩ : Cell), (⟨s64, X40⟩ : Cell), (⟨s64, X41⟩ : Cell), (⟨s64, X42⟩ : Cell), (⟨i32, X43⟩ : Cell), (⟨s64, X44⟩ : Cell), (⟨s64, X45⟩ : Cell), (⟨s64, X46⟩ : Cell), (⟨s64, X47⟩ : Cell), (⟨i32, X48⟩ : Cell), (⟨s64, X49⟩ : Cell), (⟨s64, X50⟩ : Cell), (⟨s64, X51⟩ : Cell), (⟨s64, X52⟩ : Cell), (⟨s64, X53⟩ : Cell), (⟨s64, X54⟩ : Cell), (⟨i32, (((W1 : Int) + (W2 : Int)) / 2)⟩ : Cell)] : List Cell))) (VVB (uc24 (uc23 (uc22 (uc21 (uc20 (uc19 (uc18 (uc17 (uc16 (uc15 (uc14 (uc13 (uc12 (uc11 (uc10 (uc9 (uc8 (uc7 (uc6 (uc5 (uc4 (uc3 (uc2 (uc1 b (2 * W0 + 1) X28) (2 * W0 + 1) X29) (2 * W0 + 1) X11) (2 * W0 + 1) X27) (2 * W0 + 1) X24) (2 * W0 + 1) X14) (2 * W0 + 1) X19) (2 * W0 + 1) X30) (2 * W0 + 2) X50) (2 * W0 + 2) X51) (2 * W0 + 2) X33) (2 * W0 + 2) X49) (2 * W0 + 2) X46) (2 * W0 + 2) X36) (2 * W0 + 2) X41) (2 * W0 + 2) X52) W0 X53) W0 X54) (sp - 1) ((2 * (W0 : Int)) + 2)) (sp - 1) (((W1 : Int) + (W2 : Int)) / 2)) (sp - 1) (W2 : Int)) ((sp - 1) + 1) ((2 * (W0 : Int)) + 1)) ((sp - 1) + 1) (W1 : Int)) ((sp - 1) + 1) (((W1 : Int) + (W2 : Int)) / 2))) = some rE ∧
      rE.ret = none ∧ rE.ps = gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, X55⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, (((2 * W0 + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, Z10⟩ : Cell), (⟨s64, Z11⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨s64, Z13⟩ : Cell), (⟨s64, Z14⟩ : Cell), (⟨s64, Z15⟩ : Cell), (⟨s64, Z16⟩ : Cell), (⟨s64, Z17⟩ : Cell), (⟨s64, Z18⟩ : Cell), (⟨s64, Z19⟩ : Cell), (⟨s64, Z20⟩ : Cell), (⟨s64, Z21⟩ : Cell), (⟨s64, Z22⟩ : Cell), (⟨s64, Z23⟩ : Cell), (⟨s64, Z24⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨s64, X10⟩ : Cell), (⟨s64, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X14⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X16⟩ : Cell), (⟨s64, (X9 + X7)⟩ : Cell), (⟨s64, X17⟩ : Cell), (⟨s64, (X12 + X7)⟩ : Cell), (⟨s64, X18⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X20⟩ : Cell), (⟨i32, X21⟩ : Cell), (⟨s64, X22⟩ : Cell), (⟨s64, X23⟩ : Cell), (⟨s64, X24⟩ : Cell), (⟨s64, X25⟩ : Cell), (⟨i32, X26⟩ : Cell), (⟨s64, X27⟩ : Cell), (⟨s64, X28⟩ : Cell), (⟨s64, X29⟩ : Cell), (⟨s64, X30⟩ : Cell), (⟨s64, X31⟩ : Cell), (⟨s64, X32⟩ : Cell), (⟨s64, X33⟩ : Cell), (⟨s64, X34⟩ : Cell), (⟨s64, X35⟩ : Cell), (⟨s64, X36⟩ : Cell), (⟨s64, X37⟩ : Cell), (⟨s64, X38⟩ : Cell), (⟨s64, (X31 + X7)⟩ : Cell), (⟨s64, X39⟩ : Cell), (⟨s64, (X34 + X7)⟩ : Cell), (⟨s64, X40⟩ : Cell), (⟨s64, X41⟩ : Cell), (⟨s64, X42⟩ : Cell), (⟨i32, X43⟩ : Cell), (⟨s64, X44⟩ : Cell), (⟨s64, X45⟩ : Cell), (⟨s64, X46⟩ : Cell), (⟨s64, X47⟩ : Cell), (⟨i32, X48⟩ : Cell), (⟨s64, X49⟩ : Cell), (⟨s64, X50⟩ : Cell), (⟨s64, X51⟩ : Cell), (⟨s64, X52⟩ : Cell), (⟨s64, X53⟩ : Cell), (⟨s64, X54⟩ : Cell), (⟨i32, (((W1 : Int) + (W2 : Int)) / 2)⟩ : Cell)] : List Cell)) ∧ rE.vv = VVB (uc24 (uc23 (uc22 (uc21 (uc20 (uc19 (uc18 (uc17 (uc16 (uc15 (uc14 (uc13 (uc12 (uc11 (uc10 (uc9 (uc8 (uc7 (uc6 (uc5 (uc4 (uc3 (uc2 (uc1 b (2 * W0 + 1) X28) (2 * W0 + 1) X29) (2 * W0 + 1) X11) (2 * W0 + 1) X27) (2 * W0 + 1) X24) (2 * W0 + 1) X14) (2 * W0 + 1) X19) (2 * W0 + 1) X30) (2 * W0 + 2) X50) (2 * W0 + 2) X51) (2 * W0 + 2) X33) (2 * W0 + 2) X49) (2 * W0 + 2) X46) (2 * W0 + 2) X36) (2 * W0 + 2) X41) (2 * W0 + 2) X52) W0 X53) W0 X54) (sp - 1) ((2 * (W0 : Int)) + 2)) (sp - 1) (((W1 : Int) + (W2 : Int)) / 2)) (sp - 1) (W2 : Int)) ((sp - 1) + 1) ((2 * (W0 : Int)) + 1)) ((sp - 1) + 1) (W1 : Int)) ((sp - 1) + 1) (((W1 : Int) + (W2 : Int)) / 2)) ∧ rE.cost ≤ 0 ∧ rE.wk ≤ 0 :=
    ⟨_, pexecM_skip _ _ _ _, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  obtain ⟨c8, hc_8, hrc_8, hpc_8, hvc_8, hcc_8, hwc_8⟩ := CalcLoop_ch8 mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu Sk rE hE hrE
  obtain ⟨c7, hc_7, hrc_7, hpc_7, hvc_7, hcc_7, hwc_7⟩ := CalcLoop_ch7 mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu (CalcLoopc8 (mv.nv + pre.length) Sk) c8 hc_8 hrc_8
  obtain ⟨c6, hc_6, hrc_6, hpc_6, hvc_6, hcc_6, hwc_6⟩ := CalcLoop_ch6 mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu (CalcLoopc7 (mv.nv + pre.length) (CalcLoopc8 (mv.nv + pre.length) Sk)) c7 hc_7 hrc_7
  obtain ⟨c5, hc_5, hrc_5, hpc_5, hvc_5, hcc_5, hwc_5⟩ := CalcLoop_ch5 mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu (CalcLoopc6 (mv.nv + pre.length) (CalcLoopc7 (mv.nv + pre.length) (CalcLoopc8 (mv.nv + pre.length) Sk))) c6 hc_6 hrc_6
  obtain ⟨c4, hc_4, hrc_4, hpc_4, hvc_4, hcc_4, hwc_4⟩ := CalcLoop_ch4 mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu (CalcLoopc5 (mv.nv + pre.length) (CalcLoopc6 (mv.nv + pre.length) (CalcLoopc7 (mv.nv + pre.length) (CalcLoopc8 (mv.nv + pre.length) Sk)))) c5 hc_5 hrc_5
  obtain ⟨c3, hc_3, hrc_3, hpc_3, hvc_3, hcc_3, hwc_3⟩ := CalcLoop_ch3 mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu (CalcLoopc4 (mv.nv + pre.length) (CalcLoopc5 (mv.nv + pre.length) (CalcLoopc6 (mv.nv + pre.length) (CalcLoopc7 (mv.nv + pre.length) (CalcLoopc8 (mv.nv + pre.length) Sk))))) c4 hc_4 hrc_4
  obtain ⟨c2, hc_2, hrc_2, hpc_2, hvc_2, hcc_2, hwc_2⟩ := CalcLoop_ch2 mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu (CalcLoopc3 (mv.nv + pre.length) (CalcLoopc4 (mv.nv + pre.length) (CalcLoopc5 (mv.nv + pre.length) (CalcLoopc6 (mv.nv + pre.length) (CalcLoopc7 (mv.nv + pre.length) (CalcLoopc8 (mv.nv + pre.length) Sk)))))) c3 hc_3 hrc_3
  obtain ⟨c1, hc_1, hrc_1, hpc_1, hvc_1, hcc_1, hwc_1⟩ := CalcLoop_ch1 mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu (CalcLoopc2 (mv.nv + pre.length) (CalcLoopc3 (mv.nv + pre.length) (CalcLoopc4 (mv.nv + pre.length) (CalcLoopc5 (mv.nv + pre.length) (CalcLoopc6 (mv.nv + pre.length) (CalcLoopc7 (mv.nv + pre.length) (CalcLoopc8 (mv.nv + pre.length) Sk))))))) c2 hc_2 hrc_2
  obtain ⟨c0, hc_0, hrc_0, hpc_0, hvc_0, hcc_0, hwc_0⟩ := CalcLoop_ch0 mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu (CalcLoopc1 (mv.nv + pre.length) (CalcLoopc2 (mv.nv + pre.length) (CalcLoopc3 (mv.nv + pre.length) (CalcLoopc4 (mv.nv + pre.length) (CalcLoopc5 (mv.nv + pre.length) (CalcLoopc6 (mv.nv + pre.length) (CalcLoopc7 (mv.nv + pre.length) (CalcLoopc8 (mv.nv + pre.length) Sk)))))))) c1 hc_1 hrc_1
  clear hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13 hX14 hX15 hX16 hX17 hX18 hX19 hX20 hX21 hX22 hX23 hX24 hX25 hX26 hX27 hX28 hX29 hX30 hX31 hX32 hX33 hX34 hX35 hX36 hX37 hX38 hX39 hX40 hX41 hX42 hX43 hX44 hX45 hX46 hX47 hX48 hX49 hX50 hX51 hX52 hX53 hX54 hX55
  refine ⟨c0, hc_0, hrc_0, ?_, ?_, ?_, ?_⟩
  · rw [hpc_0, hpc_1, hpc_2, hpc_3, hpc_4, hpc_5, hpc_6, hpc_7, hpc_8, hpE]
  · rw [hvc_0, hvc_1, hvc_2, hvc_3, hvc_4, hvc_5, hvc_6, hvc_7, hvc_8, hvE]
  · omega
  · omega

end Proofs.BeatsExec
