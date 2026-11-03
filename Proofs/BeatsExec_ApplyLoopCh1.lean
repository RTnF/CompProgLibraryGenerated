import Proofs.BeatsExec_ApplyLoopDefs
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
theorem ApplyLoop_ch1 (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (b : BS) (P : List Cell)
    (inf : Int) (n op qa qb sp ne : Nat) (x : Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hopM : op < M31) (hqaM : qa < M31) (hqbM : qb < M31) (hspM : sp < M31) (hneM : ne < M31) (hsp : 0 < sp) (hx : s64.valid x = true) (hvl0 : ∀ w ∈ b.mxv, s64.valid w = true) (hvl1 : ∀ w ∈ b.smx, s64.valid w = true) (hvl2 : ∀ w ∈ b.mxc, s64.valid w = true) (hvl3 : ∀ w ∈ b.mnv, s64.valid w = true) (hvl4 : ∀ w ∈ b.smn, s64.valid w = true) (hvl5 : ∀ w ∈ b.mnc, s64.valid w = true) (hvl6 : ∀ w ∈ b.len, s64.valid w = true) (hvl7 : ∀ w ∈ b.ladd, s64.valid w = true) (hvl8 : ∀ w ∈ b.lval, s64.valid w = true) (hvl11 : ∀ w ∈ b.sk, i32.valid w = true) (hvl12 : ∀ w ∈ b.sl, i32.valid w = true) (hvl13 : ∀ w ∈ b.sr, i32.valid w = true) (hvl14 : ∀ w ∈ b.ent, i32.valid w = true) (W0 : Nat) (hNW0 : W0 < M31) (hD_W0 : b.sk.getD (sp - 1) 0 = (W0 : Int)) (W1 : Nat) (hNW1 : W1 < M31) (hD_W1 : b.sl.getD (sp - 1) 0 = (W1 : Int)) (W2 : Nat) (hNW2 : W2 < M31) (hD_W2 : b.sr.getD (sp - 1) 0 = (W2 : Int)) (Z3 : Int) (hD_Z3 : b.mxv.getD W0 0 = Z3) (Z4 : Int) (hD_Z4 : b.smx.getD W0 0 = Z4) (Z5 : Int) (hD_Z5 : b.mnv.getD W0 0 = Z5) (Z6 : Int) (hD_Z6 : b.smn.getD W0 0 = Z6) (Z7 : Int) (hD_Z7 : b.lval.getD W0 0 = Z7) (Z8 : Int) (hD_Z8 : b.ladd.getD W0 0 = Z8) (Z9 : Int) (hD_Z9 : b.len.getD W0 0 = Z9) (Z10 : Int) (hD_Z10 : b.mxc.getD W0 0 = Z10) (Z11 : Int) (hD_Z11 : b.mnc.getD W0 0 = Z11) (Z12 : Int) (hD_Z12 : b.mxv.getD (2 * W0 + 1) 0 = Z12) (Z13 : Int) (hD_Z13 : b.smx.getD (2 * W0 + 1) 0 = Z13) (Z14 : Int) (hD_Z14 : b.mxc.getD (2 * W0 + 1) 0 = Z14) (Z15 : Int) (hD_Z15 : b.mnv.getD (2 * W0 + 1) 0 = Z15) (Z16 : Int) (hD_Z16 : b.smn.getD (2 * W0 + 1) 0 = Z16) (Z17 : Int) (hD_Z17 : b.mnc.getD (2 * W0 + 1) 0 = Z17) (Z18 : Int) (hD_Z18 : b.ladd.getD (2 * W0 + 1) 0 = Z18) (Z19 : Int) (hD_Z19 : b.lval.getD (2 * W0 + 1) 0 = Z19) (Z20 : Int) (hD_Z20 : b.len.getD (2 * W0 + 1) 0 = Z20) (Z21 : Int) (hD_Z21 : b.mxv.getD (2 * W0 + 2) 0 = Z21) (Z22 : Int) (hD_Z22 : b.smx.getD (2 * W0 + 2) 0 = Z22) (Z23 : Int) (hD_Z23 : b.mxc.getD (2 * W0 + 2) 0 = Z23) (Z24 : Int) (hD_Z24 : b.mnv.getD (2 * W0 + 2) 0 = Z24) (Z25 : Int) (hD_Z25 : b.smn.getD (2 * W0 + 2) 0 = Z25) (Z26 : Int) (hD_Z26 : b.mnc.getD (2 * W0 + 2) 0 = Z26) (Z27 : Int) (hD_Z27 : b.ladd.getD (2 * W0 + 2) 0 = Z27) (Z28 : Int) (hD_Z28 : b.lval.getD (2 * W0 + 2) 0 = Z28) (Z29 : Int) (hD_Z29 : b.len.getD (2 * W0 + 2) 0 = Z29) (hl11_0 : (sp - 1) < (b.sk).length) (hl12_1 : (sp - 1) < (b.sl).length) (hl13_2 : (sp - 1) < (b.sr).length) (hl0_3 : W0 < (b.mxv).length) (hl1_4 : W0 < (b.smx).length) (hl3_5 : W0 < (b.mnv).length) (hl4_6 : W0 < (b.smn).length) (hl8_7 : W0 < (b.lval).length) (hl7_8 : W0 < (b.ladd).length) (hl6_9 : W0 < (b.len).length) (hl2_10 : W0 < (b.mxc).length) (hl5_11 : W0 < (b.mnc).length) (hl0_12 : (2 * W0 + 1) < (b.mxv).length) (hl1_13 : (2 * W0 + 1) < (b.smx).length) (hl2_14 : (2 * W0 + 1) < (b.mxc).length) (hl3_15 : (2 * W0 + 1) < (b.mnv).length) (hl4_16 : (2 * W0 + 1) < (b.smn).length) (hl5_17 : (2 * W0 + 1) < (b.mnc).length) (hl7_18 : (2 * W0 + 1) < (b.ladd).length) (hl8_19 : (2 * W0 + 1) < (b.lval).length) (hl6_20 : (2 * W0 + 1) < (b.len).length) (hl0_21 : (2 * W0 + 2) < (b.mxv).length) (hl1_22 : (2 * W0 + 2) < (b.smx).length) (hl2_23 : (2 * W0 + 2) < (b.mxc).length) (hl3_24 : (2 * W0 + 2) < (b.mnv).length) (hl4_25 : (2 * W0 + 2) < (b.smn).length) (hl5_26 : (2 * W0 + 2) < (b.mnc).length) (hl7_27 : (2 * W0 + 2) < (b.ladd).length) (hl8_28 : (2 * W0 + 2) < (b.lval).length) (hl6_29 : (2 * W0 + 2) < (b.len).length) (hl14_30 : ne < (b.ent).length) (hl11_31 : ((sp - 1) + 1) < (b.sk).length) (hl12_32 : ((sp - 1) + 1) < (b.sl).length) (hl13_33 : ((sp - 1) + 1) < (b.sr).length) (hk1_W0 : (2 * W0 + 1) < M31) (hk2_W0 : (2 * W0 + 2) < M31) (hix2 : ((sp - 1) + 1) < M31) (hix3 : ((sp - 1) + 1) < M31) (hix4 : ((sp - 1) + 1) < M31) (X0 : Int) (hX0 : X0 = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0)) (X1 : Int) (hX1 : X1 = (if (((op : Int) = 0) ∧ (Z3 ≤ x)) then 1 else X0)) (X2 : Int) (hX2 : X2 = (if (((op : Int) = 1) ∧ (x ≤ Z5)) then 1 else X1)) (X3 : Int) (hX3 : X3 = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0)) (X4 : Int) (hX4 : X4 = (if (((op : Int) = 0) ∧ (x ≤ Z4)) then 0 else 1)) (X5 : Int) (hX5 : X5 = (if (((op : Int) = 1) ∧ (Z6 ≤ x)) then 0 else X4)) (X6 : Int) (hX6 : X6 = (if (((X2 = 0) ∧ (X3 = 1)) ∧ (X5 = 1)) then 1 else 0)) (X7 : Int) (hX7 : X7 = (if ((X2 = 0) ∧ (X6 = 0)) then 1 else 0)) (X8 : Int) (hX8 : X8 = (if ((X6 = 1) ∧ ((op : Int) = 0)) then 1 else 0)) (X9 : Int) (hX9 : X9 = (if ((X6 = 1) ∧ ((op : Int) = 1)) then 1 else 0)) (X10 : Int) (hX10 : X10 = (if ((X6 = 1) ∧ ((op : Int) = 2)) then 1 else 0)) (X11 : Int) (hX11 : X11 = (if ((X6 = 1) ∧ ((op : Int) = 3)) then 1 else 0)) (X12 : Int) (hX12 : X12 = (if (X10 = 1) then x else 0)) (X13 : Int) (hX13 : X13 = (if (X8 = 1) then x else Z3)) (X14 : Int) (hX14 : X14 = (if ((X8 = 1) ∧ (Z3 = Z5)) then x else Z5)) (X15 : Int) (hX15 : X15 = (if (((X8 = 1) ∧ (Z3 ≠ Z5)) ∧ (Z3 = Z6)) then x else Z6)) (X16 : Int) (hX16 : X16 = (if (((X8 = 1) ∧ (Z7 ≠ inf)) ∧ (x < Z7)) then x else Z7)) (X17 : Int) (hX17 : X17 = (if (X9 = 1) then x else X14)) (X18 : Int) (hX18 : X18 = (if ((X9 = 1) ∧ (X13 = X14)) then x else X13)) (X19 : Int) (hX19 : X19 = (if (((X9 = 1) ∧ (X13 ≠ X14)) ∧ (Z4 = X14)) then x else Z4)) (X20 : Int) (hX20 : X20 = (if (((X9 = 1) ∧ (X16 ≠ inf)) ∧ (X16 < x)) then x else X16)) (X21 : Int) (hX21 : X21 = (if (X19 ≠ (-inf)) then (X19 + X12) else X19)) (X22 : Int) (hX22 : X22 = (if (X15 ≠ inf) then (X15 + X12) else X15)) (X23 : Int) (hX23 : X23 = (if ((X20 = inf) ∧ (Z9 ≠ 1)) then (Z8 + X12) else Z8)) (X24 : Int) (hX24 : X24 = (if ((X20 ≠ inf) ∧ (Z9 ≠ 1)) then (X20 + X12) else X20)) (X25 : Int) (hX25 : X25 = (if (X11 = 1) then x else (X18 + X12))) (X26 : Int) (hX26 : X26 = (if (X11 = 1) then (-inf) else X21)) (X27 : Int) (hX27 : X27 = (if (X11 = 1) then x else (X17 + X12))) (X28 : Int) (hX28 : X28 = (if (X11 = 1) then inf else X22)) (X29 : Int) (hX29 : X29 = (if (X11 = 1) then Z9 else Z10)) (X30 : Int) (hX30 : X30 = (if (X11 = 1) then Z9 else Z11)) (X31 : Int) (hX31 : X31 = (if ((X11 = 1) ∧ (Z9 ≠ 1)) then x else X24)) (X32 : Int) (hX32 : X32 = (if ((X11 = 1) ∧ (Z9 ≠ 1)) then 0 else X23)) (X33 : Int) (hX33 : X33 = (if ((X7 = 1) ∧ (X31 ≠ inf)) then 1 else 0)) (X34 : Int) (hX34 : X34 = (if ((X7 = 1) ∧ (X33 = 0)) then X32 else 0)) (X35 : Int) (hX35 : X35 = (if ((X7 = 1) ∧ (X33 = 0)) then 1 else 0)) (X36 : Int) (hX36 : X36 = (if (X33 = 1) then X31 else Z12)) (X37 : Int) (hX37 : X37 = (if (X33 = 1) then (-inf) else Z13)) (X38 : Int) (hX38 : X38 = (if (X33 = 1) then Z20 else Z14)) (X39 : Int) (hX39 : X39 = (if (X33 = 1) then X31 else Z15)) (X40 : Int) (hX40 : X40 = (if (X33 = 1) then inf else Z16)) (X41 : Int) (hX41 : X41 = (if (X33 = 1) then Z20 else Z17)) (X42 : Int) (hX42 : X42 = (if (X33 = 1) then 0 else Z18)) (X43 : Int) (hX43 : X43 = (if ((X33 = 1) ∧ (Z20 ≠ 1)) then X31 else Z19)) (X44 : Int) (hX44 : X44 = (if (X37 ≠ (-inf)) then (X37 + X34) else X37)) (X45 : Int) (hX45 : X45 = (if (X40 ≠ inf) then (X40 + X34) else X40)) (X46 : Int) (hX46 : X46 = (if ((X43 = inf) ∧ (Z20 ≠ 1)) then (X42 + X34) else X42)) (X47 : Int) (hX47 : X47 = (if (X43 ≠ inf) then (X43 + X34) else X43)) (X48 : Int) (hX48 : X48 = (if ((X35 = 1) ∧ (X25 < (X36 + X34))) then 1 else 0)) (X49 : Int) (hX49 : X49 = (if (X48 = 1) then X25 else (X36 + X34))) (X50 : Int) (hX50 : X50 = (if ((X48 = 1) ∧ ((X36 + X34) = (X39 + X34))) then X25 else (X39 + X34))) (X51 : Int) (hX51 : X51 = (if (((X48 = 1) ∧ ((X36 + X34) ≠ (X39 + X34))) ∧ ((X36 + X34) = X45)) then X25 else X45)) (X52 : Int) (hX52 : X52 = (if (((X48 = 1) ∧ (X47 ≠ inf)) ∧ (X25 < X47)) then X25 else X47)) (X53 : Int) (hX53 : X53 = (if ((X35 = 1) ∧ (X50 < X27)) then 1 else 0)) (X54 : Int) (hX54 : X54 = (if (X53 = 1) then X27 else X50)) (X55 : Int) (hX55 : X55 = (if ((X53 = 1) ∧ (X49 = X50)) then X27 else X49)) (X56 : Int) (hX56 : X56 = (if (((X53 = 1) ∧ (X49 ≠ X50)) ∧ (X44 = X50)) then X27 else X44)) (X57 : Int) (hX57 : X57 = (if (((X53 = 1) ∧ (X52 ≠ inf)) ∧ (X52 < X27)) then X27 else X52)) (X58 : Int) (hX58 : X58 = (if (X33 = 1) then X31 else Z21)) (X59 : Int) (hX59 : X59 = (if (X33 = 1) then (-inf) else Z22)) (X60 : Int) (hX60 : X60 = (if (X33 = 1) then Z29 else Z23)) (X61 : Int) (hX61 : X61 = (if (X33 = 1) then X31 else Z24)) (X62 : Int) (hX62 : X62 = (if (X33 = 1) then inf else Z25)) (X63 : Int) (hX63 : X63 = (if (X33 = 1) then Z29 else Z26)) (X64 : Int) (hX64 : X64 = (if (X33 = 1) then 0 else Z27)) (X65 : Int) (hX65 : X65 = (if ((X33 = 1) ∧ (Z29 ≠ 1)) then X31 else Z28)) (X66 : Int) (hX66 : X66 = (if (X59 ≠ (-inf)) then (X59 + X34) else X59)) (X67 : Int) (hX67 : X67 = (if (X62 ≠ inf) then (X62 + X34) else X62)) (X68 : Int) (hX68 : X68 = (if ((X65 = inf) ∧ (Z29 ≠ 1)) then (X64 + X34) else X64)) (X69 : Int) (hX69 : X69 = (if (X65 ≠ inf) then (X65 + X34) else X65)) (X70 : Int) (hX70 : X70 = (if ((X35 = 1) ∧ (X25 < (X58 + X34))) then 1 else 0)) (X71 : Int) (hX71 : X71 = (if (X70 = 1) then X25 else (X58 + X34))) (X72 : Int) (hX72 : X72 = (if ((X70 = 1) ∧ ((X58 + X34) = (X61 + X34))) then X25 else (X61 + X34))) (X73 : Int) (hX73 : X73 = (if (((X70 = 1) ∧ ((X58 + X34) ≠ (X61 + X34))) ∧ ((X58 + X34) = X67)) then X25 else X67)) (X74 : Int) (hX74 : X74 = (if (((X70 = 1) ∧ (X69 ≠ inf)) ∧ (X25 < X69)) then X25 else X69)) (X75 : Int) (hX75 : X75 = (if ((X35 = 1) ∧ (X72 < X27)) then 1 else 0)) (X76 : Int) (hX76 : X76 = (if (X75 = 1) then X27 else X72)) (X77 : Int) (hX77 : X77 = (if ((X75 = 1) ∧ (X71 = X72)) then X27 else X71)) (X78 : Int) (hX78 : X78 = (if (((X75 = 1) ∧ (X71 ≠ X72)) ∧ (X66 = X72)) then X27 else X66)) (X79 : Int) (hX79 : X79 = (if (((X75 = 1) ∧ (X74 ≠ inf)) ∧ (X74 < X27)) then X27 else X74)) (X80 : Int) (hX80 : X80 = (if (X7 = 1) then inf else X31)) (X81 : Int) (hX81 : X81 = (if (X7 = 1) then 0 else X32)) (X82 : Int) (hX82 : X82 = ((ne : Int) + X7)) (X83 : Int) (hX83 : X83 = (((sp - 1 : Nat) : Int) + (2 * X7))) (hsc0 : i32.valid ((sp : Int) - 1) = true) (hsc1 : s64.valid (X18 + X12) = true) (hsc2 : s64.valid (-inf) = true) (hsc3 : ((X19 ≠ (-inf))) → s64.valid (X19 + X12) = true) (hsc4 : s64.valid (X17 + X12) = true) (hsc5 : ((X15 ≠ inf)) → s64.valid (X15 + X12) = true) (hsc6 : (((X20 = inf) ∧ (Z9 ≠ 1))) → s64.valid (Z8 + X12) = true) (hsc7 : (((X20 ≠ inf) ∧ (Z9 ≠ 1))) → s64.valid (X20 + X12) = true) (hsc8 : ((X11 = 1)) → s64.valid (-inf) = true) (hsc9 : ((X33 = 1)) → s64.valid (-inf) = true) (hsc10 : s64.valid (X36 + X34) = true) (hsc11 : ((X37 ≠ (-inf))) → s64.valid (X37 + X34) = true) (hsc12 : s64.valid (X39 + X34) = true) (hsc13 : ((X40 ≠ inf)) → s64.valid (X40 + X34) = true) (hsc14 : (((X43 = inf) ∧ (Z20 ≠ 1))) → s64.valid (X42 + X34) = true) (hsc15 : ((X43 ≠ inf)) → s64.valid (X43 + X34) = true) (hsc16 : s64.valid (X58 + X34) = true) (hsc17 : ((X59 ≠ (-inf))) → s64.valid (X59 + X34) = true) (hsc18 : s64.valid (X61 + X34) = true) (hsc19 : ((X62 ≠ inf)) → s64.valid (X62 + X34) = true) (hsc20 : (((X65 = inf) ∧ (Z29 ≠ 1))) → s64.valid (X64 + X34) = true) (hsc21 : ((X65 ≠ inf)) → s64.valid (X65 + X34) = true) (hsc22 : i32.valid ((ne : Int) + X7) = true) (hsc23 : i32.valid ((W1 : Int) + (W2 : Int)) = true) (hsc25 : i32.valid (2 * (W0 : Int)) = true) (hsc26 : i32.valid ((2 * (W0 : Int)) + 2) = true) (hsc27 : i32.valid ((2 * (W0 : Int)) + 1) = true) (hsc28 : i32.valid (2 * X7) = true) (hsc29 : i32.valid (((sp - 1 : Nat) : Int) + (2 * X7)) = true) (fu : Nat)
    (REST : Command) (r : PRM) (hrest : pexecM mv fu REST (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell)] : List Cell))) (VVB b) = some r) (hret : r.ret = none) :
    ∃ r0 : PRM, pexecM mv fu (ApplyLoopc1 (mv.nv + pre.length) REST) (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell))) (VVB b) = some r0 ∧ r0.ret = none ∧
      r0.ps = r.ps ∧ r0.vv = r.vv ∧ r0.cost ≤ 8400 + r.cost ∧ r0.wk ≤ 0 + r.wk := by
  classical
  have vW0 : i32.valid (W0 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW0
  have vW1 : i32.valid (W1 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW1
  have vW2 : i32.valid (W2 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW2
  have vZ3 : s64.valid Z3 = true := by rw [← hD_Z3]; exact getD_mem_valid b.mxv W0 hl0_3 hvl0
  have vZ4 : s64.valid Z4 = true := by rw [← hD_Z4]; exact getD_mem_valid b.smx W0 hl1_4 hvl1
  have vZ5 : s64.valid Z5 = true := by rw [← hD_Z5]; exact getD_mem_valid b.mnv W0 hl3_5 hvl3
  have vZ6 : s64.valid Z6 = true := by rw [← hD_Z6]; exact getD_mem_valid b.smn W0 hl4_6 hvl4
  have vZ7 : s64.valid Z7 = true := by rw [← hD_Z7]; exact getD_mem_valid b.lval W0 hl8_7 hvl8
  have vZ8 : s64.valid Z8 = true := by rw [← hD_Z8]; exact getD_mem_valid b.ladd W0 hl7_8 hvl7
  have vZ9 : s64.valid Z9 = true := by rw [← hD_Z9]; exact getD_mem_valid b.len W0 hl6_9 hvl6
  have vZ10 : s64.valid Z10 = true := by rw [← hD_Z10]; exact getD_mem_valid b.mxc W0 hl2_10 hvl2
  have vZ11 : s64.valid Z11 = true := by rw [← hD_Z11]; exact getD_mem_valid b.mnc W0 hl5_11 hvl5
  have vZ12 : s64.valid Z12 = true := by rw [← hD_Z12]; exact getD_mem_valid b.mxv (2 * W0 + 1) hl0_12 hvl0
  have vZ13 : s64.valid Z13 = true := by rw [← hD_Z13]; exact getD_mem_valid b.smx (2 * W0 + 1) hl1_13 hvl1
  have vZ14 : s64.valid Z14 = true := by rw [← hD_Z14]; exact getD_mem_valid b.mxc (2 * W0 + 1) hl2_14 hvl2
  have vZ15 : s64.valid Z15 = true := by rw [← hD_Z15]; exact getD_mem_valid b.mnv (2 * W0 + 1) hl3_15 hvl3
  have vZ16 : s64.valid Z16 = true := by rw [← hD_Z16]; exact getD_mem_valid b.smn (2 * W0 + 1) hl4_16 hvl4
  have vZ17 : s64.valid Z17 = true := by rw [← hD_Z17]; exact getD_mem_valid b.mnc (2 * W0 + 1) hl5_17 hvl5
  have vZ18 : s64.valid Z18 = true := by rw [← hD_Z18]; exact getD_mem_valid b.ladd (2 * W0 + 1) hl7_18 hvl7
  have vZ19 : s64.valid Z19 = true := by rw [← hD_Z19]; exact getD_mem_valid b.lval (2 * W0 + 1) hl8_19 hvl8
  have vZ20 : s64.valid Z20 = true := by rw [← hD_Z20]; exact getD_mem_valid b.len (2 * W0 + 1) hl6_20 hvl6
  have vZ21 : s64.valid Z21 = true := by rw [← hD_Z21]; exact getD_mem_valid b.mxv (2 * W0 + 2) hl0_21 hvl0
  have vZ22 : s64.valid Z22 = true := by rw [← hD_Z22]; exact getD_mem_valid b.smx (2 * W0 + 2) hl1_22 hvl1
  have vZ23 : s64.valid Z23 = true := by rw [← hD_Z23]; exact getD_mem_valid b.mxc (2 * W0 + 2) hl2_23 hvl2
  have vZ24 : s64.valid Z24 = true := by rw [← hD_Z24]; exact getD_mem_valid b.mnv (2 * W0 + 2) hl3_24 hvl3
  have vZ25 : s64.valid Z25 = true := by rw [← hD_Z25]; exact getD_mem_valid b.smn (2 * W0 + 2) hl4_25 hvl4
  have vZ26 : s64.valid Z26 = true := by rw [← hD_Z26]; exact getD_mem_valid b.mnc (2 * W0 + 2) hl5_26 hvl5
  have vZ27 : s64.valid Z27 = true := by rw [← hD_Z27]; exact getD_mem_valid b.ladd (2 * W0 + 2) hl7_27 hvl7
  have vZ28 : s64.valid Z28 = true := by rw [← hD_Z28]; exact getD_mem_valid b.lval (2 * W0 + 2) hl8_28 hvl8
  have vZ29 : s64.valid Z29 = true := by rw [← hD_Z29]; exact getD_mem_valid b.len (2 * W0 + 2) hl6_29 hvl6
  have vX0 : i32.valid X0 = true := by
    rw [hX0]
    by_cases hC : (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX1 : i32.valid X1 = true := by
    rw [hX1]
    by_cases hC : (((op : Int) = 0) ∧ (Z3 ≤ x))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vX0
  have vX2 : i32.valid X2 = true := by
    rw [hX2]
    by_cases hC : (((op : Int) = 1) ∧ (x ≤ Z5))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vX1
  have vX3 : i32.valid X3 = true := by
    rw [hX3]
    by_cases hC : (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX4 : i32.valid X4 = true := by
    rw [hX4]
    by_cases hC : (((op : Int) = 0) ∧ (x ≤ Z4))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX5 : i32.valid X5 = true := by
    rw [hX5]
    by_cases hC : (((op : Int) = 1) ∧ (Z6 ≤ x))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vX4
  have vX6 : i32.valid X6 = true := by
    rw [hX6]
    by_cases hC : (((X2 = 0) ∧ (X3 = 1)) ∧ (X5 = 1))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX7 : i32.valid X7 = true := by
    rw [hX7]
    by_cases hC : ((X2 = 0) ∧ (X6 = 0))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX8 : i32.valid X8 = true := by
    rw [hX8]
    by_cases hC : ((X6 = 1) ∧ ((op : Int) = 0))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX9 : i32.valid X9 = true := by
    rw [hX9]
    by_cases hC : ((X6 = 1) ∧ ((op : Int) = 1))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX10 : i32.valid X10 = true := by
    rw [hX10]
    by_cases hC : ((X6 = 1) ∧ ((op : Int) = 2))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX11 : i32.valid X11 = true := by
    rw [hX11]
    by_cases hC : ((X6 = 1) ∧ ((op : Int) = 3))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX12 : s64.valid X12 = true := by
    rw [hX12]
    by_cases hC : (X10 = 1)
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact (by decide)
  have vX13 : s64.valid X13 = true := by
    rw [hX13]
    by_cases hC : (X8 = 1)
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact vZ3
  have vX14 : s64.valid X14 = true := by
    rw [hX14]
    by_cases hC : ((X8 = 1) ∧ (Z3 = Z5))
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact vZ5
  have vX15 : s64.valid X15 = true := by
    rw [hX15]
    by_cases hC : (((X8 = 1) ∧ (Z3 ≠ Z5)) ∧ (Z3 = Z6))
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact vZ6
  have vX16 : s64.valid X16 = true := by
    rw [hX16]
    by_cases hC : (((X8 = 1) ∧ (Z7 ≠ inf)) ∧ (x < Z7))
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact vZ7
  have vX17 : s64.valid X17 = true := by
    rw [hX17]
    by_cases hC : (X9 = 1)
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact vX14
  have vX18 : s64.valid X18 = true := by
    rw [hX18]
    by_cases hC : ((X9 = 1) ∧ (X13 = X14))
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact vX13
  have vX19 : s64.valid X19 = true := by
    rw [hX19]
    by_cases hC : (((X9 = 1) ∧ (X13 ≠ X14)) ∧ (Z4 = X14))
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact vZ4
  have vX20 : s64.valid X20 = true := by
    rw [hX20]
    by_cases hC : (((X9 = 1) ∧ (X16 ≠ inf)) ∧ (X16 < x))
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact vX16
  have vX21 : s64.valid X21 = true := by
    rw [hX21]
    by_cases hC : (X19 ≠ (-inf))
    · rw [if_pos hC]; exact (hsc3 hC)
    · rw [if_neg hC]; exact vX19
  have vX22 : s64.valid X22 = true := by
    rw [hX22]
    by_cases hC : (X15 ≠ inf)
    · rw [if_pos hC]; exact (hsc5 hC)
    · rw [if_neg hC]; exact vX15
  have vX23 : s64.valid X23 = true := by
    rw [hX23]
    by_cases hC : ((X20 = inf) ∧ (Z9 ≠ 1))
    · rw [if_pos hC]; exact (hsc6 hC)
    · rw [if_neg hC]; exact vZ8
  have vX24 : s64.valid X24 = true := by
    rw [hX24]
    by_cases hC : ((X20 ≠ inf) ∧ (Z9 ≠ 1))
    · rw [if_pos hC]; exact (hsc7 hC)
    · rw [if_neg hC]; exact vX20
  have vX25 : s64.valid X25 = true := by
    rw [hX25]
    by_cases hC : (X11 = 1)
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact hsc1
  have vX26 : s64.valid X26 = true := by
    rw [hX26]
    by_cases hC : (X11 = 1)
    · rw [if_pos hC]; exact (hsc8 hC)
    · rw [if_neg hC]; exact vX21
  have vX27 : s64.valid X27 = true := by
    rw [hX27]
    by_cases hC : (X11 = 1)
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact hsc4
  have vX28 : s64.valid X28 = true := by
    rw [hX28]
    by_cases hC : (X11 = 1)
    · rw [if_pos hC]; exact hinf
    · rw [if_neg hC]; exact vX22
  have vX29 : s64.valid X29 = true := by
    rw [hX29]
    by_cases hC : (X11 = 1)
    · rw [if_pos hC]; exact vZ9
    · rw [if_neg hC]; exact vZ10
  have vX30 : s64.valid X30 = true := by
    rw [hX30]
    by_cases hC : (X11 = 1)
    · rw [if_pos hC]; exact vZ9
    · rw [if_neg hC]; exact vZ11
  have vX31 : s64.valid X31 = true := by
    rw [hX31]
    by_cases hC : ((X11 = 1) ∧ (Z9 ≠ 1))
    · rw [if_pos hC]; exact hx
    · rw [if_neg hC]; exact vX24
  have vX32 : s64.valid X32 = true := by
    rw [hX32]
    by_cases hC : ((X11 = 1) ∧ (Z9 ≠ 1))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vX23
  have vX33 : i32.valid X33 = true := by
    rw [hX33]
    by_cases hC : ((X7 = 1) ∧ (X31 ≠ inf))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX34 : s64.valid X34 = true := by
    rw [hX34]
    by_cases hC : ((X7 = 1) ∧ (X33 = 0))
    · rw [if_pos hC]; exact vX32
    · rw [if_neg hC]; exact (by decide)
  have vX35 : i32.valid X35 = true := by
    rw [hX35]
    by_cases hC : ((X7 = 1) ∧ (X33 = 0))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX36 : s64.valid X36 = true := by
    rw [hX36]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact vX31
    · rw [if_neg hC]; exact vZ12
  have vX37 : s64.valid X37 = true := by
    rw [hX37]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact (hsc9 hC)
    · rw [if_neg hC]; exact vZ13
  have vX38 : s64.valid X38 = true := by
    rw [hX38]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact vZ20
    · rw [if_neg hC]; exact vZ14
  have vX39 : s64.valid X39 = true := by
    rw [hX39]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact vX31
    · rw [if_neg hC]; exact vZ15
  have vX40 : s64.valid X40 = true := by
    rw [hX40]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact hinf
    · rw [if_neg hC]; exact vZ16
  have vX41 : s64.valid X41 = true := by
    rw [hX41]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact vZ20
    · rw [if_neg hC]; exact vZ17
  have vX42 : s64.valid X42 = true := by
    rw [hX42]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vZ18
  have vX43 : s64.valid X43 = true := by
    rw [hX43]
    by_cases hC : ((X33 = 1) ∧ (Z20 ≠ 1))
    · rw [if_pos hC]; exact vX31
    · rw [if_neg hC]; exact vZ19
  have vX44 : s64.valid X44 = true := by
    rw [hX44]
    by_cases hC : (X37 ≠ (-inf))
    · rw [if_pos hC]; exact (hsc11 hC)
    · rw [if_neg hC]; exact vX37
  have vX45 : s64.valid X45 = true := by
    rw [hX45]
    by_cases hC : (X40 ≠ inf)
    · rw [if_pos hC]; exact (hsc13 hC)
    · rw [if_neg hC]; exact vX40
  have vX46 : s64.valid X46 = true := by
    rw [hX46]
    by_cases hC : ((X43 = inf) ∧ (Z20 ≠ 1))
    · rw [if_pos hC]; exact (hsc14 hC)
    · rw [if_neg hC]; exact vX42
  have vX47 : s64.valid X47 = true := by
    rw [hX47]
    by_cases hC : (X43 ≠ inf)
    · rw [if_pos hC]; exact (hsc15 hC)
    · rw [if_neg hC]; exact vX43
  have vX48 : i32.valid X48 = true := by
    rw [hX48]
    by_cases hC : ((X35 = 1) ∧ (X25 < (X36 + X34)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX49 : s64.valid X49 = true := by
    rw [hX49]
    by_cases hC : (X48 = 1)
    · rw [if_pos hC]; exact vX25
    · rw [if_neg hC]; exact hsc10
  have vX50 : s64.valid X50 = true := by
    rw [hX50]
    by_cases hC : ((X48 = 1) ∧ ((X36 + X34) = (X39 + X34)))
    · rw [if_pos hC]; exact vX25
    · rw [if_neg hC]; exact hsc12
  have vX51 : s64.valid X51 = true := by
    rw [hX51]
    by_cases hC : (((X48 = 1) ∧ ((X36 + X34) ≠ (X39 + X34))) ∧ ((X36 + X34) = X45))
    · rw [if_pos hC]; exact vX25
    · rw [if_neg hC]; exact vX45
  have vX52 : s64.valid X52 = true := by
    rw [hX52]
    by_cases hC : (((X48 = 1) ∧ (X47 ≠ inf)) ∧ (X25 < X47))
    · rw [if_pos hC]; exact vX25
    · rw [if_neg hC]; exact vX47
  have vX53 : i32.valid X53 = true := by
    rw [hX53]
    by_cases hC : ((X35 = 1) ∧ (X50 < X27))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX54 : s64.valid X54 = true := by
    rw [hX54]
    by_cases hC : (X53 = 1)
    · rw [if_pos hC]; exact vX27
    · rw [if_neg hC]; exact vX50
  have vX55 : s64.valid X55 = true := by
    rw [hX55]
    by_cases hC : ((X53 = 1) ∧ (X49 = X50))
    · rw [if_pos hC]; exact vX27
    · rw [if_neg hC]; exact vX49
  have vX56 : s64.valid X56 = true := by
    rw [hX56]
    by_cases hC : (((X53 = 1) ∧ (X49 ≠ X50)) ∧ (X44 = X50))
    · rw [if_pos hC]; exact vX27
    · rw [if_neg hC]; exact vX44
  have vX57 : s64.valid X57 = true := by
    rw [hX57]
    by_cases hC : (((X53 = 1) ∧ (X52 ≠ inf)) ∧ (X52 < X27))
    · rw [if_pos hC]; exact vX27
    · rw [if_neg hC]; exact vX52
  have vX58 : s64.valid X58 = true := by
    rw [hX58]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact vX31
    · rw [if_neg hC]; exact vZ21
  have vX59 : s64.valid X59 = true := by
    rw [hX59]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact (hsc9 hC)
    · rw [if_neg hC]; exact vZ22
  have vX60 : s64.valid X60 = true := by
    rw [hX60]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact vZ29
    · rw [if_neg hC]; exact vZ23
  have vX61 : s64.valid X61 = true := by
    rw [hX61]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact vX31
    · rw [if_neg hC]; exact vZ24
  have vX62 : s64.valid X62 = true := by
    rw [hX62]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact hinf
    · rw [if_neg hC]; exact vZ25
  have vX63 : s64.valid X63 = true := by
    rw [hX63]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact vZ29
    · rw [if_neg hC]; exact vZ26
  have vX64 : s64.valid X64 = true := by
    rw [hX64]
    by_cases hC : (X33 = 1)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vZ27
  have vX65 : s64.valid X65 = true := by
    rw [hX65]
    by_cases hC : ((X33 = 1) ∧ (Z29 ≠ 1))
    · rw [if_pos hC]; exact vX31
    · rw [if_neg hC]; exact vZ28
  have vX66 : s64.valid X66 = true := by
    rw [hX66]
    by_cases hC : (X59 ≠ (-inf))
    · rw [if_pos hC]; exact (hsc17 hC)
    · rw [if_neg hC]; exact vX59
  have vX67 : s64.valid X67 = true := by
    rw [hX67]
    by_cases hC : (X62 ≠ inf)
    · rw [if_pos hC]; exact (hsc19 hC)
    · rw [if_neg hC]; exact vX62
  have vX68 : s64.valid X68 = true := by
    rw [hX68]
    by_cases hC : ((X65 = inf) ∧ (Z29 ≠ 1))
    · rw [if_pos hC]; exact (hsc20 hC)
    · rw [if_neg hC]; exact vX64
  have vX69 : s64.valid X69 = true := by
    rw [hX69]
    by_cases hC : (X65 ≠ inf)
    · rw [if_pos hC]; exact (hsc21 hC)
    · rw [if_neg hC]; exact vX65
  have vX70 : i32.valid X70 = true := by
    rw [hX70]
    by_cases hC : ((X35 = 1) ∧ (X25 < (X58 + X34)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX71 : s64.valid X71 = true := by
    rw [hX71]
    by_cases hC : (X70 = 1)
    · rw [if_pos hC]; exact vX25
    · rw [if_neg hC]; exact hsc16
  have vX72 : s64.valid X72 = true := by
    rw [hX72]
    by_cases hC : ((X70 = 1) ∧ ((X58 + X34) = (X61 + X34)))
    · rw [if_pos hC]; exact vX25
    · rw [if_neg hC]; exact hsc18
  have vX73 : s64.valid X73 = true := by
    rw [hX73]
    by_cases hC : (((X70 = 1) ∧ ((X58 + X34) ≠ (X61 + X34))) ∧ ((X58 + X34) = X67))
    · rw [if_pos hC]; exact vX25
    · rw [if_neg hC]; exact vX67
  have vX74 : s64.valid X74 = true := by
    rw [hX74]
    by_cases hC : (((X70 = 1) ∧ (X69 ≠ inf)) ∧ (X25 < X69))
    · rw [if_pos hC]; exact vX25
    · rw [if_neg hC]; exact vX69
  have vX75 : i32.valid X75 = true := by
    rw [hX75]
    by_cases hC : ((X35 = 1) ∧ (X72 < X27))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX76 : s64.valid X76 = true := by
    rw [hX76]
    by_cases hC : (X75 = 1)
    · rw [if_pos hC]; exact vX27
    · rw [if_neg hC]; exact vX72
  have vX77 : s64.valid X77 = true := by
    rw [hX77]
    by_cases hC : ((X75 = 1) ∧ (X71 = X72))
    · rw [if_pos hC]; exact vX27
    · rw [if_neg hC]; exact vX71
  have vX78 : s64.valid X78 = true := by
    rw [hX78]
    by_cases hC : (((X75 = 1) ∧ (X71 ≠ X72)) ∧ (X66 = X72))
    · rw [if_pos hC]; exact vX27
    · rw [if_neg hC]; exact vX66
  have vX79 : s64.valid X79 = true := by
    rw [hX79]
    by_cases hC : (((X75 = 1) ∧ (X74 ≠ inf)) ∧ (X74 < X27))
    · rw [if_pos hC]; exact vX27
    · rw [if_neg hC]; exact vX74
  have vX80 : s64.valid X80 = true := by
    rw [hX80]
    by_cases hC : (X7 = 1)
    · rw [if_pos hC]; exact hinf
    · rw [if_neg hC]; exact vX31
  have vX81 : s64.valid X81 = true := by
    rw [hX81]
    by_cases hC : (X7 = 1)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact vX32
  have vX82 : i32.valid X82 = true := by rw [hX82]; exact hsc22
  have vX83 : i32.valid X83 = true := by rw [hX83]; exact hsc29
  obtain ⟨r39, h39, hr39, hp39, hv39, hc39, hn39, hw39⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.read s64 (.local 8) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 27)))) Z7 Z7
    (den_rd mv (VVB (b)) _ 8 (by rw [hnv]; decide) (hty 8 (by decide)) Z7 (.cast u64 (.variable i32 ((mv.nv + pre.length) + 27))) (by simp [NExpr.scalarOnly]) W0 (by rw [VVB_get8]; simpa [up1, up2, up3, up4, up5, up6, up7, up8, up9, up10, up11, up12, up13, up14, up15, up16, up17, up18, up19, up20, up21, up22, up23, up24, up25, up26, up27, up28, up29, up30, up31, up32, up33, up34, up35, up36, up37, up38, up39, up40, up41, up42, up43, up44, up45, up46, up47] using hl8_7) (by rw [VVB_get8]; exact hD_Z7) (by rw [VVB_get8]; exact hvl8) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell)] : List Cell)) (pre.length + 27) _ (Nat.add_assoc _ _ _) W0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell)] : List Cell) 27 _ rfl) hNW0 (VVB (b)))) (conv_s64 _ vZ7) (ApplyLoopc1_40 (mv.nv + pre.length) REST) r (by rw [List.append_assoc]; exact hrest) hret
  have hc39' : r39.cost ≤ 400 + r.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc39); exact Nat.le_trans hc39 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r38, h38, hr38, hp38, hv38, hc38, hn38, hw38⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z5⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.read s64 (.local 4) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 27)))) Z6 Z6
    (den_rd mv (VVB (b)) _ 4 (by rw [hnv]; decide) (hty 4 (by decide)) Z6 (.cast u64 (.variable i32 ((mv.nv + pre.length) + 27))) (by simp [NExpr.scalarOnly]) W0 (by rw [VVB_get4]; simpa [up1, up2, up3, up4, up5, up6, up7, up8, up9, up10, up11, up12, up13, up14, up15, up16, up17, up18, up19, up20, up21, up22, up23, up24, up25, up26, up27, up28, up29, up30, up31, up32, up33, up34, up35, up36, up37, up38, up39, up40, up41, up42, up43, up44, up45, up46, up47] using hl4_6) (by rw [VVB_get4]; exact hD_Z6) (by rw [VVB_get4]; exact hvl4) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z5⟩ : Cell)] : List Cell)) (pre.length + 27) _ (Nat.add_assoc _ _ _) W0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z5⟩ : Cell)] : List Cell) 27 _ rfl) hNW0 (VVB (b)))) (conv_s64 _ vZ6) (ApplyLoopc1_39 (mv.nv + pre.length) REST) r39 (by rw [List.append_assoc]; exact h39) hr39
  have hc38' : r38.cost ≤ 400 + r39.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc38); exact Nat.le_trans hc38 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r37, h37, hr37, hp37, hv37, hc37, hn37, hw37⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.read s64 (.local 3) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 27)))) Z5 Z5
    (den_rd mv (VVB (b)) _ 3 (by rw [hnv]; decide) (hty 3 (by decide)) Z5 (.cast u64 (.variable i32 ((mv.nv + pre.length) + 27))) (by simp [NExpr.scalarOnly]) W0 (by rw [VVB_get3]; simpa [up1, up2, up3, up4, up5, up6, up7, up8, up9, up10, up11, up12, up13, up14, up15, up16, up17, up18, up19, up20, up21, up22, up23, up24, up25, up26, up27, up28, up29, up30, up31, up32, up33, up34, up35, up36, up37, up38, up39, up40, up41, up42, up43, up44, up45, up46, up47] using hl3_5) (by rw [VVB_get3]; exact hD_Z5) (by rw [VVB_get3]; exact hvl3) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell)] : List Cell)) (pre.length + 27) _ (Nat.add_assoc _ _ _) W0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell)] : List Cell) 27 _ rfl) hNW0 (VVB (b)))) (conv_s64 _ vZ5) (ApplyLoopc1_38 (mv.nv + pre.length) REST) r38 (by rw [List.append_assoc]; exact h38) hr38
  have hc37' : r37.cost ≤ 400 + r38.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc37); exact Nat.le_trans hc37 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r36, h36, hr36, hp36, hv36, hc36, hn36, hw36⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.read s64 (.local 0) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 27)))) Z3 Z3
    (den_rd mv (VVB (b)) _ 0 (by rw [hnv]; decide) (hty 0 (by decide)) Z3 (.cast u64 (.variable i32 ((mv.nv + pre.length) + 27))) (by simp [NExpr.scalarOnly]) W0 (by rw [VVB_get0]; simpa [up1, up2, up3, up4, up5, up6, up7, up8, up9, up10, up11, up12, up13, up14, up15, up16, up17, up18, up19, up20, up21, up22, up23, up24, up25, up26, up27, up28, up29, up30, up31, up32, up33, up34, up35, up36, up37, up38, up39, up40, up41, up42, up43, up44, up45, up46, up47] using hl0_3) (by rw [VVB_get0]; exact hD_Z3) (by rw [VVB_get0]; exact hvl0) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell)] : List Cell)) (pre.length + 27) _ (Nat.add_assoc _ _ _) W0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell)] : List Cell) 27 _ rfl) hNW0 (VVB (b)))) (conv_s64 _ vZ3) (ApplyLoopc1_37 (mv.nv + pre.length) REST) r37 (by rw [List.append_assoc]; exact h37) hr37
  have hc36' : r36.cost ≤ 400 + r37.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc36); exact Nat.le_trans hc36 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r35, h35, hr35, hp35, hv35, hc35, hn35, hw35⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.variable i32 ((mv.nv + pre.length) + 20)) X8 X8
    (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell)] : List Cell)) i32 (pre.length + 20) _ (Nat.add_assoc _ _ _) X8 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell)] : List Cell) 20 _ rfl) vX8 _) (conv_i32 _ vX8) (ApplyLoopc1_36 (mv.nv + pre.length) REST) r36 (by rw [List.append_assoc]; exact h36) hr36
  have hc35' : r35.cost ≤ 400 + r36.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc35); exact Nat.le_trans hc35 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r34, h34, hr34, hp34, hv34, hc34, hn34, hw34⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.variable s64 ((mv.nv + pre.length) + 5)) x x
    (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell)] : List Cell)) s64 (pre.length + 5) _ (Nat.add_assoc _ _ _) x (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell)] : List Cell) 5 _ rfl) hx _) (conv_s64 _ hx) (ApplyLoopc1_35 (mv.nv + pre.length) REST) r35 (by rw [List.append_assoc]; exact h35) hr35
  have hc34' : r34.cost ≤ 400 + r35.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc34); exact Nat.le_trans hc34 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r33, h33, hr33, hp33, hv33, hc33, hn33, hw33⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.variable i32 ((mv.nv + pre.length) + 8)) (W0 : Int) (W0 : Int)
    (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell)] : List Cell)) i32 (pre.length + 8) _ (Nat.add_assoc _ _ _) (W0 : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell)] : List Cell) 8 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat W0 hNW0) _) (conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat W0 hNW0)) (ApplyLoopc1_34 (mv.nv + pre.length) REST) r34 (by rw [List.append_assoc]; exact h34) hr34
  have hc33' : r33.cost ≤ 400 + r34.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc33); exact Nat.le_trans hc33 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r32, h32, hr32, hp32, hv32, hc32, hn32, hw32⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.variable i32 ((mv.nv + pre.length) + 1)) (n : Int) (n : Int)
    (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell)] : List Cell)) i32 (pre.length + 1) _ (Nat.add_assoc _ _ _) (n : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell)] : List Cell) 1 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat n hnM) _) (conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat n hnM)) (ApplyLoopc1_33 (mv.nv + pre.length) REST) r33 (by rw [List.append_assoc]; exact h33) hr33
  have hc32' : r32.cost ≤ 400 + r33.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc32); exact Nat.le_trans hc32 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r31, h31, hr31, hp31, hv31, hc31, hn31, hw31⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.variable s64 ((mv.nv + pre.length) + 0)) inf inf
    (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell)] : List Cell)) s64 (pre.length + 0) _ (Nat.add_assoc _ _ _) inf (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell)] : List Cell) 0 _ rfl) hinf _) (conv_s64 _ hinf) (ApplyLoopc1_32 (mv.nv + pre.length) REST) r32 (by rw [List.append_assoc]; exact h32) hr32
  have hc31' : r31.cost ≤ 400 + r32.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc31); exact Nat.le_trans hc31 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r30, h30, hr30, hp30, hv30, hc30, hn30, hw30⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 24) (by simp) s64
    (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 22)) (.literal i32 (1))) (.variable s64 ((mv.nv + pre.length) + 5)) ((X10 = 1)) x x 0 (⟨s64, 0⟩ : Cell)
    (den_cmpw mv _ _ _ _ _ X10 1 ((X10 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 22) _ (Nat.add_assoc _ _ _) X10 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, 0⟩ : Cell)] : List Cell) 22 _ rfl) vX10 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (fun hC => (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, 0⟩ : Cell)] : List Cell)) s64 (pre.length + 5) _ (Nat.add_assoc _ _ _) x (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, 0⟩ : Cell)] : List Cell) 5 _ rfl) hx _)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, 0⟩ : Cell)] : List Cell) 24 _ rfl) rfl (by decide) rfl (fun hC => conv_s64 _ hx)
    (ApplyLoopc1_31 (mv.nv + pre.length) REST) r31 (by
      rw [set_ext0 pre _ 24 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, 0⟩ : Cell)] : List Cell).set 24 (⟨s64, if (X10 = 1) then x else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell)] : List Cell) := by
        rw [show (⟨s64, if (X10 = 1) then x else 0⟩ : Cell) = ⟨s64, X12⟩ from by rw [hX12]]
        rfl
      rw [e2]; exact h31) hr31
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc30' : r30.cost ≤ 400 + r31.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc30); exact Nat.le_trans hc30 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r29, h29, hr29, hp29, hv29, hc29, hn29, hw29⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.cast s64 (.literal i32 (0))) 0 0
    (den_castlit mv _ _ 0 (by decide) (by decide)) (conv_s64 _ (by decide)) (ApplyLoopc1_30 (mv.nv + pre.length) REST) r30 (by rw [List.append_assoc]; exact h30) hr30
  have hc29' : r29.cost ≤ 400 + r30.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc29); exact Nat.le_trans hc29 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r28, h28, hr28, hp28, hv28, hc28, hn28, hw28⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 23) (by simp) i32
    (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 18)) (.literal i32 (1))) (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 2)) (.literal i32 (3)))) (.literal i32 (1)) (((X6 = 1) ∧ ((op : Int) = 3))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_andw mv _ _ _ _ (X6 = 1) ((op : Int) = 3) (den_cmpw mv _ _ _ _ _ X6 1 ((X6 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 18) _ (Nat.add_assoc _ _ _) X6 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 18 _ rfl) vX6 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ (op : Int) 3 (((op : Int) = 3)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 2) _ (Nat.add_assoc _ _ _) (op : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 2 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat op hopM) _) (den_lit32 mv _ _ 3 (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 23 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (ApplyLoopc1_29 (mv.nv + pre.length) REST) r29 (by
      rw [set_ext0 pre _ 23 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 23 (⟨i32, if ((X6 = 1) ∧ ((op : Int) = 3)) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if ((X6 = 1) ∧ ((op : Int) = 3)) then 1 else 0⟩ : Cell) = ⟨i32, X11⟩ from by rw [hX11]]
        rfl
      rw [e2]; exact h29) hr29
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc28' : r28.cost ≤ 400 + r29.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc28); exact Nat.le_trans hc28 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r27, h27, hr27, hp27, hv27, hc27, hn27, hw27⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 22) (by simp) i32
    (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 18)) (.literal i32 (1))) (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 2)) (.literal i32 (2)))) (.literal i32 (1)) (((X6 = 1) ∧ ((op : Int) = 2))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_andw mv _ _ _ _ (X6 = 1) ((op : Int) = 2) (den_cmpw mv _ _ _ _ _ X6 1 ((X6 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 18) _ (Nat.add_assoc _ _ _) X6 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 18 _ rfl) vX6 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ (op : Int) 2 (((op : Int) = 2)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 2) _ (Nat.add_assoc _ _ _) (op : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 2 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat op hopM) _) (den_lit32 mv _ _ 2 (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 22 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (ApplyLoopc1_28 (mv.nv + pre.length) REST) r28 (by
      rw [set_ext0 pre _ 22 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 22 (⟨i32, if ((X6 = 1) ∧ ((op : Int) = 2)) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if ((X6 = 1) ∧ ((op : Int) = 2)) then 1 else 0⟩ : Cell) = ⟨i32, X10⟩ from by rw [hX10]]
        rfl
      rw [e2]; exact h28) hr28
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc27' : r27.cost ≤ 400 + r28.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc27); exact Nat.le_trans hc27 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r26, h26, hr26, hp26, hv26, hc26, hn26, hw26⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 21) (by simp) i32
    (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 18)) (.literal i32 (1))) (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 2)) (.literal i32 (1)))) (.literal i32 (1)) (((X6 = 1) ∧ ((op : Int) = 1))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_andw mv _ _ _ _ (X6 = 1) ((op : Int) = 1) (den_cmpw mv _ _ _ _ _ X6 1 ((X6 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 18) _ (Nat.add_assoc _ _ _) X6 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 18 _ rfl) vX6 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ (op : Int) 1 (((op : Int) = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 2) _ (Nat.add_assoc _ _ _) (op : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 2 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat op hopM) _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 21 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (ApplyLoopc1_27 (mv.nv + pre.length) REST) r27 (by
      rw [set_ext0 pre _ 21 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 21 (⟨i32, if ((X6 = 1) ∧ ((op : Int) = 1)) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if ((X6 = 1) ∧ ((op : Int) = 1)) then 1 else 0⟩ : Cell) = ⟨i32, X9⟩ from by rw [hX9]]
        rfl
      rw [e2]; exact h27) hr27
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc26' : r26.cost ≤ 400 + r27.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc26); exact Nat.le_trans hc26 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r25, h25, hr25, hp25, hv25, hc25, hn25, hw25⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 20) (by simp) i32
    (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 18)) (.literal i32 (1))) (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 2)) (.literal i32 (0)))) (.literal i32 (1)) (((X6 = 1) ∧ ((op : Int) = 0))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_andw mv _ _ _ _ (X6 = 1) ((op : Int) = 0) (den_cmpw mv _ _ _ _ _ X6 1 ((X6 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 18) _ (Nat.add_assoc _ _ _) X6 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 18 _ rfl) vX6 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ (op : Int) 0 (((op : Int) = 0)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 2) _ (Nat.add_assoc _ _ _) (op : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 2 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat op hopM) _) (den_lit32 mv _ _ 0 (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 20 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (ApplyLoopc1_26 (mv.nv + pre.length) REST) r26 (by
      rw [set_ext0 pre _ 20 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 20 (⟨i32, if ((X6 = 1) ∧ ((op : Int) = 0)) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if ((X6 = 1) ∧ ((op : Int) = 0)) then 1 else 0⟩ : Cell) = ⟨i32, X8⟩ from by rw [hX8]]
        rfl
      rw [e2]; exact h26) hr26
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc25' : r25.cost ≤ 400 + r26.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc25); exact Nat.le_trans hc25 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r24, h24, hr24, hp24, hv24, hc24, hn24, hw24⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.literal i32 (0)) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 _ (by decide)) (ApplyLoopc1_25 (mv.nv + pre.length) REST) r25 (by rw [List.append_assoc]; exact h25) hr25
  have hc24' : r24.cost ≤ 400 + r25.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc24); exact Nat.le_trans hc24 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r23, h23, hr23, hp23, hv23, hc23, hn23, hw23⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.literal i32 (0)) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 _ (by decide)) (ApplyLoopc1_24 (mv.nv + pre.length) REST) r24 (by rw [List.append_assoc]; exact h24) hr24
  have hc23' : r23.cost ≤ 400 + r24.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc23); exact Nat.le_trans hc23 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r22, h22, hr22, hp22, hv22, hc22, hn22, hw22⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.literal i32 (0)) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 _ (by decide)) (ApplyLoopc1_23 (mv.nv + pre.length) REST) r23 (by rw [List.append_assoc]; exact h23) hr23
  have hc22' : r22.cost ≤ 400 + r23.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc22); exact Nat.le_trans hc22 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r21, h21, hr21, hp21, hv21, hc21, hn21, hw21⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.literal i32 (0)) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 _ (by decide)) (ApplyLoopc1_22 (mv.nv + pre.length) REST) r22 (by rw [List.append_assoc]; exact h22) hr22
  have hc21' : r21.cost ≤ 400 + r22.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc21); exact Nat.le_trans hc21 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r20, h20, hr20, hp20, hv20, hc20, hn20, hw20⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 19) (by simp) i32
    (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 15)) (.literal i32 (0))) (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 18)) (.literal i32 (0)))) (.literal i32 (1)) (((X2 = 0) ∧ (X6 = 0))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_andw mv _ _ _ _ (X2 = 0) (X6 = 0) (den_cmpw mv _ _ _ _ _ X2 0 ((X2 = 0)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 15) _ (Nat.add_assoc _ _ _) X2 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 15 _ rfl) vX2 _) (den_lit32 mv _ _ 0 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ X6 0 ((X6 = 0)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 18) _ (Nat.add_assoc _ _ _) X6 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 18 _ rfl) vX6 _) (den_lit32 mv _ _ 0 (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 19 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (ApplyLoopc1_21 (mv.nv + pre.length) REST) r21 (by
      rw [set_ext0 pre _ 19 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 19 (⟨i32, if ((X2 = 0) ∧ (X6 = 0)) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if ((X2 = 0) ∧ (X6 = 0)) then 1 else 0⟩ : Cell) = ⟨i32, X7⟩ from by rw [hX7]]
        rfl
      rw [e2]; exact h21) hr21
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc20' : r20.cost ≤ 400 + r21.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc20); exact Nat.le_trans hc20 (Nat.add_le_add_right (by decide) _)
  clear hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13 hX14 hX15 hX16 hX17 hX18 hX19 hX20 hX21 hX22 hX23 hX24 hX25 hX26 hX27 hX28 hX29 hX30 hX31 hX32 hX33 hX34 hX35 hX36 hX37 hX38 hX39 hX40 hX41 hX42 hX43 hX44 hX45 hX46 hX47 hX48 hX49 hX50 hX51 hX52 hX53 hX54 hX55 hX56 hX57 hX58 hX59 hX60 hX61 hX62 hX63 hX64 hX65 hX66 hX67 hX68 hX69 hX70 hX71 hX72 hX73 hX74 hX75 hX76 hX77 hX78 hX79 hX80 hX81 hX82 hX83
  refine ⟨r20, h20, hr20, ?_, ?_, ?_, ?_⟩
  · rw [hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29, hp30, hp31, hp32, hp33, hp34, hp35, hp36, hp37, hp38, hp39]
  · rw [hv20, hv21, hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31, hv32, hv33, hv34, hv35, hv36, hv37, hv38, hv39]
  · omega
  · omega


end Proofs.BeatsExec
