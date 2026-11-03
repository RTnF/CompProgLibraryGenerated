import Proofs.BeatsExec_CalcLoopDefs
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
theorem CalcLoop_ch0 (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (b : BS) (P : List Cell)
    (inf : Int) (n op qa qb sp : Nat) (x : Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hopM : op < M31) (hqaM : qa < M31) (hqbM : qb < M31) (hspM : sp < M31) (hpos : 0 < sp) (hx : s64.valid x = true) (hvl0 : ∀ w ∈ b.mxv, s64.valid w = true) (hvl1 : ∀ w ∈ b.smx, s64.valid w = true) (hvl2 : ∀ w ∈ b.mxc, s64.valid w = true) (hvl3 : ∀ w ∈ b.mnv, s64.valid w = true) (hvl4 : ∀ w ∈ b.smn, s64.valid w = true) (hvl5 : ∀ w ∈ b.mnc, s64.valid w = true) (hvl6 : ∀ w ∈ b.len, s64.valid w = true) (hvl7 : ∀ w ∈ b.ladd, s64.valid w = true) (hvl8 : ∀ w ∈ b.lval, s64.valid w = true) (hvl11 : ∀ w ∈ b.sk, i32.valid w = true) (hvl12 : ∀ w ∈ b.sl, i32.valid w = true) (hvl13 : ∀ w ∈ b.sr, i32.valid w = true) (W0 : Nat) (hNW0 : W0 < M31) (hD_W0 : b.sk.getD (sp - 1) 0 = (W0 : Int)) (W1 : Nat) (hNW1 : W1 < M31) (hD_W1 : b.sl.getD (sp - 1) 0 = (W1 : Int)) (W2 : Nat) (hNW2 : W2 < M31) (hD_W2 : b.sr.getD (sp - 1) 0 = (W2 : Int)) (Z3 : Int) (hD_Z3 : b.mxv.getD W0 0 = Z3) (Z4 : Int) (hD_Z4 : b.mnv.getD W0 0 = Z4) (Z5 : Int) (hD_Z5 : b.lval.getD W0 0 = Z5) (Z6 : Int) (hD_Z6 : b.ladd.getD W0 0 = Z6) (Z7 : Int) (hD_Z7 : b.mxv.getD (2 * W0 + 1) 0 = Z7) (Z8 : Int) (hD_Z8 : b.smx.getD (2 * W0 + 1) 0 = Z8) (Z9 : Int) (hD_Z9 : b.mxc.getD (2 * W0 + 1) 0 = Z9) (Z10 : Int) (hD_Z10 : b.mnv.getD (2 * W0 + 1) 0 = Z10) (Z11 : Int) (hD_Z11 : b.smn.getD (2 * W0 + 1) 0 = Z11) (Z12 : Int) (hD_Z12 : b.mnc.getD (2 * W0 + 1) 0 = Z12) (Z13 : Int) (hD_Z13 : b.ladd.getD (2 * W0 + 1) 0 = Z13) (Z14 : Int) (hD_Z14 : b.lval.getD (2 * W0 + 1) 0 = Z14) (Z15 : Int) (hD_Z15 : b.len.getD (2 * W0 + 1) 0 = Z15) (Z16 : Int) (hD_Z16 : b.mxv.getD (2 * W0 + 2) 0 = Z16) (Z17 : Int) (hD_Z17 : b.smx.getD (2 * W0 + 2) 0 = Z17) (Z18 : Int) (hD_Z18 : b.mxc.getD (2 * W0 + 2) 0 = Z18) (Z19 : Int) (hD_Z19 : b.mnv.getD (2 * W0 + 2) 0 = Z19) (Z20 : Int) (hD_Z20 : b.smn.getD (2 * W0 + 2) 0 = Z20) (Z21 : Int) (hD_Z21 : b.mnc.getD (2 * W0 + 2) 0 = Z21) (Z22 : Int) (hD_Z22 : b.ladd.getD (2 * W0 + 2) 0 = Z22) (Z23 : Int) (hD_Z23 : b.lval.getD (2 * W0 + 2) 0 = Z23) (Z24 : Int) (hD_Z24 : b.len.getD (2 * W0 + 2) 0 = Z24) (hl11_0 : (sp - 1) < (b.sk).length) (hl12_1 : (sp - 1) < (b.sl).length) (hl13_2 : (sp - 1) < (b.sr).length) (hl0_3 : W0 < (b.mxv).length) (hl3_4 : W0 < (b.mnv).length) (hl8_5 : W0 < (b.lval).length) (hl7_6 : W0 < (b.ladd).length) (hl0_7 : (2 * W0 + 1) < (b.mxv).length) (hl1_8 : (2 * W0 + 1) < (b.smx).length) (hl2_9 : (2 * W0 + 1) < (b.mxc).length) (hl3_10 : (2 * W0 + 1) < (b.mnv).length) (hl4_11 : (2 * W0 + 1) < (b.smn).length) (hl5_12 : (2 * W0 + 1) < (b.mnc).length) (hl7_13 : (2 * W0 + 1) < (b.ladd).length) (hl8_14 : (2 * W0 + 1) < (b.lval).length) (hl6_15 : (2 * W0 + 1) < (b.len).length) (hl0_16 : (2 * W0 + 2) < (b.mxv).length) (hl1_17 : (2 * W0 + 2) < (b.smx).length) (hl2_18 : (2 * W0 + 2) < (b.mxc).length) (hl3_19 : (2 * W0 + 2) < (b.mnv).length) (hl4_20 : (2 * W0 + 2) < (b.smn).length) (hl5_21 : (2 * W0 + 2) < (b.mnc).length) (hl7_22 : (2 * W0 + 2) < (b.ladd).length) (hl8_23 : (2 * W0 + 2) < (b.lval).length) (hl6_24 : (2 * W0 + 2) < (b.len).length) (hl11_25 : ((sp - 1) + 1) < (b.sk).length) (hl12_26 : ((sp - 1) + 1) < (b.sl).length) (hl13_27 : ((sp - 1) + 1) < (b.sr).length) (hk1_W0 : (2 * W0 + 1) < M31) (hk2_W0 : (2 * W0 + 2) < M31) (hix2 : ((sp - 1) + 1) < M31) (hix3 : ((sp - 1) + 1) < M31) (hix4 : ((sp - 1) + 1) < M31) (X0 : Int) (hX0 : X0 = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0)) (X1 : Int) (hX1 : X1 = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0)) (X2 : Int) (hX2 : X2 = (if ((X0 = 0) ∧ (X1 = 1)) then 1 else 0)) (X3 : Int) (hX3 : X3 = (if ((X0 = 0) ∧ (X2 = 0)) then 1 else 0)) (X4 : Int) (hX4 : X4 = (if (((X2 = 1) ∧ ((op : Int) = 0)) ∧ (x < Z3)) then Z3 else x)) (X5 : Int) (hX5 : X5 = (if (((X2 = 1) ∧ ((op : Int) = 1)) ∧ (Z4 < X4)) then Z4 else X4)) (X6 : Int) (hX6 : X6 = (if ((X3 = 1) ∧ (Z5 ≠ inf)) then 1 else 0)) (X7 : Int) (hX7 : X7 = (if ((X3 = 1) ∧ (X6 = 0)) then Z6 else 0)) (X8 : Int) (hX8 : X8 = (if ((X3 = 1) ∧ (X6 = 0)) then 1 else 0)) (X9 : Int) (hX9 : X9 = (if (X6 = 1) then Z5 else Z7)) (X10 : Int) (hX10 : X10 = (if (X6 = 1) then (-inf) else Z8)) (X11 : Int) (hX11 : X11 = (if (X6 = 1) then Z15 else Z9)) (X12 : Int) (hX12 : X12 = (if (X6 = 1) then Z5 else Z10)) (X13 : Int) (hX13 : X13 = (if (X6 = 1) then inf else Z11)) (X14 : Int) (hX14 : X14 = (if (X6 = 1) then Z15 else Z12)) (X15 : Int) (hX15 : X15 = (if (X6 = 1) then 0 else Z13)) (X16 : Int) (hX16 : X16 = (if ((X6 = 1) ∧ (Z15 ≠ 1)) then Z5 else Z14)) (X17 : Int) (hX17 : X17 = (if (X10 ≠ (-inf)) then (X10 + X7) else X10)) (X18 : Int) (hX18 : X18 = (if (X13 ≠ inf) then (X13 + X7) else X13)) (X19 : Int) (hX19 : X19 = (if ((X16 = inf) ∧ (Z15 ≠ 1)) then (X15 + X7) else X15)) (X20 : Int) (hX20 : X20 = (if (X16 ≠ inf) then (X16 + X7) else X16)) (X21 : Int) (hX21 : X21 = (if ((X8 = 1) ∧ (Z3 < (X9 + X7))) then 1 else 0)) (X22 : Int) (hX22 : X22 = (if (X21 = 1) then Z3 else (X9 + X7))) (X23 : Int) (hX23 : X23 = (if ((X21 = 1) ∧ ((X9 + X7) = (X12 + X7))) then Z3 else (X12 + X7))) (X24 : Int) (hX24 : X24 = (if (((X21 = 1) ∧ ((X9 + X7) ≠ (X12 + X7))) ∧ ((X9 + X7) = X18)) then Z3 else X18)) (X25 : Int) (hX25 : X25 = (if (((X21 = 1) ∧ (X20 ≠ inf)) ∧ (Z3 < X20)) then Z3 else X20)) (X26 : Int) (hX26 : X26 = (if ((X8 = 1) ∧ (X23 < Z4)) then 1 else 0)) (X27 : Int) (hX27 : X27 = (if (X26 = 1) then Z4 else X23)) (X28 : Int) (hX28 : X28 = (if ((X26 = 1) ∧ (X22 = X23)) then Z4 else X22)) (X29 : Int) (hX29 : X29 = (if (((X26 = 1) ∧ (X22 ≠ X23)) ∧ (X17 = X23)) then Z4 else X17)) (X30 : Int) (hX30 : X30 = (if (((X26 = 1) ∧ (X25 ≠ inf)) ∧ (X25 < Z4)) then Z4 else X25)) (X31 : Int) (hX31 : X31 = (if (X6 = 1) then Z5 else Z16)) (X32 : Int) (hX32 : X32 = (if (X6 = 1) then (-inf) else Z17)) (X33 : Int) (hX33 : X33 = (if (X6 = 1) then Z24 else Z18)) (X34 : Int) (hX34 : X34 = (if (X6 = 1) then Z5 else Z19)) (X35 : Int) (hX35 : X35 = (if (X6 = 1) then inf else Z20)) (X36 : Int) (hX36 : X36 = (if (X6 = 1) then Z24 else Z21)) (X37 : Int) (hX37 : X37 = (if (X6 = 1) then 0 else Z22)) (X38 : Int) (hX38 : X38 = (if ((X6 = 1) ∧ (Z24 ≠ 1)) then Z5 else Z23)) (X39 : Int) (hX39 : X39 = (if (X32 ≠ (-inf)) then (X32 + X7) else X32)) (X40 : Int) (hX40 : X40 = (if (X35 ≠ inf) then (X35 + X7) else X35)) (X41 : Int) (hX41 : X41 = (if ((X38 = inf) ∧ (Z24 ≠ 1)) then (X37 + X7) else X37)) (X42 : Int) (hX42 : X42 = (if (X38 ≠ inf) then (X38 + X7) else X38)) (X43 : Int) (hX43 : X43 = (if ((X8 = 1) ∧ (Z3 < (X31 + X7))) then 1 else 0)) (X44 : Int) (hX44 : X44 = (if (X43 = 1) then Z3 else (X31 + X7))) (X45 : Int) (hX45 : X45 = (if ((X43 = 1) ∧ ((X31 + X7) = (X34 + X7))) then Z3 else (X34 + X7))) (X46 : Int) (hX46 : X46 = (if (((X43 = 1) ∧ ((X31 + X7) ≠ (X34 + X7))) ∧ ((X31 + X7) = X40)) then Z3 else X40)) (X47 : Int) (hX47 : X47 = (if (((X43 = 1) ∧ (X42 ≠ inf)) ∧ (Z3 < X42)) then Z3 else X42)) (X48 : Int) (hX48 : X48 = (if ((X8 = 1) ∧ (X45 < Z4)) then 1 else 0)) (X49 : Int) (hX49 : X49 = (if (X48 = 1) then Z4 else X45)) (X50 : Int) (hX50 : X50 = (if ((X48 = 1) ∧ (X44 = X45)) then Z4 else X44)) (X51 : Int) (hX51 : X51 = (if (((X48 = 1) ∧ (X44 ≠ X45)) ∧ (X39 = X45)) then Z4 else X39)) (X52 : Int) (hX52 : X52 = (if (((X48 = 1) ∧ (X47 ≠ inf)) ∧ (X47 < Z4)) then Z4 else X47)) (X53 : Int) (hX53 : X53 = (if (X3 = 1) then inf else Z5)) (X54 : Int) (hX54 : X54 = (if (X3 = 1) then 0 else Z6)) (X55 : Int) (hX55 : X55 = (((sp - 1 : Nat) : Int) + (2 * X3))) (hsc0 : i32.valid ((sp : Int) - 1) = true) (hsc1 : ((X6 = 1)) → s64.valid (-inf) = true) (hsc2 : s64.valid (X9 + X7) = true) (hsc3 : s64.valid (-inf) = true) (hsc4 : ((X10 ≠ (-inf))) → s64.valid (X10 + X7) = true) (hsc5 : s64.valid (X12 + X7) = true) (hsc6 : ((X13 ≠ inf)) → s64.valid (X13 + X7) = true) (hsc7 : (((X16 = inf) ∧ (Z15 ≠ 1))) → s64.valid (X15 + X7) = true) (hsc8 : ((X16 ≠ inf)) → s64.valid (X16 + X7) = true) (hsc9 : s64.valid (X31 + X7) = true) (hsc10 : ((X32 ≠ (-inf))) → s64.valid (X32 + X7) = true) (hsc11 : s64.valid (X34 + X7) = true) (hsc12 : ((X35 ≠ inf)) → s64.valid (X35 + X7) = true) (hsc13 : (((X38 = inf) ∧ (Z24 ≠ 1))) → s64.valid (X37 + X7) = true) (hsc14 : ((X38 ≠ inf)) → s64.valid (X38 + X7) = true) (hsc15 : i32.valid ((W1 : Int) + (W2 : Int)) = true) (hsc17 : i32.valid (2 * (W0 : Int)) = true) (hsc18 : i32.valid ((2 * (W0 : Int)) + 2) = true) (hsc19 : i32.valid ((2 * (W0 : Int)) + 1) = true) (hsc20 : i32.valid (2 * X3) = true) (hsc21 : i32.valid (((sp - 1 : Nat) : Int) + (2 * X3)) = true) (fu : Nat)
    (REST : Command) (r : PRM) (hrest : pexecM mv fu REST (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell))) (VVB b) = some r) (hret : r.ret = none) :
    ∃ r0 : PRM, pexecM mv fu (CalcLoopc0 (mv.nv + pre.length) REST) (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell)] : List Cell))) (VVB b) = some r0 ∧ r0.ret = none ∧
      r0.ps = r.ps ∧ r0.vv = r.vv ∧ r0.cost ≤ 8400 + r.cost ∧ r0.wk ≤ 0 + r.wk := by
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
  obtain ⟨r19, h19, hr19, hp19, hv19, hc19, hn19, hw19⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.variable i32 ((mv.nv + pre.length) + 15)) X3 X3
    (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell)] : List Cell)) i32 (pre.length + 15) _ (Nat.add_assoc _ _ _) X3 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell)] : List Cell) 15 _ rfl) vX3 _) (conv_i32 _ vX3) (CalcLoopc0_20 (mv.nv + pre.length) REST) r (by rw [List.append_assoc]; exact hrest) hret
  have hc19' : r19.cost ≤ 400 + r.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc19); exact Nat.le_trans hc19 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r18, h18, hr18, hp18, hv18, hc18, hn18, hw18⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.variable i32 ((mv.nv + pre.length) + 7)) (W0 : Int) (W0 : Int)
    (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell)] : List Cell)) i32 (pre.length + 7) _ (Nat.add_assoc _ _ _) (W0 : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell)] : List Cell) 7 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat W0 hNW0) _) (conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat W0 hNW0)) (CalcLoopc0_19 (mv.nv + pre.length) REST) r19 (by rw [List.append_assoc]; exact h19) hr19
  have hc18' : r18.cost ≤ 400 + r19.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc18); exact Nat.le_trans hc18 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r17, h17, hr17, hp17, hv17, hc17, hn17, hw17⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.variable i32 ((mv.nv + pre.length) + 1)) (n : Int) (n : Int)
    (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell)] : List Cell)) i32 (pre.length + 1) _ (Nat.add_assoc _ _ _) (n : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell)] : List Cell) 1 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat n hnM) _) (conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat n hnM)) (CalcLoopc0_18 (mv.nv + pre.length) REST) r18 (by rw [List.append_assoc]; exact h18) hr18
  have hc17' : r17.cost ≤ 400 + r18.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc17); exact Nat.le_trans hc17 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r16, h16, hr16, hp16, hv16, hc16, hn16, hw16⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.variable s64 ((mv.nv + pre.length) + 0)) inf inf
    (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) s64 (pre.length + 0) _ (Nat.add_assoc _ _ _) inf (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 0 _ rfl) hinf _) (conv_s64 _ hinf) (CalcLoopc0_17 (mv.nv + pre.length) REST) r17 (by rw [List.append_assoc]; exact h17) hr17
  have hc16' : r16.cost ≤ 400 + r17.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc16); exact Nat.le_trans hc16 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r15, h15, hr15, hp15, hv15, hc15, hn15, hw15⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 5) (by simp) s64
    (.logical true (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 14)) (.literal i32 (1))) (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 2)) (.literal i32 (1)))) (.binary bT .lt (.variable s64 ((mv.nv + pre.length) + 11)) (.variable s64 ((mv.nv + pre.length) + 5)))) (.variable s64 ((mv.nv + pre.length) + 11)) ((((X2 = 1) ∧ ((op : Int) = 1)) ∧ (Z4 < X4))) Z4 Z4 X4 (⟨s64, X4⟩ : Cell)
    (den_andw mv _ _ _ _ ((X2 = 1) ∧ ((op : Int) = 1)) (Z4 < X4) (den_andw mv _ _ _ _ (X2 = 1) ((op : Int) = 1) (den_cmpw mv _ _ _ _ _ X2 1 ((X2 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) i32 (pre.length + 14) _ (Nat.add_assoc _ _ _) X2 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 14 _ rfl) vX2 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ (op : Int) 1 (((op : Int) = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) i32 (pre.length + 2) _ (Nat.add_assoc _ _ _) (op : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 2 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat op hopM) _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (den_cmpw mv _ _ _ _ _ Z4 X4 ((Z4 < X4)) (lt_conv _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) s64 (pre.length + 11) _ (Nat.add_assoc _ _ _) Z4 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 11 _ rfl) vZ4 _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) s64 (pre.length + 5) _ (Nat.add_assoc _ _ _) X4 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 5 _ rfl) vX4 _) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) s64 (pre.length + 11) _ (Nat.add_assoc _ _ _) Z4 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 11 _ rfl) vZ4 _)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 5 _ rfl) rfl vX4 rfl (fun hC => conv_s64 _ vZ4)
    (CalcLoopc0_16 (mv.nv + pre.length) REST) r16 (by
      rw [set_ext0 pre _ 5 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell).set 5 (⟨s64, if (((X2 = 1) ∧ ((op : Int) = 1)) ∧ (Z4 < X4)) then Z4 else X4⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) := by
        rw [show (⟨s64, if (((X2 = 1) ∧ ((op : Int) = 1)) ∧ (Z4 < X4)) then Z4 else X4⟩ : Cell) = ⟨s64, X5⟩ from by rw [hX5]]
        rfl
      rw [e2]; exact h16) hr16
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc15' : r15.cost ≤ 400 + r16.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc15); exact Nat.le_trans hc15 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r14, h14, hr14, hp14, hv14, hc14, hn14, hw14⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 5) (by simp) s64
    (.logical true (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 14)) (.literal i32 (1))) (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 2)) (.literal i32 (0)))) (.binary bT .lt (.variable s64 ((mv.nv + pre.length) + 5)) (.variable s64 ((mv.nv + pre.length) + 10)))) (.variable s64 ((mv.nv + pre.length) + 10)) ((((X2 = 1) ∧ ((op : Int) = 0)) ∧ (x < Z3))) Z3 Z3 x (⟨s64, x⟩ : Cell)
    (den_andw mv _ _ _ _ ((X2 = 1) ∧ ((op : Int) = 0)) (x < Z3) (den_andw mv _ _ _ _ (X2 = 1) ((op : Int) = 0) (den_cmpw mv _ _ _ _ _ X2 1 ((X2 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) i32 (pre.length + 14) _ (Nat.add_assoc _ _ _) X2 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 14 _ rfl) vX2 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ (op : Int) 0 (((op : Int) = 0)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) i32 (pre.length + 2) _ (Nat.add_assoc _ _ _) (op : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 2 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat op hopM) _) (den_lit32 mv _ _ 0 (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (den_cmpw mv _ _ _ _ _ x Z3 ((x < Z3)) (lt_conv _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) s64 (pre.length + 5) _ (Nat.add_assoc _ _ _) x (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 5 _ rfl) hx _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) s64 (pre.length + 10) _ (Nat.add_assoc _ _ _) Z3 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 10 _ rfl) vZ3 _) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell)) s64 (pre.length + 10) _ (Nat.add_assoc _ _ _) Z3 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 10 _ rfl) vZ3 _)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) 5 _ rfl) rfl hx rfl (fun hC => conv_s64 _ vZ3)
    (CalcLoopc0_15 (mv.nv + pre.length) REST) r15 (by
      rw [set_ext0 pre _ 5 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell).set 5 (⟨s64, if (((X2 = 1) ∧ ((op : Int) = 0)) ∧ (x < Z3)) then Z3 else x⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) := by
        rw [show (⟨s64, if (((X2 = 1) ∧ ((op : Int) = 0)) ∧ (x < Z3)) then Z3 else x⟩ : Cell) = ⟨s64, X4⟩ from by rw [hX4]]
        rfl
      rw [e2]; exact h15) hr15
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc14' : r14.cost ≤ 400 + r15.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc14); exact Nat.le_trans hc14 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r13, h13, hr13, hp13, hv13, hc13, hn13, hw13⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 15) (by simp) i32
    (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 12)) (.literal i32 (0))) (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 14)) (.literal i32 (0)))) (.literal i32 (1)) (((X0 = 0) ∧ (X2 = 0))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_andw mv _ _ _ _ (X0 = 0) (X2 = 0) (den_cmpw mv _ _ _ _ _ X0 0 ((X0 = 0)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 12) _ (Nat.add_assoc _ _ _) X0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 12 _ rfl) vX0 _) (den_lit32 mv _ _ 0 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ X2 0 ((X2 = 0)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 14) _ (Nat.add_assoc _ _ _) X2 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 14 _ rfl) vX2 _) (den_lit32 mv _ _ 0 (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 15 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (CalcLoopc0_14 (mv.nv + pre.length) REST) r14 (by
      rw [set_ext0 pre _ 15 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 15 (⟨i32, if ((X0 = 0) ∧ (X2 = 0)) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if ((X0 = 0) ∧ (X2 = 0)) then 1 else 0⟩ : Cell) = ⟨i32, X3⟩ from by rw [hX3]]
        rfl
      rw [e2]; exact h14) hr14
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc13' : r13.cost ≤ 400 + r14.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc13); exact Nat.le_trans hc13 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r12, h12, hr12, hp12, hv12, hc12, hn12, hw12⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.literal i32 (0)) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 _ (by decide)) (CalcLoopc0_13 (mv.nv + pre.length) REST) r13 (by rw [List.append_assoc]; exact h13) hr13
  have hc12' : r12.cost ≤ 400 + r13.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc12); exact Nat.le_trans hc12 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r11, h11, hr11, hp11, hv11, hc11, hn11, hw11⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 14) (by simp) i32
    (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 12)) (.literal i32 (0))) (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 13)) (.literal i32 (1)))) (.literal i32 (1)) (((X0 = 0) ∧ (X1 = 1))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_andw mv _ _ _ _ (X0 = 0) (X1 = 1) (den_cmpw mv _ _ _ _ _ X0 0 ((X0 = 0)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 12) _ (Nat.add_assoc _ _ _) X0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 12 _ rfl) vX0 _) (den_lit32 mv _ _ 0 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ X1 1 ((X1 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 13) _ (Nat.add_assoc _ _ _) X1 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 13 _ rfl) vX1 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 14 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (CalcLoopc0_12 (mv.nv + pre.length) REST) r12 (by
      rw [set_ext0 pre _ 14 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 14 (⟨i32, if ((X0 = 0) ∧ (X1 = 1)) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if ((X0 = 0) ∧ (X1 = 1)) then 1 else 0⟩ : Cell) = ⟨i32, X2⟩ from by rw [hX2]]
        rfl
      rw [e2]; exact h12) hr12
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc11' : r11.cost ≤ 400 + r12.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc11); exact Nat.le_trans hc11 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r10, h10, hr10, hp10, hv10, hc10, hn10, hw10⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.literal i32 (0)) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 _ (by decide)) (CalcLoopc0_11 (mv.nv + pre.length) REST) r11 (by rw [List.append_assoc]; exact h11) hr11
  have hc10' : r10.cost ≤ 400 + r11.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc10); exact Nat.le_trans hc10 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r9, h9, hr9, hp9, hv9, hc9, hn9, hw9⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 13) (by simp) i32
    (.logical true (.binary bT .le (.variable i32 ((mv.nv + pre.length) + 3)) (.variable i32 ((mv.nv + pre.length) + 8))) (.binary bT .le (.variable i32 ((mv.nv + pre.length) + 9)) (.variable i32 ((mv.nv + pre.length) + 4)))) (.literal i32 (1)) ((((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int)))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_andw mv _ _ _ _ ((qa : Int) ≤ (W1 : Int)) ((W2 : Int) ≤ (qb : Int)) (den_cmpw mv _ _ _ _ _ (qa : Int) (W1 : Int) (((qa : Int) ≤ (W1 : Int))) (le_conv _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 3) _ (Nat.add_assoc _ _ _) (qa : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 3 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat qa hqaM) _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 8) _ (Nat.add_assoc _ _ _) (W1 : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 8 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat W1 hNW1) _) rfl rfl) (den_cmpw mv _ _ _ _ _ (W2 : Int) (qb : Int) (((W2 : Int) ≤ (qb : Int))) (le_conv _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 9) _ (Nat.add_assoc _ _ _) (W2 : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 9 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat W2 hNW2) _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 4) _ (Nat.add_assoc _ _ _) (qb : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 4 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat qb hqbM) _) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 13 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (CalcLoopc0_10 (mv.nv + pre.length) REST) r10 (by
      rw [set_ext0 pre _ 13 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 13 (⟨i32, if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0⟩ : Cell) = ⟨i32, X1⟩ from by rw [hX1]]
        rfl
      rw [e2]; exact h10) hr10
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc9' : r9.cost ≤ 400 + r10.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc9); exact Nat.le_trans hc9 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r8, h8, hr8, hp8, hv8, hc8, hn8, hw8⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.literal i32 (0)) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 _ (by decide)) (CalcLoopc0_9 (mv.nv + pre.length) REST) r9 (by rw [List.append_assoc]; exact h9) hr9
  have hc8' : r8.cost ≤ 400 + r9.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc8); exact Nat.le_trans hc8 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r7, h7, hr7, hp7, hv7, hc7, hn7, hw7⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 12) (by simp) i32
    (.logical false (.binary bT .le (.variable i32 ((mv.nv + pre.length) + 4)) (.variable i32 ((mv.nv + pre.length) + 8))) (.binary bT .le (.variable i32 ((mv.nv + pre.length) + 9)) (.variable i32 ((mv.nv + pre.length) + 3)))) (.literal i32 (1)) ((((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int)))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_orw mv _ _ _ _ ((qb : Int) ≤ (W1 : Int)) ((W2 : Int) ≤ (qa : Int)) (den_cmpw mv _ _ _ _ _ (qb : Int) (W1 : Int) (((qb : Int) ≤ (W1 : Int))) (le_conv _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 4) _ (Nat.add_assoc _ _ _) (qb : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 4 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat qb hqbM) _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 8) _ (Nat.add_assoc _ _ _) (W1 : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 8 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat W1 hNW1) _) rfl rfl) (den_cmpw mv _ _ _ _ _ (W2 : Int) (qa : Int) (((W2 : Int) ≤ (qa : Int))) (le_conv _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 9) _ (Nat.add_assoc _ _ _) (W2 : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 9 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat W2 hNW2) _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 3) _ (Nat.add_assoc _ _ _) (qa : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 3 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat qa hqaM) _) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 12 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (CalcLoopc0_8 (mv.nv + pre.length) REST) r8 (by
      rw [set_ext0 pre _ 12 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 12 (⟨i32, if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0⟩ : Cell) = ⟨i32, X0⟩ from by rw [hX0]]
        rfl
      rw [e2]; exact h8) hr8
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc7' : r7.cost ≤ 400 + r8.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc7); exact Nat.le_trans hc7 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r6, h6, hr6, hp6, hv6, hc6, hn6, hw6⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.literal i32 (0)) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 _ (by decide)) (CalcLoopc0_7 (mv.nv + pre.length) REST) r7 (by rw [List.append_assoc]; exact h7) hr7
  have hc6' : r6.cost ≤ 400 + r7.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc6); exact Nat.le_trans hc6 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r5, h5, hr5, hp5, hv5, hc5, hn5, hw5⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.read s64 (.local 3) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 7)))) Z4 Z4
    (den_rd mv (VVB (b)) _ 3 (by rw [hnv]; decide) (hty 3 (by decide)) Z4 (.cast u64 (.variable i32 ((mv.nv + pre.length) + 7))) (by simp [NExpr.scalarOnly]) W0 (by rw [VVB_get3]; simpa [uc1, uc2, uc3, uc4, uc5, uc6, uc7, uc8, uc9, uc10, uc11, uc12, uc13, uc14, uc15, uc16, uc17, uc18, uc19, uc20, uc21, uc22, uc23, uc24] using hl3_4) (by rw [VVB_get3]; exact hD_Z4) (by rw [VVB_get3]; exact hvl3) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell)] : List Cell)) (pre.length + 7) _ (Nat.add_assoc _ _ _) W0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell)] : List Cell) 7 _ rfl) hNW0 (VVB (b)))) (conv_s64 _ vZ4) (CalcLoopc0_6 (mv.nv + pre.length) REST) r6 (by rw [List.append_assoc]; exact h6) hr6
  have hc5' : r5.cost ≤ 400 + r6.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc5); exact Nat.le_trans hc5 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r4, h4, hr4, hp4, hv4, hc4, hn4, hw4⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.read s64 (.local 0) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 7)))) Z3 Z3
    (den_rd mv (VVB (b)) _ 0 (by rw [hnv]; decide) (hty 0 (by decide)) Z3 (.cast u64 (.variable i32 ((mv.nv + pre.length) + 7))) (by simp [NExpr.scalarOnly]) W0 (by rw [VVB_get0]; simpa [uc1, uc2, uc3, uc4, uc5, uc6, uc7, uc8, uc9, uc10, uc11, uc12, uc13, uc14, uc15, uc16, uc17, uc18, uc19, uc20, uc21, uc22, uc23, uc24] using hl0_3) (by rw [VVB_get0]; exact hD_Z3) (by rw [VVB_get0]; exact hvl0) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell)] : List Cell)) (pre.length + 7) _ (Nat.add_assoc _ _ _) W0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell)] : List Cell) 7 _ rfl) hNW0 (VVB (b)))) (conv_s64 _ vZ3) (CalcLoopc0_5 (mv.nv + pre.length) REST) r5 (by rw [List.append_assoc]; exact h5) hr5
  have hc4' : r4.cost ≤ 400 + r5.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc4); exact Nat.le_trans hc4 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r3, h3, hr3, hp3, hv3, hc3, hn3, hw3⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.read i32 (.local 13) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 6)))) (W2 : Int) (W2 : Int)
    (den_rd32 mv (VVB (b)) _ 13 (by rw [hnv]; decide) (hty32 13 (by decide) (by decide)) (W2 : Int) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 6))) (by simp [NExpr.scalarOnly]) (sp - 1) (by rw [VVB_get13]; simpa [uc1, uc2, uc3, uc4, uc5, uc6, uc7, uc8, uc9, uc10, uc11, uc12, uc13, uc14, uc15, uc16, uc17, uc18, uc19, uc20, uc21, uc22, uc23, uc24] using hl13_2) (by rw [VVB_get13]; exact hD_W2) (by rw [VVB_get13]; exact hvl13) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell)] : List Cell)) (pre.length + 6) _ (Nat.add_assoc _ _ _) (sp - 1) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell)] : List Cell) 6 _ rfl) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hspM) (VVB (b)))) (conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat W2 hNW2)) (CalcLoopc0_4 (mv.nv + pre.length) REST) r4 (by rw [List.append_assoc]; exact h4) hr4
  have hc3' : r3.cost ≤ 400 + r4.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc3); exact Nat.le_trans hc3 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hn2, hw2⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.read i32 (.local 12) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 6)))) (W1 : Int) (W1 : Int)
    (den_rd32 mv (VVB (b)) _ 12 (by rw [hnv]; decide) (hty32 12 (by decide) (by decide)) (W1 : Int) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 6))) (by simp [NExpr.scalarOnly]) (sp - 1) (by rw [VVB_get12]; simpa [uc1, uc2, uc3, uc4, uc5, uc6, uc7, uc8, uc9, uc10, uc11, uc12, uc13, uc14, uc15, uc16, uc17, uc18, uc19, uc20, uc21, uc22, uc23, uc24] using hl12_1) (by rw [VVB_get12]; exact hD_W1) (by rw [VVB_get12]; exact hvl12) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell)] : List Cell)) (pre.length + 6) _ (Nat.add_assoc _ _ _) (sp - 1) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell)] : List Cell) 6 _ rfl) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hspM) (VVB (b)))) (conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat W1 hNW1)) (CalcLoopc0_3 (mv.nv + pre.length) REST) r3 (by rw [List.append_assoc]; exact h3) hr3
  have hc2' : r2.cost ≤ 400 + r3.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc2); exact Nat.le_trans hc2 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hn1, hw1⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.read i32 (.local 11) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 6)))) (W0 : Int) (W0 : Int)
    (den_rd32 mv (VVB (b)) _ 11 (by rw [hnv]; decide) (hty32 11 (by decide) (by decide)) (W0 : Int) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 6))) (by simp [NExpr.scalarOnly]) (sp - 1) (by rw [VVB_get11]; simpa [uc1, uc2, uc3, uc4, uc5, uc6, uc7, uc8, uc9, uc10, uc11, uc12, uc13, uc14, uc15, uc16, uc17, uc18, uc19, uc20, uc21, uc22, uc23, uc24] using hl11_0) (by rw [VVB_get11]; exact hD_W0) (by rw [VVB_get11]; exact hvl11) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell)] : List Cell)) (pre.length + 6) _ (Nat.add_assoc _ _ _) (sp - 1) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, ((sp - 1 : Nat) : Int)⟩ : Cell)] : List Cell) 6 _ rfl) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hspM) (VVB (b)))) (conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat W0 hNW0)) (CalcLoopc0_2 (mv.nv + pre.length) REST) r2 (by rw [List.append_assoc]; exact h2) hr2
  have hc1' : r1.cost ≤ 400 + r2.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc1); exact Nat.le_trans hc1 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hn0, hw0⟩ := seq_assign mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 6) (by simp) i32
    (.binary i32 .sub (.variable i32 ((mv.nv + pre.length) + 6)) (.literal i32 (1))) ((sp : Int) - 1) ((sp - 1 : Nat) : Int) (⟨i32, (sp : Int)⟩ : Cell) (den_binw mv _ _ i32 .sub _ _ (sp : Int) 1 (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell)] : List Cell)) i32 (pre.length + 6) _ (Nat.add_assoc _ _ _) (sp : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell)] : List Cell) 6 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat sp hspM) _) (den_lit32 mv _ _ 1 (by decide)) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly]) (conv_i32 _ hsc0)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell)] : List Cell) 6 _ rfl) rfl (Proofs.BellmanFordExec.i32_valid_nat sp hspM) (by rw [sub_one_cast _ hpos]; exact conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hspM)))
    (CalcLoopc0_1 (mv.nv + pre.length) REST) r1 (by
      rw [set_ext0 pre _ 6 _]
      exact h1) hr1
  have hc0' : r0.cost ≤ 400 + r1.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc0); exact Nat.le_trans hc0 (Nat.add_le_add_right (by decide) _)
  clear hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13 hX14 hX15 hX16 hX17 hX18 hX19 hX20 hX21 hX22 hX23 hX24 hX25 hX26 hX27 hX28 hX29 hX30 hX31 hX32 hX33 hX34 hX35 hX36 hX37 hX38 hX39 hX40 hX41 hX42 hX43 hX44 hX45 hX46 hX47 hX48 hX49 hX50 hX51 hX52 hX53 hX54 hX55
  refine ⟨r0, h0, hr0, ?_, ?_, ?_, ?_⟩
  · rw [hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19]
  · rw [hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15, hv16, hv17, hv18, hv19]
  · omega
  · omega


end Proofs.BeatsExec
