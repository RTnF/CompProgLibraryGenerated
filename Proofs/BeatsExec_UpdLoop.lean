import Proofs.BeatsExec_UpdLoopCh0
import Proofs.BeatsExec_UpdLoopCh1
import Proofs.BeatsExec_UpdLoopCh2
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
theorem UpdLoop_body (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (b : BS) (P : List Cell)
    (inf : Int) (n op qa qb sp ne : Nat) (x : Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hopM : op < M31) (hqaM : qa < M31) (hqbM : qb < M31) (hspM : sp < M31) (hneM : ne < M31) (hpos : 0 < ne) (hx : s64.valid x = true) (hvl0 : ∀ w ∈ b.mxv, s64.valid w = true) (hvl1 : ∀ w ∈ b.smx, s64.valid w = true) (hvl2 : ∀ w ∈ b.mxc, s64.valid w = true) (hvl3 : ∀ w ∈ b.mnv, s64.valid w = true) (hvl4 : ∀ w ∈ b.smn, s64.valid w = true) (hvl5 : ∀ w ∈ b.mnc, s64.valid w = true) (hvl14 : ∀ w ∈ b.ent, i32.valid w = true) (W0 : Nat) (hNW0 : W0 < M31) (hD_W0 : b.ent.getD (ne - 1) 0 = (W0 : Int)) (Z1 : Int) (hD_Z1 : b.mxv.getD (2 * W0 + 1) 0 = Z1) (Z2 : Int) (hD_Z2 : b.mxv.getD (2 * W0 + 2) 0 = Z2) (Z3 : Int) (hD_Z3 : b.smx.getD (2 * W0 + 1) 0 = Z3) (Z4 : Int) (hD_Z4 : b.smx.getD (2 * W0 + 2) 0 = Z4) (Z5 : Int) (hD_Z5 : b.mxc.getD (2 * W0 + 1) 0 = Z5) (Z6 : Int) (hD_Z6 : b.mxc.getD (2 * W0 + 2) 0 = Z6) (Z7 : Int) (hD_Z7 : b.mnv.getD (2 * W0 + 1) 0 = Z7) (Z8 : Int) (hD_Z8 : b.mnv.getD (2 * W0 + 2) 0 = Z8) (Z9 : Int) (hD_Z9 : b.smn.getD (2 * W0 + 1) 0 = Z9) (Z10 : Int) (hD_Z10 : b.smn.getD (2 * W0 + 2) 0 = Z10) (Z11 : Int) (hD_Z11 : b.mnc.getD (2 * W0 + 1) 0 = Z11) (Z12 : Int) (hD_Z12 : b.mnc.getD (2 * W0 + 2) 0 = Z12) (hl14_0 : (ne - 1) < (b.ent).length) (hl0_1 : (2 * W0 + 1) < (b.mxv).length) (hl0_2 : (2 * W0 + 2) < (b.mxv).length) (hl1_3 : (2 * W0 + 1) < (b.smx).length) (hl1_4 : (2 * W0 + 2) < (b.smx).length) (hl2_5 : (2 * W0 + 1) < (b.mxc).length) (hl2_6 : (2 * W0 + 2) < (b.mxc).length) (hl0_7 : W0 < (b.mxv).length) (hl2_8 : W0 < (b.mxc).length) (hl1_9 : W0 < (b.smx).length) (hl3_10 : (2 * W0 + 1) < (b.mnv).length) (hl3_11 : (2 * W0 + 2) < (b.mnv).length) (hl4_12 : (2 * W0 + 1) < (b.smn).length) (hl4_13 : (2 * W0 + 2) < (b.smn).length) (hl5_14 : (2 * W0 + 1) < (b.mnc).length) (hl5_15 : (2 * W0 + 2) < (b.mnc).length) (hl3_16 : W0 < (b.mnv).length) (hl5_17 : W0 < (b.mnc).length) (hl4_18 : W0 < (b.smn).length) (hk1_W0 : (2 * W0 + 1) < M31) (hk2_W0 : (2 * W0 + 2) < M31) (X0 : Int) (hX0 : X0 = (if (Z1 < Z2) then 1 else 0)) (X1 : Int) (hX1 : X1 = (if (Z1 > Z2) then 1 else 0)) (X2 : Int) (hX2 : X2 = (if (Z1 = Z2) then 1 else 0)) (X3 : Int) (hX3 : X3 = (if (X0 = 1) then Z2 else Z1)) (X4 : Int) (hX4 : X4 = (if (X0 = 1) then Z6 else Z5)) (X5 : Int) (hX5 : X5 = (if (X2 = 1) then (Z5 + Z6) else X4)) (X6 : Int) (hX6 : X6 = (if (X0 = 1) then Z1 else Z3)) (X7 : Int) (hX7 : X7 = (if (X1 = 1) then Z2 else X6)) (X8 : Int) (hX8 : X8 = (if (X1 = 1) then Z3 else Z4)) (X9 : Int) (hX9 : X9 = (if (X7 < X8) then X8 else X7)) (X10 : Int) (hX10 : X10 = (if (Z7 < Z8) then 1 else 0)) (X11 : Int) (hX11 : X11 = (if (Z7 > Z8) then 1 else 0)) (X12 : Int) (hX12 : X12 = (if (Z7 = Z8) then 1 else 0)) (X13 : Int) (hX13 : X13 = (if (X11 = 1) then Z8 else Z7)) (X14 : Int) (hX14 : X14 = (if (X11 = 1) then Z12 else Z11)) (X15 : Int) (hX15 : X15 = (if (X12 = 1) then (Z11 + Z12) else X14)) (X16 : Int) (hX16 : X16 = (if (X10 = 1) then Z8 else Z9)) (X17 : Int) (hX17 : X17 = (if (X11 = 1) then Z7 else X16)) (X18 : Int) (hX18 : X18 = (if (X10 = 1) then Z9 else Z10)) (X19 : Int) (hX19 : X19 = (if (X18 < X17) then X18 else X17)) (hsc0 : i32.valid ((ne : Int) - 1) = true) (hsc1 : ((X2 = 1)) → s64.valid (Z5 + Z6) = true) (hsc2 : ((X12 = 1)) → s64.valid (Z11 + Z12) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (UpdLoopBody (mv.nv + pre.length)) (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell)] : List Cell))) (VVB b) = some r ∧ r.ret = none ∧
      r.ps = gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell), (⟨i32, ((ne - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z1⟩ : Cell), (⟨s64, Z2⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, Z10⟩ : Cell), (⟨s64, Z11⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X18⟩ : Cell)] : List Cell)) ∧ r.vv = VVB (uu6 (uu5 (uu4 (uu3 (uu2 (uu1 b W0 X3) W0 X5) W0 X9) W0 X13) W0 X15) W0 X19) ∧ r.cost ≤ 24780 ∧ r.wk ≤ 6 := by
  classical
  have vW0 : i32.valid (W0 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW0
  have vZ1 : s64.valid Z1 = true := by rw [← hD_Z1]; exact getD_mem_valid b.mxv (2 * W0 + 1) hl0_1 hvl0
  have vZ2 : s64.valid Z2 = true := by rw [← hD_Z2]; exact getD_mem_valid b.mxv (2 * W0 + 2) hl0_2 hvl0
  have vZ3 : s64.valid Z3 = true := by rw [← hD_Z3]; exact getD_mem_valid b.smx (2 * W0 + 1) hl1_3 hvl1
  have vZ4 : s64.valid Z4 = true := by rw [← hD_Z4]; exact getD_mem_valid b.smx (2 * W0 + 2) hl1_4 hvl1
  have vZ5 : s64.valid Z5 = true := by rw [← hD_Z5]; exact getD_mem_valid b.mxc (2 * W0 + 1) hl2_5 hvl2
  have vZ6 : s64.valid Z6 = true := by rw [← hD_Z6]; exact getD_mem_valid b.mxc (2 * W0 + 2) hl2_6 hvl2
  have vZ7 : s64.valid Z7 = true := by rw [← hD_Z7]; exact getD_mem_valid b.mnv (2 * W0 + 1) hl3_10 hvl3
  have vZ8 : s64.valid Z8 = true := by rw [← hD_Z8]; exact getD_mem_valid b.mnv (2 * W0 + 2) hl3_11 hvl3
  have vZ9 : s64.valid Z9 = true := by rw [← hD_Z9]; exact getD_mem_valid b.smn (2 * W0 + 1) hl4_12 hvl4
  have vZ10 : s64.valid Z10 = true := by rw [← hD_Z10]; exact getD_mem_valid b.smn (2 * W0 + 2) hl4_13 hvl4
  have vZ11 : s64.valid Z11 = true := by rw [← hD_Z11]; exact getD_mem_valid b.mnc (2 * W0 + 1) hl5_14 hvl5
  have vZ12 : s64.valid Z12 = true := by rw [← hD_Z12]; exact getD_mem_valid b.mnc (2 * W0 + 2) hl5_15 hvl5
  have vX0 : i32.valid X0 = true := by
    rw [hX0]
    by_cases hC : (Z1 < Z2)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX1 : i32.valid X1 = true := by
    rw [hX1]
    by_cases hC : (Z1 > Z2)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX2 : i32.valid X2 = true := by
    rw [hX2]
    by_cases hC : (Z1 = Z2)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX3 : s64.valid X3 = true := by
    rw [hX3]
    by_cases hC : (X0 = 1)
    · rw [if_pos hC]; exact vZ2
    · rw [if_neg hC]; exact vZ1
  have vX4 : s64.valid X4 = true := by
    rw [hX4]
    by_cases hC : (X0 = 1)
    · rw [if_pos hC]; exact vZ6
    · rw [if_neg hC]; exact vZ5
  have vX5 : s64.valid X5 = true := by
    rw [hX5]
    by_cases hC : (X2 = 1)
    · rw [if_pos hC]; exact (hsc1 hC)
    · rw [if_neg hC]; exact vX4
  have vX6 : s64.valid X6 = true := by
    rw [hX6]
    by_cases hC : (X0 = 1)
    · rw [if_pos hC]; exact vZ1
    · rw [if_neg hC]; exact vZ3
  have vX7 : s64.valid X7 = true := by
    rw [hX7]
    by_cases hC : (X1 = 1)
    · rw [if_pos hC]; exact vZ2
    · rw [if_neg hC]; exact vX6
  have vX8 : s64.valid X8 = true := by
    rw [hX8]
    by_cases hC : (X1 = 1)
    · rw [if_pos hC]; exact vZ3
    · rw [if_neg hC]; exact vZ4
  have vX9 : s64.valid X9 = true := by
    rw [hX9]
    by_cases hC : (X7 < X8)
    · rw [if_pos hC]; exact vX8
    · rw [if_neg hC]; exact vX7
  have vX10 : i32.valid X10 = true := by
    rw [hX10]
    by_cases hC : (Z7 < Z8)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX11 : i32.valid X11 = true := by
    rw [hX11]
    by_cases hC : (Z7 > Z8)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX12 : i32.valid X12 = true := by
    rw [hX12]
    by_cases hC : (Z7 = Z8)
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX13 : s64.valid X13 = true := by
    rw [hX13]
    by_cases hC : (X11 = 1)
    · rw [if_pos hC]; exact vZ8
    · rw [if_neg hC]; exact vZ7
  have vX14 : s64.valid X14 = true := by
    rw [hX14]
    by_cases hC : (X11 = 1)
    · rw [if_pos hC]; exact vZ12
    · rw [if_neg hC]; exact vZ11
  have vX15 : s64.valid X15 = true := by
    rw [hX15]
    by_cases hC : (X12 = 1)
    · rw [if_pos hC]; exact (hsc2 hC)
    · rw [if_neg hC]; exact vX14
  have vX16 : s64.valid X16 = true := by
    rw [hX16]
    by_cases hC : (X10 = 1)
    · rw [if_pos hC]; exact vZ8
    · rw [if_neg hC]; exact vZ9
  have vX17 : s64.valid X17 = true := by
    rw [hX17]
    by_cases hC : (X11 = 1)
    · rw [if_pos hC]; exact vZ7
    · rw [if_neg hC]; exact vX16
  have vX18 : s64.valid X18 = true := by
    rw [hX18]
    by_cases hC : (X10 = 1)
    · rw [if_pos hC]; exact vZ9
    · rw [if_neg hC]; exact vZ10
  have vX19 : s64.valid X19 = true := by
    rw [hX19]
    by_cases hC : (X18 < X17)
    · rw [if_pos hC]; exact vX18
    · rw [if_neg hC]; exact vX17
  obtain ⟨rE, hE, hrE, hpE, hvE, hcE, hwE⟩ : ∃ rE : PRM, pexecM mv fu Sk (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell), (⟨i32, ((ne - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z1⟩ : Cell), (⟨s64, Z2⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, Z10⟩ : Cell), (⟨s64, Z11⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X18⟩ : Cell)] : List Cell))) (VVB (uu6 (uu5 (uu4 (uu3 (uu2 (uu1 b W0 X3) W0 X5) W0 X9) W0 X13) W0 X15) W0 X19)) = some rE ∧
      rE.ret = none ∧ rE.ps = gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell), (⟨i32, ((ne - 1 : Nat) : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z1⟩ : Cell), (⟨s64, Z2⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, Z10⟩ : Cell), (⟨s64, Z11⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X18⟩ : Cell)] : List Cell)) ∧ rE.vv = VVB (uu6 (uu5 (uu4 (uu3 (uu2 (uu1 b W0 X3) W0 X5) W0 X9) W0 X13) W0 X15) W0 X19) ∧ rE.cost ≤ 0 ∧ rE.wk ≤ 0 :=
    ⟨_, pexecM_skip _ _ _ _, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  obtain ⟨c2, hc_2, hrc_2, hpc_2, hvc_2, hcc_2, hwc_2⟩ := UpdLoop_ch2 mv hnv pre hty hty32 b P inf n op qa qb sp ne x hinf hnM hopM hqaM hqbM hspM hneM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl14 W0 hNW0 hD_W0 Z1 hD_Z1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 hl14_0 hl0_1 hl0_2 hl1_3 hl1_4 hl2_5 hl2_6 hl0_7 hl2_8 hl1_9 hl3_10 hl3_11 hl4_12 hl4_13 hl5_14 hl5_15 hl3_16 hl5_17 hl4_18 hk1_W0 hk2_W0 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 hsc0 hsc1 hsc2 fu Sk rE hE hrE
  obtain ⟨c1, hc_1, hrc_1, hpc_1, hvc_1, hcc_1, hwc_1⟩ := UpdLoop_ch1 mv hnv pre hty hty32 b P inf n op qa qb sp ne x hinf hnM hopM hqaM hqbM hspM hneM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl14 W0 hNW0 hD_W0 Z1 hD_Z1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 hl14_0 hl0_1 hl0_2 hl1_3 hl1_4 hl2_5 hl2_6 hl0_7 hl2_8 hl1_9 hl3_10 hl3_11 hl4_12 hl4_13 hl5_14 hl5_15 hl3_16 hl5_17 hl4_18 hk1_W0 hk2_W0 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 hsc0 hsc1 hsc2 fu (UpdLoopc2 (mv.nv + pre.length) Sk) c2 hc_2 hrc_2
  obtain ⟨c0, hc_0, hrc_0, hpc_0, hvc_0, hcc_0, hwc_0⟩ := UpdLoop_ch0 mv hnv pre hty hty32 b P inf n op qa qb sp ne x hinf hnM hopM hqaM hqbM hspM hneM hpos hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl14 W0 hNW0 hD_W0 Z1 hD_Z1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 hl14_0 hl0_1 hl0_2 hl1_3 hl1_4 hl2_5 hl2_6 hl0_7 hl2_8 hl1_9 hl3_10 hl3_11 hl4_12 hl4_13 hl5_14 hl5_15 hl3_16 hl5_17 hl4_18 hk1_W0 hk2_W0 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 hsc0 hsc1 hsc2 fu (UpdLoopc1 (mv.nv + pre.length) (UpdLoopc2 (mv.nv + pre.length) Sk)) c1 hc_1 hrc_1
  clear hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13 hX14 hX15 hX16 hX17 hX18 hX19
  refine ⟨c0, hc_0, hrc_0, ?_, ?_, ?_, ?_⟩
  · rw [hpc_0, hpc_1, hpc_2, hpE]
  · rw [hvc_0, hvc_1, hvc_2, hvE]
  · omega
  · omega

end Proofs.BeatsExec
