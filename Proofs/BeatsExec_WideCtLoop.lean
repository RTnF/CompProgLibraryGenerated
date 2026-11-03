import Proofs.BeatsExec_WideCtLoopCh0
import Proofs.BeatsExec_WideCtLoopCh1
import Proofs.BeatsExec_WideCtLoopCh2
import Proofs.BeatsExec_WideCtLoopCh3
import Proofs.BeatsExec_WideCtLoopCh4
import Proofs.BeatsExec_WideCtLoopCh5
import Proofs.BeatsExec_WideCtLoopCh6
import Proofs.BeatsExec_WideCtLoopCh7
import Proofs.BeatsExec_WideCtLoopCh8
import Proofs.BeatsExec_WideCtLoopCh9
import Proofs.BeatsExec_WideCtLoopCh10
import Proofs.BeatsExec_WideCtLoopCh11
import Proofs.BeatsExec_WideCtLoopCh12
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

theorem WideCtLoop_body (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (b : BS) (A : List Int) (P : List Cell)
    (inf : Int) (n ne k : Nat) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hneM : ne < M31) (hkM : k < M31) (hvl0 : ∀ w ∈ b.mxv, s64.valid w = true) (hvl1 : ∀ w ∈ b.smx, s64.valid w = true) (hvl2 : ∀ w ∈ b.mxc, s64.valid w = true) (hvl3 : ∀ w ∈ b.mnv, s64.valid w = true) (hvl4 : ∀ w ∈ b.smn, s64.valid w = true) (hvl5 : ∀ w ∈ b.mnc, s64.valid w = true) (hvl6 : ∀ w ∈ b.len, s64.valid w = true) (hvl9 : ∀ w ∈ b.lo, i32.valid w = true) (hvl10 : ∀ w ∈ b.hi, i32.valid w = true) (hvl14 : ∀ w ∈ b.ent, i32.valid w = true) (hvl15 : ∀ w ∈ A, s64.valid w = true) (W0 : Nat) (hNW0 : W0 < M31) (hD_W0 : b.lo.getD k 0 = (W0 : Int)) (W1 : Nat) (hNW1 : W1 < M31) (hD_W1 : b.hi.getD k 0 = (W1 : Int)) (Z2 : Int) (hD_Z2 : b.len.getD k 0 = Z2) (Z3 : Int) (hD_Z3 : A.getD W0 0 = Z3) (Z4 : Int) (hD_Z4 : b.mxv.getD k 0 = Z4) (Z5 : Int) (hD_Z5 : b.mnv.getD k 0 = Z5) (Z6 : Int) (hD_Z6 : b.smx.getD k 0 = Z6) (Z7 : Int) (hD_Z7 : b.smn.getD k 0 = Z7) (Z8 : Int) (hD_Z8 : b.mxc.getD k 0 = Z8) (Z9 : Int) (hD_Z9 : b.mnc.getD k 0 = Z9) (W10 : Nat) (hNW10 : W10 < M31) (hD_W10 : b.lo.getD (2 * k + 1) 0 = (W10 : Int)) (W11 : Nat) (hNW11 : W11 < M31) (hD_W11 : b.hi.getD (2 * k + 1) 0 = (W11 : Int)) (W12 : Nat) (hNW12 : W12 < M31) (hD_W12 : b.lo.getD (2 * k + 2) 0 = (W12 : Int)) (W13 : Nat) (hNW13 : W13 < M31) (hD_W13 : b.hi.getD (2 * k + 2) 0 = (W13 : Int)) (hl9_0 : k < (b.lo).length) (hl10_1 : k < (b.hi).length) (hl6_2 : k < (b.len).length) (hl15_3 : W0 < (A).length) (hl0_4 : k < (b.mxv).length) (hl3_5 : k < (b.mnv).length) (hl1_6 : k < (b.smx).length) (hl4_7 : k < (b.smn).length) (hl2_8 : k < (b.mxc).length) (hl5_9 : k < (b.mnc).length) (hl9_10 : (2 * k + 1) < (b.lo).length) (hl10_11 : (2 * k + 1) < (b.hi).length) (hl9_12 : (2 * k + 2) < (b.lo).length) (hl10_13 : (2 * k + 2) < (b.hi).length) (hl14_14 : ne < (b.ent).length) (X0 : Int) (hX0 : X0 = (if ((W0 : Int) < (W1 : Int)) then 1 else 0)) (X1 : Int) (hX1 : X1 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) = 1)) then 1 else 0)) (X2 : Int) (hX2 : X2 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) ≠ 1)) then 1 else 0)) (X3 : Int) (hX3 : X3 = (if (X0 = 1) then ((W1 : Int) - (W0 : Int)) else Z2)) (X4 : Int) (hX4 : X4 = (if (X1 = 1) then Z3 else Z4)) (X5 : Int) (hX5 : X5 = (if (X1 = 1) then Z3 else Z5)) (X6 : Int) (hX6 : X6 = (if (X1 = 1) then (-inf) else Z6)) (X7 : Int) (hX7 : X7 = (if (X1 = 1) then inf else Z7)) (X8 : Int) (hX8 : X8 = (if (X1 = 1) then 1 else Z8)) (X9 : Int) (hX9 : X9 = (if (X1 = 1) then 1 else Z9)) (X10 : Int) (hX10 : X10 = (if (X2 = 1) then (W0 : Int) else (W10 : Int))) (X11 : Int) (hX11 : X11 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W11 : Int))) (X12 : Int) (hX12 : X12 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W12 : Int))) (X13 : Int) (hX13 : X13 = (if (X2 = 1) then (W1 : Int) else (W13 : Int))) (X14 : Int) (hX14 : X14 = ((ne : Int) + X2)) (X15 : Int) (hX15 : X15 = ((k : Int) + 1)) (hsc0 : i32.valid ((W1 : Int) - (W0 : Int)) = true) (hsc1 : ((X1 = 1)) → s64.valid (-inf) = true) (hsc2 : i32.valid ((W0 : Int) + (W1 : Int)) = true) (hsc4 : i32.valid ((ne : Int) + X2) = true) (hsc5 : i32.valid ((k : Int) + 1) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (WideCtLoopBody (mv.nv + pre.length)) (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell)] : List Cell))) (VVA A b) = some r ∧ r.ret = none ∧
      r.ps = gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, X14⟩ : Cell), (⟨i32, X15⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨i32, (((W0 : Int) + (W1 : Int)) / 2)⟩ : Cell), (⟨u64, (((2 * k + 1) : Nat) : Int)⟩ : Cell), (⟨u64, (((2 * k + 2) : Nat) : Int)⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨i32, X13⟩ : Cell)] : List Cell)) ∧ r.vv = VVA A (uw12 (uw11 (uw10 (uw9 (uw8 (uw7 (uw6 (uw5 (uw4 (uw3 (uw2 (uw1 b k X3) k X4) k X5) k X6) k X7) k X8) k X9) (2 * k + 1) X10) (2 * k + 1) X11) (2 * k + 2) X12) (2 * k + 2) X13) ne (k : Int)) ∧ r.cost ≤ 20580 ∧ r.wk ≤ 12 := by
  classical
  have vW0 : i32.valid (W0 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW0
  have vW1 : i32.valid (W1 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW1
  have vZ2 : s64.valid Z2 = true := by rw [← hD_Z2]; exact getD_mem_valid b.len k hl6_2 hvl6
  have vZ3 : s64.valid Z3 = true := by rw [← hD_Z3]; exact getD_mem_valid A W0 hl15_3 hvl15
  have vZ4 : s64.valid Z4 = true := by rw [← hD_Z4]; exact getD_mem_valid b.mxv k hl0_4 hvl0
  have vZ5 : s64.valid Z5 = true := by rw [← hD_Z5]; exact getD_mem_valid b.mnv k hl3_5 hvl3
  have vZ6 : s64.valid Z6 = true := by rw [← hD_Z6]; exact getD_mem_valid b.smx k hl1_6 hvl1
  have vZ7 : s64.valid Z7 = true := by rw [← hD_Z7]; exact getD_mem_valid b.smn k hl4_7 hvl4
  have vZ8 : s64.valid Z8 = true := by rw [← hD_Z8]; exact getD_mem_valid b.mxc k hl2_8 hvl2
  have vZ9 : s64.valid Z9 = true := by rw [← hD_Z9]; exact getD_mem_valid b.mnc k hl5_9 hvl5
  have vW10 : i32.valid (W10 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW10
  have vW11 : i32.valid (W11 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW11
  have vW12 : i32.valid (W12 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW12
  have vW13 : i32.valid (W13 : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hNW13
  have vX0 : i32.valid X0 = true := by
    rw [hX0]
    by_cases hC : ((W0 : Int) < (W1 : Int))
    · rw [ite_eq_left hC]; exact (by decide)
    · rw [ite_eq_right hC]; exact (by decide)
  have vX1 : i32.valid X1 = true := by
    rw [hX1]
    by_cases hC : ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) = 1))
    · rw [ite_eq_left hC]; exact (by decide)
    · rw [ite_eq_right hC]; exact (by decide)
  have vX2 : i32.valid X2 = true := by
    rw [hX2]
    by_cases hC : ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) ≠ 1))
    · rw [ite_eq_left hC]; exact (by decide)
    · rw [ite_eq_right hC]; exact (by decide)
  have vX3 : s64.valid X3 = true := by
    rw [hX3]
    by_cases hC : (X0 = 1)
    · rw [ite_eq_left hC]; exact (s64_of_i32 _ hsc0)
    · rw [ite_eq_right hC]; exact vZ2
  have vX4 : s64.valid X4 = true := by
    rw [hX4]
    by_cases hC : (X1 = 1)
    · rw [ite_eq_left hC]; exact vZ3
    · rw [ite_eq_right hC]; exact vZ4
  have vX5 : s64.valid X5 = true := by
    rw [hX5]
    by_cases hC : (X1 = 1)
    · rw [ite_eq_left hC]; exact vZ3
    · rw [ite_eq_right hC]; exact vZ5
  have vX6 : s64.valid X6 = true := by
    rw [hX6]
    by_cases hC : (X1 = 1)
    · rw [ite_eq_left hC]; exact (hsc1 hC)
    · rw [ite_eq_right hC]; exact vZ6
  have vX7 : s64.valid X7 = true := by
    rw [hX7]
    by_cases hC : (X1 = 1)
    · rw [ite_eq_left hC]; exact hinf
    · rw [ite_eq_right hC]; exact vZ7
  have vX8 : s64.valid X8 = true := by
    rw [hX8]
    by_cases hC : (X1 = 1)
    · rw [ite_eq_left hC]; exact (by decide)
    · rw [ite_eq_right hC]; exact vZ8
  have vX9 : s64.valid X9 = true := by
    rw [hX9]
    by_cases hC : (X1 = 1)
    · rw [ite_eq_left hC]; exact (by decide)
    · rw [ite_eq_right hC]; exact vZ9
  have vX10 : i32.valid X10 = true := by
    rw [hX10]
    by_cases hC : (X2 = 1)
    · rw [ite_eq_left hC]; exact (Proofs.BellmanFordExec.i32_valid_nat W0 hNW0)
    · rw [ite_eq_right hC]; exact (Proofs.BellmanFordExec.i32_valid_nat W10 hNW10)
  have vX11 : i32.valid X11 = true := by
    rw [hX11]
    by_cases hC : (X2 = 1)
    · rw [ite_eq_left hC]; exact (i32_valid_div2 _ hsc2 (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)))
    · rw [ite_eq_right hC]; exact (Proofs.BellmanFordExec.i32_valid_nat W11 hNW11)
  have vX12 : i32.valid X12 = true := by
    rw [hX12]
    by_cases hC : (X2 = 1)
    · rw [ite_eq_left hC]; exact (i32_valid_div2 _ hsc2 (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)))
    · rw [ite_eq_right hC]; exact (Proofs.BellmanFordExec.i32_valid_nat W12 hNW12)
  have vX13 : i32.valid X13 = true := by
    rw [hX13]
    by_cases hC : (X2 = 1)
    · rw [ite_eq_left hC]; exact (Proofs.BellmanFordExec.i32_valid_nat W1 hNW1)
    · rw [ite_eq_right hC]; exact (Proofs.BellmanFordExec.i32_valid_nat W13 hNW13)
  have vX14 : i32.valid X14 = true := by rw [hX14]; exact hsc4
  have vX15 : i32.valid X15 = true := by rw [hX15]; exact hsc5
  obtain ⟨rE, hE, hrE, hpE, hvE, hcE, hwE⟩ : ∃ rE : PRM, pexecM mv fu Sk (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, X14⟩ : Cell), (⟨i32, X15⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨i32, (((W0 : Int) + (W1 : Int)) / 2)⟩ : Cell), (⟨u64, (((2 * k + 1) : Nat) : Int)⟩ : Cell), (⟨u64, (((2 * k + 2) : Nat) : Int)⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨i32, X13⟩ : Cell)] : List Cell))) (VVA A (uw12 (uw11 (uw10 (uw9 (uw8 (uw7 (uw6 (uw5 (uw4 (uw3 (uw2 (uw1 b k X3) k X4) k X5) k X6) k X7) k X8) k X9) (2 * k + 1) X10) (2 * k + 1) X11) (2 * k + 2) X12) (2 * k + 2) X13) ne (k : Int))) = some rE ∧
      rE.ret = none ∧ rE.ps = gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, X14⟩ : Cell), (⟨i32, X15⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨i32, (((W0 : Int) + (W1 : Int)) / 2)⟩ : Cell), (⟨u64, (((2 * k + 1) : Nat) : Int)⟩ : Cell), (⟨u64, (((2 * k + 2) : Nat) : Int)⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨i32, X13⟩ : Cell)] : List Cell)) ∧ rE.vv = VVA A (uw12 (uw11 (uw10 (uw9 (uw8 (uw7 (uw6 (uw5 (uw4 (uw3 (uw2 (uw1 b k X3) k X4) k X5) k X6) k X7) k X8) k X9) (2 * k + 1) X10) (2 * k + 1) X11) (2 * k + 2) X12) (2 * k + 2) X13) ne (k : Int)) ∧ rE.cost ≤ 0 ∧ rE.wk ≤ 0 :=
    ⟨_, pexecM_skip _ _ _ _, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  obtain ⟨c12, hc_12, hrc_12, hpc_12, hvc_12, hcc_12, hwc_12⟩ := WideCtLoop_ch12 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu Sk rE hE hrE
  obtain ⟨c11, hc_11, hrc_11, hpc_11, hvc_11, hcc_11, hwc_11⟩ := WideCtLoop_ch11 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc12 (mv.nv + pre.length) Sk) c12 hc_12 hrc_12
  obtain ⟨c10, hc_10, hrc_10, hpc_10, hvc_10, hcc_10, hwc_10⟩ := WideCtLoop_ch10 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk)) c11 hc_11 hrc_11
  obtain ⟨c9, hc_9, hrc_9, hpc_9, hvc_9, hcc_9, hwc_9⟩ := WideCtLoop_ch9 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk))) c10 hc_10 hrc_10
  obtain ⟨c8, hc_8, hrc_8, hpc_8, hvc_8, hcc_8, hwc_8⟩ := WideCtLoop_ch8 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc9 (mv.nv + pre.length) (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk)))) c9 hc_9 hrc_9
  obtain ⟨c7, hc_7, hrc_7, hpc_7, hvc_7, hcc_7, hwc_7⟩ := WideCtLoop_ch7 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc8 (mv.nv + pre.length) (WideCtLoopc9 (mv.nv + pre.length) (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk))))) c8 hc_8 hrc_8
  obtain ⟨c6, hc_6, hrc_6, hpc_6, hvc_6, hcc_6, hwc_6⟩ := WideCtLoop_ch6 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc7 (mv.nv + pre.length) (WideCtLoopc8 (mv.nv + pre.length) (WideCtLoopc9 (mv.nv + pre.length) (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk)))))) c7 hc_7 hrc_7
  obtain ⟨c5, hc_5, hrc_5, hpc_5, hvc_5, hcc_5, hwc_5⟩ := WideCtLoop_ch5 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc6 (mv.nv + pre.length) (WideCtLoopc7 (mv.nv + pre.length) (WideCtLoopc8 (mv.nv + pre.length) (WideCtLoopc9 (mv.nv + pre.length) (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk))))))) c6 hc_6 hrc_6
  obtain ⟨c4, hc_4, hrc_4, hpc_4, hvc_4, hcc_4, hwc_4⟩ := WideCtLoop_ch4 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc5 (mv.nv + pre.length) (WideCtLoopc6 (mv.nv + pre.length) (WideCtLoopc7 (mv.nv + pre.length) (WideCtLoopc8 (mv.nv + pre.length) (WideCtLoopc9 (mv.nv + pre.length) (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk)))))))) c5 hc_5 hrc_5
  obtain ⟨c3, hc_3, hrc_3, hpc_3, hvc_3, hcc_3, hwc_3⟩ := WideCtLoop_ch3 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc4 (mv.nv + pre.length) (WideCtLoopc5 (mv.nv + pre.length) (WideCtLoopc6 (mv.nv + pre.length) (WideCtLoopc7 (mv.nv + pre.length) (WideCtLoopc8 (mv.nv + pre.length) (WideCtLoopc9 (mv.nv + pre.length) (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk))))))))) c4 hc_4 hrc_4
  obtain ⟨c2, hc_2, hrc_2, hpc_2, hvc_2, hcc_2, hwc_2⟩ := WideCtLoop_ch2 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc3 (mv.nv + pre.length) (WideCtLoopc4 (mv.nv + pre.length) (WideCtLoopc5 (mv.nv + pre.length) (WideCtLoopc6 (mv.nv + pre.length) (WideCtLoopc7 (mv.nv + pre.length) (WideCtLoopc8 (mv.nv + pre.length) (WideCtLoopc9 (mv.nv + pre.length) (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk)))))))))) c3 hc_3 hrc_3
  obtain ⟨c1, hc_1, hrc_1, hpc_1, hvc_1, hcc_1, hwc_1⟩ := WideCtLoop_ch1 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc2 (mv.nv + pre.length) (WideCtLoopc3 (mv.nv + pre.length) (WideCtLoopc4 (mv.nv + pre.length) (WideCtLoopc5 (mv.nv + pre.length) (WideCtLoopc6 (mv.nv + pre.length) (WideCtLoopc7 (mv.nv + pre.length) (WideCtLoopc8 (mv.nv + pre.length) (WideCtLoopc9 (mv.nv + pre.length) (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk))))))))))) c2 hc_2 hrc_2
  obtain ⟨c0, hc_0, hrc_0, hpc_0, hvc_0, hcc_0, hwc_0⟩ := WideCtLoop_ch0 mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl9 hvl10 hvl14 hvl15 W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0 hsc1 hsc2 hsc4 hsc5 fu (WideCtLoopc1 (mv.nv + pre.length) (WideCtLoopc2 (mv.nv + pre.length) (WideCtLoopc3 (mv.nv + pre.length) (WideCtLoopc4 (mv.nv + pre.length) (WideCtLoopc5 (mv.nv + pre.length) (WideCtLoopc6 (mv.nv + pre.length) (WideCtLoopc7 (mv.nv + pre.length) (WideCtLoopc8 (mv.nv + pre.length) (WideCtLoopc9 (mv.nv + pre.length) (WideCtLoopc10 (mv.nv + pre.length) (WideCtLoopc11 (mv.nv + pre.length) (WideCtLoopc12 (mv.nv + pre.length) Sk)))))))))))) c1 hc_1 hrc_1
  clear hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13 hX14 hX15
  refine ⟨c0, hc_0, hrc_0, ?_, ?_, ?_, ?_⟩
  · rw [hpc_0, hpc_1, hpc_2, hpc_3, hpc_4, hpc_5, hpc_6, hpc_7, hpc_8, hpc_9, hpc_10, hpc_11, hpc_12, hpE]
  · rw [hvc_0, hvc_1, hvc_2, hvc_3, hvc_4, hvc_5, hvc_6, hvc_7, hvc_8, hvc_9, hvc_10, hvc_11, hvc_12, hvE]
  · omega
  · omega

end Proofs.BeatsExec
