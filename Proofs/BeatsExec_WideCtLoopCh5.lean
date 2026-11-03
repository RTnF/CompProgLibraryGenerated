import Proofs.BeatsExec_WideCtLoopDefs
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

theorem WideCtLoop_ch5 (mv : MV) (_hnv : mv.nv = 16) (pre : List Cell) (_hty : ∀ v, v < 9 → mv.ty v = s64) (_hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (_hty15 : mv.ty 15 = s64) (b : BS) (A : List Int) (P : List Cell)
    (inf : Int) (n ne k : Nat) (hinf : s64.valid inf = true)
    (_hnM : n < M31) (_hneM : ne < M31) (_hkM : k < M31) (hvl0 : ∀ w ∈ b.mxv, s64.valid w = true) (hvl1 : ∀ w ∈ b.smx, s64.valid w = true) (hvl2 : ∀ w ∈ b.mxc, s64.valid w = true) (hvl3 : ∀ w ∈ b.mnv, s64.valid w = true) (hvl4 : ∀ w ∈ b.smn, s64.valid w = true) (hvl5 : ∀ w ∈ b.mnc, s64.valid w = true) (hvl6 : ∀ w ∈ b.len, s64.valid w = true) (_hvl9 : ∀ w ∈ b.lo, i32.valid w = true) (_hvl10 : ∀ w ∈ b.hi, i32.valid w = true) (_hvl14 : ∀ w ∈ b.ent, i32.valid w = true) (hvl15 : ∀ w ∈ A, s64.valid w = true) (W0 : Nat) (hNW0 : W0 < M31) (_hD_W0 : b.lo.getD k 0 = (W0 : Int)) (W1 : Nat) (hNW1 : W1 < M31) (_hD_W1 : b.hi.getD k 0 = (W1 : Int)) (Z2 : Int) (hD_Z2 : b.len.getD k 0 = Z2) (Z3 : Int) (hD_Z3 : A.getD W0 0 = Z3) (Z4 : Int) (hD_Z4 : b.mxv.getD k 0 = Z4) (Z5 : Int) (hD_Z5 : b.mnv.getD k 0 = Z5) (Z6 : Int) (hD_Z6 : b.smx.getD k 0 = Z6) (Z7 : Int) (hD_Z7 : b.smn.getD k 0 = Z7) (Z8 : Int) (hD_Z8 : b.mxc.getD k 0 = Z8) (Z9 : Int) (hD_Z9 : b.mnc.getD k 0 = Z9) (W10 : Nat) (hNW10 : W10 < M31) (_hD_W10 : b.lo.getD (2 * k + 1) 0 = (W10 : Int)) (W11 : Nat) (hNW11 : W11 < M31) (_hD_W11 : b.hi.getD (2 * k + 1) 0 = (W11 : Int)) (W12 : Nat) (hNW12 : W12 < M31) (_hD_W12 : b.lo.getD (2 * k + 2) 0 = (W12 : Int)) (W13 : Nat) (hNW13 : W13 < M31) (_hD_W13 : b.hi.getD (2 * k + 2) 0 = (W13 : Int)) (_hl9_0 : k < (b.lo).length) (_hl10_1 : k < (b.hi).length) (hl6_2 : k < (b.len).length) (hl15_3 : W0 < (A).length) (hl0_4 : k < (b.mxv).length) (hl3_5 : k < (b.mnv).length) (hl1_6 : k < (b.smx).length) (hl4_7 : k < (b.smn).length) (hl2_8 : k < (b.mxc).length) (hl5_9 : k < (b.mnc).length) (_hl9_10 : (2 * k + 1) < (b.lo).length) (_hl10_11 : (2 * k + 1) < (b.hi).length) (_hl9_12 : (2 * k + 2) < (b.lo).length) (_hl10_13 : (2 * k + 2) < (b.hi).length) (_hl14_14 : ne < (b.ent).length) (X0 : Int) (hX0 : X0 = (if ((W0 : Int) < (W1 : Int)) then 1 else 0)) (X1 : Int) (hX1 : X1 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) = 1)) then 1 else 0)) (X2 : Int) (hX2 : X2 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) ≠ 1)) then 1 else 0)) (X3 : Int) (hX3 : X3 = (if (X0 = 1) then ((W1 : Int) - (W0 : Int)) else Z2)) (X4 : Int) (hX4 : X4 = (if (X1 = 1) then Z3 else Z4)) (X5 : Int) (hX5 : X5 = (if (X1 = 1) then Z3 else Z5)) (X6 : Int) (hX6 : X6 = (if (X1 = 1) then (-inf) else Z6)) (X7 : Int) (hX7 : X7 = (if (X1 = 1) then inf else Z7)) (X8 : Int) (hX8 : X8 = (if (X1 = 1) then 1 else Z8)) (X9 : Int) (hX9 : X9 = (if (X1 = 1) then 1 else Z9)) (X10 : Int) (hX10 : X10 = (if (X2 = 1) then (W0 : Int) else (W10 : Int))) (X11 : Int) (hX11 : X11 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W11 : Int))) (X12 : Int) (hX12 : X12 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W12 : Int))) (X13 : Int) (hX13 : X13 = (if (X2 = 1) then (W1 : Int) else (W13 : Int))) (X14 : Int) (hX14 : X14 = ((ne : Int) + X2)) (X15 : Int) (hX15 : X15 = ((k : Int) + 1)) (hsc0 : i32.valid ((W1 : Int) - (W0 : Int)) = true) (hsc1 : ((X1 = 1)) → s64.valid (-inf) = true) (hsc2 : i32.valid ((W0 : Int) + (W1 : Int)) = true) (hsc4 : i32.valid ((ne : Int) + X2) = true) (hsc5 : i32.valid ((k : Int) + 1) = true) (fu : Nat)
    (REST : Command) (r : PRM) (hrest : pexecM mv fu REST (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell))) (VVA A (uw1 b k X3)) = some r) (hret : r.ret = none) :
    ∃ r0 : PRM, pexecM mv fu (WideCtLoopc5 (mv.nv + pre.length) REST) (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell))) (VVA A (uw1 b k X3)) = some r0 ∧ r0.ret = none ∧
      r0.ps = r.ps ∧ r0.vv = r.vv ∧ r0.cost ≤ 1680 + r.cost ∧ r0.wk ≤ 0 + r.wk := by
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
  obtain ⟨r23, h23, hr23, hp23, hv23, hc23, hn23, hw23⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) (VVA A ((uw1 b k X3))) (pre.length + 16) (by simp) s64
    (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 8)) (.literal i32 (1))) (.cast s64 (.literal i32 (1))) ((X1 = 1)) 1 1 Z8 (⟨s64, Z8⟩ : Cell)
    (den_cmpw mv _ _ _ _ _ X1 1 ((X1 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) i32 (pre.length + 8) _ (Nat.add_assoc _ _ _) X1 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 8 _ rfl) vX1 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (fun hC => (den_castlit mv _ _ 1 (by decide) (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 16 _ rfl) rfl vZ8 rfl (fun hC => conv_s64 _ (by decide))
    (WideCtLoopc5_24 (mv.nv + pre.length) REST) r (by
      rw [set_ext0 pre _ 16 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell).set 16 (⟨s64, if (X1 = 1) then 1 else Z8⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) := by
        rw [show (⟨s64, if (X1 = 1) then 1 else Z8⟩ : Cell) = ⟨s64, X8⟩ from by rw [hX8]]
        rfl
      rw [e2]; exact hrest) hret
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega)
  have hc23' : r23.cost ≤ 400 + r.cost := by exact Nat.le_trans hc23 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r22, h22, hr22, hp22, hv22, hc22, hn22, hw22⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) (VVA A ((uw1 b k X3))) (pre.length + 15) (by simp) s64
    (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 8)) (.literal i32 (1))) (.variable s64 ((mv.nv + pre.length) + 0)) ((X1 = 1)) inf inf Z7 (⟨s64, Z7⟩ : Cell)
    (den_cmpw mv _ _ _ _ _ X1 1 ((X1 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) i32 (pre.length + 8) _ (Nat.add_assoc _ _ _) X1 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 8 _ rfl) vX1 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (fun hC => (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) s64 (pre.length + 0) _ (Nat.add_assoc _ _ _) inf (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 0 _ rfl) hinf _)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 15 _ rfl) rfl vZ7 rfl (fun hC => conv_s64 _ hinf)
    (WideCtLoopc5_23 (mv.nv + pre.length) REST) r23 (by
      rw [set_ext0 pre _ 15 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell).set 15 (⟨s64, if (X1 = 1) then inf else Z7⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) := by
        rw [show (⟨s64, if (X1 = 1) then inf else Z7⟩ : Cell) = ⟨s64, X7⟩ from by rw [hX7]]
        rfl
      rw [e2]; exact h23) hr23
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega)
  have hc22' : r22.cost ≤ 400 + r23.cost := by exact Nat.le_trans hc22 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r21, h21, hr21, hp21, hv21, hc21, hn21, hw21⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) (VVA A ((uw1 b k X3))) (pre.length + 14) (by simp) s64
    (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 8)) (.literal i32 (1))) (.unary s64 .neg (.variable s64 ((mv.nv + pre.length) + 0))) ((X1 = 1)) (-inf) (-inf) Z6 (⟨s64, Z6⟩ : Cell)
    (den_cmpw mv _ _ _ _ _ X1 1 ((X1 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) i32 (pre.length + 8) _ (Nat.add_assoc _ _ _) X1 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 8 _ rfl) vX1 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (fun hC => (den_negw mv _ _ _ inf (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) s64 (pre.length + 0) _ (Nat.add_assoc _ _ _) inf (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 0 _ rfl) hinf _) (by simp [NExpr.scalarOnly]) (hsc1 hC))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 14 _ rfl) rfl vZ6 rfl (fun hC => conv_s64 _ (hsc1 hC))
    (WideCtLoopc5_22 (mv.nv + pre.length) REST) r22 (by
      rw [set_ext0 pre _ 14 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell).set 14 (⟨s64, if (X1 = 1) then (-inf) else Z6⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) := by
        rw [show (⟨s64, if (X1 = 1) then (-inf) else Z6⟩ : Cell) = ⟨s64, X6⟩ from by rw [hX6]]
        rfl
      rw [e2]; exact h22) hr22
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega)
  have hc21' : r21.cost ≤ 400 + r22.cost := by exact Nat.le_trans hc21 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r20, h20, hr20, hp20, hv20, hc20, hn20, hw20⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) (VVA A ((uw1 b k X3))) (pre.length + 13) (by simp) s64
    (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 8)) (.literal i32 (1))) (.variable s64 ((mv.nv + pre.length) + 11)) ((X1 = 1)) Z3 Z3 Z5 (⟨s64, Z5⟩ : Cell)
    (den_cmpw mv _ _ _ _ _ X1 1 ((X1 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) i32 (pre.length + 8) _ (Nat.add_assoc _ _ _) X1 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 8 _ rfl) vX1 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (fun hC => (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell)) s64 (pre.length + 11) _ (Nat.add_assoc _ _ _) Z3 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 11 _ rfl) vZ3 _)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) 13 _ rfl) rfl vZ5 rfl (fun hC => conv_s64 _ vZ3)
    (WideCtLoopc5_21 (mv.nv + pre.length) REST) r21 (by
      rw [set_ext0 pre _ 13 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell).set 13 (⟨s64, if (X1 = 1) then Z3 else Z5⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell)] : List Cell) := by
        rw [show (⟨s64, if (X1 = 1) then Z3 else Z5⟩ : Cell) = ⟨s64, X5⟩ from by rw [hX5]]
        rfl
      rw [e2]; exact h21) hr21
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega)
  have hc20' : r20.cost ≤ 400 + r21.cost := by exact Nat.le_trans hc20 (Nat.add_le_add_right (by decide) _)
  clear hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13 hX14 hX15
  refine ⟨r20, h20, hr20, ?_, ?_, ?_, ?_⟩
  · rw [hp20, hp21, hp22, hp23]
  · rw [hv20, hv21, hv22, hv23]
  · omega
  · omega


end Proofs.BeatsExec
