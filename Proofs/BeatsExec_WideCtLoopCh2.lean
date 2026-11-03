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

theorem WideCtLoop_ch2 (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (_hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (_hty15 : mv.ty 15 = s64) (b : BS) (A : List Int) (P : List Cell)
    (inf : Int) (n ne k : Nat) (hinf : s64.valid inf = true)
    (_hnM : n < M31) (_hneM : ne < M31) (hkM : k < M31) (hvl0 : ∀ w ∈ b.mxv, s64.valid w = true) (hvl1 : ∀ w ∈ b.smx, s64.valid w = true) (hvl2 : ∀ w ∈ b.mxc, s64.valid w = true) (hvl3 : ∀ w ∈ b.mnv, s64.valid w = true) (hvl4 : ∀ w ∈ b.smn, s64.valid w = true) (hvl5 : ∀ w ∈ b.mnc, s64.valid w = true) (hvl6 : ∀ w ∈ b.len, s64.valid w = true) (_hvl9 : ∀ w ∈ b.lo, i32.valid w = true) (_hvl10 : ∀ w ∈ b.hi, i32.valid w = true) (_hvl14 : ∀ w ∈ b.ent, i32.valid w = true) (hvl15 : ∀ w ∈ A, s64.valid w = true) (W0 : Nat) (hNW0 : W0 < M31) (_hD_W0 : b.lo.getD k 0 = (W0 : Int)) (W1 : Nat) (hNW1 : W1 < M31) (_hD_W1 : b.hi.getD k 0 = (W1 : Int)) (Z2 : Int) (hD_Z2 : b.len.getD k 0 = Z2) (Z3 : Int) (hD_Z3 : A.getD W0 0 = Z3) (Z4 : Int) (hD_Z4 : b.mxv.getD k 0 = Z4) (Z5 : Int) (hD_Z5 : b.mnv.getD k 0 = Z5) (Z6 : Int) (hD_Z6 : b.smx.getD k 0 = Z6) (Z7 : Int) (hD_Z7 : b.smn.getD k 0 = Z7) (Z8 : Int) (hD_Z8 : b.mxc.getD k 0 = Z8) (Z9 : Int) (hD_Z9 : b.mnc.getD k 0 = Z9) (W10 : Nat) (hNW10 : W10 < M31) (_hD_W10 : b.lo.getD (2 * k + 1) 0 = (W10 : Int)) (W11 : Nat) (hNW11 : W11 < M31) (_hD_W11 : b.hi.getD (2 * k + 1) 0 = (W11 : Int)) (W12 : Nat) (hNW12 : W12 < M31) (_hD_W12 : b.lo.getD (2 * k + 2) 0 = (W12 : Int)) (W13 : Nat) (hNW13 : W13 < M31) (_hD_W13 : b.hi.getD (2 * k + 2) 0 = (W13 : Int)) (_hl9_0 : k < (b.lo).length) (_hl10_1 : k < (b.hi).length) (hl6_2 : k < (b.len).length) (hl15_3 : W0 < (A).length) (hl0_4 : k < (b.mxv).length) (hl3_5 : k < (b.mnv).length) (hl1_6 : k < (b.smx).length) (hl4_7 : k < (b.smn).length) (hl2_8 : k < (b.mxc).length) (hl5_9 : k < (b.mnc).length) (_hl9_10 : (2 * k + 1) < (b.lo).length) (_hl10_11 : (2 * k + 1) < (b.hi).length) (_hl9_12 : (2 * k + 2) < (b.lo).length) (_hl10_13 : (2 * k + 2) < (b.hi).length) (_hl14_14 : ne < (b.ent).length) (X0 : Int) (hX0 : X0 = (if ((W0 : Int) < (W1 : Int)) then 1 else 0)) (X1 : Int) (hX1 : X1 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) = 1)) then 1 else 0)) (X2 : Int) (hX2 : X2 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) ≠ 1)) then 1 else 0)) (X3 : Int) (hX3 : X3 = (if (X0 = 1) then ((W1 : Int) - (W0 : Int)) else Z2)) (X4 : Int) (hX4 : X4 = (if (X1 = 1) then Z3 else Z4)) (X5 : Int) (hX5 : X5 = (if (X1 = 1) then Z3 else Z5)) (X6 : Int) (hX6 : X6 = (if (X1 = 1) then (-inf) else Z6)) (X7 : Int) (hX7 : X7 = (if (X1 = 1) then inf else Z7)) (X8 : Int) (hX8 : X8 = (if (X1 = 1) then 1 else Z8)) (X9 : Int) (hX9 : X9 = (if (X1 = 1) then 1 else Z9)) (X10 : Int) (hX10 : X10 = (if (X2 = 1) then (W0 : Int) else (W10 : Int))) (X11 : Int) (hX11 : X11 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W11 : Int))) (X12 : Int) (hX12 : X12 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W12 : Int))) (X13 : Int) (hX13 : X13 = (if (X2 = 1) then (W1 : Int) else (W13 : Int))) (X14 : Int) (hX14 : X14 = ((ne : Int) + X2)) (X15 : Int) (hX15 : X15 = ((k : Int) + 1)) (hsc0 : i32.valid ((W1 : Int) - (W0 : Int)) = true) (hsc1 : ((X1 = 1)) → s64.valid (-inf) = true) (hsc2 : i32.valid ((W0 : Int) + (W1 : Int)) = true) (hsc4 : i32.valid ((ne : Int) + X2) = true) (hsc5 : i32.valid ((k : Int) + 1) = true) (fu : Nat)
    (REST : Command) (r : PRM) (hrest : pexecM mv fu REST (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell)] : List Cell))) (VVA A (uw1 b k X3)) = some r) (hret : r.ret = none) :
    ∃ r0 : PRM, pexecM mv fu (WideCtLoopc2 (mv.nv + pre.length) REST) (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell))) (VVA A b) = some r0 ∧ r0.ret = none ∧
      r0.ps = r.ps ∧ r0.vv = r.vv ∧ r0.cost ≤ 1680 + r.cost ∧ r0.wk ≤ 1 + r.wk := by
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
  obtain ⟨r11, h11, hr11, hp11, hv11, hc11, hn11, hw11⟩ := seq_write mv fu (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell)] : List Cell))) (VVA A (b)) 6 (by rw [hnv]; decide) s64 (hty 6 (by decide))
    (.cast u64 (.variable i32 ((mv.nv + pre.length) + 3))) (.variable s64 ((mv.nv + pre.length) + 10)) X3 k (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell)] : List Cell)) s64 (pre.length + 10) _ (Nat.add_assoc _ _ _) X3 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell)] : List Cell) 10 _ rfl) vX3 _)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell)] : List Cell)) (pre.length + 3) _ (Nat.add_assoc _ _ _) k (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell)] : List Cell) 3 _ rfl) hkM (VVA A (b))))
    (by rw [VVA_get6]; simpa [uw1, uw2, uw3, uw4, uw5, uw6, uw7, uw8, uw9, uw10, uw11, uw12] using hl6_2) vX3
    (WideCtLoopc2_12 (mv.nv + pre.length) REST) r (by rw [VVA_get6, VVA_upd6]; exact hrest) hret
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_size]; omega)
  have hc11' : r11.cost ≤ 400 + r.cost := by exact Nat.le_trans hc11 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r10, h10, hr10, hp10, hv10, hc10, hn10, hw10⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, Z2⟩ : Cell)] : List Cell)) (VVA A (b)) (pre.length + 10) (by simp) s64
    (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 6)) (.literal i32 (1))) (.variable s64 ((mv.nv + pre.length) + 7)) ((X0 = 1)) ((W1 : Int) - (W0 : Int)) ((W1 : Int) - (W0 : Int)) Z2 (⟨s64, Z2⟩ : Cell)
    (den_cmpw mv _ _ _ _ _ X0 1 ((X0 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, Z2⟩ : Cell)] : List Cell)) i32 (pre.length + 6) _ (Nat.add_assoc _ _ _) X0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, Z2⟩ : Cell)] : List Cell) 6 _ rfl) vX0 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (fun hC => (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, Z2⟩ : Cell)] : List Cell)) s64 (pre.length + 7) _ (Nat.add_assoc _ _ _) ((W1 : Int) - (W0 : Int)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, Z2⟩ : Cell)] : List Cell) 7 _ rfl) (s64_of_i32 _ hsc0) _)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, Z2⟩ : Cell)] : List Cell) 10 _ rfl) rfl vZ2 rfl (fun hC => conv_s64 _ (s64_of_i32 _ hsc0))
    (WideCtLoopc2_11 (mv.nv + pre.length) REST) r11 (by
      rw [set_ext0 pre _ 10 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, Z2⟩ : Cell)] : List Cell).set 10 (⟨s64, if (X0 = 1) then ((W1 : Int) - (W0 : Int)) else Z2⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell)] : List Cell) := by
        rw [show (⟨s64, if (X0 = 1) then ((W1 : Int) - (W0 : Int)) else Z2⟩ : Cell) = ⟨s64, X3⟩ from by rw [hX3]]
        rfl
      rw [e2]; exact h11) hr11
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega)
  have hc10' : r10.cost ≤ 400 + r11.cost := by exact Nat.le_trans hc10 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r9, h9, hr9, hp9, hv9, hc9, hn9, hw9⟩ := seq_decl mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell)] : List Cell)) (VVA A (b)) s64 (.read s64 (.local 6) (.cast u64 (.variable i32 ((mv.nv + pre.length) + 3)))) Z2 Z2
    (den_rd mv (VVA A (b)) _ 6 (by rw [hnv]; decide) (hty 6 (by decide)) Z2 (.cast u64 (.variable i32 ((mv.nv + pre.length) + 3))) (by simp [NExpr.scalarOnly]) k (by rw [VVA_get6]; simpa [uw1, uw2, uw3, uw4, uw5, uw6, uw7, uw8, uw9, uw10, uw11, uw12] using hl6_2) (by rw [VVA_get6]; exact hD_Z2) (by rw [VVA_get6]; exact hvl6) (den_idx mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell)] : List Cell)) (pre.length + 3) _ (Nat.add_assoc _ _ _) k (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell)] : List Cell) 3 _ rfl) hkM (VVA A (b)))) (conv_s64 _ vZ2) (WideCtLoopc2_10 (mv.nv + pre.length) REST) r10 (by rw [List.append_assoc]; exact h10) hr10
  have hc9' : r9.cost ≤ 400 + r10.cost := by (try simp [vwp, NExpr.nodes] at hc9); exact Nat.le_trans hc9 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r8, h8, hr8, hp8, hv8, hc8, hn8, hw8⟩ := seq_sbranch3 mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVA A (b)) (pre.length + 9) (by simp) i32
    (.logical true (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 6)) (.literal i32 (1))) (.binary bT .ne (.variable s64 ((mv.nv + pre.length) + 7)) (.cast s64 (.literal i32 (1))))) (.literal i32 (1)) (((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) ≠ 1))) 1 1 0 (⟨i32, 0⟩ : Cell)
    (den_andw mv _ _ _ _ (X0 = 1) (((W1 : Int) - (W0 : Int)) ≠ 1) (den_cmpw mv _ _ _ _ _ X0 1 ((X0 = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 6) _ (Nat.add_assoc _ _ _) X0 (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 6 _ rfl) vX0 _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (den_cmpw mv _ _ _ _ _ ((W1 : Int) - (W0 : Int)) 1 ((((W1 : Int) - (W0 : Int)) ≠ 1)) (Proofs.BellmanFordExec.ne_conv _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) s64 (pre.length + 7) _ (Nat.add_assoc _ _ _) ((W1 : Int) - (W0 : Int)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 7 _ rfl) (s64_of_i32 _ hsc0) _) (den_castlit mv _ _ 1 (by decide) (by decide)) rfl rfl) (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly])) (fun hC => (den_lit32 mv _ _ 1 (by decide))) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 9 _ rfl) rfl (by decide) rfl (fun hC => conv_i32 _ (by decide))
    (WideCtLoopc2_9 (mv.nv + pre.length) REST) r9 (by
      rw [set_ext0 pre _ 9 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell).set 9 (⟨i32, if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) ≠ 1)) then 1 else 0⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell), (⟨i32, (k : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell)] : List Cell) := by
        rw [show (⟨i32, if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) ≠ 1)) then 1 else 0⟩ : Cell) = ⟨i32, X2⟩ from by rw [hX2]]
        rfl
      rw [e2]; exact h9) hr9
    300 (by simp [vwp, NExpr.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes]; omega)
  have hc8' : r8.cost ≤ 400 + r9.cost := by exact Nat.le_trans hc8 (Nat.add_le_add_right (by decide) _)
  clear hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13 hX14 hX15
  refine ⟨r8, h8, hr8, ?_, ?_, ?_, ?_⟩
  · rw [hp8, hp9, hp10, hp11]
  · rw [hv8, hv9, hv10, hv11]
  · omega
  · omega


end Proofs.BeatsExec
