import Proofs.BeatsRep
import Proofs.BeatsCalcFlags
import Proofs.BeatsExec_CalcLoop
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
theorem citer_down_set (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (b : BS) (P : List Cell)
    (inf : Int) (n op qa qb sp ne : Nat) (x : Int) (S : List Fr) (E : List Nat) (W0 W1 W2 : Nat)
    (C : IterCtx b inf n op qa qb sp ne x W0 W1 W2) (hstk : StkRep b sp (⟨W0, W1, W2⟩ :: S)) (hent : EntRep b ne E) (hnot : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) (hnotc : ¬ (qa ≤ W1 ∧ W2 ≤ qb)) (hne1 : ne + 1 < M31) (hsp2 : sp - 1 + 2 < M31) (hinfI : inf = INF) (hmode : (b.lval.getD W0 0) ≠ inf) (hlenL : (b.len.getD (2 * W0 + 1) 0) = ((((W1 + W2) / 2) - W1 : Nat) : Int)) (hlenR : (b.len.getD (2 * W0 + 2) 0) = ((W2 - ((W1 + W2) / 2) : Nat) : Int)) (hZ7 : (b.lval.getD W0 0) ≠ inf) (H : Heap) (hH : HRel inf b H) (hint : b.len.getD W0 0 ≠ 1) :
    ∃ (b' : BS), HRel inf b' (pushH H W0 (((((W1 + W2) / 2) - W1 : Nat)) : Int) ((W2 - ((W1 + W2) / 2) : Nat) : Int)) ∧
      StkRep b' (sp - 1 + 2) (⟨2 * W0 + 1, W1, ((W1 + W2) / 2)⟩ :: ⟨2 * W0 + 2, ((W1 + W2) / 2), W2⟩ :: S) ∧ EntRep b' ne E ∧ ValidOK b' ∧ SameLen b b' ∧ ∀ fu : Nat, ∃ r : PRM, pexecM mv fu (.sequence (.scope (CalcLoopBody (mv.nv + pre.length))) Sk) (gS P (pre ++ [cs inf, ci n, ci op, ci qa, ci qb, cs x, ci sp])) (VVB b) = some r ∧ r.ret = none ∧ r.ps = gS P (pre ++ [cs inf, ci n, ci op, ci qa, ci qb, cs x, ci (sp - 1 + 2)]) ∧ r.vv = VVB b' ∧ r.cost ≤ 72250 ∧ r.wk ≤ 24 := by
  classical
  have vz0 : s64.valid 0 = true := by decide
  obtain ⟨hinf, hninf, hnM, hopM, hqaM, hqbM, hspM, hneM, hsp, hx, hV, hW0, hW1, hW2, hk2, hlohi, hne1, hsp2, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hlsk, hlsl, hlsr, hlent⟩ := C
  have hD_W0 : b.sk.getD (sp - 1) 0 = (W0 : Int) := by simpa using (hstk.2 0 _ rfl).1
  have hD_W1 : b.sl.getD (sp - 1) 0 = (W1 : Int) := by simpa using (hstk.2 0 _ rfl).2.1
  have hD_W2 : b.sr.getD (sp - 1) 0 = (W2 : Int) := by simpa using (hstk.2 0 _ rfl).2.2
  have hl11_0 : (sp - 1) < (b.sk).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl12_1 : (sp - 1) < (b.sl).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl13_2 : (sp - 1) < (b.sr).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl0_3 : W0 < (b.mxv).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl3_4 : W0 < (b.mnv).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl8_5 : W0 < (b.lval).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl7_6 : W0 < (b.ladd).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl0_7 : (2 * W0 + 1) < (b.mxv).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl1_8 : (2 * W0 + 1) < (b.smx).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl2_9 : (2 * W0 + 1) < (b.mxc).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl3_10 : (2 * W0 + 1) < (b.mnv).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl4_11 : (2 * W0 + 1) < (b.smn).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl5_12 : (2 * W0 + 1) < (b.mnc).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl7_13 : (2 * W0 + 1) < (b.ladd).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl8_14 : (2 * W0 + 1) < (b.lval).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl6_15 : (2 * W0 + 1) < (b.len).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl0_16 : (2 * W0 + 2) < (b.mxv).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl1_17 : (2 * W0 + 2) < (b.smx).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl2_18 : (2 * W0 + 2) < (b.mxc).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl3_19 : (2 * W0 + 2) < (b.mnv).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl4_20 : (2 * W0 + 2) < (b.smn).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl5_21 : (2 * W0 + 2) < (b.mnc).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl7_22 : (2 * W0 + 2) < (b.ladd).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl8_23 : (2 * W0 + 2) < (b.lval).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl6_24 : (2 * W0 + 2) < (b.len).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl11_25 : ((sp - 1) + 1) < (b.sk).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl12_26 : ((sp - 1) + 1) < (b.sl).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hl13_27 : ((sp - 1) + 1) < (b.sr).length := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hk1_W0 : (2 * W0 + 1) < M31 := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hk2_W0 : (2 * W0 + 2) < M31 := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hix2 : ((sp - 1) + 1) < M31 := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hix3 : ((sp - 1) + 1) < M31 := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hix4 : ((sp - 1) + 1) < M31 := by clear hnot hnotc hne1 hsp2 hinfI hmode hlenL hlenR hZ7 hH hint; omega
  have hNW0 : W0 < M31 := hW0
  have hNW1 : W1 < M31 := hW1
  have hNW2 : W2 < M31 := hW2
  generalize hD_Z3 : b.mxv.getD W0 0 = Z3 at *
  generalize hD_Z4 : b.mnv.getD W0 0 = Z4 at *
  generalize hD_Z5 : b.lval.getD W0 0 = Z5 at *
  generalize hD_Z6 : b.ladd.getD W0 0 = Z6 at *
  generalize hD_Z7 : b.mxv.getD (2 * W0 + 1) 0 = Z7 at *
  generalize hD_Z8 : b.smx.getD (2 * W0 + 1) 0 = Z8 at *
  generalize hD_Z9 : b.mxc.getD (2 * W0 + 1) 0 = Z9 at *
  generalize hD_Z10 : b.mnv.getD (2 * W0 + 1) 0 = Z10 at *
  generalize hD_Z11 : b.smn.getD (2 * W0 + 1) 0 = Z11 at *
  generalize hD_Z12 : b.mnc.getD (2 * W0 + 1) 0 = Z12 at *
  generalize hD_Z13 : b.ladd.getD (2 * W0 + 1) 0 = Z13 at *
  generalize hD_Z14 : b.lval.getD (2 * W0 + 1) 0 = Z14 at *
  generalize hD_Z15 : b.len.getD (2 * W0 + 1) 0 = Z15 at *
  generalize hD_Z16 : b.mxv.getD (2 * W0 + 2) 0 = Z16 at *
  generalize hD_Z17 : b.smx.getD (2 * W0 + 2) 0 = Z17 at *
  generalize hD_Z18 : b.mxc.getD (2 * W0 + 2) 0 = Z18 at *
  generalize hD_Z19 : b.mnv.getD (2 * W0 + 2) 0 = Z19 at *
  generalize hD_Z20 : b.smn.getD (2 * W0 + 2) 0 = Z20 at *
  generalize hD_Z21 : b.mnc.getD (2 * W0 + 2) 0 = Z21 at *
  generalize hD_Z22 : b.ladd.getD (2 * W0 + 2) 0 = Z22 at *
  generalize hD_Z23 : b.lval.getD (2 * W0 + 2) 0 = Z23 at *
  generalize hD_Z24 : b.len.getD (2 * W0 + 2) 0 = Z24 at *
  have hvl0 : ∀ w ∈ b.mxv, s64.valid w = true := hV.v0
  have hvl1 : ∀ w ∈ b.smx, s64.valid w = true := hV.v1
  have hvl2 : ∀ w ∈ b.mxc, s64.valid w = true := hV.v2
  have hvl3 : ∀ w ∈ b.mnv, s64.valid w = true := hV.v3
  have hvl4 : ∀ w ∈ b.smn, s64.valid w = true := hV.v4
  have hvl5 : ∀ w ∈ b.mnc, s64.valid w = true := hV.v5
  have hvl6 : ∀ w ∈ b.len, s64.valid w = true := hV.v6
  have hvl7 : ∀ w ∈ b.ladd, s64.valid w = true := hV.v7
  have hvl8 : ∀ w ∈ b.lval, s64.valid w = true := hV.v8
  have hvl11 : ∀ w ∈ b.sk, i32.valid w = true := hV.v11
  have hvl12 : ∀ w ∈ b.sl, i32.valid w = true := hV.v12
  have hvl13 : ∀ w ∈ b.sr, i32.valid w = true := hV.v13
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
  obtain ⟨X0, hX0⟩ : ∃ v : Int, v = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ v : Int, v = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ v : Int, v = (if ((X0 = 0) ∧ (X1 = 1)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X3, hX3⟩ : ∃ v : Int, v = (if ((X0 = 0) ∧ (X2 = 0)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X4, hX4⟩ : ∃ v : Int, v = (if (((X2 = 1) ∧ ((op : Int) = 0)) ∧ (x < Z3)) then Z3 else x) := ⟨_, rfl⟩
  obtain ⟨X5, hX5⟩ : ∃ v : Int, v = (if (((X2 = 1) ∧ ((op : Int) = 1)) ∧ (Z4 < X4)) then Z4 else X4) := ⟨_, rfl⟩
  obtain ⟨X6, hX6⟩ : ∃ v : Int, v = (if ((X3 = 1) ∧ (Z5 ≠ inf)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X7, hX7⟩ : ∃ v : Int, v = (if ((X3 = 1) ∧ (X6 = 0)) then Z6 else 0) := ⟨_, rfl⟩
  obtain ⟨X8, hX8⟩ : ∃ v : Int, v = (if ((X3 = 1) ∧ (X6 = 0)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X9, hX9⟩ : ∃ v : Int, v = (if (X6 = 1) then Z5 else Z7) := ⟨_, rfl⟩
  obtain ⟨X10, hX10⟩ : ∃ v : Int, v = (if (X6 = 1) then (-inf) else Z8) := ⟨_, rfl⟩
  obtain ⟨X11, hX11⟩ : ∃ v : Int, v = (if (X6 = 1) then Z15 else Z9) := ⟨_, rfl⟩
  obtain ⟨X12, hX12⟩ : ∃ v : Int, v = (if (X6 = 1) then Z5 else Z10) := ⟨_, rfl⟩
  obtain ⟨X13, hX13⟩ : ∃ v : Int, v = (if (X6 = 1) then inf else Z11) := ⟨_, rfl⟩
  obtain ⟨X14, hX14⟩ : ∃ v : Int, v = (if (X6 = 1) then Z15 else Z12) := ⟨_, rfl⟩
  obtain ⟨X15, hX15⟩ : ∃ v : Int, v = (if (X6 = 1) then 0 else Z13) := ⟨_, rfl⟩
  obtain ⟨X16, hX16⟩ : ∃ v : Int, v = (if ((X6 = 1) ∧ (Z15 ≠ 1)) then Z5 else Z14) := ⟨_, rfl⟩
  obtain ⟨X17, hX17⟩ : ∃ v : Int, v = (if (X10 ≠ (-inf)) then (X10 + X7) else X10) := ⟨_, rfl⟩
  obtain ⟨X18, hX18⟩ : ∃ v : Int, v = (if (X13 ≠ inf) then (X13 + X7) else X13) := ⟨_, rfl⟩
  obtain ⟨X19, hX19⟩ : ∃ v : Int, v = (if ((X16 = inf) ∧ (Z15 ≠ 1)) then (X15 + X7) else X15) := ⟨_, rfl⟩
  obtain ⟨X20, hX20⟩ : ∃ v : Int, v = (if (X16 ≠ inf) then (X16 + X7) else X16) := ⟨_, rfl⟩
  obtain ⟨X21, hX21⟩ : ∃ v : Int, v = (if ((X8 = 1) ∧ (Z3 < (X9 + X7))) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X22, hX22⟩ : ∃ v : Int, v = (if (X21 = 1) then Z3 else (X9 + X7)) := ⟨_, rfl⟩
  obtain ⟨X23, hX23⟩ : ∃ v : Int, v = (if ((X21 = 1) ∧ ((X9 + X7) = (X12 + X7))) then Z3 else (X12 + X7)) := ⟨_, rfl⟩
  obtain ⟨X24, hX24⟩ : ∃ v : Int, v = (if (((X21 = 1) ∧ ((X9 + X7) ≠ (X12 + X7))) ∧ ((X9 + X7) = X18)) then Z3 else X18) := ⟨_, rfl⟩
  obtain ⟨X25, hX25⟩ : ∃ v : Int, v = (if (((X21 = 1) ∧ (X20 ≠ inf)) ∧ (Z3 < X20)) then Z3 else X20) := ⟨_, rfl⟩
  obtain ⟨X26, hX26⟩ : ∃ v : Int, v = (if ((X8 = 1) ∧ (X23 < Z4)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X27, hX27⟩ : ∃ v : Int, v = (if (X26 = 1) then Z4 else X23) := ⟨_, rfl⟩
  obtain ⟨X28, hX28⟩ : ∃ v : Int, v = (if ((X26 = 1) ∧ (X22 = X23)) then Z4 else X22) := ⟨_, rfl⟩
  obtain ⟨X29, hX29⟩ : ∃ v : Int, v = (if (((X26 = 1) ∧ (X22 ≠ X23)) ∧ (X17 = X23)) then Z4 else X17) := ⟨_, rfl⟩
  obtain ⟨X30, hX30⟩ : ∃ v : Int, v = (if (((X26 = 1) ∧ (X25 ≠ inf)) ∧ (X25 < Z4)) then Z4 else X25) := ⟨_, rfl⟩
  obtain ⟨X31, hX31⟩ : ∃ v : Int, v = (if (X6 = 1) then Z5 else Z16) := ⟨_, rfl⟩
  obtain ⟨X32, hX32⟩ : ∃ v : Int, v = (if (X6 = 1) then (-inf) else Z17) := ⟨_, rfl⟩
  obtain ⟨X33, hX33⟩ : ∃ v : Int, v = (if (X6 = 1) then Z24 else Z18) := ⟨_, rfl⟩
  obtain ⟨X34, hX34⟩ : ∃ v : Int, v = (if (X6 = 1) then Z5 else Z19) := ⟨_, rfl⟩
  obtain ⟨X35, hX35⟩ : ∃ v : Int, v = (if (X6 = 1) then inf else Z20) := ⟨_, rfl⟩
  obtain ⟨X36, hX36⟩ : ∃ v : Int, v = (if (X6 = 1) then Z24 else Z21) := ⟨_, rfl⟩
  obtain ⟨X37, hX37⟩ : ∃ v : Int, v = (if (X6 = 1) then 0 else Z22) := ⟨_, rfl⟩
  obtain ⟨X38, hX38⟩ : ∃ v : Int, v = (if ((X6 = 1) ∧ (Z24 ≠ 1)) then Z5 else Z23) := ⟨_, rfl⟩
  obtain ⟨X39, hX39⟩ : ∃ v : Int, v = (if (X32 ≠ (-inf)) then (X32 + X7) else X32) := ⟨_, rfl⟩
  obtain ⟨X40, hX40⟩ : ∃ v : Int, v = (if (X35 ≠ inf) then (X35 + X7) else X35) := ⟨_, rfl⟩
  obtain ⟨X41, hX41⟩ : ∃ v : Int, v = (if ((X38 = inf) ∧ (Z24 ≠ 1)) then (X37 + X7) else X37) := ⟨_, rfl⟩
  obtain ⟨X42, hX42⟩ : ∃ v : Int, v = (if (X38 ≠ inf) then (X38 + X7) else X38) := ⟨_, rfl⟩
  obtain ⟨X43, hX43⟩ : ∃ v : Int, v = (if ((X8 = 1) ∧ (Z3 < (X31 + X7))) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X44, hX44⟩ : ∃ v : Int, v = (if (X43 = 1) then Z3 else (X31 + X7)) := ⟨_, rfl⟩
  obtain ⟨X45, hX45⟩ : ∃ v : Int, v = (if ((X43 = 1) ∧ ((X31 + X7) = (X34 + X7))) then Z3 else (X34 + X7)) := ⟨_, rfl⟩
  obtain ⟨X46, hX46⟩ : ∃ v : Int, v = (if (((X43 = 1) ∧ ((X31 + X7) ≠ (X34 + X7))) ∧ ((X31 + X7) = X40)) then Z3 else X40) := ⟨_, rfl⟩
  obtain ⟨X47, hX47⟩ : ∃ v : Int, v = (if (((X43 = 1) ∧ (X42 ≠ inf)) ∧ (Z3 < X42)) then Z3 else X42) := ⟨_, rfl⟩
  obtain ⟨X48, hX48⟩ : ∃ v : Int, v = (if ((X8 = 1) ∧ (X45 < Z4)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X49, hX49⟩ : ∃ v : Int, v = (if (X48 = 1) then Z4 else X45) := ⟨_, rfl⟩
  obtain ⟨X50, hX50⟩ : ∃ v : Int, v = (if ((X48 = 1) ∧ (X44 = X45)) then Z4 else X44) := ⟨_, rfl⟩
  obtain ⟨X51, hX51⟩ : ∃ v : Int, v = (if (((X48 = 1) ∧ (X44 ≠ X45)) ∧ (X39 = X45)) then Z4 else X39) := ⟨_, rfl⟩
  obtain ⟨X52, hX52⟩ : ∃ v : Int, v = (if (((X48 = 1) ∧ (X47 ≠ inf)) ∧ (X47 < Z4)) then Z4 else X47) := ⟨_, rfl⟩
  obtain ⟨X53, hX53⟩ : ∃ v : Int, v = (if (X3 = 1) then inf else Z5) := ⟨_, rfl⟩
  obtain ⟨X54, hX54⟩ : ∃ v : Int, v = (if (X3 = 1) then 0 else Z6) := ⟨_, rfl⟩
  obtain ⟨X55, hX55⟩ : ∃ v : Int, v = (((sp - 1 : Nat) : Int) + (2 * X3)) := ⟨_, rfl⟩
  have hs' : ¬ (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) := cflag_nstop qa qb W1 W2 hnot
  have hc' : ¬ (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) := cflag_ncov qa qb W1 W2 hnotc
  have eX0 : X0 = 0 := by rw [hX0, if_neg hs']
  have eX1 : X1 = 0 := by rw [hX1, if_neg hc']
  have eX2 : X2 = 0 := by rw [hX2, eX0, eX1]; simp
  have eX3 : X3 = 1 := by rw [hX3, eX0, eX2]; simp
  have eX4 : X4 = x := by rw [hX4]; try simp [hmode, eX2]
  have eX5 : X5 = x := by rw [hX5]; try simp [hmode, eX2, eX4]
  have eX6 : X6 = 1 := by rw [hX6]; try simp [hmode, eX3]
  have eX7 : X7 = 0 := by rw [hX7]; try simp [hmode, eX3, eX6]
  have eX8 : X8 = 0 := by rw [hX8]; try simp [hmode, eX3, eX6]
  have eX9 : X9 = Z5 := by rw [hX9]; try simp [hmode, eX6]
  have eX10 : X10 = (-inf) := by rw [hX10]; try simp [hmode, eX6]
  have eX11 : X11 = Z15 := by rw [hX11]; try simp [hmode, eX6]
  have eX12 : X12 = Z5 := by rw [hX12]; try simp [hmode, eX6]
  have eX13 : X13 = inf := by rw [hX13]; try simp [hmode, eX6]
  have eX14 : X14 = Z15 := by rw [hX14]; try simp [hmode, eX6]
  have eX15 : X15 = 0 := by rw [hX15]; try simp [hmode, eX6]
  have eX16 : X16 = (if (Z15 ≠ 1) then Z5 else Z14) := by rw [hX16]; try simp [hmode, eX6]
  have eX17 : X17 = (-inf) := by rw [hX17]; try simp [hmode, eX7, eX10]
  have eX18 : X18 = inf := by rw [hX18]; try simp [hmode, eX7, eX13]
  have eX19 : X19 = 0 := by rw [hX19]; try simp [hmode, eX7, eX15]
  have eX20 : X20 = X16 := by rw [hX20]; try simp [hmode, eX7]
  have eX21 : X21 = 0 := by rw [hX21]; try simp [hmode, eX7, eX8, eX9]
  have eX22 : X22 = Z5 := by rw [hX22]; try simp [hmode, eX7, eX9, eX21]
  have eX23 : X23 = Z5 := by rw [hX23]; try simp [hmode, eX7, eX9, eX12, eX21]
  have eX24 : X24 = inf := by rw [hX24]; try simp [hmode, eX7, eX9, eX12, eX18, eX21]
  have eX25 : X25 = X16 := by rw [hX25]; try simp [hmode, eX20, eX21]
  have eX26 : X26 = 0 := by rw [hX26]; try simp [hmode, eX8, eX23]
  have eX27 : X27 = Z5 := by rw [hX27]; try simp [hmode, eX23, eX26]
  have eX28 : X28 = Z5 := by rw [hX28]; try simp [hmode, eX22, eX23, eX26]
  have eX29 : X29 = (-inf) := by rw [hX29]; try simp [hmode, eX17, eX22, eX23, eX26]
  have eX30 : X30 = X16 := by rw [hX30]; try simp [hmode, eX25, eX26]
  have eX31 : X31 = Z5 := by rw [hX31]; try simp [hmode, eX6]
  have eX32 : X32 = (-inf) := by rw [hX32]; try simp [hmode, eX6]
  have eX33 : X33 = Z24 := by rw [hX33]; try simp [hmode, eX6]
  have eX34 : X34 = Z5 := by rw [hX34]; try simp [hmode, eX6]
  have eX35 : X35 = inf := by rw [hX35]; try simp [hmode, eX6]
  have eX36 : X36 = Z24 := by rw [hX36]; try simp [hmode, eX6]
  have eX37 : X37 = 0 := by rw [hX37]; try simp [hmode, eX6]
  have eX38 : X38 = (if (Z24 ≠ 1) then Z5 else Z23) := by rw [hX38]; try simp [hmode, eX6]
  have eX39 : X39 = (-inf) := by rw [hX39]; try simp [hmode, eX7, eX32]
  have eX40 : X40 = inf := by rw [hX40]; try simp [hmode, eX7, eX35]
  have eX41 : X41 = 0 := by rw [hX41]; try simp [hmode, eX7, eX37]
  have eX42 : X42 = X38 := by rw [hX42]; try simp [hmode, eX7]
  have eX43 : X43 = 0 := by rw [hX43]; try simp [hmode, eX7, eX8, eX31]
  have eX44 : X44 = Z5 := by rw [hX44]; try simp [hmode, eX7, eX31, eX43]
  have eX45 : X45 = Z5 := by rw [hX45]; try simp [hmode, eX7, eX31, eX34, eX43]
  have eX46 : X46 = inf := by rw [hX46]; try simp [hmode, eX7, eX31, eX34, eX40, eX43]
  have eX47 : X47 = X38 := by rw [hX47]; try simp [hmode, eX42, eX43]
  have eX48 : X48 = 0 := by rw [hX48]; try simp [hmode, eX8, eX45]
  have eX49 : X49 = Z5 := by rw [hX49]; try simp [hmode, eX45, eX48]
  have eX50 : X50 = Z5 := by rw [hX50]; try simp [hmode, eX44, eX45, eX48]
  have eX51 : X51 = (-inf) := by rw [hX51]; try simp [hmode, eX39, eX44, eX45, eX48]
  have eX52 : X52 = X38 := by rw [hX52]; try simp [hmode, eX47, eX48]
  have eX53 : X53 = inf := by rw [hX53]; try simp [hmode, eX3]
  have eX54 : X54 = 0 := by rw [hX54]; try simp [hmode, eX3]
  have eX55 : X55 = (((sp - 1 : Nat) : Int) + 2) := by rw [hX55]; try simp [hmode, eX3]
  have hsc0 : i32.valid ((sp : Int) - 1) = true := (by rw [sub_one_cast sp hsp]; exact Proofs.BellmanFordExec.i32_valid_nat _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hspM))
  have hsc3 : s64.valid (-inf) = true := by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf]
  have hsc15 : i32.valid ((W1 : Int) + (W2 : Int)) = true := (by have := Proofs.BellmanFordExec.i32_valid_nat (W1 + W2) hlohi; simpa using this)
  have hsc17 : i32.valid (2 * (W0 : Int)) = true := (by have := Proofs.BellmanFordExec.i32_valid_nat (2 * W0) (Nat.lt_of_le_of_lt (by omega) hk2_W0); simpa using this)
  have hsc18 : i32.valid ((2 * (W0 : Int)) + 2) = true := (by have := Proofs.BellmanFordExec.i32_valid_nat (2 * W0 + 2) hk2_W0; simpa using this)
  have hsc19 : i32.valid ((2 * (W0 : Int)) + 1) = true := (by have := Proofs.BellmanFordExec.i32_valid_nat (2 * W0 + 1) hk1_W0; simpa using this)
  have hsc20 : i32.valid (2 * X3) = true := (by rw [eX3]; decide)
  have hsc21 : i32.valid (((sp - 1 : Nat) : Int) + (2 * X3)) = true := (by rw [eX3]; have := Proofs.BellmanFordExec.i32_valid_nat (sp - 1 + 2) hsp2; simpa using this)
  have vX4 : s64.valid X4 = true := by rw [eX4]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX5 : s64.valid X5 = true := by rw [eX5]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX6 : i32.valid X6 = true := by rw [eX6]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc1 : ((X6 = 1)) → s64.valid (-inf) = true := fun hC => by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf]
  have vX7 : s64.valid X7 = true := by rw [eX7]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX8 : i32.valid X8 = true := by rw [eX8]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX9 : s64.valid X9 = true := by rw [eX9]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc2 : s64.valid (X9 + X7) = true := by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf]
  have vX10 : s64.valid X10 = true := by rw [eX10]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc4 : ((X10 ≠ (-inf))) → s64.valid (X10 + X7) = true := fun hC => by exfalso; revert hC; simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55]
  have vX11 : s64.valid X11 = true := by rw [eX11]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX12 : s64.valid X12 = true := by rw [eX12]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc5 : s64.valid (X12 + X7) = true := by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf]
  have vX13 : s64.valid X13 = true := by rw [eX13]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc6 : ((X13 ≠ inf)) → s64.valid (X13 + X7) = true := fun hC => by exfalso; revert hC; simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55]
  have vX14 : s64.valid X14 = true := by rw [eX14]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX15 : s64.valid X15 = true := by rw [eX15]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, hx, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX16 : s64.valid X16 = true := by
    rw [hX16]
    by_cases hC : ((X6 = 1) ∧ (Z15 ≠ 1))
    · rw [if_pos hC]; exact vZ5
    · rw [if_neg hC]; exact vZ14
  have hsc7 : (((X16 = inf) ∧ (Z15 ≠ 1))) → s64.valid (X15 + X7) = true := fun hC => by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf]
  have hsc8 : ((X16 ≠ inf)) → s64.valid (X16 + X7) = true := fun hC => by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf]
  have vX17 : s64.valid X17 = true := by rw [eX17]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX18 : s64.valid X18 = true := by rw [eX18]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX19 : s64.valid X19 = true := by rw [eX19]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX20 : s64.valid X20 = true := by rw [eX20]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX21 : i32.valid X21 = true := by rw [eX21]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX22 : s64.valid X22 = true := by rw [eX22]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX23 : s64.valid X23 = true := by rw [eX23]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX24 : s64.valid X24 = true := by rw [eX24]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX25 : s64.valid X25 = true := by rw [eX25]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX26 : i32.valid X26 = true := by rw [eX26]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX27 : s64.valid X27 = true := by rw [eX27]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX28 : s64.valid X28 = true := by rw [eX28]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX29 : s64.valid X29 = true := by rw [eX29]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX30 : s64.valid X30 = true := by rw [eX30]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX31 : s64.valid X31 = true := by rw [eX31]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc9 : s64.valid (X31 + X7) = true := by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf]
  have vX32 : s64.valid X32 = true := by rw [eX32]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc10 : ((X32 ≠ (-inf))) → s64.valid (X32 + X7) = true := fun hC => by exfalso; revert hC; simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55]
  have vX33 : s64.valid X33 = true := by rw [eX33]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX34 : s64.valid X34 = true := by rw [eX34]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc11 : s64.valid (X34 + X7) = true := by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf]
  have vX35 : s64.valid X35 = true := by rw [eX35]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc12 : ((X35 ≠ inf)) → s64.valid (X35 + X7) = true := fun hC => by exfalso; revert hC; simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55]
  have vX36 : s64.valid X36 = true := by rw [eX36]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX37 : s64.valid X37 = true := by rw [eX37]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX38 : s64.valid X38 = true := by
    rw [hX38]
    by_cases hC : ((X6 = 1) ∧ (Z24 ≠ 1))
    · rw [if_pos hC]; exact vZ5
    · rw [if_neg hC]; exact vZ23
  have hsc13 : (((X38 = inf) ∧ (Z24 ≠ 1))) → s64.valid (X37 + X7) = true := fun hC => by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf]
  have hsc14 : ((X38 ≠ inf)) → s64.valid (X38 + X7) = true := fun hC => by simp [eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf]
  have vX39 : s64.valid X39 = true := by rw [eX39]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX40 : s64.valid X40 = true := by rw [eX40]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX41 : s64.valid X41 = true := by rw [eX41]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX42 : s64.valid X42 = true := by rw [eX42]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX43 : i32.valid X43 = true := by rw [eX43]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX44 : s64.valid X44 = true := by rw [eX44]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX45 : s64.valid X45 = true := by rw [eX45]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX46 : s64.valid X46 = true := by rw [eX46]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX47 : s64.valid X47 = true := by rw [eX47]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX48 : i32.valid X48 = true := by rw [eX48]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX49 : s64.valid X49 = true := by rw [eX49]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX50 : s64.valid X50 = true := by rw [eX50]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX51 : s64.valid X51 = true := by rw [eX51]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX52 : s64.valid X52 = true := by rw [eX52]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX53 : s64.valid X53 = true := by rw [eX53]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX54 : s64.valid X54 = true := by rw [eX54]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vz0, vX16, vX38, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hn1 : W0 ≠ 2 * W0 + 1 := by omega
  have hn2 : W0 ≠ 2 * W0 + 2 := by omega
  have hn3 : 2 * W0 + 1 ≠ W0 := by omega
  have hn4 : 2 * W0 + 2 ≠ W0 := by omega
  have hn5 : 2 * W0 + 1 ≠ 2 * W0 + 2 := by omega
  have hn6 : 2 * W0 + 2 ≠ 2 * W0 + 1 := by omega
  have hD'_Z3 : b.mxv[W0]?.getD 0 = Z3 := by simpa [List.getD_eq_getElem?_getD] using hD_Z3
  have hD'_Z4 : b.mnv[W0]?.getD 0 = Z4 := by simpa [List.getD_eq_getElem?_getD] using hD_Z4
  have hD'_Z5 : b.lval[W0]?.getD 0 = Z5 := by simpa [List.getD_eq_getElem?_getD] using hD_Z5
  have hD'_Z6 : b.ladd[W0]?.getD 0 = Z6 := by simpa [List.getD_eq_getElem?_getD] using hD_Z6
  have hD'_Z7 : b.mxv[(2 * W0 + 1)]?.getD 0 = Z7 := by simpa [List.getD_eq_getElem?_getD] using hD_Z7
  have hD'_Z8 : b.smx[(2 * W0 + 1)]?.getD 0 = Z8 := by simpa [List.getD_eq_getElem?_getD] using hD_Z8
  have hD'_Z9 : b.mxc[(2 * W0 + 1)]?.getD 0 = Z9 := by simpa [List.getD_eq_getElem?_getD] using hD_Z9
  have hD'_Z10 : b.mnv[(2 * W0 + 1)]?.getD 0 = Z10 := by simpa [List.getD_eq_getElem?_getD] using hD_Z10
  have hD'_Z11 : b.smn[(2 * W0 + 1)]?.getD 0 = Z11 := by simpa [List.getD_eq_getElem?_getD] using hD_Z11
  have hD'_Z12 : b.mnc[(2 * W0 + 1)]?.getD 0 = Z12 := by simpa [List.getD_eq_getElem?_getD] using hD_Z12
  have hD'_Z13 : b.ladd[(2 * W0 + 1)]?.getD 0 = Z13 := by simpa [List.getD_eq_getElem?_getD] using hD_Z13
  have hD'_Z14 : b.lval[(2 * W0 + 1)]?.getD 0 = Z14 := by simpa [List.getD_eq_getElem?_getD] using hD_Z14
  have hD'_Z15 : b.len[(2 * W0 + 1)]?.getD 0 = Z15 := by simpa [List.getD_eq_getElem?_getD] using hD_Z15
  have hD'_Z16 : b.mxv[(2 * W0 + 2)]?.getD 0 = Z16 := by simpa [List.getD_eq_getElem?_getD] using hD_Z16
  have hD'_Z17 : b.smx[(2 * W0 + 2)]?.getD 0 = Z17 := by simpa [List.getD_eq_getElem?_getD] using hD_Z17
  have hD'_Z18 : b.mxc[(2 * W0 + 2)]?.getD 0 = Z18 := by simpa [List.getD_eq_getElem?_getD] using hD_Z18
  have hD'_Z19 : b.mnv[(2 * W0 + 2)]?.getD 0 = Z19 := by simpa [List.getD_eq_getElem?_getD] using hD_Z19
  have hD'_Z20 : b.smn[(2 * W0 + 2)]?.getD 0 = Z20 := by simpa [List.getD_eq_getElem?_getD] using hD_Z20
  have hD'_Z21 : b.mnc[(2 * W0 + 2)]?.getD 0 = Z21 := by simpa [List.getD_eq_getElem?_getD] using hD_Z21
  have hD'_Z22 : b.ladd[(2 * W0 + 2)]?.getD 0 = Z22 := by simpa [List.getD_eq_getElem?_getD] using hD_Z22
  have hD'_Z23 : b.lval[(2 * W0 + 2)]?.getD 0 = Z23 := by simpa [List.getD_eq_getElem?_getD] using hD_Z23
  have hD'_Z24 : b.len[(2 * W0 + 2)]?.getD 0 = Z24 := by simpa [List.getD_eq_getElem?_getD] using hD_Z24
  obtain ⟨B, hB⟩ : ∃ B : BS, B = (uc24 (uc23 (uc22 (uc21 (uc20 (uc19 (uc18 (uc17 (uc16 (uc15 (uc14 (uc13 (uc12 (uc11 (uc10 (uc9 (uc8 (uc7 (uc6 (uc5 (uc4 (uc3 (uc2 (uc1 b (2 * W0 + 1) X28) (2 * W0 + 1) X29) (2 * W0 + 1) X11) (2 * W0 + 1) X27) (2 * W0 + 1) X24) (2 * W0 + 1) X14) (2 * W0 + 1) X19) (2 * W0 + 1) X30) (2 * W0 + 2) X50) (2 * W0 + 2) X51) (2 * W0 + 2) X33) (2 * W0 + 2) X49) (2 * W0 + 2) X46) (2 * W0 + 2) X36) (2 * W0 + 2) X41) (2 * W0 + 2) X52) W0 X53) W0 X54) (sp - 1) ((2 * (W0 : Int)) + 2)) (sp - 1) (((W1 : Int) + (W2 : Int)) / 2)) (sp - 1) (W2 : Int)) ((sp - 1) + 1) ((2 * (W0 : Int)) + 1)) ((sp - 1) + 1) (W1 : Int)) ((sp - 1) + 1) (((W1 : Int) + (W2 : Int)) / 2)) := ⟨_, rfl⟩
  have g_mxv : ∀ i, B.mxv.getD i 0 = (lastW [((2 * W0 + 1), X28), ((2 * W0 + 2), X50)] i).getD (b.mxv.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((2 * W0 + 1), X28), ((2 * W0 + 2), X50)] b.mxv i (by simp [hl0_3, hl0_7, hl0_16])
  have g'_mxv : ∀ i, B.mxv[i]?.getD 0 = (lastW [((2 * W0 + 1), X28), ((2 * W0 + 2), X50)] i).getD (b.mxv[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_mxv i
  have g_smx : ∀ i, B.smx.getD i 0 = (lastW [((2 * W0 + 1), X29), ((2 * W0 + 2), X51)] i).getD (b.smx.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((2 * W0 + 1), X29), ((2 * W0 + 2), X51)] b.smx i (by simp [hl1_8, hl1_17])
  have g'_smx : ∀ i, B.smx[i]?.getD 0 = (lastW [((2 * W0 + 1), X29), ((2 * W0 + 2), X51)] i).getD (b.smx[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_smx i
  have g_mxc : ∀ i, B.mxc.getD i 0 = (lastW [((2 * W0 + 1), X11), ((2 * W0 + 2), X33)] i).getD (b.mxc.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((2 * W0 + 1), X11), ((2 * W0 + 2), X33)] b.mxc i (by simp [hl2_9, hl2_18])
  have g'_mxc : ∀ i, B.mxc[i]?.getD 0 = (lastW [((2 * W0 + 1), X11), ((2 * W0 + 2), X33)] i).getD (b.mxc[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_mxc i
  have g_mnv : ∀ i, B.mnv.getD i 0 = (lastW [((2 * W0 + 1), X27), ((2 * W0 + 2), X49)] i).getD (b.mnv.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((2 * W0 + 1), X27), ((2 * W0 + 2), X49)] b.mnv i (by simp [hl3_4, hl3_10, hl3_19])
  have g'_mnv : ∀ i, B.mnv[i]?.getD 0 = (lastW [((2 * W0 + 1), X27), ((2 * W0 + 2), X49)] i).getD (b.mnv[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_mnv i
  have g_smn : ∀ i, B.smn.getD i 0 = (lastW [((2 * W0 + 1), X24), ((2 * W0 + 2), X46)] i).getD (b.smn.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((2 * W0 + 1), X24), ((2 * W0 + 2), X46)] b.smn i (by simp [hl4_11, hl4_20])
  have g'_smn : ∀ i, B.smn[i]?.getD 0 = (lastW [((2 * W0 + 1), X24), ((2 * W0 + 2), X46)] i).getD (b.smn[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_smn i
  have g_mnc : ∀ i, B.mnc.getD i 0 = (lastW [((2 * W0 + 1), X14), ((2 * W0 + 2), X36)] i).getD (b.mnc.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((2 * W0 + 1), X14), ((2 * W0 + 2), X36)] b.mnc i (by simp [hl5_12, hl5_21])
  have g'_mnc : ∀ i, B.mnc[i]?.getD 0 = (lastW [((2 * W0 + 1), X14), ((2 * W0 + 2), X36)] i).getD (b.mnc[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_mnc i
  have g_ladd : ∀ i, B.ladd.getD i 0 = (lastW [((2 * W0 + 1), X19), ((2 * W0 + 2), X41), (W0, X54)] i).getD (b.ladd.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((2 * W0 + 1), X19), ((2 * W0 + 2), X41), (W0, X54)] b.ladd i (by simp [hl7_6, hl7_13, hl7_22])
  have g'_ladd : ∀ i, B.ladd[i]?.getD 0 = (lastW [((2 * W0 + 1), X19), ((2 * W0 + 2), X41), (W0, X54)] i).getD (b.ladd[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_ladd i
  have g_lval : ∀ i, B.lval.getD i 0 = (lastW [((2 * W0 + 1), X30), ((2 * W0 + 2), X52), (W0, X53)] i).getD (b.lval.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((2 * W0 + 1), X30), ((2 * W0 + 2), X52), (W0, X53)] b.lval i (by simp [hl8_5, hl8_14, hl8_23])
  have g'_lval : ∀ i, B.lval[i]?.getD 0 = (lastW [((2 * W0 + 1), X30), ((2 * W0 + 2), X52), (W0, X53)] i).getD (b.lval[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_lval i
  have g_sk : ∀ i, B.sk.getD i 0 = (lastW [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] i).getD (b.sk.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] b.sk i (by simp [hl11_0, hl11_25])
  have g'_sk : ∀ i, B.sk[i]?.getD 0 = (lastW [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] i).getD (b.sk[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_sk i
  have g_sl : ∀ i, B.sl.getD i 0 = (lastW [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] i).getD (b.sl.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] b.sl i (by simp [hl12_1, hl12_26])
  have g'_sl : ∀ i, B.sl[i]?.getD 0 = (lastW [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] i).getD (b.sl[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_sl i
  have g_sr : ∀ i, B.sr.getD i 0 = (lastW [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] i).getD (b.sr.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] b.sr i (by simp [hl13_2, hl13_27])
  have g'_sr : ∀ i, B.sr[i]?.getD 0 = (lastW [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] i).getD (b.sr[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_sr i
  have wv0 : s64.valid X28 = true := vX28
  have wv1 : s64.valid X29 = true := vX29
  have wv2 : s64.valid X11 = true := vX11
  have wv3 : s64.valid X27 = true := vX27
  have wv4 : s64.valid X24 = true := vX24
  have wv5 : s64.valid X14 = true := vX14
  have wv6 : s64.valid X19 = true := vX19
  have wv7 : s64.valid X30 = true := vX30
  have wv8 : s64.valid X50 = true := vX50
  have wv9 : s64.valid X51 = true := vX51
  have wv10 : s64.valid X33 = true := vX33
  have wv11 : s64.valid X49 = true := vX49
  have wv12 : s64.valid X46 = true := vX46
  have wv13 : s64.valid X36 = true := vX36
  have wv14 : s64.valid X41 = true := vX41
  have wv15 : s64.valid X52 = true := vX52
  have wv16 : s64.valid X53 = true := vX53
  have wv17 : s64.valid X54 = true := vX54
  have wv18 : i32.valid ((2 * (W0 : Int)) + 2) = true := hsc18
  have wv19 : i32.valid (((W1 : Int) + (W2 : Int)) / 2) = true := (i32_valid_div2 _ hsc15 (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)))
  have wv20 : i32.valid (W2 : Int) = true := (Proofs.BellmanFordExec.i32_valid_nat W2 hNW2)
  have wv21 : i32.valid ((2 * (W0 : Int)) + 1) = true := hsc19
  have wv22 : i32.valid (W1 : Int) = true := (Proofs.BellmanFordExec.i32_valid_nat W1 hNW1)
  have wv23 : i32.valid (((W1 : Int) + (W2 : Int)) / 2) = true := (i32_valid_div2 _ hsc15 (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)))
  have gv_mxv : ∀ w ∈ B.mxv, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [((2 * W0 + 1), X28), ((2 * W0 + 2), X50)] b.mxv hV.v0 (by simp [wv0, wv8])
  have gl_mxv : B.mxv.length = b.mxv.length := by
    rw [hB]
    exact applySets_length [((2 * W0 + 1), X28), ((2 * W0 + 2), X50)] b.mxv
  have gv_smx : ∀ w ∈ B.smx, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [((2 * W0 + 1), X29), ((2 * W0 + 2), X51)] b.smx hV.v1 (by simp [wv1, wv9])
  have gl_smx : B.smx.length = b.smx.length := by
    rw [hB]
    exact applySets_length [((2 * W0 + 1), X29), ((2 * W0 + 2), X51)] b.smx
  have gv_mxc : ∀ w ∈ B.mxc, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [((2 * W0 + 1), X11), ((2 * W0 + 2), X33)] b.mxc hV.v2 (by simp [wv2, wv10])
  have gl_mxc : B.mxc.length = b.mxc.length := by
    rw [hB]
    exact applySets_length [((2 * W0 + 1), X11), ((2 * W0 + 2), X33)] b.mxc
  have gv_mnv : ∀ w ∈ B.mnv, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [((2 * W0 + 1), X27), ((2 * W0 + 2), X49)] b.mnv hV.v3 (by simp [wv3, wv11])
  have gl_mnv : B.mnv.length = b.mnv.length := by
    rw [hB]
    exact applySets_length [((2 * W0 + 1), X27), ((2 * W0 + 2), X49)] b.mnv
  have gv_smn : ∀ w ∈ B.smn, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [((2 * W0 + 1), X24), ((2 * W0 + 2), X46)] b.smn hV.v4 (by simp [wv4, wv12])
  have gl_smn : B.smn.length = b.smn.length := by
    rw [hB]
    exact applySets_length [((2 * W0 + 1), X24), ((2 * W0 + 2), X46)] b.smn
  have gv_mnc : ∀ w ∈ B.mnc, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [((2 * W0 + 1), X14), ((2 * W0 + 2), X36)] b.mnc hV.v5 (by simp [wv5, wv13])
  have gl_mnc : B.mnc.length = b.mnc.length := by
    rw [hB]
    exact applySets_length [((2 * W0 + 1), X14), ((2 * W0 + 2), X36)] b.mnc
  have gv_len : ∀ w ∈ B.len, s64.valid w = true := by
    rw [hB]
    exact hV.v6
  have gl_len : B.len.length = b.len.length := by
    rw [hB]
    rfl
  have gv_ladd : ∀ w ∈ B.ladd, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [((2 * W0 + 1), X19), ((2 * W0 + 2), X41), (W0, X54)] b.ladd hV.v7 (by simp [wv6, wv14, wv17])
  have gl_ladd : B.ladd.length = b.ladd.length := by
    rw [hB]
    exact applySets_length [((2 * W0 + 1), X19), ((2 * W0 + 2), X41), (W0, X54)] b.ladd
  have gv_lval : ∀ w ∈ B.lval, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [((2 * W0 + 1), X30), ((2 * W0 + 2), X52), (W0, X53)] b.lval hV.v8 (by simp [wv7, wv15, wv16])
  have gl_lval : B.lval.length = b.lval.length := by
    rw [hB]
    exact applySets_length [((2 * W0 + 1), X30), ((2 * W0 + 2), X52), (W0, X53)] b.lval
  have gv_lo : ∀ w ∈ B.lo, i32.valid w = true := by
    rw [hB]
    exact hV.v9
  have gl_lo : B.lo.length = b.lo.length := by
    rw [hB]
    rfl
  have gv_hi : ∀ w ∈ B.hi, i32.valid w = true := by
    rw [hB]
    exact hV.v10
  have gl_hi : B.hi.length = b.hi.length := by
    rw [hB]
    rfl
  have gv_sk : ∀ w ∈ B.sk, i32.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => i32.valid w = true) [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] b.sk hV.v11 (by simp [wv18, wv21])
  have gl_sk : B.sk.length = b.sk.length := by
    rw [hB]
    exact applySets_length [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] b.sk
  have gv_sl : ∀ w ∈ B.sl, i32.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => i32.valid w = true) [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] b.sl hV.v12 (by simp [wv19, wv22])
  have gl_sl : B.sl.length = b.sl.length := by
    rw [hB]
    exact applySets_length [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] b.sl
  have gv_sr : ∀ w ∈ B.sr, i32.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => i32.valid w = true) [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] b.sr hV.v13 (by simp [wv20, wv23])
  have gl_sr : B.sr.length = b.sr.length := by
    rw [hB]
    exact applySets_length [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] b.sr
  have gv_ent : ∀ w ∈ B.ent, i32.valid w = true := by
    rw [hB]
    exact hV.v14
  have gl_ent : B.ent.length = b.ent.length := by
    rw [hB]
    rfl
  have hVal : ValidOK B := ⟨gv_mxv, gv_smx, gv_mxc, gv_mnv, gv_smn, gv_mnc, gv_len, gv_ladd, gv_lval, gv_lo, gv_hi, gv_sk, gv_sl, gv_sr, gv_ent⟩
  have gl_eq : B.len = b.len := by
    rw [hB]
    rfl
  have hLen : SameLen b B := ⟨gl_mxv, gl_smx, gl_mxc, gl_mnv, gl_smn, gl_mnc, gl_len, gl_ladd, gl_lval, gl_lo, gl_hi, gl_sk, gl_sl, gl_sr, gl_ent, gl_eq⟩
  have hother : ∀ i, i ≠ W0 → i ≠ 2 * W0 + 1 → i ≠ 2 * W0 + 2 → Hof inf B i = Hof inf b i := by
    intro i hi hi1 hi2
    have hi' : ¬ W0 = i := fun h => hi h.symm
    have hi1' : ¬ 2 * W0 + 1 = i := fun h => hi1 h.symm
    have hi2' : ¬ 2 * W0 + 2 = i := fun h => hi2 h.symm
    simp only [Hof, decNd, decTag]
    simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, lastW, hi', hi1', hi2']
  have hBo : ∀ i, i ≠ 2 * W0 + 1 → i ≠ 2 * W0 + 2 → i ≠ W0 → decNd B i = decNd b i ∧ decTag inf B i = decTag inf b i :=
    fun i h1 h2 h0 => ⟨congrArg Prod.fst (hother i h0 h1 h2), congrArg Prod.snd (hother i h0 h1 h2)⟩
  have hTp : decTag inf b W0 = ({ lval := if Z5 = inf then none else some Z5, ladd := Z6 } : Tag) := by
    simp [decTag, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
  have hNp : decNd b W0 = ({ mx := Z3, smx := b.smx.getD W0 0, mc := b.mxc.getD W0 0, mn := Z4, smn := b.smn.getD W0 0, mnc := b.mnc.getD W0 0 } : Nd) := by
    simp [decNd, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
  have hintZ : b.len.getD W0 0 ≠ 1 := hint
  have hHW0 : H W0 = (decNd b W0, decTag inf b W0) := Prod.ext (hH W0).1.symm ((hH W0).2.1 hintZ).symm
  have hHW0n : (H W0).1 = ({ mx := Z3, smx := b.smx.getD W0 0, mc := b.mxc.getD W0 0, mn := Z4, smn := b.smn.getD W0 0, mnc := b.mnc.getD W0 0 } : Nd) := by rw [hHW0]; exact hNp
  have hHW0t : (H W0).2 = ({ lval := if Z5 = inf then none else some Z5, ladd := Z6 } : Tag) := by rw [hHW0]; exact hTp
  have bW0n : decNd B W0 = ({ mx := Z3, smx := b.smx.getD W0 0, mc := b.mxc.getD W0 0, mn := Z4, smn := b.smn.getD W0 0, mnc := b.mnc.getD W0 0 } : Nd) := by
    simp only [decNd]
    simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hn1, hn2, hn3, hn4, hn5, hn6, eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55]
  have bW0t : decTag inf B W0 = noTag := by
    simp only [decTag]
    simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hn1, hn2, hn3, hn4, hn5, hn6, eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, noTag]
  have bC1n : decNd B (2 * W0 + 1) = ({ mx := Z5, smx := (-inf), mc := Z15, mn := Z5, smn := inf, mnc := Z15 } : Nd) := by
    simp only [decNd]
    simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hn1, hn2, hn3, hn4, hn5, hn6, eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55]
  have bC1t : decTag inf B (2 * W0 + 1) = ({ lval := if X16 = inf then none else some X16, ladd := 0 } : Tag) := by
    simp only [decTag]
    simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hn1, hn2, hn3, hn4, hn5, hn6, eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55]
  have bC2n : decNd B (2 * W0 + 2) = ({ mx := Z5, smx := (-inf), mc := Z24, mn := Z5, smn := inf, mnc := Z24 } : Nd) := by
    simp only [decNd]
    simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hn1, hn2, hn3, hn4, hn5, hn6, eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55]
  have bC2t : decTag inf B (2 * W0 + 2) = ({ lval := if X38 = inf then none else some X38, ladd := 0 } : Tag) := by
    simp only [decTag]
    simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hn1, hn2, hn3, hn4, hn5, hn6, eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX31, eX32, eX33, eX34, eX35, eX36, eX37, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55]
  have hHR : HRel inf B (pushH H W0 (((((W1 + W2) / 2) - W1 : Nat)) : Int) ((W2 - ((W1 + W2) / 2) : Nat) : Int)) := by
    unfold pushH
    refine HRel_set3 inf b B H (2 * W0 + 1) (2 * W0 + 2) W0 _ _ _ hH (by omega) (by omega) (by omega) hBo hLen.leneq ?nd1 ?t1 ?l1 ?nd2 ?t2 ?l2 ?nd3 ?t3 ?l3
    · rw [bC1n, hHW0t, hHW0n]
      have hc1 : (H (2 * W0 + 1)).1 = ({ mx := Z7, smx := Z8, mc := Z9, mn := Z10, smn := Z11, mnc := Z12 } : Nd) := by
        rw [← (hH _).1]; simp [decNd, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
      simp [Cellh.applyTagC, hmode]
      exact set_nd_key Z15 (((((W1 + W2) / 2) - W1 : Nat)) : Int) inf Z5 hinfI hlenL
    · intro hl
      have hlZ : Z15 ≠ 1 := by rw [← hD_Z15]; exact hl
      have hHt := (hH (2 * W0 + 1)).2.1 hl
      have hcn1 : (H (2 * W0 + 1)).1 = ({ mx := Z7, smx := Z8, mc := Z9, mn := Z10, smn := Z11, mnc := Z12 } : Nd) := by
        rw [← (hH _).1]; simp [decNd, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
      have hct1 : (H (2 * W0 + 1)).2 = ({ lval := if Z14 = inf then none else some Z14, ladd := Z13 } : Tag) := by
        rw [← hHt]; simp [decTag, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
      have hHc1 : H (2 * W0 + 1) = (({ mx := Z7, smx := Z8, mc := Z9, mn := Z10, smn := Z11, mnc := Z12 } : Nd), ({ lval := if Z14 = inf then none else some Z14, ladd := Z13 } : Tag)) := Prod.ext hcn1 hct1
      rw [bC1t, hHW0t, hHW0n, hHc1]
      simp [Cellh.applyTagC, hmode]
      exact (child_set_tag Z15 Z5 Z14 Z13 X16 inf eX16 hZ7).1 hlZ
    · intro hl
      have hlZ : Z15 = 1 := by rw [← hD_Z15]; exact hl
      have hnt := (hH (2 * W0 + 1)).2.2 hl
      have hT : decTag inf b (2 * W0 + 1) = ({ lval := if Z14 = inf then none else some Z14, ladd := Z13 } : Tag) := by
        simp [decTag, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
      rw [hT] at hnt
      obtain ⟨h7, h8⟩ := (tag_noTag_iff _ _ inf).mp hnt
      rw [bC1t]
      exact (child_set_tag Z15 Z5 Z14 Z13 X16 inf eX16 hZ7).2 hlZ h7 h8
    · rw [bC2n, hHW0t, hHW0n]
      have hc2 : (H (2 * W0 + 2)).1 = ({ mx := Z16, smx := Z17, mc := Z18, mn := Z19, smn := Z20, mnc := Z21 } : Nd) := by
        rw [← (hH _).1]; simp [decNd, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
      simp [Cellh.applyTagC, hmode]
      exact set_nd_key Z24 ((W2 - ((W1 + W2) / 2) : Nat) : Int) inf Z5 hinfI hlenR
    · intro hl
      have hlZ : Z24 ≠ 1 := by rw [← hD_Z24]; exact hl
      have hHt := (hH (2 * W0 + 2)).2.1 hl
      have hcn2 : (H (2 * W0 + 2)).1 = ({ mx := Z16, smx := Z17, mc := Z18, mn := Z19, smn := Z20, mnc := Z21 } : Nd) := by
        rw [← (hH _).1]; simp [decNd, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
      have hct2 : (H (2 * W0 + 2)).2 = ({ lval := if Z23 = inf then none else some Z23, ladd := Z22 } : Tag) := by
        rw [← hHt]; simp [decTag, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
      have hHc2 : H (2 * W0 + 2) = (({ mx := Z16, smx := Z17, mc := Z18, mn := Z19, smn := Z20, mnc := Z21 } : Nd), ({ lval := if Z23 = inf then none else some Z23, ladd := Z22 } : Tag)) := Prod.ext hcn2 hct2
      rw [bC2t, hHW0t, hHW0n, hHc2]
      simp [Cellh.applyTagC, hmode]
      exact (child_set_tag Z24 Z5 Z23 Z22 X38 inf eX38 hZ7).1 hlZ
    · intro hl
      have hlZ : Z24 = 1 := by rw [← hD_Z24]; exact hl
      have hnt := (hH (2 * W0 + 2)).2.2 hl
      have hT : decTag inf b (2 * W0 + 2) = ({ lval := if Z23 = inf then none else some Z23, ladd := Z22 } : Tag) := by
        simp [decTag, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24]
      rw [hT] at hnt
      obtain ⟨h7, h8⟩ := (tag_noTag_iff _ _ inf).mp hnt
      rw [bC2t]
      exact (child_set_tag Z24 Z5 Z23 Z22 X38 inf eX38 hZ7).2 hlZ h7 h8
    · show decNd B W0 = (H W0).1
      rw [bW0n, hHW0n]
    · intro hl
      exact bW0t
    · intro hl
      exact absurd hl hintZ
  have hstk' : StkRep B (sp - 1 + 2) (⟨2 * W0 + 1, W1, ((W1 + W2) / 2)⟩ :: ⟨2 * W0 + 2, ((W1 + W2) / 2), W2⟩ :: S) :=
    StkRep_push b B sp ⟨W0, W1, W2⟩ S ⟨2 * W0 + 1, W1, ((W1 + W2) / 2)⟩ ⟨2 * W0 + 2, ((W1 + W2) / 2), W2⟩ hstk
      (fun i hi => by rw [g_sk i]; exact lastW_pair_below _ _ _ _ _ hi)
      (fun i hi => by rw [g_sl i]; exact lastW_pair_below _ _ _ _ _ hi)
      (fun i hi => by rw [g_sr i]; exact lastW_pair_below _ _ _ _ _ hi)
      ⟨by rw [g_sk (sp - 1), lastW_pair_fst]; push_cast; try rfl,
       by rw [g_sl (sp - 1), lastW_pair_fst]; push_cast; try rfl,
       by rw [g_sr (sp - 1), lastW_pair_fst]⟩
      ⟨by rw [g_sk (sp - 1 + 1), lastW_pair_snd]; push_cast; try rfl,
       by rw [g_sl (sp - 1 + 1), lastW_pair_snd],
       by rw [g_sr (sp - 1 + 1), lastW_pair_snd]; push_cast; try rfl⟩
  have hent' : EntRep B ne E := EntRep_keep b B ne E hent (fun i hi => by rw [hB]; rfl)
  have hps : gS P (pre ++ [(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, X55⟩ : Cell)]) = gS P (pre ++ [cs inf, ci n, ci op, ci qa, ci qb, cs x, ci (sp - 1 + 2)]) := by
    have h1 : (⟨i32, ((sp - 1 : Nat) : Int) + 2⟩ : Cell) = ci (sp - 1 + 2) := (ci_sp_down sp hsp).symm
    rw [eX55, eX5, h1]
  refine ⟨B, hHR, hstk', hent', hVal, hLen, fun fu => ?_⟩
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ := CalcLoop_body mv hnv pre hty hty32 b P inf n op qa qb sp x hinf hnM hopM hqaM hqbM hspM hsp hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 hl11_0 hl12_1 hl13_2 hl0_3 hl3_4 hl8_5 hl7_6 hl0_7 hl1_8 hl2_9 hl3_10 hl4_11 hl5_12 hl7_13 hl8_14 hl6_15 hl0_16 hl1_17 hl2_18 hl3_19 hl4_20 hl5_21 hl7_22 hl8_23 hl6_24 hl11_25 hl12_26 hl13_27 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc17 hsc18 hsc19 hsc20 hsc21 fu
  have a3 := pexecM_scope mv fu _ _ _ r0 h0
  have tk : (⟨r0.ps.mem.take (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell)] : List Cell))).mem.length, r0.ps.bs.take (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell)] : List Cell))).bs.length⟩ : PS) = gS P (pre ++ [(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, X55⟩ : Cell)]) := by
    rw [hp0]; exact scope_take P pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell)] : List Cell) [(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, X55⟩ : Cell)] [(⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, (((2 * W0 + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, Z10⟩ : Cell), (⟨s64, Z11⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨s64, Z13⟩ : Cell), (⟨s64, Z14⟩ : Cell), (⟨s64, Z15⟩ : Cell), (⟨s64, Z16⟩ : Cell), (⟨s64, Z17⟩ : Cell), (⟨s64, Z18⟩ : Cell), (⟨s64, Z19⟩ : Cell), (⟨s64, Z20⟩ : Cell), (⟨s64, Z21⟩ : Cell), (⟨s64, Z22⟩ : Cell), (⟨s64, Z23⟩ : Cell), (⟨s64, Z24⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨s64, X10⟩ : Cell), (⟨s64, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X14⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X16⟩ : Cell), (⟨s64, (X9 + X7)⟩ : Cell), (⟨s64, X17⟩ : Cell), (⟨s64, (X12 + X7)⟩ : Cell), (⟨s64, X18⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X20⟩ : Cell), (⟨i32, X21⟩ : Cell), (⟨s64, X22⟩ : Cell), (⟨s64, X23⟩ : Cell), (⟨s64, X24⟩ : Cell), (⟨s64, X25⟩ : Cell), (⟨i32, X26⟩ : Cell), (⟨s64, X27⟩ : Cell), (⟨s64, X28⟩ : Cell), (⟨s64, X29⟩ : Cell), (⟨s64, X30⟩ : Cell), (⟨s64, X31⟩ : Cell), (⟨s64, X32⟩ : Cell), (⟨s64, X33⟩ : Cell), (⟨s64, X34⟩ : Cell), (⟨s64, X35⟩ : Cell), (⟨s64, X36⟩ : Cell), (⟨s64, X37⟩ : Cell), (⟨s64, X38⟩ : Cell), (⟨s64, (X31 + X7)⟩ : Cell), (⟨s64, X39⟩ : Cell), (⟨s64, (X34 + X7)⟩ : Cell), (⟨s64, X40⟩ : Cell), (⟨s64, X41⟩ : Cell), (⟨s64, X42⟩ : Cell), (⟨i32, X43⟩ : Cell), (⟨s64, X44⟩ : Cell), (⟨s64, X45⟩ : Cell), (⟨s64, X46⟩ : Cell), (⟨s64, X47⟩ : Cell), (⟨i32, X48⟩ : Cell), (⟨s64, X49⟩ : Cell), (⟨s64, X50⟩ : Cell), (⟨s64, X51⟩ : Cell), (⟨s64, X52⟩ : Cell), (⟨s64, X53⟩ : Cell), (⟨s64, X54⟩ : Cell), (⟨i32, (((W1 : Int) + (W2 : Int)) / 2)⟩ : Cell)] (by rfl)
  rw [tk, hv0] at a3
  have a4 := seqM_some a3 hr0 (pexecM_skip mv fu (gS P (pre ++ [(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨i32, X55⟩ : Cell)])) (VVB (uc24 (uc23 (uc22 (uc21 (uc20 (uc19 (uc18 (uc17 (uc16 (uc15 (uc14 (uc13 (uc12 (uc11 (uc10 (uc9 (uc8 (uc7 (uc6 (uc5 (uc4 (uc3 (uc2 (uc1 b (2 * W0 + 1) X28) (2 * W0 + 1) X29) (2 * W0 + 1) X11) (2 * W0 + 1) X27) (2 * W0 + 1) X24) (2 * W0 + 1) X14) (2 * W0 + 1) X19) (2 * W0 + 1) X30) (2 * W0 + 2) X50) (2 * W0 + 2) X51) (2 * W0 + 2) X33) (2 * W0 + 2) X49) (2 * W0 + 2) X46) (2 * W0 + 2) X36) (2 * W0 + 2) X41) (2 * W0 + 2) X52) W0 X53) W0 X54) (sp - 1) ((2 * (W0 : Int)) + 2)) (sp - 1) (((W1 : Int) + (W2 : Int)) / 2)) (sp - 1) (W2 : Int)) ((sp - 1) + 1) ((2 * (W0 : Int)) + 1)) ((sp - 1) + 1) (W1 : Int)) ((sp - 1) + 1) (((W1 : Int) + (W2 : Int)) / 2))))
  rw [← hB] at a4
  refine ⟨_, a4, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact hps
  · rfl
  · simp; omega
  · simp; omega

end Proofs.BeatsRep
