import Proofs.BeatsExec_ApplyLoopFlags
import Proofs.BeatsExec_ApplyLoop
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
theorem iter_whole3 (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (b : BS) (P : List Cell)
    (inf : Int) (n op qa qb sp ne : Nat) (x : Int) (S : List Fr) (E : List Nat) (W0 W1 W2 : Nat)
    (C : IterCtx b inf n op qa qb sp ne x W0 W1 W2) (hstk : StkRep b sp (⟨W0, W1, W2⟩ :: S)) (hent : EntRep b ne E) (hnot : ¬ stopP op qa qb x (decNd b W0) W1 W2) (hwhole : wholeP op qa qb x (decNd b W0) W1 W2) (hop3 : op = 3) (hxne : x ≠ inf) (hinfI : inf = INF) (hlenW : (b.len.getD W0 0) = ((W2 - W1 : Nat) : Int)) (H : Heap) (hH : HRel inf b H) :
    ∃ (b' : BS), HRel inf b' (H.set W0 (Cellh.setC ((W2 - W1 : Nat) : Int) x (H W0))) ∧
      StkRep b' (sp - 1) S ∧ EntRep b' ne E ∧ ValidOK b' ∧ SameLen b b' ∧ ∀ fu : Nat, ∃ r : PRM, pexecM mv fu (.sequence (.scope (ApplyLoopBody (mv.nv + pre.length))) Sk) (gS P (pre ++ [cs inf, ci n, ci op, ci qa, ci qb, cs x, ci sp, ci ne])) (VVB b) = some r ∧ r.ret = none ∧ r.ps = gS P (pre ++ [cs inf, ci n, ci op, ci qa, ci qb, cs x, ci (sp - 1), ci ne]) ∧ r.vv = VVB b' ∧ r.cost ≤ 117610 ∧ r.wk ≤ 47 := by
  classical
  have vz0 : s64.valid 0 = true := by decide
  obtain ⟨hinf, hninf, hnM, hopM, hqaM, hqbM, hspM, hneM, hsp, hx, hV, hW0, hW1, hW2, hk2, hlohi, hne1, hsp2, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hlsk, hlsl, hlsr, hlent⟩ := C
  have hD_W0 : b.sk.getD (sp - 1) 0 = (W0 : Int) := by simpa using (hstk.2 0 _ rfl).1
  have hD_W1 : b.sl.getD (sp - 1) 0 = (W1 : Int) := by simpa using (hstk.2 0 _ rfl).2.1
  have hD_W2 : b.sr.getD (sp - 1) 0 = (W2 : Int) := by simpa using (hstk.2 0 _ rfl).2.2
  have hl11_0 : (sp - 1) < (b.sk).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl12_1 : (sp - 1) < (b.sl).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl13_2 : (sp - 1) < (b.sr).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl0_3 : W0 < (b.mxv).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl1_4 : W0 < (b.smx).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl3_5 : W0 < (b.mnv).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl4_6 : W0 < (b.smn).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl8_7 : W0 < (b.lval).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl7_8 : W0 < (b.ladd).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl6_9 : W0 < (b.len).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl2_10 : W0 < (b.mxc).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl5_11 : W0 < (b.mnc).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl0_12 : (2 * W0 + 1) < (b.mxv).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl1_13 : (2 * W0 + 1) < (b.smx).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl2_14 : (2 * W0 + 1) < (b.mxc).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl3_15 : (2 * W0 + 1) < (b.mnv).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl4_16 : (2 * W0 + 1) < (b.smn).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl5_17 : (2 * W0 + 1) < (b.mnc).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl7_18 : (2 * W0 + 1) < (b.ladd).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl8_19 : (2 * W0 + 1) < (b.lval).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl6_20 : (2 * W0 + 1) < (b.len).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl0_21 : (2 * W0 + 2) < (b.mxv).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl1_22 : (2 * W0 + 2) < (b.smx).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl2_23 : (2 * W0 + 2) < (b.mxc).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl3_24 : (2 * W0 + 2) < (b.mnv).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl4_25 : (2 * W0 + 2) < (b.smn).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl5_26 : (2 * W0 + 2) < (b.mnc).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl7_27 : (2 * W0 + 2) < (b.ladd).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl8_28 : (2 * W0 + 2) < (b.lval).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl6_29 : (2 * W0 + 2) < (b.len).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl14_30 : ne < (b.ent).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl11_31 : ((sp - 1) + 1) < (b.sk).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl12_32 : ((sp - 1) + 1) < (b.sl).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hl13_33 : ((sp - 1) + 1) < (b.sr).length := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hk1_W0 : (2 * W0 + 1) < M31 := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hk2_W0 : (2 * W0 + 2) < M31 := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hix2 : ((sp - 1) + 1) < M31 := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hix3 : ((sp - 1) + 1) < M31 := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hix4 : ((sp - 1) + 1) < M31 := by clear hnot hwhole hop3 hxne hinfI hlenW hH; omega
  have hNW0 : W0 < M31 := hW0
  have hNW1 : W1 < M31 := hW1
  have hNW2 : W2 < M31 := hW2
  generalize hD_Z3 : b.mxv.getD W0 0 = Z3 at *
  generalize hD_Z4 : b.smx.getD W0 0 = Z4 at *
  generalize hD_Z5 : b.mnv.getD W0 0 = Z5 at *
  generalize hD_Z6 : b.smn.getD W0 0 = Z6 at *
  generalize hD_Z7 : b.lval.getD W0 0 = Z7 at *
  generalize hD_Z8 : b.ladd.getD W0 0 = Z8 at *
  generalize hD_Z9 : b.len.getD W0 0 = Z9 at *
  generalize hD_Z10 : b.mxc.getD W0 0 = Z10 at *
  generalize hD_Z11 : b.mnc.getD W0 0 = Z11 at *
  generalize hD_Z12 : b.mxv.getD (2 * W0 + 1) 0 = Z12 at *
  generalize hD_Z13 : b.smx.getD (2 * W0 + 1) 0 = Z13 at *
  generalize hD_Z14 : b.mxc.getD (2 * W0 + 1) 0 = Z14 at *
  generalize hD_Z15 : b.mnv.getD (2 * W0 + 1) 0 = Z15 at *
  generalize hD_Z16 : b.smn.getD (2 * W0 + 1) 0 = Z16 at *
  generalize hD_Z17 : b.mnc.getD (2 * W0 + 1) 0 = Z17 at *
  generalize hD_Z18 : b.ladd.getD (2 * W0 + 1) 0 = Z18 at *
  generalize hD_Z19 : b.lval.getD (2 * W0 + 1) 0 = Z19 at *
  generalize hD_Z20 : b.len.getD (2 * W0 + 1) 0 = Z20 at *
  generalize hD_Z21 : b.mxv.getD (2 * W0 + 2) 0 = Z21 at *
  generalize hD_Z22 : b.smx.getD (2 * W0 + 2) 0 = Z22 at *
  generalize hD_Z23 : b.mxc.getD (2 * W0 + 2) 0 = Z23 at *
  generalize hD_Z24 : b.mnv.getD (2 * W0 + 2) 0 = Z24 at *
  generalize hD_Z25 : b.smn.getD (2 * W0 + 2) 0 = Z25 at *
  generalize hD_Z26 : b.mnc.getD (2 * W0 + 2) 0 = Z26 at *
  generalize hD_Z27 : b.ladd.getD (2 * W0 + 2) 0 = Z27 at *
  generalize hD_Z28 : b.lval.getD (2 * W0 + 2) 0 = Z28 at *
  generalize hD_Z29 : b.len.getD (2 * W0 + 2) 0 = Z29 at *
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
  have hvl14 : ∀ w ∈ b.ent, i32.valid w = true := hV.v14
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
  obtain ⟨X0, hX0⟩ : ∃ v : Int, v = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ v : Int, v = (if (((op : Int) = 0) ∧ (Z3 ≤ x)) then 1 else X0) := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ v : Int, v = (if (((op : Int) = 1) ∧ (x ≤ Z5)) then 1 else X1) := ⟨_, rfl⟩
  obtain ⟨X3, hX3⟩ : ∃ v : Int, v = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X4, hX4⟩ : ∃ v : Int, v = (if (((op : Int) = 0) ∧ (x ≤ Z4)) then 0 else 1) := ⟨_, rfl⟩
  obtain ⟨X5, hX5⟩ : ∃ v : Int, v = (if (((op : Int) = 1) ∧ (Z6 ≤ x)) then 0 else X4) := ⟨_, rfl⟩
  obtain ⟨X6, hX6⟩ : ∃ v : Int, v = (if (((X2 = 0) ∧ (X3 = 1)) ∧ (X5 = 1)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X7, hX7⟩ : ∃ v : Int, v = (if ((X2 = 0) ∧ (X6 = 0)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X8, hX8⟩ : ∃ v : Int, v = (if ((X6 = 1) ∧ ((op : Int) = 0)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X9, hX9⟩ : ∃ v : Int, v = (if ((X6 = 1) ∧ ((op : Int) = 1)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X10, hX10⟩ : ∃ v : Int, v = (if ((X6 = 1) ∧ ((op : Int) = 2)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X11, hX11⟩ : ∃ v : Int, v = (if ((X6 = 1) ∧ ((op : Int) = 3)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X12, hX12⟩ : ∃ v : Int, v = (if (X10 = 1) then x else 0) := ⟨_, rfl⟩
  obtain ⟨X13, hX13⟩ : ∃ v : Int, v = (if (X8 = 1) then x else Z3) := ⟨_, rfl⟩
  obtain ⟨X14, hX14⟩ : ∃ v : Int, v = (if ((X8 = 1) ∧ (Z3 = Z5)) then x else Z5) := ⟨_, rfl⟩
  obtain ⟨X15, hX15⟩ : ∃ v : Int, v = (if (((X8 = 1) ∧ (Z3 ≠ Z5)) ∧ (Z3 = Z6)) then x else Z6) := ⟨_, rfl⟩
  obtain ⟨X16, hX16⟩ : ∃ v : Int, v = (if (((X8 = 1) ∧ (Z7 ≠ inf)) ∧ (x < Z7)) then x else Z7) := ⟨_, rfl⟩
  obtain ⟨X17, hX17⟩ : ∃ v : Int, v = (if (X9 = 1) then x else X14) := ⟨_, rfl⟩
  obtain ⟨X18, hX18⟩ : ∃ v : Int, v = (if ((X9 = 1) ∧ (X13 = X14)) then x else X13) := ⟨_, rfl⟩
  obtain ⟨X19, hX19⟩ : ∃ v : Int, v = (if (((X9 = 1) ∧ (X13 ≠ X14)) ∧ (Z4 = X14)) then x else Z4) := ⟨_, rfl⟩
  obtain ⟨X20, hX20⟩ : ∃ v : Int, v = (if (((X9 = 1) ∧ (X16 ≠ inf)) ∧ (X16 < x)) then x else X16) := ⟨_, rfl⟩
  obtain ⟨X21, hX21⟩ : ∃ v : Int, v = (if (X19 ≠ (-inf)) then (X19 + X12) else X19) := ⟨_, rfl⟩
  obtain ⟨X22, hX22⟩ : ∃ v : Int, v = (if (X15 ≠ inf) then (X15 + X12) else X15) := ⟨_, rfl⟩
  obtain ⟨X23, hX23⟩ : ∃ v : Int, v = (if ((X20 = inf) ∧ (Z9 ≠ 1)) then (Z8 + X12) else Z8) := ⟨_, rfl⟩
  obtain ⟨X24, hX24⟩ : ∃ v : Int, v = (if ((X20 ≠ inf) ∧ (Z9 ≠ 1)) then (X20 + X12) else X20) := ⟨_, rfl⟩
  obtain ⟨X25, hX25⟩ : ∃ v : Int, v = (if (X11 = 1) then x else (X18 + X12)) := ⟨_, rfl⟩
  obtain ⟨X26, hX26⟩ : ∃ v : Int, v = (if (X11 = 1) then (-inf) else X21) := ⟨_, rfl⟩
  obtain ⟨X27, hX27⟩ : ∃ v : Int, v = (if (X11 = 1) then x else (X17 + X12)) := ⟨_, rfl⟩
  obtain ⟨X28, hX28⟩ : ∃ v : Int, v = (if (X11 = 1) then inf else X22) := ⟨_, rfl⟩
  obtain ⟨X29, hX29⟩ : ∃ v : Int, v = (if (X11 = 1) then Z9 else Z10) := ⟨_, rfl⟩
  obtain ⟨X30, hX30⟩ : ∃ v : Int, v = (if (X11 = 1) then Z9 else Z11) := ⟨_, rfl⟩
  obtain ⟨X31, hX31⟩ : ∃ v : Int, v = (if ((X11 = 1) ∧ (Z9 ≠ 1)) then x else X24) := ⟨_, rfl⟩
  obtain ⟨X32, hX32⟩ : ∃ v : Int, v = (if ((X11 = 1) ∧ (Z9 ≠ 1)) then 0 else X23) := ⟨_, rfl⟩
  obtain ⟨X33, hX33⟩ : ∃ v : Int, v = (if ((X7 = 1) ∧ (X31 ≠ inf)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X34, hX34⟩ : ∃ v : Int, v = (if ((X7 = 1) ∧ (X33 = 0)) then X32 else 0) := ⟨_, rfl⟩
  obtain ⟨X35, hX35⟩ : ∃ v : Int, v = (if ((X7 = 1) ∧ (X33 = 0)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X36, hX36⟩ : ∃ v : Int, v = (if (X33 = 1) then X31 else Z12) := ⟨_, rfl⟩
  obtain ⟨X37, hX37⟩ : ∃ v : Int, v = (if (X33 = 1) then (-inf) else Z13) := ⟨_, rfl⟩
  obtain ⟨X38, hX38⟩ : ∃ v : Int, v = (if (X33 = 1) then Z20 else Z14) := ⟨_, rfl⟩
  obtain ⟨X39, hX39⟩ : ∃ v : Int, v = (if (X33 = 1) then X31 else Z15) := ⟨_, rfl⟩
  obtain ⟨X40, hX40⟩ : ∃ v : Int, v = (if (X33 = 1) then inf else Z16) := ⟨_, rfl⟩
  obtain ⟨X41, hX41⟩ : ∃ v : Int, v = (if (X33 = 1) then Z20 else Z17) := ⟨_, rfl⟩
  obtain ⟨X42, hX42⟩ : ∃ v : Int, v = (if (X33 = 1) then 0 else Z18) := ⟨_, rfl⟩
  obtain ⟨X43, hX43⟩ : ∃ v : Int, v = (if ((X33 = 1) ∧ (Z20 ≠ 1)) then X31 else Z19) := ⟨_, rfl⟩
  obtain ⟨X44, hX44⟩ : ∃ v : Int, v = (if (X37 ≠ (-inf)) then (X37 + X34) else X37) := ⟨_, rfl⟩
  obtain ⟨X45, hX45⟩ : ∃ v : Int, v = (if (X40 ≠ inf) then (X40 + X34) else X40) := ⟨_, rfl⟩
  obtain ⟨X46, hX46⟩ : ∃ v : Int, v = (if ((X43 = inf) ∧ (Z20 ≠ 1)) then (X42 + X34) else X42) := ⟨_, rfl⟩
  obtain ⟨X47, hX47⟩ : ∃ v : Int, v = (if (X43 ≠ inf) then (X43 + X34) else X43) := ⟨_, rfl⟩
  obtain ⟨X48, hX48⟩ : ∃ v : Int, v = (if ((X35 = 1) ∧ (X25 < (X36 + X34))) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X49, hX49⟩ : ∃ v : Int, v = (if (X48 = 1) then X25 else (X36 + X34)) := ⟨_, rfl⟩
  obtain ⟨X50, hX50⟩ : ∃ v : Int, v = (if ((X48 = 1) ∧ ((X36 + X34) = (X39 + X34))) then X25 else (X39 + X34)) := ⟨_, rfl⟩
  obtain ⟨X51, hX51⟩ : ∃ v : Int, v = (if (((X48 = 1) ∧ ((X36 + X34) ≠ (X39 + X34))) ∧ ((X36 + X34) = X45)) then X25 else X45) := ⟨_, rfl⟩
  obtain ⟨X52, hX52⟩ : ∃ v : Int, v = (if (((X48 = 1) ∧ (X47 ≠ inf)) ∧ (X25 < X47)) then X25 else X47) := ⟨_, rfl⟩
  obtain ⟨X53, hX53⟩ : ∃ v : Int, v = (if ((X35 = 1) ∧ (X50 < X27)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X54, hX54⟩ : ∃ v : Int, v = (if (X53 = 1) then X27 else X50) := ⟨_, rfl⟩
  obtain ⟨X55, hX55⟩ : ∃ v : Int, v = (if ((X53 = 1) ∧ (X49 = X50)) then X27 else X49) := ⟨_, rfl⟩
  obtain ⟨X56, hX56⟩ : ∃ v : Int, v = (if (((X53 = 1) ∧ (X49 ≠ X50)) ∧ (X44 = X50)) then X27 else X44) := ⟨_, rfl⟩
  obtain ⟨X57, hX57⟩ : ∃ v : Int, v = (if (((X53 = 1) ∧ (X52 ≠ inf)) ∧ (X52 < X27)) then X27 else X52) := ⟨_, rfl⟩
  obtain ⟨X58, hX58⟩ : ∃ v : Int, v = (if (X33 = 1) then X31 else Z21) := ⟨_, rfl⟩
  obtain ⟨X59, hX59⟩ : ∃ v : Int, v = (if (X33 = 1) then (-inf) else Z22) := ⟨_, rfl⟩
  obtain ⟨X60, hX60⟩ : ∃ v : Int, v = (if (X33 = 1) then Z29 else Z23) := ⟨_, rfl⟩
  obtain ⟨X61, hX61⟩ : ∃ v : Int, v = (if (X33 = 1) then X31 else Z24) := ⟨_, rfl⟩
  obtain ⟨X62, hX62⟩ : ∃ v : Int, v = (if (X33 = 1) then inf else Z25) := ⟨_, rfl⟩
  obtain ⟨X63, hX63⟩ : ∃ v : Int, v = (if (X33 = 1) then Z29 else Z26) := ⟨_, rfl⟩
  obtain ⟨X64, hX64⟩ : ∃ v : Int, v = (if (X33 = 1) then 0 else Z27) := ⟨_, rfl⟩
  obtain ⟨X65, hX65⟩ : ∃ v : Int, v = (if ((X33 = 1) ∧ (Z29 ≠ 1)) then X31 else Z28) := ⟨_, rfl⟩
  obtain ⟨X66, hX66⟩ : ∃ v : Int, v = (if (X59 ≠ (-inf)) then (X59 + X34) else X59) := ⟨_, rfl⟩
  obtain ⟨X67, hX67⟩ : ∃ v : Int, v = (if (X62 ≠ inf) then (X62 + X34) else X62) := ⟨_, rfl⟩
  obtain ⟨X68, hX68⟩ : ∃ v : Int, v = (if ((X65 = inf) ∧ (Z29 ≠ 1)) then (X64 + X34) else X64) := ⟨_, rfl⟩
  obtain ⟨X69, hX69⟩ : ∃ v : Int, v = (if (X65 ≠ inf) then (X65 + X34) else X65) := ⟨_, rfl⟩
  obtain ⟨X70, hX70⟩ : ∃ v : Int, v = (if ((X35 = 1) ∧ (X25 < (X58 + X34))) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X71, hX71⟩ : ∃ v : Int, v = (if (X70 = 1) then X25 else (X58 + X34)) := ⟨_, rfl⟩
  obtain ⟨X72, hX72⟩ : ∃ v : Int, v = (if ((X70 = 1) ∧ ((X58 + X34) = (X61 + X34))) then X25 else (X61 + X34)) := ⟨_, rfl⟩
  obtain ⟨X73, hX73⟩ : ∃ v : Int, v = (if (((X70 = 1) ∧ ((X58 + X34) ≠ (X61 + X34))) ∧ ((X58 + X34) = X67)) then X25 else X67) := ⟨_, rfl⟩
  obtain ⟨X74, hX74⟩ : ∃ v : Int, v = (if (((X70 = 1) ∧ (X69 ≠ inf)) ∧ (X25 < X69)) then X25 else X69) := ⟨_, rfl⟩
  obtain ⟨X75, hX75⟩ : ∃ v : Int, v = (if ((X35 = 1) ∧ (X72 < X27)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X76, hX76⟩ : ∃ v : Int, v = (if (X75 = 1) then X27 else X72) := ⟨_, rfl⟩
  obtain ⟨X77, hX77⟩ : ∃ v : Int, v = (if ((X75 = 1) ∧ (X71 = X72)) then X27 else X71) := ⟨_, rfl⟩
  obtain ⟨X78, hX78⟩ : ∃ v : Int, v = (if (((X75 = 1) ∧ (X71 ≠ X72)) ∧ (X66 = X72)) then X27 else X66) := ⟨_, rfl⟩
  obtain ⟨X79, hX79⟩ : ∃ v : Int, v = (if (((X75 = 1) ∧ (X74 ≠ inf)) ∧ (X74 < X27)) then X27 else X74) := ⟨_, rfl⟩
  obtain ⟨X80, hX80⟩ : ∃ v : Int, v = (if (X7 = 1) then inf else X31) := ⟨_, rfl⟩
  obtain ⟨X81, hX81⟩ : ∃ v : Int, v = (if (X7 = 1) then 0 else X32) := ⟨_, rfl⟩
  obtain ⟨X82, hX82⟩ : ∃ v : Int, v = ((ne : Int) + X7) := ⟨_, rfl⟩
  obtain ⟨X83, hX83⟩ : ∃ v : Int, v = (((sp - 1 : Nat) : Int) + (2 * X7)) := ⟨_, rfl⟩
  have hndZ : (decNd b W0).mx = Z3 ∧ (decNd b W0).smx = Z4 ∧ (decNd b W0).mn = Z5 ∧ (decNd b W0).smn = Z6 := ⟨hD_Z3, hD_Z4, hD_Z5, hD_Z6⟩
  have hopc : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  have hop4 : op < 4 := by omega
  have hndS : ¬ stopP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 := by
    obtain ⟨h1, h2, h3, h4⟩ := hndZ
    unfold stopP at hnot ⊢
    rw [h1, h3] at hnot
    exact hnot
  have hndW : wholeP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 := by
    obtain ⟨h1, h2, h3, h4⟩ := hndZ
    unfold wholeP at hwhole ⊢
    rw [h2, h4] at hwhole
    exact hwhole
  have hflags := cls_flags3 W1 W2 op qa qb Z3 Z4 Z5 Z6 x X0 X1 X2 X3 X4 X5 X6 hX0 hX1 hX2 hX3 hX4 hX5 hX6 hop3
  have eX2 : X2 = 0 := by rw [hflags.1]; simp [hndS]
  have eX6 : X6 = 1 := by rw [hflags.2]; simp [hndS, hndW]
  have eX0 : X0 = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0) := by rw [hX0]; try simp [hop3]
  have eX1 : X1 = X0 := by rw [hX1]; try simp [hop3]
  have eX3 : X3 = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0) := by rw [hX3]; try simp [hop3]
  have eX4 : X4 = 1 := by rw [hX4]; try simp [hop3]
  have eX5 : X5 = 1 := by rw [hX5]; try simp [hop3, eX4]
  have eX7 : X7 = 0 := by rw [hX7]; try simp [hop3, eX2, eX6]
  have eX8 : X8 = 0 := by rw [hX8]; try simp [hop3, eX6]
  have eX9 : X9 = 0 := by rw [hX9]; try simp [hop3, eX6]
  have eX10 : X10 = 0 := by rw [hX10]; try simp [hop3, eX6]
  have eX11 : X11 = 1 := by rw [hX11]; try simp [hop3, eX6]
  have eX12 : X12 = 0 := by rw [hX12]; try simp [hop3, eX10]
  have eX13 : X13 = Z3 := by rw [hX13]; try simp [hop3, eX8]
  have eX14 : X14 = Z5 := by rw [hX14]; try simp [hop3, eX8]
  have eX15 : X15 = Z6 := by rw [hX15]; try simp [hop3, eX8]
  have eX16 : X16 = Z7 := by rw [hX16]; try simp [hop3, eX8]
  have eX17 : X17 = Z5 := by rw [hX17]; try simp [hop3, eX9, eX14]
  have eX18 : X18 = Z3 := by rw [hX18]; try simp [hop3, eX9, eX13, eX14]
  have eX19 : X19 = Z4 := by rw [hX19]; try simp [hop3, eX9, eX13, eX14]
  have eX20 : X20 = Z7 := by rw [hX20]; try simp [hop3, eX9, eX16]
  have eX21 : X21 = Z4 := by rw [hX21]; try simp [hop3, eX12, eX19]
  have eX22 : X22 = Z6 := by rw [hX22]; try simp [hop3, eX12, eX15]
  have eX23 : X23 = Z8 := by rw [hX23]; try simp [hop3, eX12, eX20]
  have eX24 : X24 = Z7 := by rw [hX24]; try simp [hop3, eX12, eX20]
  have eX25 : X25 = x := by rw [hX25]; try simp [hop3, eX11, eX12, eX18]
  have eX26 : X26 = (-inf) := by rw [hX26]; try simp [hop3, eX11, eX21]
  have eX27 : X27 = x := by rw [hX27]; try simp [hop3, eX11, eX12, eX17]
  have eX28 : X28 = inf := by rw [hX28]; try simp [hop3, eX11, eX22]
  have eX29 : X29 = Z9 := by rw [hX29]; try simp [hop3, eX11]
  have eX30 : X30 = Z9 := by rw [hX30]; try simp [hop3, eX11]
  have eX31 : X31 = (if (Z9 ≠ 1) then x else Z7) := by rw [hX31]; try simp [hop3, eX11, eX24]
  have eX32 : X32 = (if (Z9 ≠ 1) then 0 else Z8) := by rw [hX32]; try simp [hop3, eX11, eX23]
  have eX33 : X33 = 0 := by rw [hX33]; try simp [hop3, eX7]
  have eX34 : X34 = 0 := by rw [hX34]; try simp [hop3, eX7, eX33]
  have eX35 : X35 = 0 := by rw [hX35]; try simp [hop3, eX7, eX33]
  have eX36 : X36 = Z12 := by rw [hX36]; try simp [hop3, eX33]
  have eX37 : X37 = Z13 := by rw [hX37]; try simp [hop3, eX33]
  have eX38 : X38 = Z14 := by rw [hX38]; try simp [hop3, eX33]
  have eX39 : X39 = Z15 := by rw [hX39]; try simp [hop3, eX33]
  have eX40 : X40 = Z16 := by rw [hX40]; try simp [hop3, eX33]
  have eX41 : X41 = Z17 := by rw [hX41]; try simp [hop3, eX33]
  have eX42 : X42 = Z18 := by rw [hX42]; try simp [hop3, eX33]
  have eX43 : X43 = Z19 := by rw [hX43]; try simp [hop3, eX33]
  have eX44 : X44 = Z13 := by rw [hX44]; try simp [hop3, eX34, eX37]
  have eX45 : X45 = Z16 := by rw [hX45]; try simp [hop3, eX34, eX40]
  have eX46 : X46 = Z18 := by rw [hX46]; try simp [hop3, eX34, eX42, eX43]
  have eX47 : X47 = Z19 := by rw [hX47]; try simp [hop3, eX34, eX43]
  have eX48 : X48 = 0 := by rw [hX48]; try simp [hop3, eX25, eX34, eX35, eX36]
  have eX49 : X49 = Z12 := by rw [hX49]; try simp [hop3, eX25, eX34, eX36, eX48]
  have eX50 : X50 = Z15 := by rw [hX50]; try simp [hop3, eX25, eX34, eX36, eX39, eX48]
  have eX51 : X51 = Z16 := by rw [hX51]; try simp [hop3, eX25, eX34, eX36, eX39, eX45, eX48]
  have eX52 : X52 = Z19 := by rw [hX52]; try simp [hop3, eX25, eX47, eX48]
  have eX53 : X53 = 0 := by rw [hX53]; try simp [hop3, eX27, eX35, eX50]
  have eX54 : X54 = Z15 := by rw [hX54]; try simp [hop3, eX27, eX50, eX53]
  have eX55 : X55 = Z12 := by rw [hX55]; try simp [hop3, eX27, eX49, eX50, eX53]
  have eX56 : X56 = Z13 := by rw [hX56]; try simp [hop3, eX27, eX44, eX49, eX50, eX53]
  have eX57 : X57 = Z19 := by rw [hX57]; try simp [hop3, eX27, eX52, eX53]
  have eX58 : X58 = Z21 := by rw [hX58]; try simp [hop3, eX33]
  have eX59 : X59 = Z22 := by rw [hX59]; try simp [hop3, eX33]
  have eX60 : X60 = Z23 := by rw [hX60]; try simp [hop3, eX33]
  have eX61 : X61 = Z24 := by rw [hX61]; try simp [hop3, eX33]
  have eX62 : X62 = Z25 := by rw [hX62]; try simp [hop3, eX33]
  have eX63 : X63 = Z26 := by rw [hX63]; try simp [hop3, eX33]
  have eX64 : X64 = Z27 := by rw [hX64]; try simp [hop3, eX33]
  have eX65 : X65 = Z28 := by rw [hX65]; try simp [hop3, eX33]
  have eX66 : X66 = Z22 := by rw [hX66]; try simp [hop3, eX34, eX59]
  have eX67 : X67 = Z25 := by rw [hX67]; try simp [hop3, eX34, eX62]
  have eX68 : X68 = Z27 := by rw [hX68]; try simp [hop3, eX34, eX64, eX65]
  have eX69 : X69 = Z28 := by rw [hX69]; try simp [hop3, eX34, eX65]
  have eX70 : X70 = 0 := by rw [hX70]; try simp [hop3, eX25, eX34, eX35, eX58]
  have eX71 : X71 = Z21 := by rw [hX71]; try simp [hop3, eX25, eX34, eX58, eX70]
  have eX72 : X72 = Z24 := by rw [hX72]; try simp [hop3, eX25, eX34, eX58, eX61, eX70]
  have eX73 : X73 = Z25 := by rw [hX73]; try simp [hop3, eX25, eX34, eX58, eX61, eX67, eX70]
  have eX74 : X74 = Z28 := by rw [hX74]; try simp [hop3, eX25, eX69, eX70]
  have eX75 : X75 = 0 := by rw [hX75]; try simp [hop3, eX27, eX35, eX72]
  have eX76 : X76 = Z24 := by rw [hX76]; try simp [hop3, eX27, eX72, eX75]
  have eX77 : X77 = Z21 := by rw [hX77]; try simp [hop3, eX27, eX71, eX72, eX75]
  have eX78 : X78 = Z22 := by rw [hX78]; try simp [hop3, eX27, eX66, eX71, eX72, eX75]
  have eX79 : X79 = Z28 := by rw [hX79]; try simp [hop3, eX27, eX74, eX75]
  have eX80 : X80 = X31 := by rw [hX80]; try simp [hop3, eX7]
  have eX81 : X81 = X32 := by rw [hX81]; try simp [hop3, eX7]
  have eX82 : X82 = (ne : Int) := by rw [hX82]; try simp [hop3, eX7]
  have eX83 : X83 = ((sp - 1 : Nat) : Int) := by rw [hX83]; try simp [hop3, eX7]
  have hsc0 : i32.valid ((sp : Int) - 1) = true := (by rw [sub_one_cast sp hsp]; exact Proofs.BellmanFordExec.i32_valid_nat _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hspM))
  have hsc2 : s64.valid (-inf) = true := by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, hx, hx, hinf, hninf]
  have hsc23 : i32.valid ((W1 : Int) + (W2 : Int)) = true := (by have := Proofs.BellmanFordExec.i32_valid_nat (W1 + W2) hlohi; simpa using this)
  have hsc25 : i32.valid (2 * (W0 : Int)) = true := (by have := Proofs.BellmanFordExec.i32_valid_nat (2 * W0) (Nat.lt_of_le_of_lt (by omega) hk2_W0); simpa using this)
  have hsc26 : i32.valid ((2 * (W0 : Int)) + 2) = true := (by have := Proofs.BellmanFordExec.i32_valid_nat (2 * W0 + 2) hk2_W0; simpa using this)
  have hsc27 : i32.valid ((2 * (W0 : Int)) + 1) = true := (by have := Proofs.BellmanFordExec.i32_valid_nat (2 * W0 + 1) hk1_W0; simpa using this)
  have vX0 : i32.valid X0 = true := by
    rw [hX0]
    by_cases hC : (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX3 : i32.valid X3 = true := by
    rw [hX3]
    by_cases hC : (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int)))
    · rw [if_pos hC]; exact (by decide)
    · rw [if_neg hC]; exact (by decide)
  have vX4 : i32.valid X4 = true := by rw [eX4]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX5 : i32.valid X5 = true := by rw [eX5]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX7 : i32.valid X7 = true := by rw [eX7]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc22 : i32.valid ((ne : Int) + X7) = true := (by rw [eX7]; simpa using Proofs.BellmanFordExec.i32_valid_nat ne hneM)
  have hsc28 : i32.valid (2 * X7) = true := (by rw [eX7]; decide)
  have hsc29 : i32.valid (((sp - 1 : Nat) : Int) + (2 * X7)) = true := (by rw [eX7]; simpa using Proofs.BellmanFordExec.i32_valid_nat (sp - 1) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hspM))
  have vX8 : i32.valid X8 = true := by rw [eX8]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX9 : i32.valid X9 = true := by rw [eX9]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX10 : i32.valid X10 = true := by rw [eX10]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX11 : i32.valid X11 = true := by rw [eX11]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc8 : ((X11 = 1)) → s64.valid (-inf) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf]
  have vX12 : s64.valid X12 = true := by rw [eX12]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX13 : s64.valid X13 = true := by rw [eX13]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX14 : s64.valid X14 = true := by rw [eX14]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX15 : s64.valid X15 = true := by rw [eX15]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc5 : ((X15 ≠ inf)) → s64.valid (X15 + X12) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf]
  have vX16 : s64.valid X16 = true := by rw [eX16]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX17 : s64.valid X17 = true := by rw [eX17]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc4 : s64.valid (X17 + X12) = true := by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf]
  have vX18 : s64.valid X18 = true := by rw [eX18]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc1 : s64.valid (X18 + X12) = true := by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf]
  have vX19 : s64.valid X19 = true := by rw [eX19]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc3 : ((X19 ≠ (-inf))) → s64.valid (X19 + X12) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf]
  have vX20 : s64.valid X20 = true := by rw [eX20]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc6 : (((X20 = inf) ∧ (Z9 ≠ 1))) → s64.valid (Z8 + X12) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf]
  have hsc7 : (((X20 ≠ inf) ∧ (Z9 ≠ 1))) → s64.valid (X20 + X12) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf]
  have vX21 : s64.valid X21 = true := by rw [eX21]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX22 : s64.valid X22 = true := by rw [eX22]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX23 : s64.valid X23 = true := by rw [eX23]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX24 : s64.valid X24 = true := by rw [eX24]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX25 : s64.valid X25 = true := by rw [eX25]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX26 : s64.valid X26 = true := by rw [eX26]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX27 : s64.valid X27 = true := by rw [eX27]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX28 : s64.valid X28 = true := by rw [eX28]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX29 : s64.valid X29 = true := by rw [eX29]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX30 : s64.valid X30 = true := by rw [eX30]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
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
  have vX33 : i32.valid X33 = true := by rw [eX33]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc9 : ((X33 = 1)) → s64.valid (-inf) = true := fun hC => by exfalso; revert hC; simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83]
  have vX34 : s64.valid X34 = true := by rw [eX34]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX35 : i32.valid X35 = true := by rw [eX35]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX36 : s64.valid X36 = true := by rw [eX36]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc10 : s64.valid (X36 + X34) = true := by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX37 : s64.valid X37 = true := by rw [eX37]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc11 : ((X37 ≠ (-inf))) → s64.valid (X37 + X34) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX38 : s64.valid X38 = true := by rw [eX38]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX39 : s64.valid X39 = true := by rw [eX39]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc12 : s64.valid (X39 + X34) = true := by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX40 : s64.valid X40 = true := by rw [eX40]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc13 : ((X40 ≠ inf)) → s64.valid (X40 + X34) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX41 : s64.valid X41 = true := by rw [eX41]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX42 : s64.valid X42 = true := by rw [eX42]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX43 : s64.valid X43 = true := by rw [eX43]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc14 : (((X43 = inf) ∧ (Z20 ≠ 1))) → s64.valid (X42 + X34) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have hsc15 : ((X43 ≠ inf)) → s64.valid (X43 + X34) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX44 : s64.valid X44 = true := by rw [eX44]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX45 : s64.valid X45 = true := by rw [eX45]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX46 : s64.valid X46 = true := by rw [eX46]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX47 : s64.valid X47 = true := by rw [eX47]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX48 : i32.valid X48 = true := by rw [eX48]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX49 : s64.valid X49 = true := by rw [eX49]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX50 : s64.valid X50 = true := by rw [eX50]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX51 : s64.valid X51 = true := by rw [eX51]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX52 : s64.valid X52 = true := by rw [eX52]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX53 : i32.valid X53 = true := by rw [eX53]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX54 : s64.valid X54 = true := by rw [eX54]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX55 : s64.valid X55 = true := by rw [eX55]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX56 : s64.valid X56 = true := by rw [eX56]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX57 : s64.valid X57 = true := by rw [eX57]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX58 : s64.valid X58 = true := by rw [eX58]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc16 : s64.valid (X58 + X34) = true := by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX59 : s64.valid X59 = true := by rw [eX59]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc17 : ((X59 ≠ (-inf))) → s64.valid (X59 + X34) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX60 : s64.valid X60 = true := by rw [eX60]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX61 : s64.valid X61 = true := by rw [eX61]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc18 : s64.valid (X61 + X34) = true := by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX62 : s64.valid X62 = true := by rw [eX62]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc19 : ((X62 ≠ inf)) → s64.valid (X62 + X34) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX63 : s64.valid X63 = true := by rw [eX63]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX64 : s64.valid X64 = true := by rw [eX64]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX65 : s64.valid X65 = true := by rw [eX65]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hsc20 : (((X65 = inf) ∧ (Z29 ≠ 1))) → s64.valid (X64 + X34) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have hsc21 : ((X65 ≠ inf)) → s64.valid (X65 + X34) = true := fun hC => by simp [eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83, vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf]
  have vX66 : s64.valid X66 = true := by rw [eX66]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX67 : s64.valid X67 = true := by rw [eX67]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX68 : s64.valid X68 = true := by rw [eX68]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX69 : s64.valid X69 = true := by rw [eX69]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX70 : i32.valid X70 = true := by rw [eX70]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX71 : s64.valid X71 = true := by rw [eX71]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX72 : s64.valid X72 = true := by rw [eX72]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX73 : s64.valid X73 = true := by rw [eX73]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX74 : s64.valid X74 = true := by rw [eX74]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX75 : i32.valid X75 = true := by rw [eX75]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX76 : s64.valid X76 = true := by rw [eX76]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX77 : s64.valid X77 = true := by rw [eX77]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX78 : s64.valid X78 = true := by rw [eX78]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX79 : s64.valid X79 = true := by rw [eX79]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX80 : s64.valid X80 = true := by rw [eX80]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have vX81 : s64.valid X81 = true := by rw [eX81]; first | decide | simp [vW0, vW1, vW2, vZ3, vZ4, vZ5, vZ6, vZ7, vZ8, vZ9, vZ10, vZ11, vZ12, vZ13, vZ14, vZ15, vZ16, vZ17, vZ18, vZ19, vZ20, vZ21, vZ22, vZ23, vZ24, vZ25, vZ26, vZ27, vZ28, vZ29, vz0, vX0, vX3, vX31, vX32, hx, hinf, hninf, Proofs.BellmanFordExec.i32_valid_nat, hneM, hspM]
  have hn1 : W0 ≠ 2 * W0 + 1 := by omega
  have hn2 : W0 ≠ 2 * W0 + 2 := by omega
  have hn3 : 2 * W0 + 1 ≠ W0 := by omega
  have hn4 : 2 * W0 + 2 ≠ W0 := by omega
  have hn5 : 2 * W0 + 1 ≠ 2 * W0 + 2 := by omega
  have hn6 : 2 * W0 + 2 ≠ 2 * W0 + 1 := by omega
  have hD'_Z3 : b.mxv[W0]?.getD 0 = Z3 := by simpa [List.getD_eq_getElem?_getD] using hD_Z3
  have hD'_Z4 : b.smx[W0]?.getD 0 = Z4 := by simpa [List.getD_eq_getElem?_getD] using hD_Z4
  have hD'_Z5 : b.mnv[W0]?.getD 0 = Z5 := by simpa [List.getD_eq_getElem?_getD] using hD_Z5
  have hD'_Z6 : b.smn[W0]?.getD 0 = Z6 := by simpa [List.getD_eq_getElem?_getD] using hD_Z6
  have hD'_Z7 : b.lval[W0]?.getD 0 = Z7 := by simpa [List.getD_eq_getElem?_getD] using hD_Z7
  have hD'_Z8 : b.ladd[W0]?.getD 0 = Z8 := by simpa [List.getD_eq_getElem?_getD] using hD_Z8
  have hD'_Z9 : b.len[W0]?.getD 0 = Z9 := by simpa [List.getD_eq_getElem?_getD] using hD_Z9
  have hD'_Z10 : b.mxc[W0]?.getD 0 = Z10 := by simpa [List.getD_eq_getElem?_getD] using hD_Z10
  have hD'_Z11 : b.mnc[W0]?.getD 0 = Z11 := by simpa [List.getD_eq_getElem?_getD] using hD_Z11
  have hD'_Z12 : b.mxv[(2 * W0 + 1)]?.getD 0 = Z12 := by simpa [List.getD_eq_getElem?_getD] using hD_Z12
  have hD'_Z13 : b.smx[(2 * W0 + 1)]?.getD 0 = Z13 := by simpa [List.getD_eq_getElem?_getD] using hD_Z13
  have hD'_Z14 : b.mxc[(2 * W0 + 1)]?.getD 0 = Z14 := by simpa [List.getD_eq_getElem?_getD] using hD_Z14
  have hD'_Z15 : b.mnv[(2 * W0 + 1)]?.getD 0 = Z15 := by simpa [List.getD_eq_getElem?_getD] using hD_Z15
  have hD'_Z16 : b.smn[(2 * W0 + 1)]?.getD 0 = Z16 := by simpa [List.getD_eq_getElem?_getD] using hD_Z16
  have hD'_Z17 : b.mnc[(2 * W0 + 1)]?.getD 0 = Z17 := by simpa [List.getD_eq_getElem?_getD] using hD_Z17
  have hD'_Z18 : b.ladd[(2 * W0 + 1)]?.getD 0 = Z18 := by simpa [List.getD_eq_getElem?_getD] using hD_Z18
  have hD'_Z19 : b.lval[(2 * W0 + 1)]?.getD 0 = Z19 := by simpa [List.getD_eq_getElem?_getD] using hD_Z19
  have hD'_Z20 : b.len[(2 * W0 + 1)]?.getD 0 = Z20 := by simpa [List.getD_eq_getElem?_getD] using hD_Z20
  have hD'_Z21 : b.mxv[(2 * W0 + 2)]?.getD 0 = Z21 := by simpa [List.getD_eq_getElem?_getD] using hD_Z21
  have hD'_Z22 : b.smx[(2 * W0 + 2)]?.getD 0 = Z22 := by simpa [List.getD_eq_getElem?_getD] using hD_Z22
  have hD'_Z23 : b.mxc[(2 * W0 + 2)]?.getD 0 = Z23 := by simpa [List.getD_eq_getElem?_getD] using hD_Z23
  have hD'_Z24 : b.mnv[(2 * W0 + 2)]?.getD 0 = Z24 := by simpa [List.getD_eq_getElem?_getD] using hD_Z24
  have hD'_Z25 : b.smn[(2 * W0 + 2)]?.getD 0 = Z25 := by simpa [List.getD_eq_getElem?_getD] using hD_Z25
  have hD'_Z26 : b.mnc[(2 * W0 + 2)]?.getD 0 = Z26 := by simpa [List.getD_eq_getElem?_getD] using hD_Z26
  have hD'_Z27 : b.ladd[(2 * W0 + 2)]?.getD 0 = Z27 := by simpa [List.getD_eq_getElem?_getD] using hD_Z27
  have hD'_Z28 : b.lval[(2 * W0 + 2)]?.getD 0 = Z28 := by simpa [List.getD_eq_getElem?_getD] using hD_Z28
  have hD'_Z29 : b.len[(2 * W0 + 2)]?.getD 0 = Z29 := by simpa [List.getD_eq_getElem?_getD] using hD_Z29
  obtain ⟨B, hB⟩ : ∃ B : BS, B = (up47 (up46 (up45 (up44 (up43 (up42 (up41 (up40 (up39 (up38 (up37 (up36 (up35 (up34 (up33 (up32 (up31 (up30 (up29 (up28 (up27 (up26 (up25 (up24 (up23 (up22 (up21 (up20 (up19 (up18 (up17 (up16 (up15 (up14 (up13 (up12 (up11 (up10 (up9 (up8 (up7 (up6 (up5 (up4 (up3 (up2 (up1 b W0 X13) W0 X14) W0 X15) W0 X16) W0 X17) W0 X18) W0 X19) W0 X20) W0 (X18 + X12)) W0 X21) W0 (X17 + X12)) W0 X22) W0 X23) W0 X24) W0 X25) W0 X26) W0 X27) W0 X28) W0 X29) W0 X30) W0 X31) W0 X32) (2 * W0 + 1) X55) (2 * W0 + 1) X56) (2 * W0 + 1) X38) (2 * W0 + 1) X54) (2 * W0 + 1) X51) (2 * W0 + 1) X41) (2 * W0 + 1) X46) (2 * W0 + 1) X57) (2 * W0 + 2) X77) (2 * W0 + 2) X78) (2 * W0 + 2) X60) (2 * W0 + 2) X76) (2 * W0 + 2) X73) (2 * W0 + 2) X63) (2 * W0 + 2) X68) (2 * W0 + 2) X79) W0 X80) W0 X81) ne (W0 : Int)) (sp - 1) ((2 * (W0 : Int)) + 2)) (sp - 1) (((W1 : Int) + (W2 : Int)) / 2)) (sp - 1) (W2 : Int)) ((sp - 1) + 1) ((2 * (W0 : Int)) + 1)) ((sp - 1) + 1) (W1 : Int)) ((sp - 1) + 1) (((W1 : Int) + (W2 : Int)) / 2)) := ⟨_, rfl⟩
  have g_mxv : ∀ i, B.mxv.getD i 0 = (lastW [(W0, X13), (W0, X18), (W0, (X18 + X12)), (W0, X25), ((2 * W0 + 1), X55), ((2 * W0 + 2), X77)] i).getD (b.mxv.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [(W0, X13), (W0, X18), (W0, (X18 + X12)), (W0, X25), ((2 * W0 + 1), X55), ((2 * W0 + 2), X77)] b.mxv i (by simp [hl0_3, hl0_12, hl0_21])
  have g'_mxv : ∀ i, B.mxv[i]?.getD 0 = (lastW [(W0, X13), (W0, X18), (W0, (X18 + X12)), (W0, X25), ((2 * W0 + 1), X55), ((2 * W0 + 2), X77)] i).getD (b.mxv[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_mxv i
  have g_smx : ∀ i, B.smx.getD i 0 = (lastW [(W0, X19), (W0, X21), (W0, X26), ((2 * W0 + 1), X56), ((2 * W0 + 2), X78)] i).getD (b.smx.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [(W0, X19), (W0, X21), (W0, X26), ((2 * W0 + 1), X56), ((2 * W0 + 2), X78)] b.smx i (by simp [hl1_4, hl1_13, hl1_22])
  have g'_smx : ∀ i, B.smx[i]?.getD 0 = (lastW [(W0, X19), (W0, X21), (W0, X26), ((2 * W0 + 1), X56), ((2 * W0 + 2), X78)] i).getD (b.smx[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_smx i
  have g_mxc : ∀ i, B.mxc.getD i 0 = (lastW [(W0, X29), ((2 * W0 + 1), X38), ((2 * W0 + 2), X60)] i).getD (b.mxc.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [(W0, X29), ((2 * W0 + 1), X38), ((2 * W0 + 2), X60)] b.mxc i (by simp [hl2_10, hl2_14, hl2_23])
  have g'_mxc : ∀ i, B.mxc[i]?.getD 0 = (lastW [(W0, X29), ((2 * W0 + 1), X38), ((2 * W0 + 2), X60)] i).getD (b.mxc[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_mxc i
  have g_mnv : ∀ i, B.mnv.getD i 0 = (lastW [(W0, X14), (W0, X17), (W0, (X17 + X12)), (W0, X27), ((2 * W0 + 1), X54), ((2 * W0 + 2), X76)] i).getD (b.mnv.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [(W0, X14), (W0, X17), (W0, (X17 + X12)), (W0, X27), ((2 * W0 + 1), X54), ((2 * W0 + 2), X76)] b.mnv i (by simp [hl3_5, hl3_15, hl3_24])
  have g'_mnv : ∀ i, B.mnv[i]?.getD 0 = (lastW [(W0, X14), (W0, X17), (W0, (X17 + X12)), (W0, X27), ((2 * W0 + 1), X54), ((2 * W0 + 2), X76)] i).getD (b.mnv[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_mnv i
  have g_smn : ∀ i, B.smn.getD i 0 = (lastW [(W0, X15), (W0, X22), (W0, X28), ((2 * W0 + 1), X51), ((2 * W0 + 2), X73)] i).getD (b.smn.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [(W0, X15), (W0, X22), (W0, X28), ((2 * W0 + 1), X51), ((2 * W0 + 2), X73)] b.smn i (by simp [hl4_6, hl4_16, hl4_25])
  have g'_smn : ∀ i, B.smn[i]?.getD 0 = (lastW [(W0, X15), (W0, X22), (W0, X28), ((2 * W0 + 1), X51), ((2 * W0 + 2), X73)] i).getD (b.smn[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_smn i
  have g_mnc : ∀ i, B.mnc.getD i 0 = (lastW [(W0, X30), ((2 * W0 + 1), X41), ((2 * W0 + 2), X63)] i).getD (b.mnc.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [(W0, X30), ((2 * W0 + 1), X41), ((2 * W0 + 2), X63)] b.mnc i (by simp [hl5_11, hl5_17, hl5_26])
  have g'_mnc : ∀ i, B.mnc[i]?.getD 0 = (lastW [(W0, X30), ((2 * W0 + 1), X41), ((2 * W0 + 2), X63)] i).getD (b.mnc[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_mnc i
  have g_ladd : ∀ i, B.ladd.getD i 0 = (lastW [(W0, X23), (W0, X32), ((2 * W0 + 1), X46), ((2 * W0 + 2), X68), (W0, X81)] i).getD (b.ladd.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [(W0, X23), (W0, X32), ((2 * W0 + 1), X46), ((2 * W0 + 2), X68), (W0, X81)] b.ladd i (by simp [hl7_8, hl7_18, hl7_27])
  have g'_ladd : ∀ i, B.ladd[i]?.getD 0 = (lastW [(W0, X23), (W0, X32), ((2 * W0 + 1), X46), ((2 * W0 + 2), X68), (W0, X81)] i).getD (b.ladd[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_ladd i
  have g_lval : ∀ i, B.lval.getD i 0 = (lastW [(W0, X16), (W0, X20), (W0, X24), (W0, X31), ((2 * W0 + 1), X57), ((2 * W0 + 2), X79), (W0, X80)] i).getD (b.lval.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [(W0, X16), (W0, X20), (W0, X24), (W0, X31), ((2 * W0 + 1), X57), ((2 * W0 + 2), X79), (W0, X80)] b.lval i (by simp [hl8_7, hl8_19, hl8_28])
  have g'_lval : ∀ i, B.lval[i]?.getD 0 = (lastW [(W0, X16), (W0, X20), (W0, X24), (W0, X31), ((2 * W0 + 1), X57), ((2 * W0 + 2), X79), (W0, X80)] i).getD (b.lval[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_lval i
  have g_sk : ∀ i, B.sk.getD i 0 = (lastW [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] i).getD (b.sk.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] b.sk i (by simp [hl11_0, hl11_31])
  have g'_sk : ∀ i, B.sk[i]?.getD 0 = (lastW [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] i).getD (b.sk[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_sk i
  have g_sl : ∀ i, B.sl.getD i 0 = (lastW [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] i).getD (b.sl.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] b.sl i (by simp [hl12_1, hl12_32])
  have g'_sl : ∀ i, B.sl[i]?.getD 0 = (lastW [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] i).getD (b.sl[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_sl i
  have g_sr : ∀ i, B.sr.getD i 0 = (lastW [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] i).getD (b.sr.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] b.sr i (by simp [hl13_2, hl13_33])
  have g'_sr : ∀ i, B.sr[i]?.getD 0 = (lastW [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] i).getD (b.sr[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_sr i
  have g_ent : ∀ i, B.ent.getD i 0 = (lastW [(ne, (W0 : Int))] i).getD (b.ent.getD i 0) := fun i => by
    rw [hB]; exact getD_applySets [(ne, (W0 : Int))] b.ent i (by simp [hl14_30])
  have g'_ent : ∀ i, B.ent[i]?.getD 0 = (lastW [(ne, (W0 : Int))] i).getD (b.ent[i]?.getD 0) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using g_ent i
  have wv0 : s64.valid X13 = true := vX13
  have wv1 : s64.valid X14 = true := vX14
  have wv2 : s64.valid X15 = true := vX15
  have wv3 : s64.valid X16 = true := vX16
  have wv4 : s64.valid X17 = true := vX17
  have wv5 : s64.valid X18 = true := vX18
  have wv6 : s64.valid X19 = true := vX19
  have wv7 : s64.valid X20 = true := vX20
  have wv8 : s64.valid (X18 + X12) = true := hsc1
  have wv9 : s64.valid X21 = true := vX21
  have wv10 : s64.valid (X17 + X12) = true := hsc4
  have wv11 : s64.valid X22 = true := vX22
  have wv12 : s64.valid X23 = true := vX23
  have wv13 : s64.valid X24 = true := vX24
  have wv14 : s64.valid X25 = true := vX25
  have wv15 : s64.valid X26 = true := vX26
  have wv16 : s64.valid X27 = true := vX27
  have wv17 : s64.valid X28 = true := vX28
  have wv18 : s64.valid X29 = true := vX29
  have wv19 : s64.valid X30 = true := vX30
  have wv20 : s64.valid X31 = true := vX31
  have wv21 : s64.valid X32 = true := vX32
  have wv22 : s64.valid X55 = true := vX55
  have wv23 : s64.valid X56 = true := vX56
  have wv24 : s64.valid X38 = true := vX38
  have wv25 : s64.valid X54 = true := vX54
  have wv26 : s64.valid X51 = true := vX51
  have wv27 : s64.valid X41 = true := vX41
  have wv28 : s64.valid X46 = true := vX46
  have wv29 : s64.valid X57 = true := vX57
  have wv30 : s64.valid X77 = true := vX77
  have wv31 : s64.valid X78 = true := vX78
  have wv32 : s64.valid X60 = true := vX60
  have wv33 : s64.valid X76 = true := vX76
  have wv34 : s64.valid X73 = true := vX73
  have wv35 : s64.valid X63 = true := vX63
  have wv36 : s64.valid X68 = true := vX68
  have wv37 : s64.valid X79 = true := vX79
  have wv38 : s64.valid X80 = true := vX80
  have wv39 : s64.valid X81 = true := vX81
  have wv40 : i32.valid (W0 : Int) = true := (Proofs.BellmanFordExec.i32_valid_nat W0 hNW0)
  have wv41 : i32.valid ((2 * (W0 : Int)) + 2) = true := hsc26
  have wv42 : i32.valid (((W1 : Int) + (W2 : Int)) / 2) = true := (i32_valid_div2 _ hsc23 (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)))
  have wv43 : i32.valid (W2 : Int) = true := (Proofs.BellmanFordExec.i32_valid_nat W2 hNW2)
  have wv44 : i32.valid ((2 * (W0 : Int)) + 1) = true := hsc27
  have wv45 : i32.valid (W1 : Int) = true := (Proofs.BellmanFordExec.i32_valid_nat W1 hNW1)
  have wv46 : i32.valid (((W1 : Int) + (W2 : Int)) / 2) = true := (i32_valid_div2 _ hsc23 (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)))
  have gv_mxv : ∀ w ∈ B.mxv, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [(W0, X13), (W0, X18), (W0, (X18 + X12)), (W0, X25), ((2 * W0 + 1), X55), ((2 * W0 + 2), X77)] b.mxv hV.v0 (by simp [wv0, wv5, wv8, wv14, wv22, wv30])
  have gl_mxv : B.mxv.length = b.mxv.length := by
    rw [hB]
    exact applySets_length [(W0, X13), (W0, X18), (W0, (X18 + X12)), (W0, X25), ((2 * W0 + 1), X55), ((2 * W0 + 2), X77)] b.mxv
  have gv_smx : ∀ w ∈ B.smx, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [(W0, X19), (W0, X21), (W0, X26), ((2 * W0 + 1), X56), ((2 * W0 + 2), X78)] b.smx hV.v1 (by simp [wv6, wv9, wv15, wv23, wv31])
  have gl_smx : B.smx.length = b.smx.length := by
    rw [hB]
    exact applySets_length [(W0, X19), (W0, X21), (W0, X26), ((2 * W0 + 1), X56), ((2 * W0 + 2), X78)] b.smx
  have gv_mxc : ∀ w ∈ B.mxc, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [(W0, X29), ((2 * W0 + 1), X38), ((2 * W0 + 2), X60)] b.mxc hV.v2 (by simp [wv18, wv24, wv32])
  have gl_mxc : B.mxc.length = b.mxc.length := by
    rw [hB]
    exact applySets_length [(W0, X29), ((2 * W0 + 1), X38), ((2 * W0 + 2), X60)] b.mxc
  have gv_mnv : ∀ w ∈ B.mnv, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [(W0, X14), (W0, X17), (W0, (X17 + X12)), (W0, X27), ((2 * W0 + 1), X54), ((2 * W0 + 2), X76)] b.mnv hV.v3 (by simp [wv1, wv4, wv10, wv16, wv25, wv33])
  have gl_mnv : B.mnv.length = b.mnv.length := by
    rw [hB]
    exact applySets_length [(W0, X14), (W0, X17), (W0, (X17 + X12)), (W0, X27), ((2 * W0 + 1), X54), ((2 * W0 + 2), X76)] b.mnv
  have gv_smn : ∀ w ∈ B.smn, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [(W0, X15), (W0, X22), (W0, X28), ((2 * W0 + 1), X51), ((2 * W0 + 2), X73)] b.smn hV.v4 (by simp [wv2, wv11, wv17, wv26, wv34])
  have gl_smn : B.smn.length = b.smn.length := by
    rw [hB]
    exact applySets_length [(W0, X15), (W0, X22), (W0, X28), ((2 * W0 + 1), X51), ((2 * W0 + 2), X73)] b.smn
  have gv_mnc : ∀ w ∈ B.mnc, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [(W0, X30), ((2 * W0 + 1), X41), ((2 * W0 + 2), X63)] b.mnc hV.v5 (by simp [wv19, wv27, wv35])
  have gl_mnc : B.mnc.length = b.mnc.length := by
    rw [hB]
    exact applySets_length [(W0, X30), ((2 * W0 + 1), X41), ((2 * W0 + 2), X63)] b.mnc
  have gv_len : ∀ w ∈ B.len, s64.valid w = true := by
    rw [hB]
    exact hV.v6
  have gl_len : B.len.length = b.len.length := by
    rw [hB]
    rfl
  have gv_ladd : ∀ w ∈ B.ladd, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [(W0, X23), (W0, X32), ((2 * W0 + 1), X46), ((2 * W0 + 2), X68), (W0, X81)] b.ladd hV.v7 (by simp [wv12, wv21, wv28, wv36, wv39])
  have gl_ladd : B.ladd.length = b.ladd.length := by
    rw [hB]
    exact applySets_length [(W0, X23), (W0, X32), ((2 * W0 + 1), X46), ((2 * W0 + 2), X68), (W0, X81)] b.ladd
  have gv_lval : ∀ w ∈ B.lval, s64.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => s64.valid w = true) [(W0, X16), (W0, X20), (W0, X24), (W0, X31), ((2 * W0 + 1), X57), ((2 * W0 + 2), X79), (W0, X80)] b.lval hV.v8 (by simp [wv3, wv7, wv13, wv20, wv29, wv37, wv38])
  have gl_lval : B.lval.length = b.lval.length := by
    rw [hB]
    exact applySets_length [(W0, X16), (W0, X20), (W0, X24), (W0, X31), ((2 * W0 + 1), X57), ((2 * W0 + 2), X79), (W0, X80)] b.lval
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
    exact valid_applySets (fun w => i32.valid w = true) [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] b.sk hV.v11 (by simp [wv41, wv44])
  have gl_sk : B.sk.length = b.sk.length := by
    rw [hB]
    exact applySets_length [((sp - 1), ((2 * (W0 : Int)) + 2)), (((sp - 1) + 1), ((2 * (W0 : Int)) + 1))] b.sk
  have gv_sl : ∀ w ∈ B.sl, i32.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => i32.valid w = true) [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] b.sl hV.v12 (by simp [wv42, wv45])
  have gl_sl : B.sl.length = b.sl.length := by
    rw [hB]
    exact applySets_length [((sp - 1), (((W1 : Int) + (W2 : Int)) / 2)), (((sp - 1) + 1), (W1 : Int))] b.sl
  have gv_sr : ∀ w ∈ B.sr, i32.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => i32.valid w = true) [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] b.sr hV.v13 (by simp [wv43, wv46])
  have gl_sr : B.sr.length = b.sr.length := by
    rw [hB]
    exact applySets_length [((sp - 1), (W2 : Int)), (((sp - 1) + 1), (((W1 : Int) + (W2 : Int)) / 2))] b.sr
  have gv_ent : ∀ w ∈ B.ent, i32.valid w = true := by
    rw [hB]
    exact valid_applySets (fun w => i32.valid w = true) [(ne, (W0 : Int))] b.ent hV.v14 (by simp [wv40])
  have gl_ent : B.ent.length = b.ent.length := by
    rw [hB]
    exact applySets_length [(ne, (W0 : Int))] b.ent
  have hVal : ValidOK B := ⟨gv_mxv, gv_smx, gv_mxc, gv_mnv, gv_smn, gv_mnc, gv_len, gv_ladd, gv_lval, gv_lo, gv_hi, gv_sk, gv_sl, gv_sr, gv_ent⟩
  have gl_eq : B.len = b.len := by
    rw [hB]
    rfl
  have hLen : SameLen b B := ⟨gl_mxv, gl_smx, gl_mxc, gl_mnv, gl_smn, gl_mnc, gl_len, gl_ladd, gl_lval, gl_lo, gl_hi, gl_sk, gl_sl, gl_sr, gl_ent, gl_eq⟩
  have hother : ∀ i, i ≠ W0 → Hof inf B i = Hof inf b i := by
    intro i hi
    by_cases hi1 : i = 2 * W0 + 1
    · rw [hi1]
      simp only [Hof, decNd, decTag]
      simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g_ent, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, g'_ent, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD_Z25, hD_Z26, hD_Z27, hD_Z28, hD_Z29, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hD'_Z25, hD'_Z26, hD'_Z27, hD'_Z28, hD'_Z29, hn1, hn2, hn3, hn4, hn5, hn6, eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83]
    · by_cases hi2 : i = 2 * W0 + 2
      · rw [hi2]
        simp only [Hof, decNd, decTag]
        simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g_ent, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, g'_ent, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD_Z25, hD_Z26, hD_Z27, hD_Z28, hD_Z29, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hD'_Z25, hD'_Z26, hD'_Z27, hD'_Z28, hD'_Z29, hn1, hn2, hn3, hn4, hn5, hn6, eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83]
      · have hi' : ¬ W0 = i := fun h => hi h.symm
        have hi1' : ¬ 2 * W0 + 1 = i := fun h => hi1 h.symm
        have hi2' : ¬ 2 * W0 + 2 = i := fun h => hi2 h.symm
        simp only [Hof, decNd, decTag]
        simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g_ent, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, g'_ent, lastW, hi', hi1', hi2']
  have hBo : ∀ i, i ≠ W0 → decNd B i = decNd b i ∧ decTag inf B i = decTag inf b i :=
    fun i hi => ⟨congrArg Prod.fst (hother i hi), congrArg Prod.snd (hother i hi)⟩
  have hT : decTag inf b W0 = ({ lval := if Z7 = inf then none else some Z7, ladd := Z8 } : Tag) := by
    simp [decTag, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD_Z25, hD_Z26, hD_Z27, hD_Z28, hD_Z29, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hD'_Z25, hD'_Z26, hD'_Z27, hD'_Z28, hD'_Z29]
  have hNb : decNd b W0 = ({ mx := Z3, smx := Z4, mc := Z10, mn := Z5, smn := Z6, mnc := Z11 } : Nd) := by
    simp [decNd, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD_Z25, hD_Z26, hD_Z27, hD_Z28, hD_Z29, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hD'_Z25, hD'_Z26, hD'_Z27, hD'_Z28, hD'_Z29]
  have bn_eq : decNd B W0 = ({ mx := x, smx := -inf, mc := Z9, mn := x, smn := inf, mnc := Z9 } : Nd) := by
    simp only [decNd]
    simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g_ent, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, g'_ent, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD_Z25, hD_Z26, hD_Z27, hD_Z28, hD_Z29, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hD'_Z25, hD'_Z26, hD'_Z27, hD'_Z28, hD'_Z29, hn1, hn2, hn3, hn4, hn5, hn6, eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83]
  have hBn : decNd B W0 = ({ mx := x, smx := -inf, mc := Z9, mn := x, smn := inf, mnc := Z9 } : Nd) := bn_eq
  have hBt : decTag inf B W0 = ({ lval := if X31 = inf then none else some X31, ladd := X32 } : Tag) := by
    simp only [decTag]
    simp [g_mxv, g_smx, g_mxc, g_mnv, g_smn, g_mnc, g_ladd, g_lval, g_sk, g_sl, g_sr, g_ent, g'_mxv, g'_smx, g'_mxc, g'_mnv, g'_smn, g'_mnc, g'_ladd, g'_lval, g'_sk, g'_sl, g'_sr, g'_ent, lastW, hD_Z3, hD_Z4, hD_Z5, hD_Z6, hD_Z7, hD_Z8, hD_Z9, hD_Z10, hD_Z11, hD_Z12, hD_Z13, hD_Z14, hD_Z15, hD_Z16, hD_Z17, hD_Z18, hD_Z19, hD_Z20, hD_Z21, hD_Z22, hD_Z23, hD_Z24, hD_Z25, hD_Z26, hD_Z27, hD_Z28, hD_Z29, hD'_Z3, hD'_Z4, hD'_Z5, hD'_Z6, hD'_Z7, hD'_Z8, hD'_Z9, hD'_Z10, hD'_Z11, hD'_Z12, hD'_Z13, hD'_Z14, hD'_Z15, hD'_Z16, hD'_Z17, hD'_Z18, hD'_Z19, hD'_Z20, hD'_Z21, hD'_Z22, hD'_Z23, hD'_Z24, hD'_Z25, hD'_Z26, hD'_Z27, hD'_Z28, hD'_Z29, hn1, hn2, hn3, hn4, hn5, hn6, eX2, eX6, eX1, eX4, eX5, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26, eX27, eX28, eX29, eX30, eX33, eX34, eX35, eX36, eX37, eX38, eX39, eX40, eX41, eX42, eX43, eX44, eX45, eX46, eX47, eX48, eX49, eX50, eX51, eX52, eX53, eX54, eX55, eX56, eX57, eX58, eX59, eX60, eX61, eX62, eX63, eX64, eX65, eX66, eX67, eX68, eX69, eX70, eX71, eX72, eX73, eX74, eX75, eX76, eX77, eX78, eX79, eX80, eX81, eX82, eX83]
  have hHR : HRel inf B (H.set W0 (Cellh.setC ((W2 - W1 : Nat) : Int) x (H W0))) := by
    refine HRel_set inf b B H W0 _ hH hBo hLen.leneq ?_ ?_ ?_
    · simp only [Cellh.addC, Cellh.setC]
      rw [bn_eq]; exact (set_nd_key Z9 _ inf x hinfI hlenW)
    · intro hl
      have hlZ : Z9 ≠ 1 := by rw [← hD_Z9]; exact hl
      have hHt := (hH W0).2.1 hl
      rw [hBt]
      simp only [Cellh.addC, Cellh.setC]
      skip
      exact (set_tag_key Z9 Z7 Z8 x inf X31 X32 eX31 eX32 hxne).1 hlZ
    · intro hl
      have hlZ : Z9 = 1 := by rw [← hD_Z9]; exact hl
      have hHt := (hH W0).2.2 hl
      rw [hT] at hHt
      have h78 := (tag_noTag_iff Z7 Z8 inf).mp hHt
      obtain ⟨h7, h8⟩ := h78
      rw [hBt]
      exact (set_tag_key Z9 Z7 Z8 x inf X31 X32 eX31 eX32 hxne).2 hlZ h7 h8
  have hstk' : StkRep B (sp - 1) S := StkRep_pop b B sp ⟨W0, W1, W2⟩ S hstk
    (fun i hi => by rw [g_sk i]; exact lastW_pair_below _ _ _ _ _ hi)
    (fun i hi => by rw [g_sl i]; exact lastW_pair_below _ _ _ _ _ hi)
    (fun i hi => by rw [g_sr i]; exact lastW_pair_below _ _ _ _ _ hi)
  have hent' : EntRep B ne E := EntRep_keep b B ne E hent
    (fun i hi => by rw [g_ent i]; exact lastW_single_below _ _ _ _ hi)
  have hps : gS P (pre ++ [(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X83⟩ : Cell), (⟨i32, X82⟩ : Cell)]) = gS P (pre ++ [cs inf, ci n, ci op, ci qa, ci qb, cs x, ci (sp - 1), ci ne]) := by rw [eX83, eX82]
  refine ⟨B, hHR, hstk', hent', hVal, hLen, fun fu => ?_⟩
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ := ApplyLoop_body mv hnv pre hty hty32 b P inf n op qa qb sp ne x hinf hnM hopM hqaM hqbM hspM hneM hsp hx hvl0 hvl1 hvl2 hvl3 hvl4 hvl5 hvl6 hvl7 hvl8 hvl11 hvl12 hvl13 hvl14 W0 hNW0 hD_W0 W1 hNW1 hD_W1 W2 hNW2 hD_W2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 Z13 hD_Z13 Z14 hD_Z14 Z15 hD_Z15 Z16 hD_Z16 Z17 hD_Z17 Z18 hD_Z18 Z19 hD_Z19 Z20 hD_Z20 Z21 hD_Z21 Z22 hD_Z22 Z23 hD_Z23 Z24 hD_Z24 Z25 hD_Z25 Z26 hD_Z26 Z27 hD_Z27 Z28 hD_Z28 Z29 hD_Z29 hl11_0 hl12_1 hl13_2 hl0_3 hl1_4 hl3_5 hl4_6 hl8_7 hl7_8 hl6_9 hl2_10 hl5_11 hl0_12 hl1_13 hl2_14 hl3_15 hl4_16 hl5_17 hl7_18 hl8_19 hl6_20 hl0_21 hl1_22 hl2_23 hl3_24 hl4_25 hl5_26 hl7_27 hl8_28 hl6_29 hl14_30 hl11_31 hl12_32 hl13_33 hk1_W0 hk2_W0 hix2 hix3 hix4 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 X20 hX20 X21 hX21 X22 hX22 X23 hX23 X24 hX24 X25 hX25 X26 hX26 X27 hX27 X28 hX28 X29 hX29 X30 hX30 X31 hX31 X32 hX32 X33 hX33 X34 hX34 X35 hX35 X36 hX36 X37 hX37 X38 hX38 X39 hX39 X40 hX40 X41 hX41 X42 hX42 X43 hX43 X44 hX44 X45 hX45 X46 hX46 X47 hX47 X48 hX48 X49 hX49 X50 hX50 X51 hX51 X52 hX52 X53 hX53 X54 hX54 X55 hX55 X56 hX56 X57 hX57 X58 hX58 X59 hX59 X60 hX60 X61 hX61 X62 hX62 X63 hX63 X64 hX64 X65 hX65 X66 hX66 X67 hX67 X68 hX68 X69 hX69 X70 hX70 X71 hX71 X72 hX72 X73 hX73 X74 hX74 X75 hX75 X76 hX76 X77 hX77 X78 hX78 X79 hX79 X80 hX80 X81 hX81 X82 hX82 X83 hX83 hsc0 hsc1 hsc2 hsc3 hsc4 hsc5 hsc6 hsc7 hsc8 hsc9 hsc10 hsc11 hsc12 hsc13 hsc14 hsc15 hsc16 hsc17 hsc18 hsc19 hsc20 hsc21 hsc22 hsc23 hsc25 hsc26 hsc27 hsc28 hsc29 fu
  have a3 := pexecM_scope mv fu _ _ _ r0 h0
  have tk : (⟨r0.ps.mem.take (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell)] : List Cell))).mem.length, r0.ps.bs.take (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell)] : List Cell))).bs.length⟩ : PS) = gS P (pre ++ [(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X83⟩ : Cell), (⟨i32, X82⟩ : Cell)]) := by
    rw [hp0]; exact scope_take P pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, (sp : Int)⟩ : Cell), (⟨i32, (ne : Int)⟩ : Cell)] : List Cell) [(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X83⟩ : Cell), (⟨i32, X82⟩ : Cell)] [(⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, (W2 : Int)⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨i32, X3⟩ : Cell), (⟨i32, X5⟩ : Cell), (⟨i32, X6⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X8⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X14⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X16⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X9⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, X14⟩ : Cell), (⟨s64, X16⟩ : Cell), (⟨s64, X17⟩ : Cell), (⟨s64, X18⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X20⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, X12⟩ : Cell), (⟨s64, X21⟩ : Cell), (⟨s64, X22⟩ : Cell), (⟨s64, X24⟩ : Cell), (⟨s64, X23⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨s64, X25⟩ : Cell), (⟨s64, X26⟩ : Cell), (⟨s64, X27⟩ : Cell), (⟨s64, X28⟩ : Cell), (⟨s64, X29⟩ : Cell), (⟨s64, X30⟩ : Cell), (⟨s64, X31⟩ : Cell), (⟨s64, X32⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, X7⟩ : Cell), (⟨s64, X31⟩ : Cell), (⟨s64, X32⟩ : Cell), (⟨s64, X25⟩ : Cell), (⟨s64, X27⟩ : Cell), (⟨i32, X33⟩ : Cell), (⟨s64, X34⟩ : Cell), (⟨i32, X35⟩ : Cell), (⟨i32, (((2 * W0 + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * W0 + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨s64, Z13⟩ : Cell), (⟨s64, Z14⟩ : Cell), (⟨s64, Z15⟩ : Cell), (⟨s64, Z16⟩ : Cell), (⟨s64, Z17⟩ : Cell), (⟨s64, Z18⟩ : Cell), (⟨s64, Z19⟩ : Cell), (⟨s64, Z20⟩ : Cell), (⟨s64, Z21⟩ : Cell), (⟨s64, Z22⟩ : Cell), (⟨s64, Z23⟩ : Cell), (⟨s64, Z24⟩ : Cell), (⟨s64, Z25⟩ : Cell), (⟨s64, Z26⟩ : Cell), (⟨s64, Z27⟩ : Cell), (⟨s64, Z28⟩ : Cell), (⟨s64, Z29⟩ : Cell), (⟨s64, X36⟩ : Cell), (⟨s64, X37⟩ : Cell), (⟨s64, X38⟩ : Cell), (⟨s64, X39⟩ : Cell), (⟨s64, X40⟩ : Cell), (⟨s64, X41⟩ : Cell), (⟨s64, X42⟩ : Cell), (⟨s64, X43⟩ : Cell), (⟨s64, (X36 + X34)⟩ : Cell), (⟨s64, X44⟩ : Cell), (⟨s64, (X39 + X34)⟩ : Cell), (⟨s64, X45⟩ : Cell), (⟨s64, X46⟩ : Cell), (⟨s64, X47⟩ : Cell), (⟨i32, X48⟩ : Cell), (⟨s64, X49⟩ : Cell), (⟨s64, X50⟩ : Cell), (⟨s64, X51⟩ : Cell), (⟨s64, X52⟩ : Cell), (⟨i32, X53⟩ : Cell), (⟨s64, X54⟩ : Cell), (⟨s64, X55⟩ : Cell), (⟨s64, X56⟩ : Cell), (⟨s64, X57⟩ : Cell), (⟨s64, X58⟩ : Cell), (⟨s64, X59⟩ : Cell), (⟨s64, X60⟩ : Cell), (⟨s64, X61⟩ : Cell), (⟨s64, X62⟩ : Cell), (⟨s64, X63⟩ : Cell), (⟨s64, X64⟩ : Cell), (⟨s64, X65⟩ : Cell), (⟨s64, (X58 + X34)⟩ : Cell), (⟨s64, X66⟩ : Cell), (⟨s64, (X61 + X34)⟩ : Cell), (⟨s64, X67⟩ : Cell), (⟨s64, X68⟩ : Cell), (⟨s64, X69⟩ : Cell), (⟨i32, X70⟩ : Cell), (⟨s64, X71⟩ : Cell), (⟨s64, X72⟩ : Cell), (⟨s64, X73⟩ : Cell), (⟨s64, X74⟩ : Cell), (⟨i32, X75⟩ : Cell), (⟨s64, X76⟩ : Cell), (⟨s64, X77⟩ : Cell), (⟨s64, X78⟩ : Cell), (⟨s64, X79⟩ : Cell), (⟨s64, X80⟩ : Cell), (⟨s64, X81⟩ : Cell), (⟨i32, (((W1 : Int) + (W2 : Int)) / 2)⟩ : Cell)] (by rfl)
  rw [tk, hv0] at a3
  have a4 := seqM_some a3 hr0 (pexecM_skip mv fu (gS P (pre ++ [(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, x⟩ : Cell), (⟨i32, X83⟩ : Cell), (⟨i32, X82⟩ : Cell)])) (VVB (up47 (up46 (up45 (up44 (up43 (up42 (up41 (up40 (up39 (up38 (up37 (up36 (up35 (up34 (up33 (up32 (up31 (up30 (up29 (up28 (up27 (up26 (up25 (up24 (up23 (up22 (up21 (up20 (up19 (up18 (up17 (up16 (up15 (up14 (up13 (up12 (up11 (up10 (up9 (up8 (up7 (up6 (up5 (up4 (up3 (up2 (up1 b W0 X13) W0 X14) W0 X15) W0 X16) W0 X17) W0 X18) W0 X19) W0 X20) W0 (X18 + X12)) W0 X21) W0 (X17 + X12)) W0 X22) W0 X23) W0 X24) W0 X25) W0 X26) W0 X27) W0 X28) W0 X29) W0 X30) W0 X31) W0 X32) (2 * W0 + 1) X55) (2 * W0 + 1) X56) (2 * W0 + 1) X38) (2 * W0 + 1) X54) (2 * W0 + 1) X51) (2 * W0 + 1) X41) (2 * W0 + 1) X46) (2 * W0 + 1) X57) (2 * W0 + 2) X77) (2 * W0 + 2) X78) (2 * W0 + 2) X60) (2 * W0 + 2) X76) (2 * W0 + 2) X73) (2 * W0 + 2) X63) (2 * W0 + 2) X68) (2 * W0 + 2) X79) W0 X80) W0 X81) ne (W0 : Int)) (sp - 1) ((2 * (W0 : Int)) + 2)) (sp - 1) (((W1 : Int) + (W2 : Int)) / 2)) (sp - 1) (W2 : Int)) ((sp - 1) + 1) ((2 * (W0 : Int)) + 1)) ((sp - 1) + 1) (W1 : Int)) ((sp - 1) + 1) (((W1 : Int) + (W2 : Int)) / 2))))
  rw [← hB] at a4
  refine ⟨_, a4, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact hps
  · rfl
  · simp; omega
  · simp; omega

end Proofs.BeatsRep
