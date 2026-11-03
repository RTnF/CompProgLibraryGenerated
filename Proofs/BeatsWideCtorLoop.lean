import Proofs.BeatsCapCtor
import Proofs.BeatsExec_WideCtLoop
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
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
theorem ct_iter_wide {S : Nat} (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (inf : Int) (hinfI : inf = INF) (a : List Int) (n ne k L : Nat) (b : BS) (hI : CtInv a n inf b k ne) (hV : ValidOK b)
    (hLens : CapS S b L) (hlo : L ≤ b.lo.length) (hhi : L ≤ b.hi.length) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hRange : 4*n < M31)
    (hkn : k < 4 * n) (hAlen : a.length = n) (hAv : ∀ w ∈ a, s64.valid w = true) :
    ∃ b' : BS, CtInv a n inf b' (k + 1) (ne + (if isInnerAt n k then 1 else 0)) ∧ CapS S b' L ∧ L ≤ b'.lo.length ∧ L ≤ b'.hi.length ∧ ValidOK b' ∧
      ∀ fu : Nat, ∃ r : PRM, pexecM mv fu (.sequence (.scope (WideCtLoopBody (mv.nv + pre.length))) Sk)
        (gS P (pre ++ CtCells inf n ne k)) (VVA a b) = some r ∧ r.ret = none ∧
        r.ps = gS P (pre ++ CtCells inf n (ne + (if isInnerAt n k then 1 else 0)) (k + 1)) ∧ r.vv = VVA a b' ∧ r.cost ≤ 20590 ∧ r.wk ≤ 12 := by
  classical
  have hM : M31 = 2147483648 := rfl
  have hinf : s64.valid inf = true := by rw [hinfI]; exact s64_valid_of_bounds _ (by unfold INF; omega) (by unfold INF; omega)
  have hninf : s64.valid (-inf) = true := by rw [hinfI]; exact s64_valid_of_bounds _ (by unfold INF; omega) (by unfold INF; omega)
  have hne : ne ≤ k := by have := hI.hent.1; have := LLr_length_le n k; omega
  have hnM : n < M31 := by omega
  have hneM : ne < M31 := by omega
  have hkM : k < M31 := by omega
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, lsk, lsl, lsr, lent⟩ := hLens
  have hb := rngOf_le n k
  have hlt := rngOf_lo_lt n hn k
  obtain ⟨W0, hW0⟩ : ∃ W0 : Nat, W0 = (rngOf n k).1 := ⟨_, rfl⟩
  obtain ⟨W1, hW1⟩ : ∃ W1 : Nat, W1 = (rngOf n k).2 := ⟨_, rfl⟩
  have hNW0 : W0 < M31 := by omega
  have hNW1 : W1 < M31 := by omega
  have hD_W0 : b.lo.getD k 0 = (W0 : Int) := by rw [hI.hlo k, ite_eq_left (by omega), hW0]
  have hD_W1 : b.hi.getD k 0 = (W1 : Int) := by rw [hI.hhi k, ite_eq_left (by omega), hW1]
  obtain ⟨W10, hNW10, hD_W10⟩ : ∃ W : Nat, W < M31 ∧ b.lo.getD (2 * k + 1) 0 = (W : Int) := ⟨0, by omega, by rw [hI.hlo, ite_eq_right (by omega)]⟩
  obtain ⟨W11, hNW11, hD_W11⟩ : ∃ W : Nat, W < M31 ∧ b.hi.getD (2 * k + 1) 0 = (W : Int) := ⟨0, by omega, by rw [hI.hhi, ite_eq_right (by omega)]⟩
  obtain ⟨W12, hNW12, hD_W12⟩ : ∃ W : Nat, W < M31 ∧ b.lo.getD (2 * k + 2) 0 = (W : Int) := ⟨0, by omega, by rw [hI.hlo, ite_eq_right (by omega)]⟩
  obtain ⟨W13, hNW13, hD_W13⟩ : ∃ W : Nat, W < M31 ∧ b.hi.getD (2 * k + 2) 0 = (W : Int) := ⟨0, by omega, by rw [hI.hhi, ite_eq_right (by omega)]⟩
  have hWa : W0 < a.length := by omega
  have hl9_0 : k < (b.lo).length := by omega
  have hl10_1 : k < (b.hi).length := by omega
  have hl6_2 : k < (b.len).length := by omega
  have hl15_3 : W0 < a.length := by omega
  have hl0_4 : k < (b.mxv).length := by omega
  have hl3_5 : k < (b.mnv).length := by omega
  have hl1_6 : k < (b.smx).length := by omega
  have hl4_7 : k < (b.smn).length := by omega
  have hl2_8 : k < (b.mxc).length := by omega
  have hl5_9 : k < (b.mnc).length := by omega
  have hl9_10 : (2 * k + 1) < (b.lo).length := by omega
  have hl10_11 : (2 * k + 1) < (b.hi).length := by omega
  have hl9_12 : (2 * k + 2) < (b.lo).length := by omega
  have hl10_13 : (2 * k + 2) < (b.hi).length := by omega
  have hl14_14 : ne < (b.ent).length := by omega
  obtain ⟨Z2, hD_Z2⟩ : ∃ Z : Int, b.len.getD k 0 = Z := ⟨_, rfl⟩
  obtain ⟨Z3, hD_Z3⟩ : ∃ Z : Int, a.getD W0 0 = Z := ⟨_, rfl⟩
  obtain ⟨Z4, hD_Z4⟩ : ∃ Z : Int, b.mxv.getD k 0 = Z := ⟨_, rfl⟩
  obtain ⟨Z5, hD_Z5⟩ : ∃ Z : Int, b.mnv.getD k 0 = Z := ⟨_, rfl⟩
  obtain ⟨Z6, hD_Z6⟩ : ∃ Z : Int, b.smx.getD k 0 = Z := ⟨_, rfl⟩
  obtain ⟨Z7, hD_Z7⟩ : ∃ Z : Int, b.smn.getD k 0 = Z := ⟨_, rfl⟩
  obtain ⟨Z8, hD_Z8⟩ : ∃ Z : Int, b.mxc.getD k 0 = Z := ⟨_, rfl⟩
  obtain ⟨Z9, hD_Z9⟩ : ∃ Z : Int, b.mnc.getD k 0 = Z := ⟨_, rfl⟩
  obtain ⟨X0, hX0⟩ : ∃ X0 : Int, X0 = (if ((W0 : Int) < (W1 : Int)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ X1 : Int, X1 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) = 1)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ X2 : Int, X2 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) ≠ 1)) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X3, hX3⟩ : ∃ X3 : Int, X3 = (if (X0 = 1) then ((W1 : Int) - (W0 : Int)) else Z2) := ⟨_, rfl⟩
  obtain ⟨X4, hX4⟩ : ∃ X4 : Int, X4 = (if (X1 = 1) then Z3 else Z4) := ⟨_, rfl⟩
  obtain ⟨X5, hX5⟩ : ∃ X5 : Int, X5 = (if (X1 = 1) then Z3 else Z5) := ⟨_, rfl⟩
  obtain ⟨X6, hX6⟩ : ∃ X6 : Int, X6 = (if (X1 = 1) then (-inf) else Z6) := ⟨_, rfl⟩
  obtain ⟨X7, hX7⟩ : ∃ X7 : Int, X7 = (if (X1 = 1) then inf else Z7) := ⟨_, rfl⟩
  obtain ⟨X8, hX8⟩ : ∃ X8 : Int, X8 = (if (X1 = 1) then 1 else Z8) := ⟨_, rfl⟩
  obtain ⟨X9, hX9⟩ : ∃ X9 : Int, X9 = (if (X1 = 1) then 1 else Z9) := ⟨_, rfl⟩
  obtain ⟨X10, hX10⟩ : ∃ X10 : Int, X10 = (if (X2 = 1) then (W0 : Int) else (W10 : Int)) := ⟨_, rfl⟩
  obtain ⟨X11, hX11⟩ : ∃ X11 : Int, X11 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W11 : Int)) := ⟨_, rfl⟩
  obtain ⟨X12, hX12⟩ : ∃ X12 : Int, X12 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W12 : Int)) := ⟨_, rfl⟩
  obtain ⟨X13, hX13⟩ : ∃ X13 : Int, X13 = (if (X2 = 1) then (W1 : Int) else (W13 : Int)) := ⟨_, rfl⟩
  obtain ⟨X14, hX14⟩ : ∃ X14 : Int, X14 = ((ne : Int) + X2) := ⟨_, rfl⟩
  obtain ⟨X15, hX15⟩ : ∃ X15 : Int, X15 = ((k : Int) + 1) := ⟨_, rfl⟩
  have hX2c : X2 = 0 ∨ X2 = 1 := by rw [hX2]; split <;> simp
  have hsc0' : i32.valid ((W1 : Int) - (W0 : Int)) = true := by simp only [Ty.valid]; simp; omega
  have hsc2' : i32.valid ((W0 : Int) + (W1 : Int)) = true := by simp only [Ty.valid]; simp; omega
  have hsc4' : i32.valid ((ne : Int) + X2) = true := by simp only [Ty.valid]; simp; omega
  have hsc5' : i32.valid ((k : Int) + 1) = true := by simp only [Ty.valid]; simp; omega
  obtain ⟨hX2eq, hInv'⟩ := ct_step_inv a n inf hinfI b k ne hI (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    W0 W1 hD_W0 hD_W1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 hD_Z2 hD_Z3 hD_Z4 hD_Z5 hD_Z6 hD_Z7 hD_Z8 hD_Z9
    W10 W11 W12 W13 hD_W10 hD_W11 hD_W12 hD_W13 X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13

  -- validity of the values that are written
  have vZ2 : s64.valid Z2 = true := by rw [← hD_Z2]; exact getD_mem_valid b.len k hl6_2 hV.v6
  have vZ3 : s64.valid Z3 = true := by rw [← hD_Z3]; exact getD_mem_valid a W0 hl15_3 hAv
  have vZ4 : s64.valid Z4 = true := by rw [← hD_Z4]; exact getD_mem_valid b.mxv k hl0_4 hV.v0
  have vZ5 : s64.valid Z5 = true := by rw [← hD_Z5]; exact getD_mem_valid b.mnv k hl3_5 hV.v3
  have vZ6 : s64.valid Z6 = true := by rw [← hD_Z6]; exact getD_mem_valid b.smx k hl1_6 hV.v1
  have vZ7 : s64.valid Z7 = true := by rw [← hD_Z7]; exact getD_mem_valid b.smn k hl4_7 hV.v4
  have vZ8 : s64.valid Z8 = true := by rw [← hD_Z8]; exact getD_mem_valid b.mxc k hl2_8 hV.v2
  have vZ9 : s64.valid Z9 = true := by rw [← hD_Z9]; exact getD_mem_valid b.mnc k hl5_9 hV.v5
  have v1s : s64.valid 1 = true := by decide
  have vX3 : s64.valid X3 = true := by rw [hX3]; split; exact s64_of_i32 _ hsc0'; exact vZ2
  have vX4 : s64.valid X4 = true := by rw [hX4]; split; exact vZ3; exact vZ4
  have vX5 : s64.valid X5 = true := by rw [hX5]; split; exact vZ3; exact vZ5
  have vX6 : s64.valid X6 = true := by rw [hX6]; split; exact hninf; exact vZ6
  have vX7 : s64.valid X7 = true := by rw [hX7]; split; exact hinf; exact vZ7
  have vX8 : s64.valid X8 = true := by rw [hX8]; split; exact v1s; exact vZ8
  have vX9 : s64.valid X9 = true := by rw [hX9]; split; exact v1s; exact vZ9
  have hmid : i32.valid (((W0 : Int) + (W1 : Int)) / 2) = true := by simp only [Ty.valid]; simp; omega
  have vX10 : i32.valid X10 = true := by rw [hX10]; split; exact Proofs.BellmanFordExec.i32_valid_nat _ hNW0; exact Proofs.BellmanFordExec.i32_valid_nat _ hNW10
  have vX11 : i32.valid X11 = true := by rw [hX11]; split; exact hmid; exact Proofs.BellmanFordExec.i32_valid_nat _ hNW11
  have vX12 : i32.valid X12 = true := by rw [hX12]; split; exact hmid; exact Proofs.BellmanFordExec.i32_valid_nat _ hNW12
  have vX13 : i32.valid X13 = true := by rw [hX13]; split; exact Proofs.BellmanFordExec.i32_valid_nat _ hNW1; exact Proofs.BellmanFordExec.i32_valid_nat _ hNW13
  have vk : i32.valid (k : Int) = true := Proofs.BellmanFordExec.i32_valid_nat _ hkM
  have hVal' : ValidOK (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hV.v7, hV.v8, ?_, ?_, hV.v11, hV.v12, hV.v13, ?_⟩
    · exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v0 vX4
    · exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v1 vX6
    · exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v2 vX8
    · exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v3 vX5
    · exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v4 vX7
    · exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v5 vX9
    · exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v6 vX3
    · exact valid_set (fun w => i32.valid w = true) _ _ _ (valid_set (fun w => i32.valid w = true) _ _ _ hV.v9 vX10) vX12
    · exact valid_set (fun w => i32.valid w = true) _ _ _ (valid_set (fun w => i32.valid w = true) _ _ _ hV.v10 vX11) vX13
    · exact valid_set (fun w => i32.valid w = true) _ _ _ hV.v14 vk
  have hLens' : CapS S (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13) L := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, l7, l8, lsk, lsl, lsr, ?_⟩
    · show L ≤ (b.mxv.set k X4).length; rw [List.length_set]; exact l0
    · show L ≤ (b.smx.set k X6).length; rw [List.length_set]; exact l1
    · show L ≤ (b.mxc.set k X8).length; rw [List.length_set]; exact l2
    · show L ≤ (b.mnv.set k X5).length; rw [List.length_set]; exact l3
    · show L ≤ (b.smn.set k X7).length; rw [List.length_set]; exact l4
    · show L ≤ (b.mnc.set k X9).length; rw [List.length_set]; exact l5
    · show L ≤ (b.len.set k X3).length; rw [List.length_set]; exact l6
    · show L ≤ (b.ent.set ne (k : Int)).length; rw [List.length_set]; exact lent
  have hlo' : L ≤ (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).lo.length := by
    show L ≤ ((b.lo.set (2 * k + 1) X10).set (2 * k + 2) X12).length; simp only [List.length_set]; exact hlo
  have hhi' : L ≤ (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).hi.length := by
    show L ≤ ((b.hi.set (2 * k + 1) X11).set (2 * k + 2) X13).length; simp only [List.length_set]; exact hhi
  refine ⟨ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13, hInv', hLens', hlo', hhi', hVal', fun fu => ?_⟩
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ := WideCtLoop_body mv hnv pre hty hty32 hty15 b a P inf n ne k hinf hnM hneM hkM hV.v0 hV.v1 hV.v2 hV.v3 hV.v4 hV.v5 hV.v6 hV.v9 hV.v10 hV.v14 hAv W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0' (fun _ => hninf) hsc2' hsc4' hsc5' fu
  have hcell : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, X14⟩ : Cell), (⟨i32, X15⟩ : Cell)] : List Cell)
      = CtCells inf n (ne + (if isInnerAt n k then 1 else 0)) (k + 1) := by
    have e14 : X14 = ((ne + (if isInnerAt n k then 1 else 0) : Nat) : Int) := by
      rw [hX14, hX2eq]; split <;> simp
    have e15 : X15 = ((k + 1 : Nat) : Int) := by rw [hX15]; simp
    rw [e14, e15]
  have a3 := pexecM_scope mv fu _ _ _ r0 h0
  have tk : (⟨r0.ps.mem.take (gS P (pre ++ CtCells inf n ne k)).mem.length, r0.ps.bs.take (gS P (pre ++ CtCells inf n ne k)).bs.length⟩ : PS)
      = gS P (pre ++ CtCells inf n (ne + (if isInnerAt n k then 1 else 0)) (k + 1)) := by
    rw [hp0, ← hcell]
    exact scope_take P pre (CtCells inf n ne k) [(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, X14⟩ : Cell), (⟨i32, X15⟩ : Cell)]
      [(⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨i32, (((W0 : Int) + (W1 : Int)) / 2)⟩ : Cell), (⟨u64, (((2 * k + 1) : Nat) : Int)⟩ : Cell), (⟨u64, (((2 * k + 2) : Nat) : Int)⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨i32, X13⟩ : Cell)] (by rfl)
  rw [tk, hv0] at a3
  have a4 := seqM_some a3 hr0 (pexecM_skip mv fu (gS P (pre ++ CtCells inf n (ne + (if isInnerAt n k then 1 else 0)) (k + 1))) (VVA a (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13)))
  refine ⟨_, a4, rfl, rfl, rfl, ?_, ?_⟩
  · simp; omega
  · simp; omega




abbrev WideCtLoop1 (o : Nat) : Command :=
  .whileLoop (.binary bT .lt (.variable i32 (o + 3)) (.binary i32 .mul (.literal i32 4) (.variable i32 (o + 1))))
    (.sequence (.scope (WideCtLoopBody o)) Sk)

theorem ct_loop_wide {S : Nat} (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (inf : Int) (hinfI : inf = INF) (a : List Int) (n L : Nat) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hRange : 4*n < M31)
    (hAlen : a.length = n) (hAv : ∀ w ∈ a, s64.valid w = true) :
    ∀ (d ne k : Nat) (b : BS), k + d = 4 * n → CtInv a n inf b k ne → ValidOK b → CapS S b L → L ≤ b.lo.length → L ≤ b.hi.length →
      ∃ (bf : BS) (nef F : Nat) (r : PRM), F ≤ d + 1 ∧
        pexecM mv F (WideCtLoop1 (mv.nv + pre.length)) (gS P (pre ++ CtCells inf n ne k)) (VVA a b) = some r ∧ r.ret = none ∧
        r.ps = gS P (pre ++ CtCells inf n nef (4 * n)) ∧ r.vv = VVA a bf ∧ r.cost ≤ d * 20620 + 20 ∧ r.wk ≤ d * 12 ∧
        CtInv a n inf bf (4 * n) nef ∧ ValidOK bf ∧ CapS S bf L ∧ L ≤ bf.lo.length ∧ L ≤ bf.hi.length := by
  have hM : M31 = 2147483648 := rfl
  intro d
  induction d with
  | zero =>
    intro ne k b hk hI hV hLens hlo hhi
    have hk' : k = 4 * n := by omega
    subst hk'
    have hc := ct_cond mv hnv P pre (VVA a b) inf n ne (4 * n) (by omega) (by omega)
    rw [ite_eq_right (by omega)] at hc
    refine ⟨b, ne, 1, _, le_refl _, while_exit_p mv 0 _ _ _ _ hc, rfl, rfl, rfl, ?_, ?_, hI, hV, hLens, hlo, hhi⟩
    · simp [vwp, NExpr.nodes]
    · simp
  | succ d ih =>
    intro ne k b hk hI hV hLens hlo hhi
    have hkn : k < 4 * n := by omega
    obtain ⟨b1, hI1, hLens1, hlo1, hhi1, hV1, hit⟩ :=
      ct_iter_wide mv hnv pre hty hty32 hty15 P inf hinfI a n ne k L b hI hV hLens hlo hhi hn hL8 hRange hkn hAlen hAv
    obtain ⟨bf, nef, F, r2, hF, h2, hr2, hp2, hv2, hc2, hw2, hIf, hVf, hLf, hlof, hhif⟩ :=
      ih (ne + (if isInnerAt n k then 1 else 0)) (k + 1) b1 (by omega) hI1 hV1 hLens1 hlo1 hhi1
    obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hw1⟩ := hit (F + 1)
    have hc := ct_cond mv hnv P pre (VVA a b) inf n ne k (by omega) (by omega)
    rw [ite_eq_left (by omega)] at hc
    have h2' : pexecM mv F (WideCtLoop1 (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hp1, hv1]; exact h2
    refine ⟨bf, nef, F + 1, _, by omega, while_step_p mv F _ _ _ _ hc r1 r2 h1 hr1 h2', hr2, hp2, hv2, ?_, ?_, hIf, hVf, hLf, hlof, hhif⟩
    · simp [vwp, NExpr.nodes]; omega
    · simp; omega



end Proofs.BeatsRep
