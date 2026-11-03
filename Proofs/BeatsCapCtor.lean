import Proofs.BeatsCtorRep
import Proofs.BeatsCtorTop
import Proofs.BeatsShape
import Proofs.BeatsRepInv

namespace Proofs.BeatsModel

-- Balanced interval subdivision needs logarithmic stack depth, independently
-- of how many array slots are reserved for heap-indexed nodes.
theorem height_le_power_width (k : Nat) (t : BT) (lo hi : Nat)
    (shape : Shape lo hi t.skel) (width : hi-lo ≤ 2^k) : t.height ≤ k := by
  induction k generalizing t lo hi with
  | zero =>
    cases t with
    | leaf nd => simp [BT.height]
    | node nd tag l r =>
      have separated := shape.1
      simp only [Nat.pow_zero] at width
      omega
  | succ k ih =>
    cases t with
    | leaf nd => simp [BT.height]
    | node nd tag l r =>
      obtain ⟨separated,left,right⟩ := shape
      have halves : (lo+hi)/2-lo ≤ 2^k ∧ hi-(lo+hi)/2 ≤ 2^k := by
        rw [Nat.pow_succ] at width
        omega
      have hl := ih l lo ((lo+hi)/2) left halves.1
      have hr := ih r ((lo+hi)/2) hi right halves.2
      simp only [BT.height]
      omega

end Proofs.BeatsModel

namespace Proofs.BeatsRep
open Proofs.BeatsExec

-- Node and entered arrays use L slots; each DFS frontier array uses S slots.
structure Capacities (b : BS) (L S : Nat) : Prop where
  l0 : L ≤ b.mxv.length
  l1 : L ≤ b.smx.length
  l2 : L ≤ b.mxc.length
  l3 : L ≤ b.mnv.length
  l4 : L ≤ b.smn.length
  l5 : L ≤ b.mnc.length
  l6 : L ≤ b.len.length
  l7 : L ≤ b.ladd.length
  l8 : L ≤ b.lval.length
  lsk : S ≤ b.sk.length
  lsl : S ≤ b.sl.length
  lsr : S ≤ b.sr.length
  lent : L ≤ b.ent.length

theorem Capacities.of_uniform {b : BS} {L : Nat} (h : Lens b L) : Capacities b L L :=
  ⟨h.l0,h.l1,h.l2,h.l3,h.l4,h.l5,h.l6,h.l7,h.l8,h.lsk,h.lsl,h.lsr,h.lent⟩

theorem Capacities.of_same {b b' : BS} {L S : Nat} (h : Capacities b L S)
    (same : SameLen b b') : Capacities b' L S :=
  ⟨by rw [same.l0]; exact h.l0,by rw [same.l1]; exact h.l1,
   by rw [same.l2]; exact h.l2,by rw [same.l3]; exact h.l3,
   by rw [same.l4]; exact h.l4,by rw [same.l5]; exact h.l5,
   by rw [same.l6]; exact h.l6,by rw [same.l7]; exact h.l7,
   by rw [same.l8]; exact h.l8,by rw [same.l11]; exact h.lsk,
   by rw [same.l12]; exact h.lsl,by rw [same.l13]; exact h.lsr,
   by rw [same.l14]; exact h.lent⟩

theorem uniform_not_actual_stack {b : BS} {n L : Nat} (large : 32 ≤ n)
    (nodes : 8*n+8 ≤ L) (stack : b.sk.length = 256) : ¬Lens b L := by
  intro h
  have enough := h.lsk
  omega

theorem actual_stack_budget (t : Proofs.BeatsModel.BT) (n : Nat)
    (shape : Proofs.BeatsModel.Shape 0 n t.skel) (size : n < 2147483648) :
    1+t.height+2 ≤ 256 := by
  have bound := Proofs.BeatsModel.height_le_power_width 31 t 0 n shape
    (by change n-0 ≤ 2147483648; omega)
  omega

end Proofs.BeatsRep

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
abbrev CapS (S : Nat) (b : BS) (L : Nat) := Capacities b L S
theorem ct_iter_separate {S : Nat} (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (inf : Int) (hinfI : inf = INF) (a : List Int) (n ne k L : Nat) (b : BS) (hI : CtInv a n inf b k ne) (hV : ValidOK b)
    (hLens : CapS S b L) (hlo : L ≤ b.lo.length) (hhi : L ≤ b.hi.length) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hLM : L < M31)
    (hkn : k < 4 * n) (hAlen : a.length = n) (hAv : ∀ w ∈ a, s64.valid w = true) :
    ∃ b' : BS, CtInv a n inf b' (k + 1) (ne + (if isInnerAt n k then 1 else 0)) ∧ CapS S b' L ∧ L ≤ b'.lo.length ∧ L ≤ b'.hi.length ∧ ValidOK b' ∧
      ∀ fu : Nat, ∃ r : PRM, pexecM mv fu (.sequence (.scope (CtLoopBody (mv.nv + pre.length))) Sk)
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
  have hD_W0 : b.lo.getD k 0 = (W0 : Int) := by rw [hI.hlo k, if_pos (by omega), hW0]
  have hD_W1 : b.hi.getD k 0 = (W1 : Int) := by rw [hI.hhi k, if_pos (by omega), hW1]
  obtain ⟨W10, hNW10, hD_W10⟩ : ∃ W : Nat, W < M31 ∧ b.lo.getD (2 * k + 1) 0 = (W : Int) := ⟨0, by omega, by rw [hI.hlo, if_neg (by omega)]⟩
  obtain ⟨W11, hNW11, hD_W11⟩ : ∃ W : Nat, W < M31 ∧ b.hi.getD (2 * k + 1) 0 = (W : Int) := ⟨0, by omega, by rw [hI.hhi, if_neg (by omega)]⟩
  obtain ⟨W12, hNW12, hD_W12⟩ : ∃ W : Nat, W < M31 ∧ b.lo.getD (2 * k + 2) 0 = (W : Int) := ⟨0, by omega, by rw [hI.hlo, if_neg (by omega)]⟩
  obtain ⟨W13, hNW13, hD_W13⟩ : ∃ W : Nat, W < M31 ∧ b.hi.getD (2 * k + 2) 0 = (W : Int) := ⟨0, by omega, by rw [hI.hhi, if_neg (by omega)]⟩
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
  have hk1_k : (2 * k + 1) < M31 := by omega
  have hk2_k : (2 * k + 2) < M31 := by omega
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
  have hsc0' : i32.valid ((W1 : Int) - (W0 : Int)) = true := by simp only [Ty.valid, i32]; simp; omega
  have hsc2' : i32.valid ((W0 : Int) + (W1 : Int)) = true := by simp only [Ty.valid, i32]; simp; omega
  have hsc4' : i32.valid ((ne : Int) + X2) = true := by simp only [Ty.valid, i32]; simp; omega
  have hsc5' : i32.valid ((k : Int) + 1) = true := by simp only [Ty.valid, i32]; simp; omega
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
  have hmid : i32.valid (((W0 : Int) + (W1 : Int)) / 2) = true := by simp only [Ty.valid, i32]; simp; omega
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
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ := CtLoop_body mv hnv pre hty hty32 hty15 b a P inf n ne k hinf hnM hneM hkM hV.v0 hV.v1 hV.v2 hV.v3 hV.v4 hV.v5 hV.v6 hV.v9 hV.v10 hV.v14 hAv W0 hNW0 hD_W0 W1 hNW1 hD_W1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 W10 hNW10 hD_W10 W11 hNW11 hD_W11 W12 hNW12 hD_W12 W13 hNW13 hD_W13 hl9_0 hl10_1 hl6_2 hl15_3 hl0_4 hl3_5 hl1_6 hl4_7 hl2_8 hl5_9 hl9_10 hl10_11 hl9_12 hl10_13 hl14_14 hk1_k hk2_k X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 hsc0' (fun _ => hninf) hsc2' hsc4' hsc5' fu
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
      [(⟨i32, (W0 : Int)⟩ : Cell), (⟨i32, (W1 : Int)⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨s64, ((W1 : Int) - (W0 : Int))⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, X4⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X6⟩ : Cell), (⟨s64, X7⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨i32, (((W0 : Int) + (W1 : Int)) / 2)⟩ : Cell), (⟨i32, (((2 * k + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * k + 2) : Nat) : Int)⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨i32, X13⟩ : Cell)] (by rfl)
  rw [tk, hv0] at a3
  have a4 := seqM_some a3 hr0 (pexecM_skip mv fu (gS P (pre ++ CtCells inf n (ne + (if isInnerAt n k then 1 else 0)) (k + 1))) (VVA a (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13)))
  refine ⟨_, a4, rfl, rfl, rfl, ?_, ?_⟩
  · simp; omega
  · simp; omega



theorem ct_loop_separate {S : Nat} (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (inf : Int) (hinfI : inf = INF) (a : List Int) (n L : Nat) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hLM : L < M31)
    (hAlen : a.length = n) (hAv : ∀ w ∈ a, s64.valid w = true) :
    ∀ (d ne k : Nat) (b : BS), k + d = 4 * n → CtInv a n inf b k ne → ValidOK b → CapS S b L → L ≤ b.lo.length → L ≤ b.hi.length →
      ∃ (bf : BS) (nef F : Nat) (r : PRM), F ≤ d + 1 ∧
        pexecM mv F (CtLoop1 (mv.nv + pre.length)) (gS P (pre ++ CtCells inf n ne k)) (VVA a b) = some r ∧ r.ret = none ∧
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
    rw [if_neg (by omega)] at hc
    refine ⟨b, ne, 1, _, le_refl _, while_exit_p mv 0 _ _ _ _ hc, rfl, rfl, rfl, ?_, ?_, hI, hV, hLens, hlo, hhi⟩
    · simp [vwp, NExpr.nodes]
    · simp
  | succ d ih =>
    intro ne k b hk hI hV hLens hlo hhi
    have hkn : k < 4 * n := by omega
    obtain ⟨b1, hI1, hLens1, hlo1, hhi1, hV1, hit⟩ :=
      ct_iter_separate mv hnv pre hty hty32 hty15 P inf hinfI a n ne k L b hI hV hLens hlo hhi hn hL8 hLM hkn hAlen hAv
    obtain ⟨bf, nef, F, r2, hF, h2, hr2, hp2, hv2, hc2, hw2, hIf, hVf, hLf, hlof, hhif⟩ :=
      ih (ne + (if isInnerAt n k then 1 else 0)) (k + 1) b1 (by omega) hI1 hV1 hLens1 hlo1 hhi1
    obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hw1⟩ := hit (F + 1)
    have hc := ct_cond mv hnv P pre (VVA a b) inf n ne k (by omega) (by omega)
    rw [if_pos (by omega)] at hc
    have h2' : pexecM mv F (CtLoop1 (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hp1, hv1]; exact h2
    refine ⟨bf, nef, F + 1, _, by omega, while_step_p mv F _ _ _ _ hc r1 r2 h1 hr1 h2', hr2, hp2, hv2, ?_, ?_, hIf, hVf, hLf, hlof, hhif⟩
    · simp [vwp, NExpr.nodes]; omega
    · simp; omega


theorem ct_upd_iter_separate {S : Nat} (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32)
    (hty15 : mv.ty 15 = s64) (b : BS) (A : List Int) (P : List Cell) (inf : Int) (n ne k : Nat) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hneM : ne < M31) (hkM : k < M31)
    (L : Nat) (hV : ValidOK b) (hLens : CapS S b L) (hLM : L < M31) (e : Nat) (E : List Nat) (hent : EntRep b ne (e :: E))
    (he : 2 * e + 2 < L) (hneL : ne ≤ L)
    (hmc : s64.valid (b.mxc.getD (2 * e + 1) 0 + b.mxc.getD (2 * e + 2) 0) = true)
    (hnc : s64.valid (b.mnc.getD (2 * e + 1) 0 + b.mnc.getD (2 * e + 2) 0) = true) (H : Heap) (hH : HRel inf b H) :
    ∃ b' : BS, HRel inf b' (updateH H e) ∧ EntRep b' (ne - 1) E ∧ ValidOK b' ∧ SameLen b b' ∧ b'.sk = b.sk ∧ b'.sl = b.sl ∧ b'.sr = b.sr ∧
      ∀ fu : Nat, ∃ r : PRM, pexecM mv fu (.sequence (.scope (CtUpdBody (mv.nv + pre.length))) Sk)
        (gS P (pre ++ CtCells inf n ne k)) (VVA A b) = some r ∧ r.ret = none ∧
        r.ps = gS P (pre ++ CtCells inf n (ne - 1) k) ∧ r.vv = VVA A b' ∧ r.cost ≤ 24790 ∧ r.wk ≤ 6 := by
  classical
  have hpos : 0 < ne := by have := hent.1; simp at this; omega
  have hDe : b.ent.getD (ne - 1) 0 = (e : Int) := by simpa using hent.2 0 e rfl
  have hl := hLens
  have hk1 : 2 * e + 1 < M31 := by omega
  have hk2 : 2 * e + 2 < M31 := by omega
  have hNe : e < M31 := by omega

  obtain ⟨Z1, hD_Z1⟩ : ∃ Z1 : Int, b.mxv.getD (2 * e + 1) 0 = Z1 := ⟨_, rfl⟩
  obtain ⟨Z2, hD_Z2⟩ : ∃ Z2 : Int, b.mxv.getD (2 * e + 2) 0 = Z2 := ⟨_, rfl⟩
  obtain ⟨Z3, hD_Z3⟩ : ∃ Z3 : Int, b.smx.getD (2 * e + 1) 0 = Z3 := ⟨_, rfl⟩
  obtain ⟨Z4, hD_Z4⟩ : ∃ Z4 : Int, b.smx.getD (2 * e + 2) 0 = Z4 := ⟨_, rfl⟩
  obtain ⟨Z5, hD_Z5⟩ : ∃ Z5 : Int, b.mxc.getD (2 * e + 1) 0 = Z5 := ⟨_, rfl⟩
  obtain ⟨Z6, hD_Z6⟩ : ∃ Z6 : Int, b.mxc.getD (2 * e + 2) 0 = Z6 := ⟨_, rfl⟩
  obtain ⟨Z7, hD_Z7⟩ : ∃ Z7 : Int, b.mnv.getD (2 * e + 1) 0 = Z7 := ⟨_, rfl⟩
  obtain ⟨Z8, hD_Z8⟩ : ∃ Z8 : Int, b.mnv.getD (2 * e + 2) 0 = Z8 := ⟨_, rfl⟩
  obtain ⟨Z9, hD_Z9⟩ : ∃ Z9 : Int, b.smn.getD (2 * e + 1) 0 = Z9 := ⟨_, rfl⟩
  obtain ⟨Z10, hD_Z10⟩ : ∃ Z10 : Int, b.smn.getD (2 * e + 2) 0 = Z10 := ⟨_, rfl⟩
  obtain ⟨Z11, hD_Z11⟩ : ∃ Z11 : Int, b.mnc.getD (2 * e + 1) 0 = Z11 := ⟨_, rfl⟩
  obtain ⟨Z12, hD_Z12⟩ : ∃ Z12 : Int, b.mnc.getD (2 * e + 2) 0 = Z12 := ⟨_, rfl⟩
  have vZ1 : s64.valid Z1 = true := by rw [← hD_Z1]; exact getD_mem_valid b.mxv _ (by have := hl.l0; omega) hV.v0
  have vZ2 : s64.valid Z2 = true := by rw [← hD_Z2]; exact getD_mem_valid b.mxv _ (by have := hl.l0; omega) hV.v0
  have vZ3 : s64.valid Z3 = true := by rw [← hD_Z3]; exact getD_mem_valid b.smx _ (by have := hl.l1; omega) hV.v1
  have vZ4 : s64.valid Z4 = true := by rw [← hD_Z4]; exact getD_mem_valid b.smx _ (by have := hl.l1; omega) hV.v1
  have vZ5 : s64.valid Z5 = true := by rw [← hD_Z5]; exact getD_mem_valid b.mxc _ (by have := hl.l2; omega) hV.v2
  have vZ6 : s64.valid Z6 = true := by rw [← hD_Z6]; exact getD_mem_valid b.mxc _ (by have := hl.l2; omega) hV.v2
  have vZ7 : s64.valid Z7 = true := by rw [← hD_Z7]; exact getD_mem_valid b.mnv _ (by have := hl.l3; omega) hV.v3
  have vZ8 : s64.valid Z8 = true := by rw [← hD_Z8]; exact getD_mem_valid b.mnv _ (by have := hl.l3; omega) hV.v3
  have vZ9 : s64.valid Z9 = true := by rw [← hD_Z9]; exact getD_mem_valid b.smn _ (by have := hl.l4; omega) hV.v4
  have vZ10 : s64.valid Z10 = true := by rw [← hD_Z10]; exact getD_mem_valid b.smn _ (by have := hl.l4; omega) hV.v4
  have vZ11 : s64.valid Z11 = true := by rw [← hD_Z11]; exact getD_mem_valid b.mnc _ (by have := hl.l5; omega) hV.v5
  have vZ12 : s64.valid Z12 = true := by rw [← hD_Z12]; exact getD_mem_valid b.mnc _ (by have := hl.l5; omega) hV.v5
  rw [hD_Z5, hD_Z6] at hmc
  rw [hD_Z11, hD_Z12] at hnc
  obtain ⟨X0, hX0⟩ : ∃ X0 : Int, X0 = (if (Z1 < Z2) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ X1 : Int, X1 = (if (Z1 > Z2) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ X2 : Int, X2 = (if (Z1 = Z2) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X3, hX3⟩ : ∃ X3 : Int, X3 = (if (X0 = 1) then Z2 else Z1) := ⟨_, rfl⟩
  obtain ⟨X4, hX4⟩ : ∃ X4 : Int, X4 = (if (X0 = 1) then Z6 else Z5) := ⟨_, rfl⟩
  obtain ⟨X5, hX5⟩ : ∃ X5 : Int, X5 = (if (X2 = 1) then (Z5 + Z6) else X4) := ⟨_, rfl⟩
  obtain ⟨X6, hX6⟩ : ∃ X6 : Int, X6 = (if (X0 = 1) then Z1 else Z3) := ⟨_, rfl⟩
  obtain ⟨X7, hX7⟩ : ∃ X7 : Int, X7 = (if (X1 = 1) then Z2 else X6) := ⟨_, rfl⟩
  obtain ⟨X8, hX8⟩ : ∃ X8 : Int, X8 = (if (X1 = 1) then Z3 else Z4) := ⟨_, rfl⟩
  obtain ⟨X9, hX9⟩ : ∃ X9 : Int, X9 = (if (X7 < X8) then X8 else X7) := ⟨_, rfl⟩
  obtain ⟨X10, hX10⟩ : ∃ X10 : Int, X10 = (if (Z7 < Z8) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X11, hX11⟩ : ∃ X11 : Int, X11 = (if (Z7 > Z8) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X12, hX12⟩ : ∃ X12 : Int, X12 = (if (Z7 = Z8) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X13, hX13⟩ : ∃ X13 : Int, X13 = (if (X11 = 1) then Z8 else Z7) := ⟨_, rfl⟩
  obtain ⟨X14, hX14⟩ : ∃ X14 : Int, X14 = (if (X11 = 1) then Z12 else Z11) := ⟨_, rfl⟩
  obtain ⟨X15, hX15⟩ : ∃ X15 : Int, X15 = (if (X12 = 1) then (Z11 + Z12) else X14) := ⟨_, rfl⟩
  obtain ⟨X16, hX16⟩ : ∃ X16 : Int, X16 = (if (X10 = 1) then Z8 else Z9) := ⟨_, rfl⟩
  obtain ⟨X17, hX17⟩ : ∃ X17 : Int, X17 = (if (X11 = 1) then Z7 else X16) := ⟨_, rfl⟩
  obtain ⟨X18, hX18⟩ : ∃ X18 : Int, X18 = (if (X10 = 1) then Z9 else Z10) := ⟨_, rfl⟩
  obtain ⟨X19, hX19⟩ : ∃ X19 : Int, X19 = (if (X18 < X17) then X18 else X17) := ⟨_, rfl⟩
  have vX0 : s64.valid X0 = true := by rw [hX0]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX1 : s64.valid X1 = true := by rw [hX1]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX2 : s64.valid X2 = true := by rw [hX2]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX3 : s64.valid X3 = true := by rw [hX3]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX4 : s64.valid X4 = true := by rw [hX4]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX5 : s64.valid X5 = true := by rw [hX5]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX6 : s64.valid X6 = true := by rw [hX6]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX7 : s64.valid X7 = true := by rw [hX7]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX8 : s64.valid X8 = true := by rw [hX8]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX9 : s64.valid X9 = true := by rw [hX9]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX10 : s64.valid X10 = true := by rw [hX10]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX11 : s64.valid X11 = true := by rw [hX11]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX12 : s64.valid X12 = true := by rw [hX12]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX13 : s64.valid X13 = true := by rw [hX13]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX14 : s64.valid X14 = true := by rw [hX14]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX15 : s64.valid X15 = true := by rw [hX15]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX16 : s64.valid X16 = true := by rw [hX16]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX17 : s64.valid X17 = true := by rw [hX17]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX18 : s64.valid X18 = true := by rw [hX18]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX19 : s64.valid X19 = true := by rw [hX19]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have key : (⟨X3, X9, X5, X13, X19, X15⟩ : Nd) = mergeNd ⟨Z1, Z3, Z5, Z7, Z9, Z11⟩ ⟨Z2, Z4, Z6, Z8, Z10, Z12⟩ := by
    subst hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13 hX14 hX15 hX16 hX17 hX18 hX19
    unfold mergeNd mergeMax negNd
    simp only [Nd.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [Int.neg_neg, Prod.fst, Prod.snd])
    all_goals (repeat' split)
    all_goals simp only []
    all_goals omega
  have hc1 : (H (2 * e + 1)).1 = ⟨Z1, Z3, Z5, Z7, Z9, Z11⟩ := by
    rw [← (hH _).1]; unfold decNd; rw [hD_Z1, hD_Z3, hD_Z5, hD_Z7, hD_Z9, hD_Z11]
  have hc2 : (H (2 * e + 2)).1 = ⟨Z2, Z4, Z6, Z8, Z10, Z12⟩ := by
    rw [← (hH _).1]; unfold decNd; rw [hD_Z2, hD_Z4, hD_Z6, hD_Z8, hD_Z10, hD_Z12]
  have hUC := HRel_UCl inf b H e hH (by have := hl.l0; omega) (by have := hl.l1; omega) (by have := hl.l2; omega) (by have := hl.l3; omega)
    (by have := hl.l4; omega) (by have := hl.l5; omega) X3 X5 X9 X13 X15 X19 (by rw [hc1, hc2]; exact key)
  have hvalid := UCl_valid b e X3 X5 X9 X13 X15 X19 hV vX3 vX5 vX9 vX13 vX15 vX19
  refine ⟨UCl b e X3 X5 X9 X13 X15 X19, hUC, ?_, hvalid, UCl_sameLen b e _ _ _ _ _ _, rfl, rfl, rfl, ?_⟩
  · refine ⟨by have := hent.1; simp at this ⊢; omega, ?_⟩
    intro j e' hj
    have h1 := hent.2 (j + 1) e' (by simpa using hj)
    rw [UCl_ent]
    have : ne - 1 - 1 - j = ne - 1 - (j + 1) := by omega
    rw [this]
    exact h1
  · intro fu
    obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ := CtUpd_body mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM hneM hkM hpos hV.v0 hV.v1 hV.v2 hV.v3 hV.v4 hV.v5 hV.v14 e hNe hDe Z1 hD_Z1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 (by have := hl.lent; omega) (by have := hl.l0; omega) (by have := hl.l0; omega) (by have := hl.l1; omega) (by have := hl.l1; omega) (by have := hl.l2; omega) (by have := hl.l2; omega) (by have := hl.l0; omega) (by have := hl.l2; omega) (by have := hl.l1; omega) (by have := hl.l3; omega) (by have := hl.l3; omega) (by have := hl.l4; omega) (by have := hl.l4; omega) (by have := hl.l5; omega) (by have := hl.l5; omega) (by have := hl.l3; omega) (by have := hl.l5; omega) (by have := hl.l4; omega) hk1 hk2 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 (by rw [sub_one_cast _ hpos]; exact i32_valid_nat _ (by omega)) (fun _ => hmc) (fun _ => hnc) fu
    have a3 := pexecM_scope mv fu _ _ _ r0 h0
    have tk : (⟨r0.ps.mem.take (gS P (pre ++ CtCells inf n ne k)).mem.length,
        r0.ps.bs.take (gS P (pre ++ CtCells inf n ne k)).bs.length⟩ : PS) = gS P (pre ++ CtCells inf n (ne - 1) k) := by
      rw [hp0]; exact scope_take P pre (CtCells inf n ne k) (CtCells inf n (ne - 1) k) [(⟨i32, (e : Int)⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (e : Int)⟩ : Cell), (⟨i32, (((2 * e + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * e + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z1⟩ : Cell), (⟨s64, Z2⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, Z10⟩ : Cell), (⟨s64, Z11⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X18⟩ : Cell)] (by rfl)
    rw [tk, hv0] at a3
    have a4 := seqM_some a3 hr0 (pexecM_skip mv fu (gS P (pre ++ CtCells inf n (ne - 1) k)) (VVA A (UCl b e X3 X5 X9 X13 X15 X19)))
    refine ⟨_, a4, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · simp; omega
    · simp; omega

theorem ct_upd_all_separate {S : Nat} (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32)
    (hty15 : mv.ty 15 = s64) (P : List Cell) (inf : Int) (n k : Nat) (A : List Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hkM : k < M31) (L : Nat) (hLM : L < M31) :
    ∀ (E : List Nat) (b : BS) (ne : Nat) (H : Heap), EntRep b ne E → ValidOK b → CapS S b L → (∀ e ∈ E, 2 * e + 2 < L) → ne ≤ L →
      SumsOK E H → HRel inf b H →
      ∃ b' : BS, ∃ F, F ≤ E.length + 1 ∧
        CtRunsU mv F P pre inf n k A b ne (gS P (pre ++ CtCells inf n 0 k)) (VVA A b') (E.length * 24794 + 4) (E.length * 6) ∧
        HRel inf b' (upPhase E H) ∧ ValidOK b' ∧ SameLen b b' ∧ b'.sk = b.sk ∧ b'.sl = b.sl ∧ b'.sr = b.sr := by
  intro E
  induction E with
  | nil =>
    intro b ne H hent hV hLens hE hne hS hH
    have h0 : ne = 0 := by have := hent.1; simp at this; omega
    subst h0
    refine ⟨b, 0 + 1, by simp, ?_, hH, hV, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
    simpa using ctRunsU_exit mv hnv 0 P pre inf n k A b
  | cons e E ih =>
    intro b ne H hent hV hLens hE hne hS hH
    have hne0 : 0 < ne := by have := hent.1; simp at this; omega
    have hS1 : SumOK H e := hS.1
    have hmc : s64.valid (b.mxc.getD (2 * e + 1) 0 + b.mxc.getD (2 * e + 2) 0) = true := by
      have a := (hH (2 * e + 1)).1; have c := (hH (2 * e + 2)).1
      have h1 := hS1.1; rw [← a, ← c] at h1; exact h1
    have hnc : s64.valid (b.mnc.getD (2 * e + 1) 0 + b.mnc.getD (2 * e + 2) 0) = true := by
      have a := (hH (2 * e + 1)).1; have c := (hH (2 * e + 2)).1
      have h1 := hS1.2; rw [← a, ← c] at h1; exact h1
    obtain ⟨b1, hH1, hent1, hV1, hSL1, hsk1, hsl1, hsr1, hit⟩ :=
      ct_upd_iter_separate mv hnv pre hty hty32 hty15 b A P inf n ne k hinf hnM (by omega) hkM L hV hLens hLM e E hent
        (hE e (by simp)) hne hmc hnc H hH
    obtain ⟨b2, F, hF, hrun, hH2, hV2, hSL2, hsk2, hsl2, hsr2⟩ :=
      ih b1 (ne - 1) (updateH H e) hent1 hV1 (Capacities.of_same hLens hSL1) (fun e' he' => hE e' (by simp [he'])) (by omega) hS.2 hH1
    refine ⟨b2, F + 1, by simp at hF ⊢; omega, ?_, ?_, hV2, ?_, ?_, ?_, ?_⟩
    · obtain ⟨r1, h1, hret, hps, hvv, hc, hw⟩ := hit (F + 1)
      have := ctRunsU_step mv hnv F P pre inf n k A b b1 ne (ne - 1) (by omega) hne0 r1 h1 hret hps hvv 24790 6 hc hw _ _ _ _ hrun
      refine ctRunsU_weaken_p this ?_ ?_ <;> simp <;> omega
    · rw [upPhase_cons]; exact hH2
    · exact ⟨by rw [hSL2.l0, hSL1.l0], by rw [hSL2.l1, hSL1.l1], by rw [hSL2.l2, hSL1.l2], by rw [hSL2.l3, hSL1.l3],
        by rw [hSL2.l4, hSL1.l4], by rw [hSL2.l5, hSL1.l5], by rw [hSL2.l6, hSL1.l6], by rw [hSL2.l7, hSL1.l7],
        by rw [hSL2.l8, hSL1.l8], by rw [hSL2.l9, hSL1.l9], by rw [hSL2.l10, hSL1.l10], by rw [hSL2.l11, hSL1.l11],
        by rw [hSL2.l12, hSL1.l12], by rw [hSL2.l13, hSL1.l13], by rw [hSL2.l14, hSL1.l14], by rw [hSL2.leneq, hSL1.leneq]⟩
    · rw [hsk2, hsk1]
    · rw [hsl2, hsl1]
    · rw [hsr2, hsr1]


theorem ct_exec_separate {S : Nat} (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (a : List Int) (n L : Nat) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hLM : L < M31) (hAlen : a.length = n) (hAr : InRange a)
    (b0 : BS) (hV0 : ValidOK b0) (hLens0 : CapS S b0 L) (hlo0 : L ≤ b0.lo.length) (hhi0 : L ≤ b0.hi.length)
    (h0 : ∀ j, b0.mxv.getD j 0 = 0) (h1 : ∀ j, b0.smx.getD j 0 = 0) (h2 : ∀ j, b0.mxc.getD j 0 = 0) (h3 : ∀ j, b0.mnv.getD j 0 = 0)
    (h4 : ∀ j, b0.smn.getD j 0 = 0) (h5 : ∀ j, b0.mnc.getD j 0 = 0) (h6 : ∀ j, b0.len.getD j 0 = 0) (h7 : ∀ j, b0.ladd.getD j 0 = 0)
    (h8 : ∀ j, j < b0.lval.length → b0.lval.getD j 0 = INF) (h9 : ∀ j, b0.lo.getD j 0 = 0) (h10 : ∀ j, b0.hi.getD j 0 = 0) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F (CtorCmd (mv.nv + pre.length)) (gS P (pre ++ [])) (VVA a b0) = some r ∧ r.ret = none ∧
      r.ps = gS P (pre ++ CtCells INF n 0 (4 * n)) ∧ r.vv = VVA a bf ∧
      HRel INF bf Hf ∧ Agree Hf (buildBT a 0 n) 0 ∧ ValidOK bf ∧ CapS S bf L ∧ L ≤ bf.lo.length ∧ L ≤ bf.hi.length ∧
      LenOK bf (buildBT a 0 n) 0 0 n ∧ r.cost ≤ 4 * n * 45414 + 100 ∧ r.wk ≤ 4 * n * 18 + 10 := by
  classical
  have hM : M31 = 2147483648 := rfl
  have hinfV : s64.valid INF = true := s64_valid_of_bounds _ (by unfold INF; omega) (by unfold INF; omega)
  have hninfV : s64.valid (-INF) = true := s64_valid_of_bounds _ (by unfold INF; omega) (by unfold INF; omega)
  have hAv : ∀ w ∈ a, s64.valid w = true := fun w hw => s64_valid_of_bounds _ (by have := (hAr w hw).1; unfold INF at *; omega) (by have := (hAr w hw).2; unfold INF at *; omega)
  have hhl : 0 < b0.hi.length := by omega
  have hI1 := ct_init_inv a n INF hn b0 hhl h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨b1, hb1⟩ : ∃ b1 : BS, b1 = { b0 with hi := b0.hi.set 0 (n : Int) } := ⟨_, rfl⟩
  rw [← hb1] at hI1
  have hV1 : ValidOK b1 := by
    subst hb1
    refine ⟨hV0.v0, hV0.v1, hV0.v2, hV0.v3, hV0.v4, hV0.v5, hV0.v6, hV0.v7, hV0.v8, hV0.v9, ?_, hV0.v11, hV0.v12, hV0.v13, hV0.v14⟩
    exact valid_set (fun w => i32.valid w = true) _ _ _ hV0.v10 (Proofs.BellmanFordExec.i32_valid_nat n (by omega))
  have hLens1 : CapS S b1 L := by
    subst hb1
    exact ⟨hLens0.l0, hLens0.l1, hLens0.l2, hLens0.l3, hLens0.l4, hLens0.l5, hLens0.l6, hLens0.l7, hLens0.l8, hLens0.lsk, hLens0.lsl, hLens0.lsr, hLens0.lent⟩
  have hlo1 : L ≤ b1.lo.length := by subst hb1; exact hlo0
  have hhi1 : L ≤ b1.hi.length := by subst hb1; show L ≤ (b0.hi.set 0 (n : Int)).length; rw [List.length_set]; exact hhi0
  obtain ⟨bf, nef, F1, r1, hF1, hl1, hr1, hp1, hv1, hc1, hw1, hIf, hVf, hLf, hlof, hhif⟩ :=
    ct_loop_separate mv hnv pre hty hty32 hty15 P INF rfl a n L hn hL8 hLM hAlen hAv (4 * n) 0 0 b1 (by omega) hI1 hV1 hLens1 hlo1 hhi1
  -- the update loop
  have hl8 := hLf.l8
  have hLv : 4 * n ≤ bf.lval.length := by omega
  have hHR := ct_hrel a n INF rfl hn bf nef hIf hLv
  have hEmem : ∀ e ∈ LLr n (4 * n), 2 * e + 2 < L := fun e he => by have := (mem_LLr n _ e he).2; omega
  have hne : nef ≤ L := by have := hIf.hent.1; have := LLr_length_le n (4 * n); omega
  have hSC := phase2_sums a n hn hAr hAlen (by omega) (4 * n) 0 (by omega)
  rw [XX_zero] at hSC
  have hS := SumsOK_lift bf.lval.length (LLr n (4 * n)) (C0 a n) (fun e he => by have := hEmem e he; omega) hSC
  obtain ⟨b2, F2, hF2, hrun2, hH2, hV2, hSL2, hsk2, hsl2, hsr2⟩ :=
    ct_upd_all_separate mv hnv pre hty hty32 hty15 P INF n (4 * n) a hinfV (by omega) (by omega) L hLM (LLr n (4 * n)) bf nef _ hIf.hent hVf hLf hEmem hne hS hHR
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hw2⟩ := hrun2
  have h1' := pexecM_mono mv _ _ _ r1 F1 F2 hl1
  have h2' := pexecM_mono mv _ _ _ r2 F2 F1 h2
  rw [Nat.add_comm F2 F1] at h2'
  have h2'' : pexecM mv (F1 + F2) (CtULoop (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hp1, hv1]; exact h2'
  have hseq6 := seqM_some h2'' hr2 (pexecM_skip mv (F1 + F2) r2.ps r2.vv)
  have hseq5 := seqM_some h1' hr1 hseq6
  obtain ⟨R5, hR5, hR5ret, hR5ps, hR5vv, hR5c, hR5w⟩ : ∃ R : PRM, pexecM mv (F1 + F2)
      (.sequence (CtLoop1 (mv.nv + pre.length)) (.sequence (CtULoop (mv.nv + pre.length)) Sk)) (gS P (pre ++ CtCells INF n 0 0)) (VVA a b1) = some R ∧
      R.ret = none ∧ R.ps = r2.ps ∧ R.vv = r2.vv ∧ R.cost ≤ r1.cost + r2.cost ∧ R.wk ≤ r1.wk + r2.wk :=
    ⟨_, hseq5, by simpa using hr2, rfl, rfl, by simp, by simp⟩
  -- the initialisation statements (innermost first)
  have hFF : (0 : Nat) = 0 := rfl
  obtain ⟨R4, hR4, hR4ret, hR4ps, hR4vv, hR4c, -, hR4w⟩ := seq_decl mv (F1 + F2) P (pre ++ [cs INF, ci n, ci 0]) (VVA a b1) i32 (.literal i32 0) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 0 (by decide)) _ _ (by rw [List.append_assoc]; exact hR5) hR5ret
  obtain ⟨R3, hR3, hR3ret, hR3ps, hR3vv, hR3c, -, hR3w⟩ := seq_decl mv (F1 + F2) P (pre ++ [cs INF, ci n]) (VVA a b1) i32 (.literal i32 0) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 0 (by decide)) _ _ (by rw [List.append_assoc]; exact hR4) hR4ret
  have hv15 : VVA a b0 15 = a := VVA_get15 a b0
  have hvx : vdenM mv (VVA a b0) (penvN mv.nv (gS P (pre ++ [cs INF, ci n]))) (.variable i32 (mv.nv + pre.length + 1)) = some (n : Int) :=
    den_cellvar_t mv P _ i32 (pre.length + 1) _ (by omega) (n : Int) (cell_at0 pre [cs INF, ci n] 1 (ci n) rfl)
      (Proofs.BellmanFordExec.i32_valid_nat n (by omega)) (VVA a b0)
  obtain ⟨Rw, hRw, hRwret, hRwps, hRwvv, hRwc, -, hRww⟩ := seq_write mv (F1 + F2) (gS P (pre ++ [cs INF, ci n])) (VVA a b0) 10 (by omega) i32
    (hty32 10 (by decide) (by decide)) (.cast u64 (.literal i32 0)) (.variable i32 (mv.nv + pre.length + 1)) (n : Int) 0 hvx
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact den_idx_lit0 mv P _)
    (by rw [VVA_get10]; omega) (Proofs.BellmanFordExec.i32_valid_nat n (by omega)) _ _
    (by rw [VVA_get10, VVA_upd10, ← hb1]; exact hR3) hR3ret _ le_rfl _ le_rfl
  obtain ⟨R1, hR1, hR1ret, hR1ps, hR1vv, hR1c, -, hR1w⟩ := seq_decl mv (F1 + F2) P (pre ++ [cs INF]) (VVA a b0) i32
    (.cast i32 (.size (.integer s64) (.local 15))) (n : Int) (n : Int)
    (by have := ct_size_val mv hnv hty15 (VVA a b0) (penvN mv.nv (gS P (pre ++ [cs INF]))) (by rw [hv15]; omega)
        rw [hv15, hAlen] at this; exact this)
    (conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat n (by omega))) _ _ (by rw [List.append_assoc]; exact hRw) hRwret
  obtain ⟨R0, hR0, hR0ret, hR0ps, hR0vv, hR0c, -, hR0w⟩ := seq_decl mv (F1 + F2) P (pre ++ []) (VVA a b0) s64
    (.literal s64 4000000000000000000) INF INF
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show s64.valid 4000000000000000000 = true from hinfV)]; rfl) (conv_s64 _ hinfV) _ _ (by rw [List.append_assoc]; exact hR1) hR1ret
  have hT := buildBT_spec a hAr n 0 n (by omega) (by omega) (by omega)
  have h0rng : rngOf n 0 = (0, n) := by simp [rngOf]
  have hsub : ∀ j nd otg, sub2 (buildBT a 0 n) 0 j = some (nd, otg) → j < bf.lval.length := by
    intro j nd otg hj
    obtain ⟨hs, -, -⟩ := sub2_build a n (n - 0) 0 n 0 rfl (by omega) h0rng j nd otg hj
    have := skel_lt n hn j hs
    omega
  have hAg := agree_lift bf.lval.length _ _ (agree_final a n hn) hsub
  refine ⟨b2, upPhase (LLr n (4 * n)) (Hlift bf.lval.length (C0 a n)), F1 + F2, R0, hR0, hR0ret, ?_, ?_, hH2, ?_, hV2, Capacities.of_same hLf hSL2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR0ps, hR1ps, hRwps, hR3ps, hR4ps, hR5ps, hp2]
  · rw [hR0vv, hR1vv, hRwvv, hR3vv, hR4vv, hR5vv, hv2]
  · rw [upPhase_lift _ _ _ (fun e he => by have := hEmem e he; omega)]; exact hAg
  · have := hSL2.l9; omega
  · have := hSL2.l10; omega
  · have hsk : Shape 0 n (buildBT a 0 n).skel := hT.2
    exact LenOKs_of_eq hSL2.leneq _ _ _ _ (lenOK_build n hn a INF bf nef hIf _ 0 0 n hsk h0rng)

  · have hl := LLr_length_le n (4 * n)
    obtain ⟨m, hm⟩ : ∃ m, m = (LLr n (4 * n)).length := ⟨_, rfl⟩
    have h3 : m * 24794 ≤ 4 * n * 24794 := Nat.mul_le_mul_right _ (hm ▸ hl)
    rw [← hm] at hc2
    have e1 : (vwp (NExpr.cast i32 (.size (.integer s64) (.local 15)))).1 ≤ 10 := by decide
    have e2 : 4 * n * 45414 = 4 * n * 20620 + 4 * n * 24794 := by omega
    have e3 : (vwp (NExpr.literal i32 0)).1 ≤ 5 := by decide
    have e4 : (vwp (NExpr.variable i32 (mv.nv + pre.length + 1))).1 ≤ 5 := by simp [vwp, NExpr.nodes]
    have e5 : (vwp (NExpr.cast u64 (NExpr.literal i32 0))).1 ≤ 5 := by decide
    have e6 : (vwp (NExpr.literal s64 4000000000000000000)).1 ≤ 5 := by decide
    omega
  · have hl := LLr_length_le n (4 * n)
    obtain ⟨m, hm⟩ : ∃ m, m = (LLr n (4 * n)).length := ⟨_, rfl⟩
    have h3 : m * 6 ≤ 4 * n * 6 := Nat.mul_le_mul_right _ (hm ▸ hl)
    rw [← hm] at hw2
    have e2 : 4 * n * 18 = 4 * n * 12 + 4 * n * 6 := by omega
    omega



structure BRepS (n L S : Nat) (ys : List Int) (b : BS) (t : BT) (H : Heap) : Prop where
  agree : Agree H t 0
  shape : Shape 0 n t.skel
  leaf : LeafOK t
  inv : BeatsModel.Inv t ys
  hrel : HRel INF b H
  valid : ValidOK b
  lens : CapS S b L
  idx : IdxOK t 0 L
  lenok : LenOK b t 0 0 n
  sp : 1 + t.height + 2 ≤ S
  ne : innerOf t + 1 < L
  nM : 2 * n < M31

theorem BRepS.step {n L S : Nat} {ys ys' : List Int} {b bf : BS} {t t' : BT} {H Hf : Heap} (R : BRepS n L S ys b t H)
    (hsk : t'.skel = t.skel) (hleaf : LeafOK t') (hinv : BeatsModel.Inv t' ys') (hag : Agree Hf t' 0)
    (hH : HRel INF bf Hf) (hV : ValidOK bf) (hSL : SameLen b bf) (hlen : bf.len = b.len) : BRepS n L S ys' bf t' Hf where
  agree := hag
  shape := by rw [hsk]; exact R.shape
  leaf := hleaf
  inv := hinv
  hrel := hH
  valid := hV
  lens := Capacities.of_same R.lens hSL
  idx := by unfold IdxOK; rw [hsk]; exact R.idx
  lenok := by
    have h := R.lenok
    unfold LenOK at h ⊢
    rw [hsk]; exact LenOKs_of_eq hlen _ _ _ _ h
  sp := by rw [height_eq_of_skel t' t hsk]; exact R.sp
  ne := by have h := R.ne; unfold innerOf at h ⊢; rw [hsk]; exact h
  nM := R.nM


open Proofs.BeatsInstance
theorem ctor_rep_separate {S : Nat} (mv : MV) (hnv : mv.nv = 16) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (a : List Int) (n L : Nat) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hLM : L < M31) (hAlen : a.length = n) (hAr : InRange a)
    (hS : 34 ≤ S) (b0 : BS) (hV0 : ValidOK b0) (hLens0 : CapS S b0 L) (hlo0 : L ≤ b0.lo.length) (hhi0 : L ≤ b0.hi.length)
    (h0 : ∀ j, b0.mxv.getD j 0 = 0) (h1 : ∀ j, b0.smx.getD j 0 = 0) (h2 : ∀ j, b0.mxc.getD j 0 = 0) (h3 : ∀ j, b0.mnv.getD j 0 = 0)
    (h4 : ∀ j, b0.smn.getD j 0 = 0) (h5 : ∀ j, b0.mnc.getD j 0 = 0) (h6 : ∀ j, b0.len.getD j 0 = 0) (h7 : ∀ j, b0.ladd.getD j 0 = 0)
    (h8 : ∀ j, j < b0.lval.length → b0.lval.getD j 0 = INF) (h9 : ∀ j, b0.lo.getD j 0 = 0) (h10 : ∀ j, b0.hi.getD j 0 = 0) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_new0.body (gS P []) (VVA a b0) = some r ∧ r.ret = none ∧
      r.ps = gS P (CtCells INF n 0 (4 * n)) ∧ r.vv = VVA a bf ∧
      r.cost ≤ 4 * n * 45414 + 100 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 4 * n * 18 + 10 ∧
      BRepS n L S a bf (buildBT a 0 n) Hf := by
  obtain ⟨bf, Hf, F, r, h1', h2', h3', h4', hH, hAg, hV, hLn, hlo, hhi, hLen, hc, hw⟩ :=
    ct_exec_separate mv hnv [] hty hty32 hty15 P a n L hn hL8 hLM hAlen hAr b0 hV0 hLens0 hlo0 hhi0 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hT := buildBT_spec a hAr n 0 n (by omega) (by omega) (by omega)
  have h0rng : rngOf n 0 = (0, n) := by simp [rngOf]
  have hexec : pexecM mv F SegmentTreeBeats_new0.body (gS P []) (VVA a b0) = some r := by
    rw [new0_body]; simpa [hnv] using h1'
  have hnd := (cmd_need mv _ new0_wf F _ (VVA a b0) r hexec).1
  have hdrop : (a.drop 0).take (n - 0) = a := by simp; rw [← hAlen]; exact List.take_length
  refine ⟨bf, Hf, F, r, hexec, h2', h3', h4', hc, ?_, hw, ?_⟩
  · simp [szP, gS] at hnd; have := new0_nb; omega
  · have hsh : Shape 0 n (buildBT a 0 n).skel := hT.2
    have hin := innerS_eq hsh
    have hhl := Proofs.BeatsModel.height_le_power_width 31 (buildBT a 0 n) 0 n hsh
      (by change n - 0 ≤ 2147483648; have hM : M31 = 2147483648 := rfl; omega)
    refine ⟨hAg, hsh, leafOK_build a n 0 n (by omega), by rw [hdrop] at hT; exact hT.1, hH, hV, hLn,
      idxOK_build n hn L hL8 _ 0 0 n hsh h0rng, hLen, ?_, ?_, ?_⟩
    · omega
    · unfold innerOf; omega
    · omega


theorem mk_ctx_separate {S : Nat} (b : BS) (inf : Int) (n op qa qb sp ne : Nat) (x : Int) (W0 W1 W2 L : Nat) (hinf : s64.valid inf = true)
    (hninf : s64.valid (-inf) = true) (hnM : n < Proofs.BellmanFordExec.M31) (hopM : op < Proofs.BellmanFordExec.M31)
    (hqaM : qa < Proofs.BellmanFordExec.M31) (hqbM : qb < Proofs.BellmanFordExec.M31) (hx : s64.valid x = true)
    (hV : ValidOK b) (hLens : CapS S b L) (hLM : L < Proofs.BellmanFordExec.M31) (hSM : S < Proofs.BellmanFordExec.M31) (hk : 2 * W0 + 2 < L) (hsp : 0 < sp)
    (hspL : sp + 2 ≤ S) (hneL : ne + 1 < L) (hlohi : W1 + W2 < Proofs.BellmanFordExec.M31) :
    IterCtx b inf n op qa qb sp ne x W0 W1 W2 :=
  ⟨hinf, hninf, hnM, hopM, hqaM, hqbM, by omega, by omega, hsp, hx, hV, by omega, by omega, by omega, by omega, hlohi,
   by omega, by omega,
   by have := hLens.l0; omega, by have := hLens.l1; omega, by have := hLens.l2; omega, by have := hLens.l3; omega,
   by have := hLens.l4; omega, by have := hLens.l5; omega, by have := hLens.l6; omega, by have := hLens.l7; omega,
   by have := hLens.l8; omega, by have := hLens.lsk; omega, by have := hLens.lsl; omega, by have := hLens.lsr; omega,
   by have := hLens.lent; omega⟩


theorem BRepS.of_uniform {n L : Nat} {ys : List Int} {b : BS} {t : BT} {H : Heap}
    (r : BRep n L ys b t H) : BRepS n L L ys b t H :=
  ⟨r.agree, r.shape, r.leaf, r.inv, r.hrel, r.valid, Capacities.of_uniform r.lens,
    r.idx, r.lenok, r.sp, r.ne, r.nM⟩

end Proofs.BeatsRep
