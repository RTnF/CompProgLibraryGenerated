import Proofs.BeatsCtUpdChain
import Proofs.BeatsRepInv
import Proofs.BeatsExec_CtUpd
import Proofs.BeatsCtorIter
import Proofs.BeatsLoopExec
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
theorem ct_upd_iter (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32)
    (hty15 : mv.ty 15 = s64) (b : BS) (A : List Int) (P : List Cell) (inf : Int) (n ne k : Nat) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hneM : ne < M31) (hkM : k < M31)
    (L : Nat) (hV : ValidOK b) (hLens : Lens b L) (hLM : L < M31) (e : Nat) (E : List Nat) (hent : EntRep b ne (e :: E))
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
end Proofs.BeatsRep
