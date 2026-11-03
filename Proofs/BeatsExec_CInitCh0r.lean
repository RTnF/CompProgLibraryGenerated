import Proofs.BeatsExec_CInitDefs
import Proofs.BeatsExecL2
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
theorem CInit_ch0r (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (b : BS) (P : List Cell)
    (inf : Int) (n op qa qb : Nat) (x : Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hopM : op < M31) (hqaM : qa < M31) (hqbM : qb < M31) (hx : s64.valid x = true) (hvl11 : ∀ w ∈ b.sk, i32.valid w = true) (hvl12 : ∀ w ∈ b.sl, i32.valid w = true) (hvl13 : ∀ w ∈ b.sr, i32.valid w = true) (hl11_0 : 0 < (b.sk).length) (hl12_1 : 0 < (b.sl).length) (hl13_2 : 0 < (b.sr).length) (X0 : Int) (hX0 : X0 = (if ((op : Int) = 1) then inf else (-inf))) (X1 : Int) (hX1 : X1 = 1) (hsc0 : s64.valid (-inf) = true) (fu : Nat)
    (REST : Command) (r : PRM) (hrest : pexecM mv fu REST (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell), (⟨i32, X1⟩ : Cell)] : List Cell))) (VVB (uj3 (uj2 (uj1 b 0 0) 0 0) 0 (n : Int))) = some r) (rv : Option Int) (hret : r.ret = rv) :
    ∃ r0 : PRM, pexecM mv fu (CInitc0 (mv.nv + pre.length) REST) (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell)] : List Cell))) (VVB b) = some r0 ∧ r0.ret = rv ∧
      r0.ps = r.ps ∧ r0.vv = r.vv ∧ r0.cost ≤ 2940 + r.cost ∧ r0.wk ≤ 3 + r.wk := by
  classical
  have vX0 : s64.valid X0 = true := by
    rw [hX0]
    by_cases hC : ((op : Int) = 1)
    · rw [if_pos hC]; exact hinf
    · rw [if_neg hC]; exact hsc0
  have vX1 : i32.valid X1 = true := by rw [hX1]; exact (by decide)
  obtain ⟨r6, h6, hr6, hp6, hv6, hc6, hn6, hw6⟩ := seq_assign_r mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) (VVB ((uj3 (uj2 (uj1 b 0 0) 0 0) 0 (n : Int)))) (pre.length + 6) (by simp) i32
    (.literal i32 (1)) 1 X1 (⟨i32, 0⟩ : Cell) (den_lit32 mv _ _ 1 (by decide)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 6 _ rfl) rfl (by decide) (by rw [hX1]; exact conv_i32 _ (by decide))
    (CInitc0_7 (mv.nv + pre.length) REST) r (by
      rw [set_ext0 pre _ 6 _]
      exact hrest) hret
  have hc6' : r6.cost ≤ 400 + r.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc6); exact Nat.le_trans hc6 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r5, h5, hr5, hp5, hv5, hc5, hn5, hw5⟩ := seq_write_r mv fu (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell))) (VVB ((uj2 (uj1 b 0 0) 0 0))) 13 (by rw [hnv]; decide) i32 (hty32 13 (by decide) (by decide))
    (.cast u64 (.literal i32 (0))) (.variable i32 ((mv.nv + pre.length) + 1)) (n : Int) 0 (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell)) i32 (pre.length + 1) _ (Nat.add_assoc _ _ _) (n : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell) 1 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat n hnM) _)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact (den_idx_lit0 mv P _))
    (by rw [VVB_get13]; simpa [uj1, uj2, uj3] using hl13_2) (Proofs.BellmanFordExec.i32_valid_nat n hnM)
    (CInitc0_6 (mv.nv + pre.length) REST) r6 (by rw [VVB_get13, VVB_upd13]; exact h6) hr6
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc5' : r5.cost ≤ 400 + r6.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc5); exact Nat.le_trans hc5 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r4, h4, hr4, hp4, hv4, hc4, hn4, hw4⟩ := seq_write_r mv fu (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell))) (VVB ((uj1 b 0 0))) 12 (by rw [hnv]; decide) i32 (hty32 12 (by decide) (by decide))
    (.cast u64 (.literal i32 (0))) (.literal i32 (0)) 0 0 (den_lit32 mv _ _ 0 (by decide))
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact (den_idx_lit0 mv P _))
    (by rw [VVB_get12]; simpa [uj1, uj2, uj3] using hl12_1) (by decide)
    (CInitc0_5 (mv.nv + pre.length) REST) r5 (by rw [VVB_get12, VVB_upd12]; exact h5) hr5
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc4' : r4.cost ≤ 400 + r5.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc4); exact Nat.le_trans hc4 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r3, h3, hr3, hp3, hv3, hc3, hn3, hw3⟩ := seq_write_r mv fu (gS P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell), (⟨i32, 0⟩ : Cell)] : List Cell))) (VVB (b)) 11 (by rw [hnv]; decide) i32 (hty32 11 (by decide) (by decide))
    (.cast u64 (.literal i32 (0))) (.literal i32 (0)) 0 0 (den_lit32 mv _ _ 0 (by decide))
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact (den_idx_lit0 mv P _))
    (by rw [VVB_get11]; simpa [uj1, uj2, uj3] using hl11_0) (by decide)
    (CInitc0_4 (mv.nv + pre.length) REST) r4 (by rw [VVB_get11, VVB_upd11]; exact h4) hr4
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc3' : r3.cost ≤ 400 + r4.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc3); exact Nat.le_trans hc3 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hn2, hw2⟩ := seq_decl_r mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell)] : List Cell)) (VVB (b)) i32 (.literal i32 (0)) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 _ (by decide)) (CInitc0_3 (mv.nv + pre.length) REST) r3 (by rw [List.append_assoc]; exact h3) hr3
  have hc2' : r2.cost ≤ 400 + r3.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc2); exact Nat.le_trans hc2 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hn1, hw1⟩ := seq_sbranch3_r mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, (-inf)⟩ : Cell)] : List Cell)) (VVB (b)) (pre.length + 5) (by simp) s64
    (.binary bT .eq (.variable i32 ((mv.nv + pre.length) + 2)) (.literal i32 (1))) (.variable s64 ((mv.nv + pre.length) + 0)) (((op : Int) = 1)) inf inf (-inf) (⟨s64, (-inf)⟩ : Cell)
    (den_cmpw mv _ _ _ _ _ (op : Int) 1 (((op : Int) = 1)) (Proofs.BellmanFordPExec.eq_convP _ _) (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, (-inf)⟩ : Cell)] : List Cell)) i32 (pre.length + 2) _ (Nat.add_assoc _ _ _) (op : Int) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, (-inf)⟩ : Cell)] : List Cell) 2 _ rfl) (Proofs.BellmanFordExec.i32_valid_nat op hopM) _) (den_lit32 mv _ _ 1 (by decide)) rfl rfl) (fun hC => (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, (-inf)⟩ : Cell)] : List Cell)) s64 (pre.length + 0) _ (Nat.add_assoc _ _ _) inf (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, (-inf)⟩ : Cell)] : List Cell) 0 _ rfl) hinf _)) (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, (-inf)⟩ : Cell)] : List Cell) 5 _ rfl) rfl hsc0 rfl (fun hC => conv_s64 _ hinf)
    (CInitc0_2 (mv.nv + pre.length) REST) r2 (by
      rw [set_ext0 pre _ 5 _]
      have e2 : ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, (-inf)⟩ : Cell)] : List Cell).set 5 (⟨s64, if ((op : Int) = 1) then inf else (-inf)⟩ : Cell) = ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell), (⟨s64, X0⟩ : Cell)] : List Cell) := by
        rw [show (⟨s64, if ((op : Int) = 1) then inf else (-inf)⟩ : Cell) = ⟨s64, X0⟩ from by rw [hX0]]
        rfl
      rw [e2]; exact h2) hr2
    300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 1000)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  have hc1' : r1.cost ≤ 400 + r2.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc1); exact Nat.le_trans hc1 (Nat.add_le_add_right (by decide) _)
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hn0, hw0⟩ := seq_decl_r mv fu P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell)] : List Cell)) (VVB (b)) s64 (.unary s64 .neg (.variable s64 ((mv.nv + pre.length) + 0))) (-inf) (-inf)
    (den_negw mv _ _ _ inf (den_cellvar_t mv P (pre ++ ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell)] : List Cell)) s64 (pre.length + 0) _ (Nat.add_assoc _ _ _) inf (cell_at0 pre ([(⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (op : Int)⟩ : Cell), (⟨i32, (qa : Int)⟩ : Cell), (⟨i32, (qb : Int)⟩ : Cell)] : List Cell) 0 _ rfl) hinf _) (by simp [NExpr.scalarOnly]) hsc0) (conv_s64 _ hsc0) (CInitc0_1 (mv.nv + pre.length) REST) r1 (by rw [List.append_assoc]; exact h1) hr1
  have hc0' : r0.cost ≤ 400 + r1.cost := by (try simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc0); exact Nat.le_trans hc0 (Nat.add_le_add_right (by decide) _)
  clear hX0 hX1
  refine ⟨r0, h0, hr0, ?_, ?_, ?_, ?_⟩
  · rw [hp0, hp1, hp2, hp3, hp4, hp5, hp6]
  · rw [hv0, hv1, hv2, hv3, hv4, hv5, hv6]
  · omega
  · omega


end Proofs.BeatsExec
