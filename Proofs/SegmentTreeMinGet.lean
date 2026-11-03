import Proofs.SegmentTreeMinExec

namespace Proofs.SegmentTreeMinGet
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.VectorSumCall (conv_signed)
open Proofs.PowModStep (Sk)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI envs cs)
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (VO VO_get0)
open Proofs.SegmentTreeMinExec

/-! ### `SegmentTree::get` (nv = 1).  Cells: 0 = n, 1 = n_node, 2 = h_node, 3 = idx -/

abbrev bodyGet (nv : Nat) : Command :=
  .sequence (.primitive (.ret (.read s64 (.local 0) (.cast u64 (.binary i32 .add (.variable i32 (nv + 3)) (.variable i32 (nv + 1)))))))
    Sk

theorem body_eqGet : Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_get.body = bodyGet 1 := rfl

set_option maxHeartbeats 8000000 in
theorem body_execGet (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (n N h idx : Nat) (V : List Int)
    (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648) (hidx : idx + N < 2147483648)
    (hlt : idx + N < V.length) (hv : s64.valid (V.getD (idx + N) 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (bodyGet mv.nv) (gS P [ci n, ci N, ci h, ci idx]) (VO V) = some r ∧
      r.ret = some (V.getD (idx + N) 0) ∧ r.vv = VO V ∧ (∃ cl : List Cell, r.ps = gS P cl) ∧ r.cost ≤ 40 ∧ r.need ≤ P.length + 40 ∧ r.wk = 0 := by
  have eI : penvN mv.nv (gS P [ci n, ci N, ci h, ci idx]) (mv.nv + 3) i32 = some (idx : Int) :=
    envs mv P [ci n, ci N, ci h, ci idx] 3 (ci idx) rfl (i32v idx (by show idx < 2147483648; omega))
  have eN : penvN mv.nv (gS P [ci n, ci N, ci h, ci idx]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci idx] 1 (ci N) rfl (i32v N hN)
  have hd : (NExpr.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1)))).denote
      (penvN mv.nv (gS P [ci n, ci N, ci h, ci idx])) = some ((idx + N : Nat) : Int) := by
    rw [den_cast, den_binary, den_variable, eI, Option.bind_some, den_variable, eN, Option.bind_some]
    have : binaryValue .add (idx : Int) (N : Int) = ((idx + N : Nat) : Int) := by
      show (idx : Int) + (N : Int) = _; push_cast; rfl
    rw [this, conv_signed i32 rfl rfl _ (i32v _ (by show idx + N < 2147483648; omega)), Option.bind_some,
      convert_u64]
    congr 1
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
  have hrd := rdM_val mv (VO V) _ 0 (by omega) s64 ty0.symm
    (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1)))) rfl rfl (idx + N) hd
    (V.getD (idx + N) 0) (by rw [VO_get0]; exact vec_getI V (idx + N) hlt) (by rw [ty0]; exact hv)
  have rr := pstmtM_ret_ok mv (gS P [ci n, ci N, ci h, ci idx]) (VO V) _ _ hrd
  have e1 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  refine ⟨_, e1, rfl, rfl, ⟨_, rfl⟩, ?_, ?_, rfl⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]

/-! ### `SegmentTree::product_all` (nv = 1).  Cells: 0 = n, 1 = n_node, 2 = h_node -/

abbrev bodyAll (nv : Nat) : Command :=
  .sequence (.primitive (.ret (.read s64 (.local 0) (.cast u64 (.literal i32 1))))) Sk

theorem body_eqAll : Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_product_all.body = bodyAll 1 := rfl

set_option maxHeartbeats 8000000 in
theorem body_execAll (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (n N h : Nat) (V : List Int)
    (hlt : 1 < V.length) (hv : s64.valid (V.getD 1 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (bodyAll mv.nv) (gS P [ci n, ci N, ci h]) (VO V) = some r ∧
      r.ret = some (V.getD 1 0) ∧ r.vv = VO V ∧ (∃ cl : List Cell, r.ps = gS P cl) ∧ r.cost ≤ 40 ∧ r.need ≤ P.length + 40 ∧ r.wk = 0 := by
  have hd : (NExpr.cast u64 (.literal i32 1)).denote (penvN mv.nv (gS P [ci n, ci N, ci h])) = some ((1 : Nat) : Int) := by
    rw [den_cast, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some, convert_u64]
    rfl
  have hrd := rdM_val mv (VO V) _ 0 (by omega) s64 ty0.symm (.cast u64 (.literal i32 1)) rfl rfl 1 hd
    (V.getD 1 0) (by rw [VO_get0]; exact vec_getI V 1 hlt) (by rw [ty0]; exact hv)
  have rr := pstmtM_ret_ok mv (gS P [ci n, ci N, ci h]) (VO V) _ _ hrd
  have e1 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  refine ⟨_, e1, rfl, rfl, ⟨_, rfl⟩, ?_, ?_, rfl⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]

end Proofs.SegmentTreeMinGet
