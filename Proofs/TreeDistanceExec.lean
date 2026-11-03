import Proofs.ForLoopB
import Proofs.BellmanFordExec
import Proofs.TopoSortExec
import Proofs.Generated.TreeDistance

namespace Proofs.TreeDistanceExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 s64_valid_of cs)
open Proofs.TopoSortExec (i32v)

/-! ### `tree_distance<long long>` (nv = 1: the cost-depth vector is slot 0).  Cells: 0 = u, 1 = v, 2 = lca, 3 = a, 4 = b, 5 = c -/

abbrev ixE (nv c : Nat) : NExpr := .cast u64 (.variable i32 (nv + c))
abbrev retE (nv : Nat) : NExpr :=
  .binary s64 .sub (.binary s64 .add (.variable s64 (nv + 3)) (.variable s64 (nv + 4)))
    (.binary s64 .mul (.variable s64 (nv + 5)) (.cast s64 (.literal i32 2)))
abbrev bodyTD (nv : Nat) : Command :=
  .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (ixE nv 0))))
    (.sequence (.primitive (.declare s64 true (.read s64 (.local 0) (ixE nv 1))))
      (.sequence (.primitive (.declare s64 true (.read s64 (.local 0) (ixE nv 2))))
        (.sequence (.primitive (.ret (retE nv))) Sk)))

theorem body_eqTD : Proofs.TreeDistanceInstance.tree_distance_std_vector_long_long.body = bodyTD 1 := rfl

theorem binary_add_val (a b : Int) : binaryValue .add a b = a + b := rfl
theorem binary_sub_val (a b : Int) : binaryValue .sub a b = a - b := rfl
theorem binary_mul_val (a b : Int) : binaryValue .mul a b = a * b := rfl

set_option maxHeartbeats 8000000 in
/-- The whole body of `tree_distance<long long>`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 1) (hty : mv.ty 0 = s64) (D : List Int) (vv : Nat → List Int) (hv0 : vv 0 = D)
    (P : List Cell) (u v l : Nat) (hu : u < D.length) (hv : v < D.length) (hl : l < D.length) (hDl : D.length < M31)
    (hDv : ∀ x ∈ D, s64.valid x = true)
    (hab : s64.valid (D.getD u 0 + D.getD v 0) = true) (hc2 : s64.valid (D.getD l 0 * 2) = true)
    (hfin : s64.valid (D.getD u 0 + D.getD v 0 - D.getD l 0 * 2) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (bodyTD mv.nv) (gS P [ci u, ci v, ci l]) vv = some r ∧
      r.ret = some (D.getD u 0 + D.getD v 0 - D.getD l 0 * 2) ∧ r.vv = vv ∧ (∃ cs : List Cell, r.ps = gS P cs) ∧
      r.cost ≤ 120 ∧ r.need ≤ P.length + 40 ∧ r.wk = 0 := by
  have hgm : ∀ x, x ∈ D → s64.valid x = true := hDv
  have hu' : u < M31 := Nat.lt_trans hu hDl
  have hv' : v < M31 := Nat.lt_trans hv hDl
  have hl' : l < M31 := Nat.lt_trans hl hDl
  have mem : ∀ j, j < D.length → s64.valid (D.getD j 0) = true := by
    intro j hj
    apply hDv
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  -- a = cost_depth[u]
  have E0 := envs mv P [ci u, ci v, ci l] 0 (ci u) rfl (i32v u hu')
  have r1 := rdM_val mv vv (penvN mv.nv (gS P [ci u, ci v, ci l])) 0 (by omega) s64 hty.symm (ixE mv.nv 0) rfl rfl u
    (cidx_den _ (mv.nv + 0) u E0 hu') (D.getD u 0) (by rw [hv0]; exact vec_getI D u hu) (by rw [hty]; exact mem u hu)
  have d1 := gSM_decl mv P [ci u, ci v, ci l] vv s64 _ _ _ r1 (conv_signed s64 rfl rfl _ (mem u hu))
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  -- b = cost_depth[v]
  have E1 := envs mv P [ci u, ci v, ci l, cs (D.getD u 0)] 1 (ci v) rfl (i32v v hv')
  have r2 := rdM_val mv vv (penvN mv.nv (gS P [ci u, ci v, ci l, cs (D.getD u 0)])) 0 (by omega) s64 hty.symm (ixE mv.nv 1)
    rfl rfl v (cidx_den _ (mv.nv + 1) v E1 hv') (D.getD v 0) (by rw [hv0]; exact vec_getI D v hv) (by rw [hty]; exact mem v hv)
  have d2 := gSM_decl mv P [ci u, ci v, ci l, cs (D.getD u 0)] vv s64 _ _ _ r2 (conv_signed s64 rfl rfl _ (mem v hv))
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  -- c = cost_depth[lca]
  have E2 := envs mv P [ci u, ci v, ci l, cs (D.getD u 0), cs (D.getD v 0)] 2 (ci l) rfl (i32v l hl')
  have r3 := rdM_val mv vv (penvN mv.nv (gS P [ci u, ci v, ci l, cs (D.getD u 0), cs (D.getD v 0)])) 0 (by omega) s64 hty.symm
    (ixE mv.nv 2) rfl rfl l (cidx_den _ (mv.nv + 2) l E2 hl') (D.getD l 0) (by rw [hv0]; exact vec_getI D l hl)
    (by rw [hty]; exact mem l hl)
  have d3 := gSM_decl mv P [ci u, ci v, ci l, cs (D.getD u 0), cs (D.getD v 0)] vv s64 _ _ _ r3
    (conv_signed s64 rfl rfl _ (mem l hl))
  have q3 := (pexecM_prim mv fu _ _ _).trans d3
  -- the result
  have ea := envs mv P [ci u, ci v, ci l, cs (D.getD u 0), cs (D.getD v 0), cs (D.getD l 0)] 3 (cs (D.getD u 0)) rfl (mem u hu)
  have eb := envs mv P [ci u, ci v, ci l, cs (D.getD u 0), cs (D.getD v 0), cs (D.getD l 0)] 4 (cs (D.getD v 0)) rfl (mem v hv)
  have ec := envs mv P [ci u, ci v, ci l, cs (D.getD u 0), cs (D.getD v 0), cs (D.getD l 0)] 5 (cs (D.getD l 0)) rfl (mem l hl)
  have hret : vdenM mv vv (penvN mv.nv (gS P [ci u, ci v, ci l, cs (D.getD u 0), cs (D.getD v 0), cs (D.getD l 0)])) (retE mv.nv) =
      some (D.getD u 0 + D.getD v 0 - D.getD l 0 * 2) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_binary, den_variable, ea, Option.bind_some, den_variable, eb,
      Option.bind_some, binary_add_val, conv_signed s64 rfl rfl _ hab, Option.bind_some, den_binary, den_variable, ec,
      Option.bind_some, den_cast, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some,
      conv_signed s64 rfl rfl 2 (by decide), Option.bind_some, binary_mul_val, conv_signed s64 rfl rfl _ hc2, Option.bind_some,
      binary_sub_val]
    exact conv_signed s64 rfl rfl _ hfin
  have rr := pstmtM_ret_ok mv (gS P [ci u, ci v, ci l, cs (D.getD u 0), cs (D.getD v 0), cs (D.getD l 0)]) vv (retE mv.nv) _ hret
  have e4 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have c3 := seqM_some q3 rfl e4
  have c2 := seqM_some q2 rfl c3
  have c1 := seqM_some q1 rfl c2
  refine ⟨_, c1, rfl, rfl, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

end Proofs.TreeDistanceExec
