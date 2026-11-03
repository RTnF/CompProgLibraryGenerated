import Proofs.LazySegBlocks

namespace Proofs.LazySegUpdE
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs pexecM_branch_true pexecM_branch_false)
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den)
open Proofs.SegmentTreeExec (maxMon mx AppBlk appblk_exec ix2 ix21 ix2_den ix21_den)

/-- The inlined `update(i)`: copies of the four arguments (the cells `j0 .. j2` and the expression `KE`), then `node[i] = apply(node[2i], node[2i+1])`.
`c` is the number of cells before the block; `i` is the fourth copy (the cell `c + 3`). -/
abbrev UpdBlkE (nv c j0 j1 j2 : Nat) (KE : NExpr) (REST : Command) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 (nv + j0))))
    (.sequence (.primitive (.declare i32 true (.variable i32 (nv + j1))))
      (.sequence (.primitive (.declare i32 true (.variable i32 (nv + j2))))
        (.sequence (.primitive (.declare i32 true KE))
          (AppBlk nv (c + 4) (.read s64 (.local 0) (ix2 (nv + c + 3))) (.read s64 (.local 0) (ix21 (nv + c + 3)))
            (.sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (nv + c + 3))) (vS nv (c + 4 + 3)))) REST)))))


set_option maxHeartbeats 16000000 in
theorem updE_exec (mv : MV) (hmv0 : 0 < mv.nv) (ty0 : mv.ty 0 = s64) (P : List Cell) (vv : Nat → List Int) (fu : Nat)
    (cl : List Cell) (c : Nat) (hc : cl.length = c) (j0 j1 j2 : Nat) (v0 v1 v2 i : Nat) (KE : NExpr)
    (hj0 : cl[j0]? = some (ci v0)) (hj1 : cl[j1]? = some (ci v1)) (hj2 : cl[j2]? = some (ci v2)) (hKE : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci v0, ci v1, ci v2]))) KE = some (i : Int))
    (hv0 : v0 < 2147483648) (hv1 : v1 < 2147483648) (hv2 : v2 < 2147483648) (hi : 2 * i + 1 < 2147483648)
    (hlt : 2 * i + 1 < (vv 0).length)
    (vx : s64.valid ((vv 0).getD (2 * i) 0) = true) (vy : s64.valid ((vv 0).getD (2 * i + 1) 0) = true)
    (REST : Command) (r2 : PRM)
    (hr : pexecM mv fu REST (gS P (cl ++ [ci v0, ci v1, ci v2, ci i, cs ((vv 0).getD (2 * i) 0), cs ((vv 0).getD (2 * i + 1) 0),
      cs (mx ((vv 0).getD (2 * i) 0) ((vv 0).getD (2 * i + 1) 0)), cs (mx ((vv 0).getD (2 * i) 0) ((vv 0).getD (2 * i + 1) 0))]))
      (upd vv 0 ((vv 0).set i (mx ((vv 0).getD (2 * i) 0) ((vv 0).getD (2 * i + 1) 0)))) = some r2) :
    ∃ r : PRM, pexecM mv fu (UpdBlkE mv.nv c j0 j1 j2 KE REST) (gS P cl) vv = some r ∧ r.ret = r2.ret ∧ r.ps = r2.ps ∧ r.vv = r2.vv ∧
      r.cost ≤ r2.cost + 300 + (vwp KE).1 ∧ (∀ N : Nat, r2.need ≤ N → P.length + 2 * c + 75 + (vwp KE).2 ≤ N → r.need ≤ N) ∧ r.wk = r2.wk + 1 := by
  have lj0 : j0 < cl.length := (List.getElem?_eq_some_iff.mp hj0).1
  have lj1 : j1 < cl.length := (List.getElem?_eq_some_iff.mp hj1).1
  have lj2 : j2 < cl.length := (List.getElem?_eq_some_iff.mp hj2).1
  have gA : ∀ (ys : List Cell) (j : Nat), j < cl.length → (cl ++ ys)[j]? = cl[j]? := fun ys j hj => List.getElem?_append_left hj
  -- the four copies
  have E0 := envs mv P cl j0 (ci v0) hj0 (i32v v0 hv0)
  have d0 := gSM_decl mv P cl vv i32 (.variable i32 (mv.nv + j0)) (v0 : Int) (v0 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E0) (conv_signed i32 rfl rfl _ (i32v v0 hv0))
  have a0 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j0))) _ _).trans d0
  have E1 := envs mv P (cl ++ [ci v0]) j1 (ci v1) (by rw [gA _ _ lj1]; exact hj1) (i32v v1 hv1)
  have d1 := gSM_decl mv P (cl ++ [ci v0]) vv i32 (.variable i32 (mv.nv + j1)) (v1 : Int) (v1 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1) (conv_signed i32 rfl rfl _ (i32v v1 hv1))
  have e1 : cl ++ [ci v0] ++ [(⟨i32, (v1 : Int)⟩ : Cell)] = cl ++ [ci v0, ci v1] := by simp
  rw [e1] at d1
  have a1 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j1))) _ _).trans d1
  have E2 := envs mv P (cl ++ [ci v0, ci v1]) j2 (ci v2) (by rw [gA _ _ lj2]; exact hj2) (i32v v2 hv2)
  have d2 := gSM_decl mv P (cl ++ [ci v0, ci v1]) vv i32 (.variable i32 (mv.nv + j2)) (v2 : Int) (v2 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2) (conv_signed i32 rfl rfl _ (i32v v2 hv2))
  have e2 : cl ++ [ci v0, ci v1] ++ [(⟨i32, (v2 : Int)⟩ : Cell)] = cl ++ [ci v0, ci v1, ci v2] := by simp
  rw [e2] at d2
  have a2 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j2))) _ _).trans d2
  have hiM : i < 2147483648 := by omega
  have d3 := gSM_decl mv P (cl ++ [ci v0, ci v1, ci v2]) vv i32 KE (i : Int) (i : Int) hKE (conv_signed i32 rfl rfl _ (i32v i hiM))
  have e3 : cl ++ [ci v0, ci v1, ci v2] ++ [(⟨i32, (i : Int)⟩ : Cell)] = cl ++ [ci v0, ci v1, ci v2, ci i] := by simp
  rw [e3] at d3
  have a3 := (pexecM_prim mv fu (.declare i32 true KE) _ _).trans d3
  -- the reads of the children
  set x := (vv 0).getD (2 * i) 0 with hxdef
  set y := (vv 0).getD (2 * i + 1) 0 with hydef
  have cell_i : ∀ ys : List Cell, (cl ++ [ci v0, ci v1, ci v2, ci i] ++ ys)[c + 3]? = some (ci i) := by
    intro ys
    rw [List.getElem?_append_left (by simp [hc])]
    rw [List.getElem?_append_right (by omega)]
    simp [hc]
  have Ei : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i] ++ ys)) (mv.nv + c + 3) i32 = some (i : Int) :=
    fun ys => envs mv P _ (c + 3) (ci i) (cell_i ys) (i32v i hiM)
  have hX : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i]))) (.read s64 (.local 0) (ix2 (mv.nv + c + 3))) = some x := by
    have := Ei []
    rw [List.append_nil] at this
    exact rdM_val mv vv _ 0 hmv0 s64 ty0.symm (ix2 (mv.nv + c + 3)) rfl rfl (2 * i)
      (ix2_den _ _ i this (by omega)) x (vec_getI (vv 0) (2 * i) (by omega)) (by rw [ty0]; exact vx)
  have hY : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i] ++ [cs x]))) (.read s64 (.local 0) (ix21 (mv.nv + c + 3))) = some y :=
    rdM_val mv vv _ 0 hmv0 s64 ty0.symm (ix21 (mv.nv + c + 3)) rfl rfl (2 * i + 1)
      (ix21_den _ _ i (Ei [cs x]) hi) y (vec_getI (vv 0) (2 * i + 1) hlt) (by rw [ty0]; exact vy)
  -- the write
  have vm : s64.valid (mx x y) = true := by unfold mx; split <;> assumption
  have cell8 : (cl ++ [ci v0, ci v1, ci v2, ci i] ++ [cs x, cs y, cs (mx x y), cs (mx x y)]) = cl ++ [ci v0, ci v1, ci v2, ci i, cs x, cs y, cs (mx x y), cs (mx x y)] := by simp
  have Ei8 : penvN mv.nv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i] ++ [cs x, cs y, cs (mx x y), cs (mx x y)])) (mv.nv + c + 3) i32 = some (i : Int) :=
    Ei [cs x, cs y, cs (mx x y), cs (mx x y)]
  have hw := pstmtM_write_ok mv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i] ++ [cs x, cs y, cs (mx x y), cs (mx x y)])) vv 0 hmv0
    (.cast u64 (.variable i32 (mv.nv + c + 3))) (vS mv.nv (c + 4 + 3)) (mx x y) i
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ (c + 4 + 3) (mx x y) (by
        rw [List.getElem?_append_right (by simp [hc])]; simp [hc]) vm)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ _ i Ei8 hiM) (by omega) (by rw [ty0]; exact vm)
  rw [ty0] at hw
  have aw := (pexecM_prim mv fu (.write (.local 0) s64 (.cast u64 (.variable i32 (mv.nv + c + 3))) (vS mv.nv (c + 4 + 3))) _ _).trans hw
  rw [cell8] at aw
  have sw := seqM_some (r2 := r2) (b := REST) aw rfl hr
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P vv fu (cl ++ [ci v0, ci v1, ci v2, ci i]) (c + 4) (by simp [hc])
    (.read s64 (.local 0) (ix2 (mv.nv + c + 3))) (.read s64 (.local 0) (ix21 (mv.nv + c + 3))) x y vx vy hX hY
    (.sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (mv.nv + c + 3))) (vS mv.nv (c + 4 + 3)))) REST) _
    (by rw [cell8]; exact sw)
  have s3 := seqM_some a3 rfl hA
  have s2 := seqM_some a2 rfl s3
  have s1 := seqM_some a1 rfl s2
  have s0 := seqM_some a0 rfl s1
  refine ⟨_, s0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using retA
  · simpa using psA
  · simpa using vvA
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA ⊢; omega
  · intro N hN hB
    have hA' := nA N
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' ⊢
    exact ⟨by omega, by omega, hA' (by omega) hN (by omega)⟩
  · simp at wA ⊢; omega

end Proofs.LazySegUpdE
