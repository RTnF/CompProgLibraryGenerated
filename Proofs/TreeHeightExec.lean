import Proofs.ForLoopB
import Proofs.BellmanFordExec
import Proofs.TopoSortExec
import Proofs.Generated.TreeHeight

namespace Proofs.TreeHeightExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false
  getD_mem cs s64_valid_of lt_conv)
open Proofs.TopoSortExec (i32v)

/-! ### `tree_height<long long>` (nv = 3: cost_depth0, cost_depth1, h).  Cells: 0 = n, 1 = i, 2 = a, 3 = b -/

abbrev ixI (nv : Nat) : NExpr := .cast u64 (.variable i32 (nv + 1))
abbrev dA (nv : Nat) : NStmt := .declare s64 true (.read s64 (.local 0) (ixI nv))
abbrev dB (nv : Nat) : NStmt := .declare s64 true (.read s64 (.local 1) (ixI nv))
abbrev cLT (nv : Nat) : NExpr := .binary bT .lt (.variable s64 (nv + 2)) (.variable s64 (nv + 3))
abbrev wB (nv : Nat) : NStmt := .write (.local 2) s64 (ixI nv) (.variable s64 (nv + 3))
abbrev wA (nv : Nat) : NStmt := .write (.local 2) s64 (ixI nv) (.variable s64 (nv + 2))
abbrev Yt (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (wB nv)) Sk)) Sk
abbrev Yf (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (wA nv)) Sk)) Sk
abbrev Bh (nv : Nat) : Command :=
  .sequence (.primitive (dA nv)) (.sequence (.primitive (dB nv)) (.sequence (.branch (cLT nv) (Yt nv) (Yf nv)) Sk))
abbrev bodyTH (nv : Nat) : Command := .sequence (forStmtB nv 1 0 (Bh nv)) Sk

theorem body_eqTH : Proofs.TreeHeightInstance.tree_height_std_vector_long_long.body = bodyTH 3 := rfl

/-- The larger of two numbers, written as the program does. -/
def mx (a b : Int) : Int := if a < b then b else a

/-- The contents of the vectors `cost_depth0`, `cost_depth1` and `h`. -/
def VH (D0 D1 H : List Int) : Nat → List Int := fun k => if k = 0 then D0 else if k = 1 then D1 else if k = 2 then H else []

theorem VH_set2 (D0 D1 H x : List Int) : upd (VH D0 D1 H) 2 x = VH D0 D1 x := by
  funext k; unfold upd VH; split <;> simp_all

/-- `h` after the first `t` entries were computed. -/
def hfill (D0 D1 H : List Int) (t : Nat) : List Int :=
  (List.range t).map (fun i => mx (D0.getD i 0) (D1.getD i 0)) ++ H.drop t

theorem hfill_succ (D0 D1 H : List Int) (t : Nat) (ht : t < H.length) :
    (hfill D0 D1 H t).set t (mx (D0.getD t 0) (D1.getD t 0)) = hfill D0 D1 H (t + 1) := by
  unfold hfill
  have hl : ((List.range t).map (fun i => mx (D0.getD i 0) (D1.getD i 0))).length = t := by simp
  have hd : H.drop t = H[t] :: H.drop (t + 1) := List.drop_eq_getElem_cons ht
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self, hd, List.range_succ, List.map_append, List.append_assoc]
  rfl

theorem hfill_length (D0 D1 H : List Int) (t : Nat) (ht : t ≤ H.length) : (hfill D0 D1 H t).length = H.length := by
  unfold hfill
  simp
  omega

theorem VH_get0 (D0 D1 H : List Int) : VH D0 D1 H 0 = D0 := by simp [VH]
theorem VH_get1 (D0 D1 H : List Int) : VH D0 D1 H 1 = D1 := by simp [VH]
theorem VH_get2 (D0 D1 H : List Int) : VH D0 D1 H 2 = H := by simp [VH]

set_option maxHeartbeats 8000000 in
/-- One iteration of the loop. -/
theorem b_body (mv : MV) (hnv : mv.nv = 3) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (ty2 : mv.ty 2 = s64)
    (D0 D1 Hc : List Int) (P : List Cell) (n t : Nat) (hn : n < M31) (ht : t < n) (h0 : t < D0.length) (h1 : t < D1.length)
    (h2 : t < Hc.length) (hv0 : s64.valid (D0.getD t 0) = true) (hv1 : s64.valid (D1.getD t 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Bh mv.nv) (gS P [ci n, ci t]) (VH D0 D1 Hc) = some r ∧ r.ret = none ∧
      r.ps = gS P ([ci n] ++ [ci t] ++ [cs (D0.getD t 0), cs (D1.getD t 0)]) ∧
      r.vv = VH D0 D1 (Hc.set t (mx (D0.getD t 0) (D1.getD t 0))) ∧ r.cost ≤ 100 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 1 := by
  have htM : t < M31 := Nat.lt_trans ht hn
  have E1 := envs mv P [ci n, ci t] 1 (ci t) rfl (i32v t htM)
  have r1 := rdM_val mv (VH D0 D1 Hc) (penvN mv.nv (gS P [ci n, ci t])) 0 (by omega) s64 ty0.symm (ixI mv.nv) rfl rfl t
    (cidx_den _ (mv.nv + 1) t E1 htM) (D0.getD t 0) (by rw [VH_get0]; exact vec_getI D0 t h0) (by rw [ty0]; exact hv0)
  have d1 := gSM_decl mv P [ci n, ci t] (VH D0 D1 Hc) s64 _ _ _ r1 (conv_signed s64 rfl rfl _ hv0)
  have q1 := (pexecM_prim mv fu (dA mv.nv) _ _).trans d1
  have E1' := envs mv P [ci n, ci t, cs (D0.getD t 0)] 1 (ci t) rfl (i32v t htM)
  have r2 := rdM_val mv (VH D0 D1 Hc) (penvN mv.nv (gS P [ci n, ci t, cs (D0.getD t 0)])) 1 (by omega) s64 ty1.symm (ixI mv.nv)
    rfl rfl t (cidx_den _ (mv.nv + 1) t E1' htM) (D1.getD t 0) (by rw [VH_get1]; exact vec_getI D1 t h1) (by rw [ty1]; exact hv1)
  have d2 := gSM_decl mv P [ci n, ci t, cs (D0.getD t 0)] (VH D0 D1 Hc) s64 _ _ _ r2 (conv_signed s64 rfl rfl _ hv1)
  have q2 := (pexecM_prim mv fu (dB mv.nv) _ _).trans d2
  have e2 := gSM_env mv.nv P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)] 2 (cs (D0.getD t 0)) rfl hv0
  have e3 := gSM_env mv.nv P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)] 3 (cs (D1.getD t 0)) rfl hv1
  have hc : vdenM mv (VH D0 D1 Hc) (penvN mv.nv (gS P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)])) (cLT mv.nv) =
      some (if D0.getD t 0 < D1.getD t 0 then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e2, Option.bind_some, den_variable, e3, Option.bind_some, lt_conv]
  have hidx : vdenM mv (VH D0 D1 Hc) (penvN mv.nv (gS P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)])) (ixI mv.nv) =
      some (t : Int) := by
    have e1 := gSM_env mv.nv P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)] 1 (ci t) rfl (i32v t htM)
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 1) t e1 htM
  by_cases hlt : D0.getD t 0 < D1.getD t 0
  · rw [if_pos hlt] at hc
    have hx : vdenM mv (VH D0 D1 Hc) (penvN mv.nv (gS P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)]))
        (.variable s64 (mv.nv + 3)) = some (D1.getD t 0) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e3
    have w := pstmtM_write_ok mv (gS P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)]) (VH D0 D1 Hc) 2 (by omega) (ixI mv.nv)
      (.variable s64 (mv.nv + 3)) (D1.getD t 0) t hx hidx (by rw [VH_get2]; exact h2) (by rw [ty2]; exact hv1)
    rw [ty2, VH_get2, VH_set2] at w
    have a1 := (pexecM_prim mv fu (wB mv.nv) _ _).trans w
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    have tk := gS_takeC P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)] [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)] [] rfl
    simp only [List.append_nil] at tk
    simp only [tk] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu (cLT mv.nv) (Yt mv.nv) (Yf mv.nv) _ _ 1 hc (by decide) _ a4
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q2 rfl b2
    have b4 := seqM_some q1 rfl b3
    refine ⟨_, b4, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · show _ = VH D0 D1 (Hc.set t (mx (D0.getD t 0) (D1.getD t 0)))
      unfold mx; rw [if_pos hlt]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  · rw [if_neg hlt] at hc
    have hx : vdenM mv (VH D0 D1 Hc) (penvN mv.nv (gS P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)]))
        (.variable s64 (mv.nv + 2)) = some (D0.getD t 0) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e2
    have w := pstmtM_write_ok mv (gS P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)]) (VH D0 D1 Hc) 2 (by omega) (ixI mv.nv)
      (.variable s64 (mv.nv + 2)) (D0.getD t 0) t hx hidx (by rw [VH_get2]; exact h2) (by rw [ty2]; exact hv0)
    rw [ty2, VH_get2, VH_set2] at w
    have a1 := (pexecM_prim mv fu (wA mv.nv) _ _).trans w
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    have tk := gS_takeC P [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)] [ci n, ci t, cs (D0.getD t 0), cs (D1.getD t 0)] [] rfl
    simp only [List.append_nil] at tk
    simp only [tk] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_false mv fu (cLT mv.nv) (Yt mv.nv) (Yf mv.nv) _ _ hc _ a4
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q2 rfl b2
    have b4 := seqM_some q1 rfl b3
    refine ⟨_, b4, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · show _ = VH D0 D1 (Hc.set t (mx (D0.getD t 0) (D1.getD t 0)))
      unfold mx; rw [if_neg hlt]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp

set_option maxHeartbeats 8000000 in
/-- The whole body of `tree_height<long long>`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 3) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (ty2 : mv.ty 2 = s64)
    (D0 D1 H : List Int) (P : List Cell) (n : Nat) (hn : n < M31) (hn2 : n < 2147483647) (h0 : n ≤ D0.length)
    (h1 : n ≤ D1.length) (h2 : n ≤ H.length) (hv0 : ∀ x ∈ D0, s64.valid x = true) (hv1 : ∀ x ∈ D1, s64.valid x = true)
    (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyTH mv.nv) (gS P [ci n]) (VH D0 D1 H) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n] ∧ r.vv = VH D0 D1 (hfill D0 D1 H n) ∧ r.cost ≤ 120 * n + 40 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ n := by
  have mem0 : ∀ j, j < D0.length → s64.valid (D0.getD j 0) = true := fun j hj => hv0 _ (getD_mem _ _ hj)
  have mem1 : ∀ j, j < D1.length → s64.valid (D1.getD j 0) = true := fun j hj => hv1 _ (getD_mem _ _ hj)
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 1 0 n (by omega) hn2 (Bh mv.nv)
    (fun t vv C => vv = VH D0 D1 (hfill D0 D1 H t) ∧ C = [ci n]) 100 60 1 0 (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hlen := hfill_length D0 D1 H t (by omega)
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := b_body mv hnv ty0 ty1 ty2 D0 D1 (hfill D0 D1 H t) P n t hn ht
        (by omega) (by omega) (by omega) (mem0 t (by omega)) (mem1 t (by omega)) fu
      refine ⟨r, [cs (D0.getD t 0), cs (D1.getD t 0)], [ci n], hr, hret, hps, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      rw [hvv, hfill_succ D0 D1 H t (by omega)])
    (VH D0 D1 (hfill D0 D1 H 0)) [ci n] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hIn
  subst hC
  have t1 := seqM_some hr' hret (pexecM_skip mv fu _ _)
  refine ⟨_, t1, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hps]
  · simp [hvv]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hps] at hnd ⊢; omega
  · simp at hw ⊢; omega

end Proofs.TreeHeightExec
