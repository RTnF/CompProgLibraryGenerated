import Proofs.DijkstraOldExec
import Proofs.PrimMath
import Proofs.PrimRelax
import Proofs.PrimStep
import Proofs.Generated.Prim

namespace Proofs.PrimExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getM vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false cs)
open Proofs.DijkstraOldScan
open Proofs.DijkstraOldExec
open Proofs.BellmanFordMath (Edge)
open Proofs.PrimStep (PInv PInv_step PInv_init degSum degSum_push degSum_init_le doneOf_ne doneOf_eq perm_sum_int sum_le_len_mul pk_bounds D_perm_range)
open Proofs.DijkstraMath (Eall mem_Eall mem_Eall_inv)
open Proofs.PrimRelax (relaxL relaxL_length relaxL_getD foldl_length foldl_le foldl_done foldl_cases foldl_cover)

/-! ### The program (nv = 5: `head`, `target`, `cost`, `dist`, `done`; variables 5 = n, 6 = inf, 7 = it, 8 = best, 9 = bd, 10 = v) -/

abbrev cNeg (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 3)) lit0
abbrev aZero (nv : Nat) : NStmt := .assign (nv + 4) s64 (.cast s64 (.literal i32 0))
abbrev FBthen (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (cDone nv)
    (.sequence (.scope (.sequence (.primitive (aBest nv)) (.sequence (.primitive (aZero nv)) Sk))) Sk) Sk) Sk)) Sk
abbrev FB (nv : Nat) : Command := .sequence (.branch (cNeg nv) (FBthen nv) Sk) Sk
abbrev BRthen (nv : Nat) : Command := .sequence (.scope (.sequence (forStmtB nv 5 0 (FB nv)) Sk)) Sk
abbrev BRfb (nv : Nat) : Command := .branch (cNeg nv) (BRthen nv) Sk
abbrev dCst (nv : Nat) : NStmt := .declare s64 true (.read s64 (.local 2) (idxSD nv))
abbrev cDoneW (nv : Nat) : NExpr := .binary bT .eq (.read i32 (.local 4) (ix nv 8)) lit0
abbrev Y1p (nv : Nat) : Command := .sequence (.scope (.sequence (.branch (cRel nv) (Yr nv) Sk) Sk)) Sk
abbrev Xp (nv : Nat) : Command :=
  .sequence (.primitive (dW nv)) (.sequence (.primitive (dCst nv)) (.sequence (.branch (cDoneW nv) (Y1p nv) Sk) Sk))
abbrev wDistB (nv : Nat) : NStmt := .write (.local 3) s64 (ix nv 3) (.variable s64 (nv + 4))
abbrev Tl (nv : Nat) : Command :=
  .sequence (.primitive (wDone nv)) (.sequence (.primitive (wDistB nv))
    (.sequence (.primitive (dStart nv)) (.sequence (.primitive (dCnt nv)) (.sequence (forStmtB nv 7 6 (Xp nv)) Sk))))
abbrev Bp (nv : Nat) : Command :=
  .sequence (.primitive dBest) (.sequence (.primitive (dBd nv)) (.sequence (forStmtB nv 5 0 (Bs nv))
    (.sequence (BRfb nv) (Tl nv))))
abbrev aTot (nv : Nat) : NStmt := .assign (nv + 2) s64 (.binary s64 .add (.variable s64 (nv + 2)) (.read s64 (.local 3) (ix nv 3)))
abbrev Bt (nv : Nat) : Command := .sequence (.primitive (aTot nv)) Sk
abbrev progPR (nv : Nat) : Command :=
  .sequence (forStmtB nv 2 0 (Bp nv))
    (.sequence (.primitive (.declare s64 true (.cast s64 (.literal i32 0))))
      (.sequence (forStmtB nv 3 0 (Bt nv)) (.sequence (.primitive (.ret (.variable s64 (nv + 2)))) Sk)))

theorem body_eqPR : Proofs.PrimInstance.prim_std_vector_int.body = progPR 5 := rfl

set_option maxHeartbeats 8000000 in
/-- One iteration of the relaxation loop: `w = target[start+d]; c = cost[start+d]; if (done[w] == 0) if (c < dist[w]) dist[w] = c;` -/
theorem xp_body (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it st cnt d : Nat) (inf bd : Int) (r : Option Nat) (hn : n < M31) (hit : it < M31) (hstM : st < M31)
    (hcM : cnt < M31) (hd : d < M31) (hsd : st + d < T.length) (hmT : T.length < M31) (hCl : C.length = T.length)
    (hDdl : Dd.length = n) (hDnl : Dn.length = n) (hw : T.getD (st + d) 0 < n) (hbd : s64.valid bd = true)
    (hinf : s64.valid inf = true) (hr : ∀ b, r = some b → b < M31) (hc : s64.valid (C.getD (st + d) 0) = true)
    (hdw : s64.valid (Dd.getD (T.getD (st + d) 0) 0) = true) (hdn : Dn.getD (T.getD (st + d) 0) 0 < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Xp mv.nv) (gS P (c8 n inf it r bd st cnt d)) (VD H T C Dd Dn) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P (c10 n inf it r bd st cnt d (T.getD (st + d) 0) (C.getD (st + d) 0)) ∧
      rr.vv = VD H T C (if Dn.getD (T.getD (st + d) 0) 0 = 0 ∧ C.getD (st + d) 0 < Dd.getD (T.getD (st + d) 0) 0
        then Dd.set (T.getD (st + d) 0) (C.getD (st + d) 0) else Dd) Dn ∧
      rr.cost ≤ 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 1 := by
  generalize hwdef : T.getD (st + d) 0 = w at *
  generalize hcdef : C.getD (st + d) 0 = c at *
  have hsum : st + d < M31 := by omega
  have E5 := envs mv P (c8 n inf it r bd st cnt d) 5 (ci st) rfl (i32v st hstM)
  have E7 := envs mv P (c8 n inf it r bd st cnt d) 7 (ci d) rfl (i32v d hd)
  have hidx := sumIdx_den (penvN mv.nv (gS P (c8 n inf it r bd st cnt d))) (mv.nv + 5) (mv.nv + 7) st d E5 E7 hsum
  have vw := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c8 n inf it r bd st cnt d))) 1 (by omega) i32 (hty1).symm
    (idxSD mv.nv) rfl rfl (st + d) hidx ((w : Nat) : Int)
    (by rw [VD_get1]; have := natList_get T (st + d) hsd; rw [hwdef] at this; exact this)
    (by rw [hty1]; exact i32v _ (by omega))
  have d1 := gSM_decl mv P (c8 n inf it r bd st cnt d) (VD H T C Dd Dn) i32 _ _ _ vw
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q1 := (pexecM_prim mv fu (dW mv.nv) _ _).trans d1
  -- c = cost[start + d]
  have E5' := envs mv P (c8 n inf it r bd st cnt d ++ [ci w]) 5 (ci st) rfl (i32v st hstM)
  have E7' := envs mv P (c8 n inf it r bd st cnt d ++ [ci w]) 7 (ci d) rfl (i32v d hd)
  have hidx' := sumIdx_den (penvN mv.nv (gS P (c8 n inf it r bd st cnt d ++ [ci w]))) (mv.nv + 5) (mv.nv + 7) st d E5' E7' hsum
  have vcost := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c8 n inf it r bd st cnt d ++ [ci w]))) 2 (by omega) s64
    (hty2).symm (idxSD mv.nv) rfl rfl (st + d) hidx' c
    (by rw [VD_get2]; have := intList_get C (st + d) (by omega); rw [hcdef] at this; exact this) (by rw [hty2]; exact hc)
  have d2 := gSM_decl mv P (c8 n inf it r bd st cnt d ++ [ci w]) (VD H T C Dd Dn) s64 _ _ _ vcost
    (conv_signed s64 rfl rfl _ hc)
  have q2 := (pexecM_prim mv fu (dCst mv.nv) _ _).trans d2
  -- the test done[w] == 0
  have E8 := envs mv P (c10 n inf it r bd st cnt d w c) 8 (ci w) rfl (i32v w (by omega))
  have E9 := envs mv P (c10 n inf it r bd st cnt d w c) 9 (cs c) rfl hc
  have vdone := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w c))) 4
    (by omega) i32 (hty4).symm (ix mv.nv 8) rfl rfl w (cidx_den _ (mv.nv + 8) w E8 (by omega)) ((Dn.getD w 0 : Nat) : Int)
    (by rw [VD_get4]; exact natList_get Dn w (by omega)) (by rw [hty4]; exact i32v _ hdn)
  have vc1 : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w c))) (cDoneW mv.nv) =
      some (if ((Dn.getD w 0 : Nat) : Int) = 0 then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdone, Option.bind_some, vdenM_scalar _ _ _ _ rfl, zero_den, Option.bind_some]
    exact eq_conv _ _
  have vdw := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w c))) 3
    (by omega) s64 (hty3).symm (ix mv.nv 8) rfl rfl w (cidx_den _ (mv.nv + 8) w E8 (by omega)) (Dd.getD w 0)
    (by rw [VD_get3]; exact intList_get Dd w (by omega)) (by rw [hty3]; exact hdw)
  have vc2 : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w c))) (cRel mv.nv) =
      some (if c < Dd.getD w 0 then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdenM_scalar _ _ _ _ rfl, den_variable, E9, Option.bind_some, vdw, Option.bind_some]
    exact lt_conv _ _
  by_cases h0 : Dn.getD w 0 = 0
  · have hc1 : (if ((Dn.getD w 0 : Nat) : Int) = 0 then (1 : Int) else 0) = 1 := by rw [h0]; simp
    rw [hc1] at vc1
    by_cases hlt : c < Dd.getD w 0
    · have hc2 : (if c < Dd.getD w 0 then (1 : Int) else 0) = 1 := by rw [if_pos hlt]
      rw [hc2] at vc2
      have hp : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w c))) (ix mv.nv 8) = some (w : Int) := by
        rw [vdenM_scalar _ _ _ _ rfl]
        exact cidx_den _ (mv.nv + 8) w E8 (by omega)
      have hx : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w c))) (.variable s64 (mv.nv + 9)) =
          some c := by
        rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E9
      have wr := pstmtM_write_ok mv (gS P (c10 n inf it r bd st cnt d w c)) (VD H T C Dd Dn) 3 (by omega)
        (ix mv.nv 8) (.variable s64 (mv.nv + 9)) c w hx hp (by rw [VD_get3]; omega) (by rw [hty3]; exact hc)
      rw [hty3, VD_get3, VD_write3] at wr
      have a1 := (pexecM_prim mv fu (wDist mv.nv) _ _).trans wr
      have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
      have a3 := scope_gS mv fu _ P (c10 n inf it r bd st cnt d w c) (c10 n inf it r bd st cnt d w c) (VD H T C Dd Dn) _ rfl a2 rfl
      have a4 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
      have b1 := pexecM_branch_true mv fu (cRel mv.nv) (Yr mv.nv) Sk _ _ 1 vc2 (by decide) _ a4
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      have b3 := scope_gS mv fu _ P (c10 n inf it r bd st cnt d w c) (c10 n inf it r bd st cnt d w c) (VD H T C Dd Dn) _ rfl b2 rfl
      have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
      have c1 := pexecM_branch_true mv fu (cDoneW mv.nv) (Y1p mv.nv) Sk _ _ 1 vc1 (by decide) _ b4
      have c2 := seqM_some c1 rfl (pexecM_skip mv fu _ _)
      have c3 := seqM_some q2 rfl c2
      have c4 := seqM_some q1 rfl c3
      obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (Xp mv.nv) (gS P (c8 n inf it r bd st cnt d))
          (VD H T C Dd Dn) = some rr ∧ rr.ps = gS P (c10 n inf it r bd st cnt d w c) ∧ rr.ret = none ∧
          rr.vv = VD H T C (Dd.set w c) Dn ∧ rr.cost ≤ 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 1 :=
        ⟨_, c4, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size],
          by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size], by simp⟩
      refine ⟨rr, hrr, hret, hps, ?_, hcost, hneed, hwk⟩
      rw [if_pos ⟨h0, hlt⟩]; exact hvv
    · have hc2 : (if c < Dd.getD w 0 then (1 : Int) else 0) = 0 := by rw [if_neg hlt]
      rw [hc2] at vc2
      have b1 := pexecM_branch_false mv fu (cRel mv.nv) (Yr mv.nv) Sk _ _ vc2 _ (pexecM_skip mv fu _ _)
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      have b3 := scope_gS mv fu _ P (c10 n inf it r bd st cnt d w c) (c10 n inf it r bd st cnt d w c) (VD H T C Dd Dn) _ rfl b2 rfl
      have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
      have c1 := pexecM_branch_true mv fu (cDoneW mv.nv) (Y1p mv.nv) Sk _ _ 1 vc1 (by decide) _ b4
      have c2 := seqM_some c1 rfl (pexecM_skip mv fu _ _)
      have c3 := seqM_some q2 rfl c2
      have c4 := seqM_some q1 rfl c3
      obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (Xp mv.nv) (gS P (c8 n inf it r bd st cnt d))
          (VD H T C Dd Dn) = some rr ∧ rr.ps = gS P (c10 n inf it r bd st cnt d w c) ∧ rr.ret = none ∧
          rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 1 :=
        ⟨_, c4, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size],
          by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size], by simp⟩
      refine ⟨rr, hrr, hret, hps, ?_, hcost, hneed, hwk⟩
      rw [if_neg (fun h => hlt h.2)]; exact hvv
  · have hc1 : (if ((Dn.getD w 0 : Nat) : Int) = 0 then (1 : Int) else 0) = 0 := by
      have : ¬ (((Dn.getD w 0 : Nat) : Int) = 0) := by omega
      rw [if_neg this]
    rw [hc1] at vc1
    have c1 := pexecM_branch_false mv fu (cDoneW mv.nv) (Y1p mv.nv) Sk _ _ vc1 _ (pexecM_skip mv fu _ _)
    have c2 := seqM_some c1 rfl (pexecM_skip mv fu _ _)
    have c3 := seqM_some q2 rfl c2
    have c4 := seqM_some q1 rfl c3
    obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (Xp mv.nv) (gS P (c8 n inf it r bd st cnt d))
        (VD H T C Dd Dn) = some rr ∧ rr.ps = gS P (c10 n inf it r bd st cnt d w c) ∧ rr.ret = none ∧
        rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 1 :=
      ⟨_, c4, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size],
        by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size], by simp⟩
    refine ⟨rr, hrr, hret, hps, ?_, hcost, hneed, hwk⟩
    rw [if_neg (fun h => h0 h.1)]; exact hvv

/-- Relaxing the first `d` arcs of `L` in order. -/
def foldRL (Dn : List Nat) (L : List Edge) (Dd0 : List Int) (d : Nat) : List Int := (L.take d).foldl (relaxL Dn) Dd0

theorem foldRL_succ (Dn : List Nat) (L : List Edge) (Dd0 : List Int) (d : Nat) (hd : d < L.length) :
    foldRL Dn L Dd0 (d + 1) = relaxL Dn (foldRL Dn L Dd0 d) L[d] := by
  unfold foldRL
  have h : L.take (d + 1) = L.take d ++ [L[d]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hd]
    rfl
  rw [h, List.foldl_append]
  rfl

theorem foldRL_full (Dn : List Nat) (L : List Edge) (Dd0 : List Int) : foldRL Dn L Dd0 L.length = L.foldl (relaxL Dn) Dd0 := by
  unfold foldRL; rw [List.take_length]

theorem relaxL_bounds (Dn : List Nat) (Dd : List Int) (e : Edge) (n : Nat) (inf : Int)
    (hb : ∀ j, j < n → 0 ≤ Dd.getD j 0 ∧ Dd.getD j 0 ≤ inf) (hc : 0 ≤ e.2.2 ∧ e.2.2 ≤ inf) :
    ∀ j, j < n → 0 ≤ (relaxL Dn Dd e).getD j 0 ∧ (relaxL Dn Dd e).getD j 0 ≤ inf := by
  intro j hj
  rw [Proofs.PrimRelax.relaxL_getD]
  by_cases h : Dn.getD e.2.1 0 = 0 ∧ e.2.2 < Dd.getD e.2.1 0 ∧ j = e.2.1 ∧ j < Dd.length
  · rw [if_pos h]; exact hc
  · rw [if_neg h]; exact hb j hj

set_option maxHeartbeats 8000000 in
/-- The relaxation loop `for (int d = 0; d < cnt; d++) {...}`. -/
theorem xp_loop (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd0 : List Int) (Dn : List Nat) (P : List Cell)
    (n it b : Nat) (inf bd : Int) (hn : n < M31) (hit : it < M31) (hb : b < n)
    (hn2 : n < 2147483647) (hTn : ∀ x ∈ T, x < n) (hTM : T.length < M31) (hCl : C.length = T.length)
    (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x ≤ inf) (hstc : H.getD b 0 + (outEdges H T C b).length ≤ T.length)
    (hDl : Dd0.length = n) (hDnl : Dn.length = n) (hDv : ∀ j, j < n → 0 ≤ Dd0.getD j 0 ∧ Dd0.getD j 0 ≤ inf)
    (hDnv : ∀ j, Dn.getD j 0 < M31) (hinf0 : 0 ≤ inf) (hinfB : inf ≤ 4611686018427387904) (hbd : 0 ≤ bd ∧ bd ≤ inf)
    (hcnt2 : (outEdges H T C b).length < 2147483647) (hstM : H.getD b 0 < M31)
    (fu : Nat) (hfu : (outEdges H T C b).length + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 7 6 (Xp mv.nv))
      (gS P (c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length)) (VD H T C Dd0 Dn) = some res ∧
      res.ps = gS P (c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length) ∧
      res.vv = VD H T C ((outEdges H T C b).foldl (relaxL Dn) Dd0) Dn ∧ res.ret = none ∧
      res.cost ≤ 420 * (outEdges H T C b).length + 30 ∧ res.need ≤ P.length + 80 ∧
      res.wk ≤ (outEdges H T C b).length := by
  have hnM : n < 2147483648 := hn
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 7 6 (outEdges H T C b).length (by omega) hcnt2
    (Xp mv.nv)
    (fun d vv Cl => vv = VD H T C (foldRL Dn (outEdges H T C b) Dd0 d) Dn ∧
      Cl = c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length ∧
      (∀ j, j < n → 0 ≤ (foldRL Dn (outEdges H T C b) Dd0 d).getD j 0 ∧ (foldRL Dn (outEdges H T C b) Dd0 d).getD j 0 ≤ inf))
    400 80 1 0 (by omega)
    (by
      intro d vv Cl fu hd hCl' hC0' ⟨hvv, hC, hgb⟩ _
      subst hvv; subst hC
      have hLb := outEdges_length H T C b
      have hdlt : d < (outEdges H T C b).length := hd
      obtain ⟨e, he⟩ : ∃ e, e = (outEdges H T C b)[d] := ⟨_, rfl⟩
      have he' : e = (b, T.getD (H.getD b 0 + d) 0, C.getD (H.getD b 0 + d) 0) := by
        rw [he]; exact outEdges_get H T C b d hdlt
      have hsd : H.getD b 0 + d < T.length := by omega
      have hwn : T.getD (H.getD b 0 + d) 0 < n := by
        rw [getD_ltN T _ hsd]; exact hTn _ (List.getElem_mem _)
      have hcmem : C.getD (H.getD b 0 + d) 0 ∈ C := Proofs.BellmanFordExec.getD_mem C _ (by omega)
      have hcb := hC0 _ hcmem
      have hbdv : s64.valid bd = true := Proofs.BellmanFordExec.s64_valid_of bd (by omega)
      have hcv : s64.valid (C.getD (H.getD b 0 + d) 0) = true :=
        Proofs.BellmanFordExec.s64_valid_of _ (by omega)
      have hDdl : (foldRL Dn (outEdges H T C b) Dd0 d).length = n := by
        unfold foldRL; rw [Proofs.PrimRelax.foldl_length]; exact hDl
      have hdwv : s64.valid ((foldRL Dn (outEdges H T C b) Dd0 d).getD (T.getD (H.getD b 0 + d) 0) 0) = true := by
        have := hgb _ hwn
        exact Proofs.BellmanFordExec.s64_valid_of _ (by omega)
      obtain ⟨rr, hrr, hret, hps, hvv, hcost, hneed, hwk⟩ := xp_body mv hnv hty0 hty1 hty2 hty3 hty4 H T C
        (foldRL Dn (outEdges H T C b) Dd0 d) Dn P n it (H.getD b 0) (outEdges H T C b).length d inf bd (some b) hn hit
        hstM (by omega) (by omega) hsd hTM hCl hDdl hDnl hwn hbdv
        (Proofs.BellmanFordExec.s64_valid_of inf (by omega)) (fun b' hb' => by simp at hb'; omega)
        hcv hdwv (hDnv _) fu
      have hsucc : foldRL Dn (outEdges H T C b) Dd0 (d + 1) = relaxL Dn (foldRL Dn (outEdges H T C b) Dd0 d) e := by
        rw [foldRL_succ Dn _ Dd0 d hdlt, he]
      have hvv' : rr.vv = VD H T C (foldRL Dn (outEdges H T C b) Dd0 (d + 1)) Dn := by
        rw [hvv, hsucc, he']
        unfold relaxL
        rfl
      have hbnd' : ∀ j, j < n → 0 ≤ (foldRL Dn (outEdges H T C b) Dd0 (d + 1)).getD j 0 ∧
          (foldRL Dn (outEdges H T C b) Dd0 (d + 1)).getD j 0 ≤ inf := by
        rw [hsucc]
        exact relaxL_bounds Dn _ e n inf hgb (by rw [he']; exact hcb)
      refine ⟨rr, [ci (T.getD (H.getD b 0 + d) 0), cs (C.getD (H.getD b 0 + d) 0)],
        c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length, hrr, hret, hps, rfl, rfl,
        ⟨hvv', rfl, hbnd'⟩, hcost, hneed, hwk⟩)
    (VD H T C (foldRL Dn (outEdges H T C b) Dd0 0) Dn) (c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length)
    rfl rfl ⟨rfl, rfl, by simpa [foldRL] using hDv⟩ fu (by omega)
  obtain ⟨hvv, hC, hgb⟩ := hIn
  subst hC
  refine ⟨res, hr', hps, ?_, hret, ?_, ?_, ?_⟩
  · rw [hvv, foldRL_full]
  · omega
  · omega
  · omega

/-! ### The fallback loop: the first unvisited vertex starts a new component -/

/-- One step of the fallback scan: `if (best < 0) if (done[v] == 0) { best = v; bd = 0; }`. -/
def fbStepL (Dn : List Nat) (s : Option Nat × Int) (v : Nat) : Option Nat × Int :=
  if s.1 = none ∧ Dn.getD v 0 = 0 then (some v, 0) else s

def fbSt (inf : Int) (Dn : List Nat) (t : Nat) : Option Nat × Int := (List.range t).foldl (fbStepL Dn) (none, inf)

theorem fbSt_succ (inf : Int) (Dn : List Nat) (t : Nat) : fbSt inf Dn (t + 1) = fbStepL Dn (fbSt inf Dn t) t := by
  unfold fbSt
  rw [List.range_succ, List.foldl_append]
  rfl

theorem zero_cast_den (env : Nat → Ty → Option Int) :
    (NExpr.cast s64 (.literal i32 0)).denote env = some 0 := by
  have a : i32.valid 0 = true := by simp [Ty.valid]
  have b : s64.valid 0 = true := by simp [Ty.valid]
  simp [NExpr.denote, a, Ty.convert_of_valid _ _ b]

theorem cNeg_val (mv : MV) (hnv : mv.nv = 5) (vv : Nat → List Int) (P cells : List Cell) (r : Option Nat)
    (hc : cells[3]? = some (cb r)) (hr : ∀ b, r = some b → b < M31) :
    vdenM mv vv (penvN mv.nv (gS P cells)) (cNeg mv.nv) = some (if r = none then 1 else 0) := by
  have e3 : penvN mv.nv (gS P cells) (mv.nv + 3) i32 = some (bI r) := by
    have := gSM_env mv.nv P cells 3 (cb r) hc (bI_valid r hr)
    exact this
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e3, Option.bind_some, zero_den, Option.bind_some]
  have h := lt_conv (bI r) 0
  rcases r with _ | b
  · have : (bI none) < 0 := by show (-1 : Int) < 0; omega
    rw [if_pos this] at h
    simpa using h
  · have : ¬ (bI (some b) < 0) := by show ¬ ((b : Int) < 0); omega
    rw [if_neg this] at h
    simpa using h

set_option maxHeartbeats 8000000 in
/-- One iteration of the fallback loop. -/
theorem fb_body (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it v : Nat) (inf bd : Int) (r : Option Nat) (hn : n < M31) (hit : it < M31) (hv : v < n)
    (hDnl : Dn.length = n) (hdn : Dn.getD v 0 < M31) (hbd : s64.valid bd = true) (hinf : s64.valid inf = true)
    (hr : ∀ b, r = some b → b < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (FB mv.nv) (gS P [ci n, cs inf, ci it, cb r, cs bd, ci v]) (VD H T C Dd Dn) = some rr ∧
      rr.ret = none ∧
      rr.ps = gS P [ci n, cs inf, ci it, cb (fbStepL Dn (r, bd) v).1, cs (fbStepL Dn (r, bd) v).2, ci v] ∧
      rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 300 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 0 := by
  have hcells : [ci n, cs inf, ci it, cb r, cs bd, ci v][3]? = some (cb r) := rfl
  have vn := cNeg_val mv hnv (VD H T C Dd Dn) P [ci n, cs inf, ci it, cb r, cs bd, ci v] r hcells hr
  rcases r with _ | b0
  · rw [if_pos rfl] at vn
    -- best < 0: look at done[v]
    have E5 := envs mv P [ci n, cs inf, ci it, cb none, cs bd, ci v] 5 (ci v) rfl (i32v v (by omega))
    have vdone := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb none, cs bd, ci v])) 4 (by omega) i32
      (hty4).symm (ix mv.nv 5) rfl rfl v (cidx_den _ (mv.nv + 5) v E5 (by omega)) ((Dn.getD v 0 : Nat) : Int)
      (by rw [VD_get4]; exact natList_get Dn v (by omega)) (by rw [hty4]; exact i32v _ hdn)
    have vc : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb none, cs bd, ci v])) (cDone mv.nv) =
        some (if ((Dn.getD v 0 : Nat) : Int) = 0 then 1 else 0) := by
      rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdone, Option.bind_some, vdenM_scalar _ _ _ _ rfl, zero_den, Option.bind_some]
      exact eq_conv _ _
    by_cases h0 : Dn.getD v 0 = 0
    · have hc1 : (if ((Dn.getD v 0 : Nat) : Int) = 0 then (1 : Int) else 0) = 1 := by rw [h0]; simp
      rw [hc1] at vc
      -- best = v; bd = 0
      have E5' := envs mv P [ci n, cs inf, ci it, cb none, cs bd, ci v] 5 (ci v) rfl (i32v v (by omega))
      have vv5 : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb none, cs bd, ci v]))
          (.variable i32 (mv.nv + 5)) = some (v : Int) := by
        rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E5'
      have as1 := gSM_assign mv P [ci n, cs inf, ci it, cb none, cs bd, ci v] (VD H T C Dd Dn) 3 (by simp) i32 _ _ (v : Int)
        vv5 (cb none) rfl rfl (bI_valid none (by simp)) (conv_signed i32 rfl rfl _ (i32v v (by omega)))
      have a1 := (pexecM_prim mv fu (aBest mv.nv) _ _).trans as1
      have vz : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb (some v), cs bd, ci v]))
          (.cast s64 (.literal i32 0)) = some 0 := by
        rw [vdenM_scalar _ _ _ _ rfl]; exact zero_cast_den _
      have as2 := gSM_assign mv P [ci n, cs inf, ci it, cb (some v), cs bd, ci v] (VD H T C Dd Dn) 4 (by simp) s64 _ _ 0
        vz (cs bd) rfl rfl hbd (conv_signed s64 rfl rfl _ (by simp [Ty.valid]))
      have a2 := (pexecM_prim mv fu (aZero mv.nv) _ _).trans as2
      have a3 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
      have a4 := seqM_some a1 rfl a3
      have a5 := scope_gS mv fu _ P [ci n, cs inf, ci it, cb none, cs bd, ci v]
        [ci n, cs inf, ci it, cb (some v), cs 0, ci v] (VD H T C Dd Dn) _ (by simp) a4 rfl
      have a6 := seqM_some a5 rfl (pexecM_skip mv fu _ _)
      have b1 := pexecM_branch_true mv fu (cDone mv.nv) (.sequence (.scope (.sequence (.primitive (aBest mv.nv))
        (.sequence (.primitive (aZero mv.nv)) Sk))) Sk) Sk _ _ 1 vc (by decide) _ a6
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      have b3 := scope_gS mv fu _ P [ci n, cs inf, ci it, cb none, cs bd, ci v]
        [ci n, cs inf, ci it, cb (some v), cs 0, ci v] (VD H T C Dd Dn) _ (by simp) b2 rfl
      have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
      have hvn : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb none, cs bd, ci v])) (cNeg mv.nv) = some 1 := vn
      have c1 := pexecM_branch_true mv fu (cNeg mv.nv) (FBthen mv.nv) Sk _ _ 1 hvn (by decide) _ b4
      have c2 := seqM_some c1 rfl (pexecM_skip mv fu _ _)
      have hst : fbStepL Dn (none, bd) v = (some v, 0) := by
        unfold fbStepL; rw [if_pos ⟨rfl, h0⟩]
      obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (FB mv.nv)
          (gS P [ci n, cs inf, ci it, cb none, cs bd, ci v]) (VD H T C Dd Dn) = some rr ∧
          rr.ps = gS P [ci n, cs inf, ci it, cb (some v), cs 0, ci v] ∧ rr.ret = none ∧
          rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 300 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 0 :=
        ⟨_, c2, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size],
          by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size], by simp⟩
      refine ⟨rr, hrr, hret, ?_, hvv, hcost, hneed, hwk⟩
      rw [hst]
      exact hps
    · have hc1 : (if ((Dn.getD v 0 : Nat) : Int) = 0 then (1 : Int) else 0) = 0 := by
        have : ¬ (((Dn.getD v 0 : Nat) : Int) = 0) := by omega
        rw [if_neg this]
      rw [hc1] at vc
      have b1 := pexecM_branch_false mv fu (cDone mv.nv) (.sequence (.scope (.sequence (.primitive (aBest mv.nv))
        (.sequence (.primitive (aZero mv.nv)) Sk))) Sk) Sk _ _ vc _ (pexecM_skip mv fu _ _)
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      have b3 := scope_gS mv fu _ P [ci n, cs inf, ci it, cb none, cs bd, ci v]
        [ci n, cs inf, ci it, cb none, cs bd, ci v] (VD H T C Dd Dn) _ rfl b2 rfl
      have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
      have hvn : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb none, cs bd, ci v])) (cNeg mv.nv) = some 1 := vn
      have c1 := pexecM_branch_true mv fu (cNeg mv.nv) (FBthen mv.nv) Sk _ _ 1 hvn (by decide) _ b4
      have c2 := seqM_some c1 rfl (pexecM_skip mv fu _ _)
      have hst : fbStepL Dn (none, bd) v = (none, bd) := by
        unfold fbStepL; rw [if_neg (fun h => h0 h.2)]
      obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (FB mv.nv)
          (gS P [ci n, cs inf, ci it, cb none, cs bd, ci v]) (VD H T C Dd Dn) = some rr ∧
          rr.ps = gS P [ci n, cs inf, ci it, cb none, cs bd, ci v] ∧ rr.ret = none ∧
          rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 300 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 0 :=
        ⟨_, c2, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size],
          by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size], by simp⟩
      refine ⟨rr, hrr, hret, ?_, hvv, hcost, hneed, hwk⟩
      rw [hst]
      exact hps
  · have : ¬ ((some b0 : Option Nat) = none) := by simp
    rw [if_neg this] at vn
    have c1 := pexecM_branch_false mv fu (cNeg mv.nv) (FBthen mv.nv) Sk _ _ vn _ (pexecM_skip mv fu _ _)
    have c2 := seqM_some c1 rfl (pexecM_skip mv fu _ _)
    have hst : fbStepL Dn (some b0, bd) v = (some b0, bd) := by
      unfold fbStepL; rw [if_neg (fun h => by simp at h)]
    obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (FB mv.nv)
        (gS P [ci n, cs inf, ci it, cb (some b0), cs bd, ci v]) (VD H T C Dd Dn) = some rr ∧
        rr.ps = gS P [ci n, cs inf, ci it, cb (some b0), cs bd, ci v] ∧ rr.ret = none ∧
        rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 300 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 0 :=
      ⟨_, c2, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size],
        by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size], by simp⟩
    refine ⟨rr, hrr, hret, ?_, hvv, hcost, hneed, hwk⟩
    rw [hst]
    exact hps

theorem fbSt_shape (inf : Int) (Dn : List Nat) :
    ∀ t, ((fbSt inf Dn t).1 = none → (fbSt inf Dn t).2 = inf ∧ ∀ v, v < t → Dn.getD v 0 ≠ 0) ∧
      ∀ b, (fbSt inf Dn t).1 = some b → b < t ∧ Dn.getD b 0 = 0 ∧ (fbSt inf Dn t).2 = 0 ∧ ∀ v, v < b → Dn.getD v 0 ≠ 0 := by
  intro t
  induction t with
  | zero => exact ⟨fun _ => ⟨rfl, fun v hv => by omega⟩, fun b hb => by simp [fbSt] at hb⟩
  | succ t ih =>
    rw [fbSt_succ]
    generalize hs : fbSt inf Dn t = s at ih ⊢
    unfold fbStepL
    by_cases hg : s.1 = none ∧ Dn.getD t 0 = 0
    · rw [if_pos hg]
      refine ⟨fun h => by simp at h, fun b hb => ?_⟩
      simp only [Option.some.injEq] at hb
      subst hb
      exact ⟨by omega, hg.2, rfl, fun v hv => (ih.1 hg.1).2 v hv⟩
    · rw [if_neg hg]
      refine ⟨fun h => ?_, fun b hb => ?_⟩
      · have h1 := ih.1 h
        refine ⟨h1.1, fun v hv => ?_⟩
        by_cases hvt : v = t
        · subst hvt
          intro hz
          exact hg ⟨h, hz⟩
        · exact h1.2 v (by omega)
      · have := ih.2 b hb
        exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩

set_option maxHeartbeats 8000000 in
/-- The fallback loop `for (int v = 0; v < n; v++) if (best < 0) if (done[v] == 0) {best = v; bd = 0;}`. -/
theorem l_fb (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it : Nat) (inf : Int) (hn : n < M31) (hn2 : n < 2147483647) (hit : it < M31) (hDnl : Dn.length = n)
    (hDnv : ∀ j, Dn.getD j 0 < M31) (hinf : s64.valid inf = true) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 5 0 (FB mv.nv)) (gS P [ci n, cs inf, ci it, cb none, cs inf])
      (VD H T C Dd Dn) = some res ∧
      res.ps = gS P [ci n, cs inf, ci it, cb (fbSt inf Dn n).1, cs (fbSt inf Dn n).2] ∧
      res.vv = VD H T C Dd Dn ∧ res.ret = none ∧ res.cost ≤ 320 * n + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ 0 := by
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 5 0 n (by omega) hn2 (FB mv.nv)
    (fun t vv Cl => vv = VD H T C Dd Dn ∧
      Cl = [ci n, cs inf, ci it, cb (fbSt inf Dn t).1, cs (fbSt inf Dn t).2]) 300 80 0 0 (by omega)
    (by
      intro t vv Cl fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hsh := fbSt_shape inf Dn t
      have hbdv : s64.valid (fbSt inf Dn t).2 = true := by
        rcases hr : (fbSt inf Dn t).1 with _ | b
        · rw [(hsh.1 hr).1]; exact hinf
        · rw [(hsh.2 b hr).2.2.1]; simp [Ty.valid]
      have hrM : ∀ b, (fbSt inf Dn t).1 = some b → b < M31 := by
        intro b hb
        have := (hsh.2 b hb).1
        have : t < n := ht
        have : n < M31 := hn
        omega
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := fb_body mv hnv hty0 hty1 hty2 hty3 hty4 H T C Dd Dn P n it t inf
        (fbSt inf Dn t).2 (fbSt inf Dn t).1 hn hit ht hDnl (hDnv t) hbdv hinf hrM fu
      refine ⟨r, [], [ci n, cs inf, ci it, cb (fbSt inf Dn (t + 1)).1, cs (fbSt inf Dn (t + 1)).2], hr, hret,
        ?_, rfl, rfl, ⟨hvv, rfl⟩, hc, hnd, hwk⟩
      rw [fbSt_succ]
      exact hps)
    (VD H T C Dd Dn) [ci n, cs inf, ci it, cb (fbSt inf Dn 0).1, cs (fbSt inf Dn 0).2] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hIn
  subst hC
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

set_option maxHeartbeats 8000000 in
/-- The tail of an iteration: `done[best] = 1; dist[best] = bd; start = ...; cnt = ...;` and the relaxation loop. -/
theorem b_tail (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it b : Nat) (inf bd : Int) (hn : n < M31) (hit : it < M31) (hb : b < n) (hn2 : n < 2147483647)
    (HK : Proofs.TopoSortMath.HeadOK H T n) (hDnl : Dn.length = n) (hDdl : Dd.length = n)
    (hTn : ∀ x ∈ T, x < n) (hTM : T.length < M31) (hCl : C.length = T.length) (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x ≤ inf)
    (hDv : ∀ j, j < n → 0 ≤ Dd.getD j 0 ∧ Dd.getD j 0 ≤ inf) (hDnv : ∀ j, Dn.getD j 0 < M31)
    (hinf0 : 0 ≤ inf) (hinfB : inf ≤ 4611686018427387904) (hbd : 0 ≤ bd ∧ bd ≤ inf)
    (hcnt2 : (outEdges H T C b).length < 2147483647) (fu : Nat) (hfu : (outEdges H T C b).length + 2 ≤ fu) :
    ∃ rr : PRM, pexecM mv fu (Tl mv.nv) (gS P (c5 n inf it (some b) bd)) (VD H T C Dd Dn) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P (c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length) ∧
      rr.vv = VD H T C ((outEdges H T C b).foldl (relaxL (Dn.set b 1)) (Dd.set b bd)) (Dn.set b 1) ∧
      rr.cost ≤ 420 * (outEdges H T C b).length + 200 ∧ rr.need ≤ P.length + 80 ∧
      rr.wk ≤ (outEdges H T C b).length + 2 := by
  have hnM : n < 2147483648 := hn
  have hHl : H.length = n + 1 := HK.len
  have hHle : ∀ j, j ≤ n → H.getD j 0 ≤ T.length := by
    intro j hj
    have := Proofs.TopoSortMath.HeadOK.le H T n HK n (Nat.le_refl _) j hj
    rw [HK.last] at this
    exact this
  have hmono := HK.mono b hb
  have hcntE : (outEdges H T C b).length = H.getD (b + 1) 0 - H.getD b 0 := outEdges_length H T C b
  have hcM : H.getD (b + 1) 0 ≤ T.length := hHle (b + 1) (by omega)
  have hstM' : H.getD b 0 ≤ T.length := hHle b (by omega)
  have E3 := envs mv P (c5 n inf it (some b) bd) 3 (cb (some b)) rfl (i32v b (by omega))
  have hp : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c5 n inf it (some b) bd))) (ix mv.nv 3) = some (b : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 3) b E3 (by omega)
  have hx1 : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c5 n inf it (some b) bd))) DijkstraOldScan.lit1 =
      some (((1 : Nat) : Int)) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact DijkstraOldScan.one_den _
  have wr := pstmtM_write_ok mv (gS P (c5 n inf it (some b) bd)) (VD H T C Dd Dn) 4 (by omega) (ix mv.nv 3)
    DijkstraOldScan.lit1 ((1 : Nat) : Int) b hx1 hp (by rw [VD_get4]; simp [hDnl]; exact hb)
    (by rw [hty4]; exact i32v 1 (by decide))
  rw [hty4, VD_write4] at wr
  have w1 := (pexecM_prim mv fu (wDone mv.nv) _ _).trans wr
  -- dist[best] = bd
  have E4 := envs mv P (c5 n inf it (some b) bd) 4 (cs bd) rfl (Proofs.BellmanFordExec.s64_valid_of bd (by omega))
  have hx2 : vdenM mv (VD H T C Dd (Dn.set b 1)) (penvN mv.nv (gS P (c5 n inf it (some b) bd))) (.variable s64 (mv.nv + 4)) =
      some bd := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E4
  have hp2 : vdenM mv (VD H T C Dd (Dn.set b 1)) (penvN mv.nv (gS P (c5 n inf it (some b) bd))) (ix mv.nv 3) = some (b : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 3) b E3 (by omega)
  have wr2 := pstmtM_write_ok mv (gS P (c5 n inf it (some b) bd)) (VD H T C Dd (Dn.set b 1)) 3 (by omega) (ix mv.nv 3)
    (.variable s64 (mv.nv + 4)) bd b hx2 hp2 (by rw [VD_get3]; omega)
    (by rw [hty3]; exact Proofs.BellmanFordExec.s64_valid_of bd (by omega))
  rw [hty3, VD_get3, VD_write3] at wr2
  have w2 := (pexecM_prim mv fu (wDistB mv.nv) _ _).trans wr2
  -- start = head[b]
  have vst := rdM_val mv (VD H T C (Dd.set b bd) (Dn.set b 1)) (penvN mv.nv (gS P (c5 n inf it (some b) bd))) 0 (by omega) i32
    (hty0).symm (ix mv.nv 3) rfl rfl b (cidx_den _ (mv.nv + 3) b E3 (by omega)) ((H.getD b 0 : Nat) : Int)
    (by rw [VD_get0]; exact natList_get H b (by omega)) (by rw [hty0]; exact i32v _ (by omega))
  have d1 := gSM_decl mv P (c5 n inf it (some b) bd) (VD H T C (Dd.set b bd) (Dn.set b 1)) i32 _ _ _ vst
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q1 := (pexecM_prim mv fu (dStart mv.nv) _ _).trans d1
  -- cnt = head[b+1] - start
  have E3'' := envs mv P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)]) 3 (cb (some b)) rfl (i32v b (by omega))
  have E5 := envs mv P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)]) 5 (ci (H.getD b 0)) rfl (i32v _ (by omega))
  have vh1 := rdM_val mv (VD H T C (Dd.set b bd) (Dn.set b 1)) (penvN mv.nv (gS P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)]))) 0
    (by omega) i32 (hty0).symm (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 3)) DijkstraOldScan.lit1)) rfl rfl (b + 1)
    (succIdx_den _ (mv.nv + 3) b E3'' (by omega)) ((H.getD (b + 1) 0 : Nat) : Int)
    (by rw [VD_get0]; exact natList_get H (b + 1) (by omega)) (by rw [hty0]; exact i32v _ (by omega))
  have vcnt : vdenM mv (VD H T C (Dd.set b bd) (Dn.set b 1)) (penvN mv.nv (gS P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)])))
      (dCntE mv.nv) = some ((H.getD (b + 1) 0 - H.getD b 0 : Nat) : Int) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vh1, Option.bind_some, vdenM_scalar _ _ _ _ rfl, den_variable, E5, Option.bind_some]
    have : binaryValue .sub ((H.getD (b + 1) 0 : Nat) : Int) ((H.getD b 0 : Nat) : Int) =
        ((H.getD (b + 1) 0 - H.getD b 0 : Nat) : Int) := by
      show _ - _ = _; omega
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ (by omega))
  have d2 := gSM_decl mv P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)]) (VD H T C (Dd.set b bd) (Dn.set b 1)) i32 _ _ _ vcnt
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q2 := (pexecM_prim mv fu (dCnt mv.nv) _ _).trans d2
  rw [← hcntE] at q2
  -- the relaxation loop
  have hDdl' : (Dd.set b bd).length = n := by simp [hDdl]
  have hDnl' : (Dn.set b 1).length = n := by simp [hDnl]
  have hDv' : ∀ j, j < n → 0 ≤ (Dd.set b bd).getD j 0 ∧ (Dd.set b bd).getD j 0 ≤ inf := by
    intro j hj
    by_cases hjb : j = b
    · subst hjb; rw [Proofs.PrimRelax.getD_set_same _ _ _ (by omega)]; exact hbd
    · rw [Proofs.PrimRelax.getD_set_ne _ _ _ _ hjb]; exact hDv j hj
  have hDnv' : ∀ j, (Dn.set b 1).getD j 0 < M31 := by
    intro j
    by_cases hjb : j = b
    · subst hjb
      by_cases hl : j < Dn.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hl]; simp
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set]
        simp [hl]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjb)]
      rw [← List.getD_eq_getElem?_getD]; exact hDnv j
  obtain ⟨rl, hrl, hrlps, hrlvv, hrlret, hrlc, hrln, hrlw⟩ := xp_loop mv hnv hty0 hty1 hty2 hty3 hty4 H T C (Dd.set b bd) (Dn.set b 1)
    P n it b inf bd hn hit hb hn2 hTn hTM hCl hC0 (by omega) hDdl' hDnl' hDv' hDnv' hinf0 hinfB hbd hcnt2 (by omega) fu (by omega)
  have f1 := seqM_some hrl hrlret (pexecM_skip mv fu _ _)
  have f2 := seqM_some q2 rfl f1
  have f3 := seqM_some q1 rfl f2
  have f4 := seqM_some w2 rfl f3
  have f5 := seqM_some w1 rfl f4
  refine ⟨_, f5, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hrlps
  · simpa using hrlvv
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrlc ⊢; omega
  · simp [hrlps, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrln ⊢; omega
  · simp at hrlw ⊢; omega

/-! ### One iteration -/

theorem scanSt_inv (inf : Int) (Dn : List Nat) (Dd : List Int) :
    ∀ t, (scanSt inf Dn Dd t).2 ≤ inf ∧
      ((scanSt inf Dn Dd t).1 = none → (scanSt inf Dn Dd t).2 = inf ∧ ∀ x, x < t → Dn.getD x 0 = 0 → inf ≤ Dd.getD x 0) ∧
      ∀ b, (scanSt inf Dn Dd t).1 = some b → b < t ∧ Dn.getD b 0 = 0 ∧ Dd.getD b 0 = (scanSt inf Dn Dd t).2 ∧
        (scanSt inf Dn Dd t).2 < inf ∧ ∀ x, x < t → Dn.getD x 0 = 0 → (scanSt inf Dn Dd t).2 ≤ Dd.getD x 0 := by
  intro t
  induction t with
  | zero => exact ⟨Int.le_refl _, fun _ => ⟨rfl, fun x hx => by omega⟩, fun b hb => by simp [scanSt] at hb⟩
  | succ t ih =>
    rw [scanSt_succ]
    generalize hs : scanSt inf Dn Dd t = s at ih ⊢
    unfold scanStepL
    by_cases hg : Dn.getD t 0 = 0 ∧ Dd.getD t 0 < s.2
    · rw [if_pos hg]
      refine ⟨by show Dd.getD t 0 ≤ inf; have := ih.1; omega, fun h => by simp at h, fun b hb => ?_⟩
      simp only [Option.some.injEq] at hb
      subst hb
      refine ⟨by omega, hg.1, rfl, by show Dd.getD t 0 < inf; have := ih.1; omega, fun x hx hxD => ?_⟩
      simp only
      by_cases hxk : x = t
      · subst hxk; exact Int.le_refl _
      · have hxl : x < t := by omega
        rcases hs1 : s.1 with _ | b0
        · have := (ih.2.1 hs1).2 x hxl hxD
          have := ih.1
          omega
        · have := (ih.2.2 b0 hs1).2.2.2.2 x hxl hxD
          omega
    · rw [if_neg hg]
      refine ⟨ih.1, fun h => ⟨(ih.2.1 h).1, fun x hx hxD => ?_⟩, fun b hb => ?_⟩
      · by_cases hxk : x = t
        · subst hxk
          have h1 := (ih.2.1 h).1
          have : ¬ Dd.getD x 0 < s.2 := fun hh => hg ⟨hxD, hh⟩
          omega
        · exact (ih.2.1 h).2 x (by omega) hxD
      · have := ih.2.2 b hb
        refine ⟨by omega, this.2.1, this.2.2.1, this.2.2.2.1, fun x hx hxD => ?_⟩
        by_cases hxk : x = t
        · subst hxk
          have : ¬ Dd.getD x 0 < s.2 := fun hh => hg ⟨hxD, hh⟩
          omega
        · exact this.2.2.2.2 x (by omega) hxD

/-- The vertex picked by the iteration: the scan's minimum, or else the first unvisited vertex. -/
def pickRes (inf : Int) (Dn : List Nat) (Dd : List Int) (n : Nat) : Option Nat × Int :=
  if (scanSt inf Dn Dd n).1 = none then fbSt inf Dn n else scanSt inf Dn Dd n

set_option maxHeartbeats 8000000 in
/-- `if (best < 0) {fallback loop}`. -/
theorem brfb_exec (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it : Nat) (inf bd : Int) (r : Option Nat) (hn : n < M31) (hn2 : n < 2147483647) (hit : it < M31)
    (hDnl : Dn.length = n) (hDnv : ∀ j, Dn.getD j 0 < M31) (hinf : s64.valid inf = true)
    (hr : ∀ b, r = some b → b < M31) (hbdinf : r = none → bd = inf) (fu : Nat) (hfu : n + 3 ≤ fu) :
    ∃ rr : PRM, pexecM mv fu (BRfb mv.nv) (gS P (c5 n inf it r bd)) (VD H T C Dd Dn) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P (c5 n inf it (if r = none then (fbSt inf Dn n).1 else r) (if r = none then (fbSt inf Dn n).2 else bd)) ∧
      rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 320 * n + 100 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 0 := by
  have hcells : (c5 n inf it r bd)[3]? = some (cb r) := rfl
  have vn := cNeg_val mv hnv (VD H T C Dd Dn) P (c5 n inf it r bd) r hcells hr
  rcases r with _ | b0
  · rw [if_pos rfl] at vn
    have hbd := hbdinf rfl
    subst hbd
    obtain ⟨res, hres, hresps, hresvv, hresret, hresc, hresn, hresw⟩ := l_fb mv hnv hty0 hty1 hty2 hty3 hty4 H T C Dd Dn P n it bd hn hn2 hit
      hDnl hDnv hinf fu (by omega)
    have a1 := seqM_some hres hresret (pexecM_skip mv fu _ _)
    have a2 := scope_gS mv fu _ P (c5 n bd it none bd) (c5 n bd it (fbSt bd Dn n).1 (fbSt bd Dn n).2) (VD H T C Dd Dn) _
      (by simp) a1 (by simp [hresps])
    have a3 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu (cNeg mv.nv) (BRthen mv.nv) Sk _ _ 1 vn (by decide) _ a3
    refine ⟨_, b1, by simpa using hresret, by simp, by simpa using hresvv, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hresc ⊢; omega
    · simp [hresps, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hresn ⊢; omega
    · simp at hresw ⊢; omega
  · have : ¬ ((some b0 : Option Nat) = none) := by simp
    rw [if_neg this] at vn
    have b1 := pexecM_branch_false mv fu (cNeg mv.nv) (BRthen mv.nv) Sk _ _ vn _ (pexecM_skip mv fu _ _)
    refine ⟨_, b1, rfl, by simp [this], rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp

set_option maxHeartbeats 8000000 in
/-- One iteration of the outer loop. -/
theorem b_iter (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it : Nat) (inf : Int) (hn : n < M31) (hn2 : n < 2147483647) (hit : it < M31)
    (HK : Proofs.TopoSortMath.HeadOK H T n) (hTn : ∀ x ∈ T, x < n) (hTM : T.length < 2147483647) (hCl : C.length = T.length)
    (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x ≤ inf) (hDl : Dd.length = n) (hDnl : Dn.length = n)
    (hDv : ∀ j, j < n → 0 ≤ Dd.getD j 0 ∧ Dd.getD j 0 ≤ inf) (hDnv : ∀ j, Dn.getD j 0 < M31)
    (hinf0 : 0 ≤ inf) (hinfB : inf ≤ 4611686018427387904) (hex : ∃ v, v < n ∧ Dn.getD v 0 = 0)
    (fu : Nat) (hfu : n + T.length + 6 ≤ fu) :
    ∃ (rr : PRM) (b : Nat) (bd' : Int), pickRes inf Dn Dd n = (some b, bd') ∧ b < n ∧ Dn.getD b 0 = 0 ∧ 0 ≤ bd' ∧ bd' ≤ inf ∧
      ((bd' < inf ∧ Dd.getD b 0 = bd' ∧ ∀ x, x < n → Dn.getD x 0 = 0 → bd' ≤ Dd.getD x 0) ∨
        (bd' = 0 ∧ ∀ x, x < n → Dn.getD x 0 = 0 → inf ≤ Dd.getD x 0)) ∧
      pexecM mv fu (Bp mv.nv) (gS P [ci n, cs inf, ci it]) (VD H T C Dd Dn) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P (c7 n inf it (some b) bd' (H.getD b 0) (outEdges H T C b).length) ∧
      rr.vv = VD H T C ((outEdges H T C b).foldl (relaxL (Dn.set b 1)) (Dd.set b bd')) (Dn.set b 1) ∧
      rr.cost ≤ 640 * n + 420 * (outEdges H T C b).length + 600 ∧ rr.need ≤ P.length + 80 ∧
      rr.wk ≤ (outEdges H T C b).length + 2 := by
  have hnM : n < 2147483648 := hn
  have hinfv : s64.valid inf = true := Proofs.BellmanFordExec.s64_valid_of inf (by omega)
  have hDdv : ∀ j, s64.valid (Dd.getD j 0) = true := by
    intro j
    by_cases hj : j < n
    · have := hDv j hj
      exact Proofs.BellmanFordExec.s64_valid_of _ (by omega)
    · have : Dd.getD j 0 = 0 := getD_oob _ _ _ (by omega)
      rw [this]; exact Proofs.BellmanFordExec.s64_valid_of _ (by omega)
  -- the two declarations
  have E1 := envs mv P [ci n, cs inf, ci it, cb none] 1 (cs inf) rfl hinfv
  have vneg : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it])) (.unary i32 .neg DijkstraOldScan.lit1)
      = some (-1) := by
    rw [vdenM_scalar _ _ _ _ rfl]; rfl
  have d1 := gSM_decl mv P [ci n, cs inf, ci it] (VD H T C Dd Dn) i32 _ _ _ vneg
    (conv_signed i32 rfl rfl _ (show i32.valid (-1) = true from rfl))
  have q1 := (pexecM_prim mv fu dBest _ _).trans d1
  have vinf : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb none])) (.variable s64 (mv.nv + 1))
      = some inf := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1
  have d2 := gSM_decl mv P [ci n, cs inf, ci it, cb none] (VD H T C Dd Dn) s64 _ _ _ vinf
    (conv_signed s64 rfl rfl _ hinfv)
  have q2 := (pexecM_prim mv fu (dBd mv.nv) _ _).trans d2
  -- the scan
  obtain ⟨rs, hrs, hrsps, hrsvv, hrsret, hrsc, hrsn, hrsw⟩ := l_scan mv hnv hty0 hty1 hty2 hty3 hty4 H T C Dd Dn P
    n it inf hn hn2 hit hDnl hDl hDnv hDdv hinfv fu (by omega)
  have hSI := scanSt_inv inf Dn Dd n
  have hSsh := scanSt_shape inf Dn Dd n
  -- the fallback branch
  have hrM : ∀ b, (scanSt inf Dn Dd n).1 = some b → b < M31 := by
    intro b hb
    have := (hSsh.2 b hb).1
    omega
  obtain ⟨rf, hrf, hrfret, hrfps, hrfvv, hrfc, hrfn, hrfw⟩ := brfb_exec mv hnv hty0 hty1 hty2 hty3 hty4 H T C Dd Dn P n it inf
    (scanSt inf Dn Dd n).2 (scanSt inf Dn Dd n).1 hn hn2 hit hDnl hDnv hinfv hrM (fun h => hSsh.1 h) fu (by omega)
  -- which vertex was picked
  have hpick : ∃ b bd', pickRes inf Dn Dd n = (some b, bd') ∧ b < n ∧ Dn.getD b 0 = 0 ∧ 0 ≤ bd' ∧ bd' ≤ inf ∧
      ((bd' < inf ∧ Dd.getD b 0 = bd' ∧ ∀ x, x < n → Dn.getD x 0 = 0 → bd' ≤ Dd.getD x 0) ∨
        (bd' = 0 ∧ ∀ x, x < n → Dn.getD x 0 = 0 → inf ≤ Dd.getD x 0)) := by
    unfold pickRes
    by_cases hnone : (scanSt inf Dn Dd n).1 = none
    · rw [if_pos hnone]
      have hall := (hSI.2.1 hnone).2
      rcases hf : (fbSt inf Dn n).1 with _ | b
      · exfalso
        obtain ⟨v, hv, hv0⟩ := hex
        exact ((fbSt_shape inf Dn n).1 hf).2 v hv hv0
      · have hs := (fbSt_shape inf Dn n).2 b hf
        refine ⟨b, 0, ?_, hs.1, hs.2.1, Int.le_refl _, hinf0, Or.inr ⟨rfl, hall⟩⟩
        rw [← hs.2.2.1]
        exact Prod.ext hf rfl
    · rw [if_neg hnone]
      obtain ⟨b, hb⟩ : ∃ b, (scanSt inf Dn Dd n).1 = some b := by
        cases h : (scanSt inf Dn Dd n).1 with
        | none => exact absurd h hnone
        | some b => exact ⟨b, rfl⟩
      have hs := hSI.2.2 b hb
      have hb0 := hDv b hs.1
      refine ⟨b, (scanSt inf Dn Dd n).2, Prod.ext hb rfl, hs.1, hs.2.1, by omega, hs.2.2.2.1.le, Or.inl ⟨hs.2.2.2.1, hs.2.2.1, hs.2.2.2.2⟩⟩
  obtain ⟨b, bd', hpr, hbn, hb0, hbd0, hbdI, hcase⟩ := hpick
  have hrfpick : (if (scanSt inf Dn Dd n).1 = none then (fbSt inf Dn n).1 else (scanSt inf Dn Dd n).1) = some b ∧
      (if (scanSt inf Dn Dd n).1 = none then (fbSt inf Dn n).2 else (scanSt inf Dn Dd n).2) = bd' := by
    unfold pickRes at hpr
    by_cases hnone : (scanSt inf Dn Dd n).1 = none
    · simp only [hnone, ite_true] at hpr ⊢
      exact ⟨(Prod.mk.inj hpr).1, (Prod.mk.inj hpr).2⟩
    · simp only [hnone, ite_false] at hpr ⊢
      exact ⟨(Prod.mk.inj hpr).1, (Prod.mk.inj hpr).2⟩
  rw [hrfpick.1, hrfpick.2] at hrfps
  -- the tail
  have hcnt : (outEdges H T C b).length ≤ T.length := by
    rw [outEdges_length]
    have := Proofs.TopoSortMath.HeadOK.le H T n HK n (Nat.le_refl _) (b + 1) (by omega)
    rw [HK.last] at this
    omega
  obtain ⟨rt, hrt, hrtret, hrtps, hrtvv, hrtc, hrtn, hrtw⟩ := b_tail mv hnv hty0 hty1 hty2 hty3 hty4 H T C Dd Dn P n it b inf bd' hn hit hbn hn2 HK
    hDnl hDl hTn (by show _ < 2147483648; omega) hCl hC0 hDv hDnv hinf0 hinfB ⟨hbd0, hbdI⟩ (by omega) fu (by omega)
  have g1 := seqM_some hrf hrfret (by rw [hrfps, hrfvv]; exact hrt)
  have g2 := seqM_some hrs hrsret (by rw [hrsps, hrsvv]; exact g1)
  have g3 := seqM_some q2 rfl g2
  have g4 := seqM_some q1 rfl g3
  refine ⟨_, b, bd', hpr, hbn, hb0, hbd0, hbdI, hcase, g4, by simpa using hrtret, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hrtps
  · simpa using hrtvv
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrsc hrfc hrtc ⊢; omega
  · simp [hrfps, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrsn hrfn hrtn ⊢; omega
  · simp at hrsw hrfw hrtw ⊢; omega

/-! ### A loop lemma with a cost potential -/

/-- Like `for_loop_runB`, but every iteration may also lower a potential: `r.cost + pot' ≤ cB + pot`. -/
theorem for_loop_runP (mv : MV) (P : List Cell) (p b n : Nat) (hb : b < p) (hn : n < 2147483647) (B : Command)
    (Inv : Nat → (Nat → List Int) → List Cell → Nat → Prop) (cB nB wB fB K : Nat) (hnB : 2 * p + 12 ≤ nB)
    (hbody : ∀ (t : Nat) (vv : Nat → List Int) (C : List Cell) (pot : Nat) (fu : Nat), t < n → C.length = p →
      C[b]? = some (ci n) → Inv t vv C pot → fB ≤ fu →
      ∃ (r : PRM) (cs' C' : List Cell) (pot' : Nat), pexecM mv fu B (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧
        r.ps = gS P (C' ++ [ci t] ++ cs') ∧ C'.length = p ∧ C'[b]? = some (ci n) ∧ Inv (t + 1) r.vv C' pot' ∧
        r.cost + K * pot' ≤ cB + K * pot ∧ r.need ≤ P.length + nB ∧ r.wk + pot' ≤ wB + pot) :
    ∀ (m t0 : Nat), n - t0 = m → t0 ≤ n → ∀ vv C pot, C.length = p → C[b]? = some (ci n) → Inv t0 vv C pot →
      ∀ fu, fB + m + 1 ≤ fu →
      ∃ (res : PRM) (C2 : List Cell) (pot2 : Nat), pexecM mv fu (forLoopB mv.nv p b B) (gS P (C ++ [ci t0])) vv = some res ∧
        res.ps = gS P (C2 ++ [ci n]) ∧ C2.length = p ∧ Inv n res.vv C2 pot2 ∧ res.ret = none ∧
        res.cost + K * pot2 ≤ (cB + 20) * m + 10 + K * pot ∧ res.need ≤ P.length + nB ∧ res.wk + pot2 ≤ wB * m + pot := by
  intro m
  induction m with
  | zero =>
    intro t0 hm hle vv C pot hCp h0 hI fu hfu
    have ht : t0 = n := by omega
    subst ht
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := forCondB_val mv vv P C p b t0 t0 hCp h0 hb (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_forCondB]
    refine ⟨_, C, pot, rfl, rfl, hCp, hI, rfl, ?_, ?_, ?_⟩
    · simp
    · simp [gS_size, hCp]; omega
    · simp
  | succ m ih =>
    intro t0 hm hle vv C pot hCp h0 hI fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hlt : t0 < n := by omega
    have hc := forCondB_val mv vv P C p b n t0 hCp h0 hb (by omega) (by omega)
    rw [if_pos hlt] at hc
    obtain ⟨r1, cs', C', pot', hB, hret, hps, hC'p, hC'0, hI', hcost, hneed, hwk⟩ :=
      hbody t0 vv C pot (fu' + 1) hlt hCp h0 hI (by omega)
    have sc := pexecM_scope mv (fu' + 1) B _ vv r1 hB
    rw [hps] at sc
    have tk := gS_takeC P (C ++ [ci t0]) (C' ++ [ci t0]) cs' (by simp [hCp, hC'p])
    simp only [List.append_assoc] at sc tk ⊢
    simp only [tk] at sc
    have inc := forInc_step mv r1.vv P C' p t0 hC'p (by omega) (by omega)
    have q := (pexecM_prim mv (fu' + 1) (forInc mv.nv p) _ _).trans inc
    have t2 := seqM_some q rfl (pexecM_skip mv (fu' + 1) (gS P (C' ++ [ci (t0 + 1)])) r1.vv)
    have body := seqM_some sc hret t2
    obtain ⟨r2, C2, pot2, h2, p2, C2p, I2, ret2, c2, n2, w2⟩ :=
      ih (t0 + 1) (by omega) (by omega) r1.vv C' pot' hC'p hC'0 hI' fu' (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, body, hret, h2, vwp_forCondB]
    refine ⟨_, C2, pot2, rfl, p2, C2p, I2, ret2, ?_, ?_, ?_⟩
    · rw [Nat.mul_succ]
      simp [vwp_forIncE, vwp_forCondB] at *
      omega
    · simp [gS_size, hCp, vwp_forIncE, vwp_forCondB] at *
      omega
    · rw [Nat.mul_succ]
      simp [vwp_forIncE] at *
      omega

theorem for_stmt_runP (mv : MV) (P : List Cell) (p b n : Nat) (hb : b < p) (hn : n < 2147483647) (B : Command)
    (Inv : Nat → (Nat → List Int) → List Cell → Nat → Prop) (cB nB wB fB K : Nat) (hnB : 2 * p + 12 ≤ nB)
    (hbody : ∀ (t : Nat) (vv : Nat → List Int) (C : List Cell) (pot : Nat) (fu : Nat), t < n → C.length = p →
      C[b]? = some (ci n) → Inv t vv C pot → fB ≤ fu →
      ∃ (r : PRM) (cs' C' : List Cell) (pot' : Nat), pexecM mv fu B (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧
        r.ps = gS P (C' ++ [ci t] ++ cs') ∧ C'.length = p ∧ C'[b]? = some (ci n) ∧ Inv (t + 1) r.vv C' pot' ∧
        r.cost + K * pot' ≤ cB + K * pot ∧ r.need ≤ P.length + nB ∧ r.wk + pot' ≤ wB + pot)
    (vv : Nat → List Int) (C : List Cell) (pot : Nat) (hCp : C.length = p) (h0 : C[b]? = some (ci n))
    (hI : Inv 0 vv C pot) (fu : Nat) (hfu : fB + n + 1 ≤ fu) :
    ∃ (res : PRM) (C2 : List Cell) (pot2 : Nat), pexecM mv fu (forStmtB mv.nv p b B) (gS P C) vv = some res ∧
      res.ps = gS P C2 ∧ C2.length = p ∧ Inv n res.vv C2 pot2 ∧ res.ret = none ∧
      res.cost + K * pot2 ≤ (cB + 20) * n + 30 + K * pot ∧ res.need ≤ P.length + nB ∧ res.wk + pot2 ≤ wB * n + pot := by
  have d := gSM_decl mv P C vv i32 _ 0 0 (zero_lit_val mv vv _) (conv_signed i32 rfl rfl _ rfl)
  have q := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d
  obtain ⟨r, C2, pot2, hr, hps, hC2, hIn, hret, hc, hnd, hw⟩ :=
    for_loop_runP mv P p b n hb hn B Inv cB nB wB fB K hnB hbody n 0 (by omega) (by omega) vv C pot hCp h0 hI fu (by omega)
  have hps0 : gS P (C ++ [(⟨i32, 0⟩ : Cell)]) = gS P (C ++ [ci 0]) := rfl
  rw [hps0] at q
  have t1 := seqM_some hr hret (pexecM_skip mv fu _ _)
  have t0 := seqM_some q rfl (by simpa using t1)
  have sc := pexecM_scope mv fu _ _ vv _ t0
  rw [hps] at sc
  have tk := gS_takeC P C C2 [ci n] (by simp [hCp, hC2])
  simp only [tk] at sc
  refine ⟨_, C2, pot2, sc, rfl, hC2, ?_, ?_, ?_, ?_, ?_⟩
  · exact hIn
  · rfl
  · show (vwp (NExpr.literal i32 0)).1 + 1 + r.cost + 1 + K * pot2 ≤ _
    simp [vwp, NExpr.nodes] at *
    rw [Nat.mul_comm] at *
    omega
  · show max (P.length + 2 * C.length + (vwp (NExpr.literal i32 0)).2 + 4)
      (max r.need ((gS P (C2 ++ [ci n])).mem.length + (gS P (C2 ++ [ci n])).bs.length)) ≤ _
    simp [vwp, NExpr.nodes, gS_size, hCp, hC2] at *
    omega
  · show 0 + r.wk + pot2 ≤ _
    omega

theorem exists_unvisited (n : Nat) (D : List Nat) (hnd : D.Nodup) (hlt : ∀ v ∈ D, v < n) (hlen : D.length < n) :
    ∃ v, v < n ∧ v ∉ D := by
  refine Classical.byContradiction fun hno => ?_
  have hall : ∀ v, v < n → v ∈ D := fun v hv => Classical.byContradiction fun h => hno ⟨v, hv, h⟩
  have hsub : List.range n ⊆ D := fun v hv => hall v (List.mem_range.mp hv)
  have := List.Nodup.length_le_of_subset List.nodup_range hsub
  simp at this
  omega

theorem outEdges_range (H T : List Nat) (C : List Int) (n : Nat) (HK : Proofs.TopoSortMath.HeadOK H T n) (hCl : C.length = T.length)
    (u : Nat) (hu : u < n) (e : Edge) (he : e ∈ outEdges H T C u) :
    e.1 = u ∧ ∃ p, p < T.length ∧ e.2.1 = T.getD p 0 ∧ e.2.2 = C.getD p 0 := by
  obtain ⟨h1, d, hd, h2, h3⟩ := outEdges_mem H T C u e he
  refine ⟨h1, H.getD u 0 + d, ?_, h2, h3⟩
  have hle : H.getD (u + 1) 0 ≤ T.length := by
    have := Proofs.TopoSortMath.HeadOK.le H T n HK n (Nat.le_refl _) (u + 1) (by omega)
    rw [HK.last] at this; exact this
  omega

theorem edges_ok (H T : List Nat) (C : List Int) (n : Nat) (inf : Int) (HK : Proofs.TopoSortMath.HeadOK H T n)
    (hTn : ∀ x ∈ T, x < n) (hCl : C.length = T.length) (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x < inf) :
    ∀ e ∈ Eall n (outEdges H T C), e.1 < n ∧ e.2.1 < n ∧ 0 ≤ e.2.2 ∧ e.2.2 < inf := by
  intro e he
  obtain ⟨u, hu, hmem⟩ := mem_Eall_inv n (outEdges H T C) e he
  obtain ⟨h1, p, hp, h2, h3⟩ := outEdges_range H T C n HK hCl u hu e hmem
  refine ⟨by rw [h1]; exact hu, ?_, ?_, ?_⟩
  · rw [h2, getD_ltN T p hp]; exact hTn _ (List.getElem_mem _)
  · rw [h3]; exact (hC0 _ (Proofs.BellmanFordExec.getD_mem C p (by omega))).1
  · rw [h3]; exact (hC0 _ (Proofs.BellmanFordExec.getD_mem C p (by omega))).2

theorem doneOf_bound (n : Nat) (D : List Nat) : ∀ j, (doneOf n D).getD j 0 < M31 := by
  intro j
  by_cases hj : j < n
  · rw [doneOf_getD n D j hj]; split <;> (show _ < 2147483648; omega)
  · have : (doneOf n D).getD j 0 = 0 := getD_oob _ _ _ (by rw [doneOf_length]; omega)
    rw [this]; show 0 < 2147483648; omega

set_option maxHeartbeats 8000000 in
/-- The outer loop `for (int it = 0; it < n; it++) {...}`. -/
theorem l_outer (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd0 : List Int) (P : List Cell) (n : Nat) (inf : Int)
    (hn : n < M31) (hn2 : n < 2147483647) (HK : Proofs.TopoSortMath.HeadOK H T n) (hTn : ∀ x ∈ T, x < n)
    (hTM : T.length < 2147483647) (hCl : C.length = T.length) (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x < inf)
    (hinf0 : 0 ≤ inf) (hinfB : inf ≤ 4611686018427387904) (hDd0 : Dd0.length = n) (hall : ∀ j, j < n → Dd0.getD j 0 = inf)
    (fu : Nat) (hfu : 2 * n + T.length + 8 ≤ fu) :
    ∃ (res : PRM) (D : List Nat) (pk : List Int) (Dd : List Int) (Dn : List Nat),
      pexecM mv fu (forStmtB mv.nv 2 0 (Bp mv.nv)) (gS P [ci n, cs inf]) (VD H T C Dd0 (doneOf n [])) = some res ∧
      res.ps = gS P [ci n, cs inf] ∧ res.vv = VD H T C Dd Dn ∧ res.ret = none ∧
      PInv n inf (Eall n (outEdges H T C)) Dd Dn D pk ∧ D.length = n ∧
      res.cost ≤ (640 * n + 620) * n + 30 + 420 * T.length ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ T.length + 2 * n := by
  have hnM : n < 2147483648 := hn
  have hEd := edges_ok H T C n inf HK hTn hCl hC0
  have hC0' : ∀ x ∈ C, 0 ≤ x ∧ x ≤ inf := fun x hx => ⟨(hC0 x hx).1, (hC0 x hx).2.le⟩
  obtain ⟨res, C2, pot2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runP mv P 2 0 n (by omega) hn2 (Bp mv.nv)
    (fun t vv Cl pot => ∃ (D : List Nat) (pk : List Int) (Dd : List Int) (Dn : List Nat),
      PInv n inf (Eall n (outEdges H T C)) Dd Dn D pk ∧ D.length = t ∧ vv = VD H T C Dd Dn ∧ Cl = [ci n, cs inf] ∧
      pot = degSum n H D)
    (640 * n + 600) 80 2 (n + T.length + 6) 420 (by omega)
    (by
      intro t vv Cl pot fu ht hCl' hC0'' ⟨D, pk, Dd, Dn, hI, hDt, hvv, hC, hpot⟩ hfu'
      subst hvv; subst hC; subst hpot
      have hDn := hI.done
      subst hDn
      obtain ⟨v0, hv0n, hv0⟩ := exists_unvisited n D hI.nodup hI.lt (by omega)
      obtain ⟨rr, b, bd', hpr, hbn, hb0, hbd0, hbdI, hcase, hrr, hret, hps, hvv, hcost, hneed, hwk⟩ := b_iter mv hnv hty0 hty1 hty2
        hty3 hty4 H T C Dd (doneOf n D) P n t inf hn hn2 (by omega) HK hTn hTM hCl hC0' hI.ddl (doneOf_length n D) hI.bnd
        (doneOf_bound n D) hinf0 hinfB ⟨v0, hv0n, doneOf_eq n D v0 hv0n hv0⟩ fu (by omega)
      have hbD : b ∉ D := fun h => doneOf_ne n D b hbn h hb0
      have hcase' : (bd' < inf ∧ Dd.getD b 0 = bd' ∧ ∀ x, x < n → x ∉ D → bd' ≤ Dd.getD x 0) ∨
          (bd' = 0 ∧ ∀ x, x < n → x ∉ D → inf ≤ Dd.getD x 0) := by
        rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2, fun x hx hxD => h3 x hx (doneOf_eq n D x hx hxD)⟩
        · exact Or.inr ⟨h1, fun x hx hxD => h2 x hx (doneOf_eq n D x hx hxD)⟩
      have hL : ∀ e ∈ outEdges H T C b, e ∈ Eall n (outEdges H T C) ∧ e.1 = b := fun e he =>
        ⟨mem_Eall n (outEdges H T C) b hbn e he, (outEdges_mem H T C b e he).1⟩
      have hLcov : ∀ e ∈ Eall n (outEdges H T C), e.1 = b → e ∈ outEdges H T C b := by
        intro e he h1
        obtain ⟨u, hu, hmem⟩ := mem_Eall_inv n (outEdges H T C) e he
        have hue := (outEdges_mem H T C u e hmem).1
        have hub : u = b := by rw [← hue]; exact h1
        rw [← hub]; exact hmem
      have hstep := PInv_step hI (outEdges H T C b) b bd' hEd hL hLcov hbn hbD hbd0 hbdI hinf0 hcase'
      rw [← doneOf_push n D b hbn] at hstep
      have hpush := degSum_push n H D b hbn hbD
      have hcnt : (outEdges H T C b).length = H.getD (b + 1) 0 - H.getD b 0 := outEdges_length H T C b
      refine ⟨rr, [cb (some b), cs bd', ci (H.getD b 0), ci (outEdges H T C b).length], [ci n, cs inf],
        degSum n H (D ++ [b]), hrr, hret, hps, rfl, rfl, ⟨D ++ [b], pk ++ [bd'], _, _, hstep, by simp [hDt], ?_, rfl, rfl⟩, ?_, hneed, ?_⟩
      · rw [hvv]
      · omega
      · omega)
    (VD H T C Dd0 (doneOf n [])) [ci n, cs inf] (degSum n H []) rfl rfl
    ⟨[], [], Dd0, doneOf n [], PInv_init n inf _ Dd0 hDd0 hall hinf0, rfl, rfl, rfl, rfl⟩ fu (by omega)
  obtain ⟨D, pk, Dd, Dn, hI, hDt, hvv, hC, hpot⟩ := hIn
  subst hC
  have hd0 := degSum_init_le n H T HK
  refine ⟨res, D, pk, Dd, Dn, hr', hps, hvv, hret, hI, hDt, ?_, hnd, ?_⟩
  · have e : 640 * n + 600 + 20 = 640 * n + 620 := by omega
    rw [e] at hc
    omega
  · omega

/-! ### The final sum -/

/-- `∑_{v < t} dist[v]`. -/
def pS (Dd : List Int) (t : Nat) : Int := ((List.range t).map (fun v => Dd.getD v 0)).sum

theorem pS_succ (Dd : List Int) (t : Nat) : pS Dd (t + 1) = pS Dd t + Dd.getD t 0 := by
  unfold pS
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

set_option maxHeartbeats 8000000 in
/-- One iteration of the summation loop: `total = total + dist[v]`. -/
theorem xs_body (mv : MV) (hnv : mv.nv = 5) (hty3 : mv.ty 3 = s64) (H T : List Nat) (C Dd : List Int) (Dn : List Nat)
    (P : List Cell) (n t : Nat) (inf s : Int) (hn : n < M31) (ht : t < n) (hDdl : Dd.length = n)
    (hinf : s64.valid inf = true) (hs : s64.valid s = true) (hd : s64.valid (Dd.getD t 0) = true)
    (hsum : s64.valid (s + Dd.getD t 0) = true) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Bt mv.nv) (gS P [ci n, cs inf, cs s, ci t]) (VD H T C Dd Dn) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P [ci n, cs inf, cs (s + Dd.getD t 0), ci t] ∧ rr.vv = VD H T C Dd Dn ∧
      rr.cost ≤ 100 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 0 := by
  have hnM : n < 2147483648 := hn
  have E2 := envs mv P [ci n, cs inf, cs s, ci t] 2 (cs s) rfl hs
  have E3 := envs mv P [ci n, cs inf, cs s, ci t] 3 (ci t) rfl (i32v t (by omega))
  have vd := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, cs s, ci t])) 3 (by omega) s64 (hty3).symm
    (ix mv.nv 3) rfl rfl t (cidx_den _ (mv.nv + 3) t E3 (by omega)) (Dd.getD t 0)
    (by rw [VD_get3]; exact intList_get Dd t (by omega)) (by rw [hty3]; exact hd)
  have vsum : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, cs s, ci t]))
      (.binary s64 .add (.variable s64 (mv.nv + 2)) (.read s64 (.local 3) (ix mv.nv 3))) = some (s + Dd.getD t 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdenM_scalar _ _ _ _ rfl, den_variable, E2, Option.bind_some, vd, Option.bind_some]
    exact conv_signed s64 rfl rfl _ hsum
  have as1 := gSM_assign mv P [ci n, cs inf, cs s, ci t] (VD H T C Dd Dn) 2 (by simp) s64 _ _ (s + Dd.getD t 0) vsum (cs s) rfl rfl hs
    (conv_signed s64 rfl rfl _ hsum)
  have a1 := (pexecM_prim mv fu (aTot mv.nv) _ _).trans as1
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, a2, rfl, by simp, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp

set_option maxHeartbeats 8000000 in
theorem xs_loop (mv : MV) (hnv : mv.nv = 5) (hty3 : mv.ty 3 = s64) (H T : List Nat) (C Dd : List Int) (Dn : List Nat)
    (P : List Cell) (n : Nat) (inf : Int) (hn : n < M31) (hn2 : n < 2147483647) (hDdl : Dd.length = n)
    (hinf : s64.valid inf = true) (hnn : ∀ j, j < n → 0 ≤ Dd.getD j 0) (hDv : ∀ j, j < n → s64.valid (Dd.getD j 0) = true)
    (hov : ∀ t, t ≤ n → s64.valid (pS Dd t) = true) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 3 0 (Bt mv.nv)) (gS P [ci n, cs inf, cs 0]) (VD H T C Dd Dn) = some res ∧
      res.ps = gS P [ci n, cs inf, cs (pS Dd n)] ∧ res.vv = VD H T C Dd Dn ∧ res.ret = none ∧
      res.cost ≤ 120 * n + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ 0 := by
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 3 0 n (by omega) hn2 (Bt mv.nv)
    (fun t vv Cl => vv = VD H T C Dd Dn ∧ Cl = [ci n, cs inf, cs (pS Dd t)]) 100 80 0 0 (by omega)
    (by
      intro t vv Cl fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      obtain ⟨rr, hrr, hret, hps, hvv, hcost, hneed, hwk⟩ := xs_body mv hnv hty3 H T C Dd Dn P n t inf (pS Dd t) hn ht hDdl hinf
        (hov t (by omega)) (hDv t ht) (by rw [← pS_succ]; exact hov (t + 1) ht) fu
      refine ⟨rr, [], [ci n, cs inf, cs (pS Dd (t + 1))], hrr, hret, ?_, rfl, rfl, ⟨hvv, rfl⟩, hcost, hneed, hwk⟩
      rw [pS_succ]
      simpa using hps)
    (VD H T C Dd Dn) [ci n, cs inf, cs (pS Dd 0)] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hIn
  subst hC
  refine ⟨res, by simpa [pS] using hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

theorem pS_eq {n : Nat} {inf : Int} {Ed : List Edge} {Dd : List Int} {Dn : List Nat} {D : List Nat} {pk : List Int}
    (I : PInv n inf Ed Dd Dn D pk) (hlen : D.length = n) : pS Dd n = pk.sum := by
  have hperm := D_perm_range I.nodup I.lt hlen
  have e : D.map (fun v => Dd.getD v 0) = pk := by
    apply List.ext_getElem
    · simp [I.len]
    · intro j h1 h2
      have hjD : j < D.length := by simpa using h1
      simp only [List.getElem_map]
      have := I.cl3 j hjD
      rw [this]
      simp [List.getD_eq_getElem?_getD, h2]
  unfold pS
  rw [← e]
  exact (perm_sum_int ((List.Perm.map (fun v => Dd.getD v 0) hperm).symm))

set_option maxHeartbeats 8000000 in
/-- The whole body of `prim`. -/
theorem prog_exec (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd0 : List Int) (P : List Cell) (n : Nat) (inf Cm : Int)
    (hn : n < M31) (hn2 : n < 2147483647) (HK : Proofs.TopoSortMath.HeadOK H T n) (hTn : ∀ x ∈ T, x < n)
    (hTM : T.length < 2147483647) (hCl : C.length = T.length) (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x < inf)
    (hCm : ∀ x ∈ C, x ≤ Cm) (hCm0 : 0 ≤ Cm) (hov : (n : Int) * Cm ≤ 9223372036854775807)
    (hinf0 : 0 ≤ inf) (hinfB : inf ≤ 4611686018427387904) (hDd0 : Dd0.length = n) (hall : ∀ j, j < n → Dd0.getD j 0 = inf)
    (fu : Nat) (hfu : 2 * n + T.length + 9 ≤ fu) :
    ∃ (r : PRM) (D : List Nat) (pk : List Int) (Dd : List Int) (Dn : List Nat),
      pexecM mv fu (progPR mv.nv) (gS P [ci n, cs inf]) (VD H T C Dd0 (doneOf n [])) = some r ∧
      r.ret = some pk.sum ∧ r.vv = VD H T C Dd Dn ∧ r.ps = gS P [ci n, cs inf, cs pk.sum] ∧
      PInv n inf (Eall n (outEdges H T C)) Dd Dn D pk ∧ D.length = n ∧ 0 ≤ pk.sum ∧ pk.sum ≤ (n : Int) * Cm ∧
      r.cost ≤ (640 * n + 760) * n + 420 * T.length + 100 ∧ r.need ≤ P.length + 80 ∧ r.wk ≤ T.length + 2 * n := by
  have hnM : n < 2147483648 := hn
  have hinfv : s64.valid inf = true := Proofs.BellmanFordExec.s64_valid_of inf (by omega)
  obtain ⟨res, D, pk, Dd, Dn, hres, hps, hvv, hret, hI, hDn, hc, hnd, hw⟩ := l_outer mv hnv hty0 hty1 hty2 hty3 hty4 H T C Dd0 P n inf
    hn hn2 HK hTn hTM hCl hC0 hinf0 hinfB hDd0 hall fu (by omega)
  have hEd := edges_ok H T C n inf HK hTn hCl hC0
  have hEm : ∀ e ∈ Eall n (outEdges H T C), 0 ≤ e.2.2 ∧ e.2.2 ≤ Cm := by
    intro e he
    obtain ⟨u, hu, hmem⟩ := mem_Eall_inv n (outEdges H T C) e he
    obtain ⟨_, p, hp, _, h3⟩ := outEdges_range H T C n HK hCl u hu e hmem
    rw [h3]
    have hmemC := Proofs.BellmanFordExec.getD_mem C p (by omega)
    exact ⟨(hC0 _ hmemC).1, hCm _ hmemC⟩
  have hpkb := pk_bounds hI Cm hCm0 hEm
  have hsum := sum_le_len_mul pk Cm hpkb
  have hlenpk : pk.length = n := by rw [hI.len]; exact hDn
  rw [hlenpk] at hsum
  have hpS : pS Dd n = pk.sum := pS_eq hI hDn
  -- the partial sums are non-negative and bounded by the total
  have hDdnn : ∀ j, j < n → 0 ≤ Dd.getD j 0 := fun j hj => (hI.bnd j hj).1
  have hmono : ∀ t, t ≤ n → 0 ≤ pS Dd t ∧ pS Dd t ≤ pS Dd n := by
    intro t ht
    have key : ∀ k, k ≤ n → 0 ≤ pS Dd k := by
      intro k
      induction k with
      | zero => intro _; simp [pS]
      | succ k ih =>
        intro hk
        rw [pS_succ]
        have := ih (by omega)
        have := hDdnn k (by omega)
        omega
    have key2 : ∀ d k, k + d ≤ n → pS Dd k ≤ pS Dd (k + d) := by
      intro d
      induction d with
      | zero => intro k _; exact Int.le_refl _
      | succ d ih =>
        intro k hk
        have h1 := ih k (by omega)
        rw [show k + (d + 1) = (k + d) + 1 by omega, pS_succ]
        have := hDdnn (k + d) (by omega)
        omega
    refine ⟨key t ht, ?_⟩
    have := key2 (n - t) t (by omega)
    rwa [show t + (n - t) = n by omega] at this
  have hovv : ∀ t, t ≤ n → s64.valid (pS Dd t) = true := by
    intro t ht
    have := hmono t ht
    exact Proofs.BellmanFordExec.s64_valid_of _ (by omega)
  -- declare total = 0
  have d1 := gSM_decl mv P [ci n, cs inf] (VD H T C Dd Dn) s64 (.cast s64 (.literal i32 0)) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact zero_cast_den _) (conv_signed s64 rfl rfl _ (by simp [Ty.valid]))
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have hq1 : [ci n, cs inf] ++ [(⟨s64, 0⟩ : Cell)] = [ci n, cs inf, cs 0] := rfl
  rw [hq1] at q1
  obtain ⟨rl, hrl, hrlps, hrlvv, hrlret, hrlc, hrln, hrlw⟩ := xs_loop mv hnv hty3 H T C Dd Dn P n inf hn hn2 hI.ddl hinfv hDdnn
    (fun j hj => Proofs.BellmanFordExec.s64_valid_of _ (by have := hI.bnd j hj; omega)) hovv fu (by omega)
  -- return total
  have E2 := envs mv P [ci n, cs inf, cs (pS Dd n)] 2 (cs (pS Dd n)) rfl (hovv n (Nat.le_refl _))
  have hret' : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, cs (pS Dd n)])) (.variable s64 (mv.nv + 2)) =
      some (pS Dd n) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2
  have r5 := pstmtM_ret_ok mv (gS P [ci n, cs inf, cs (pS Dd n)]) (VD H T C Dd Dn) _ _ hret'
  have q5 := seqM_ret (mv := mv) (fu := fu) (b := Sk) (a := .primitive (.ret (.variable s64 (mv.nv + 2)))) (by rw [pexecM_prim, r5]) rfl
  have t4 := seqM_some hrl hrlret (by rw [hrlps, hrlvv]; exact q5)
  have t3 := seqM_some q1 rfl t4
  have t2 := seqM_some hres hret (by rw [hps, hvv]; exact t3)
  refine ⟨_, D, pk, Dd, Dn, t2, ?_, ?_, ?_, hI, hDn, hsum.1, hsum.2, ?_, ?_, ?_⟩
  · simp [hpS]
  · simp
  · simp [hpS]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hc hrlc ⊢
    have e2 : (640 * n + 760) * n = (640 * n + 620) * n + 140 * n := by ring
    rw [e2]
    omega
  · simp [hps, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hn hrln ⊢
    omega
  · simp at hw hrlw ⊢
    omega

end Proofs.PrimExec
