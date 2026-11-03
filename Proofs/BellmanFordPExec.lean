import Proofs.BellmanFordExec
import Proofs.Generated.BellmanFord

namespace Proofs.BellmanFordPExec
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

/-- The contents of the five vectors: `from`, `to`, `cost`, `dist`, `parent`. -/
def VVP (F T : List Nat) (Cc D Pp : List Int) : Nat → List Int := fun k =>
  if k = 0 then F.map (fun x : Nat => (x : Int)) else if k = 1 then T.map (fun x : Nat => (x : Int))
  else if k = 2 then Cc else if k = 3 then D else if k = 4 then Pp else []

theorem VVP_write3 (F T : List Nat) (Cc D Pp : List Int) (x : List Int) : upd (VVP F T Cc D Pp) 3 x = VVP F T Cc x Pp := by
  funext k
  unfold upd VVP
  by_cases h3 : k = 3
  · subst h3; simp
  · simp [h3]

theorem VVP_write4 (F T : List Nat) (Cc D Pp : List Int) (x : List Int) : upd (VVP F T Cc D Pp) 4 x = VVP F T Cc D x := by
  funext k
  unfold upd VVP
  by_cases h4 : k = 4
  · subst h4; simp
  · simp [h4]

theorem VVP_get0 (F T : List Nat) (Cc D Pp : List Int) : VVP F T Cc D Pp 0 = F.map (fun x : Nat => (x : Int)) := by simp [VVP]
theorem VVP_get1 (F T : List Nat) (Cc D Pp : List Int) : VVP F T Cc D Pp 1 = T.map (fun x : Nat => (x : Int)) := by simp [VVP]
theorem VVP_get2 (F T : List Nat) (Cc D Pp : List Int) : VVP F T Cc D Pp 2 = Cc := by simp [VVP]
theorem VVP_get3 (F T : List Nat) (Cc D Pp : List Int) : VVP F T Cc D Pp 3 = D := by simp [VVP]
theorem VVP_get4 (F T : List Nat) (Cc D Pp : List Int) : VVP F T Cc D Pp 4 = Pp := by simp [VVP]

abbrev wrP (nv : Nat) : NStmt := .write (.local 4) i32 (rdIdx nv 7) (.variable i32 (nv + 6))
abbrev Y2P (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (wrS nv)) (.sequence (.primitive (wrP nv)) Sk))) Sk
abbrev BR2P (nv : Nat) : Command := .branch (cond2 nv) (Y2P nv) Sk
abbrev Y1P (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.declare s64 true (ndE nv))) (.sequence (BR2P nv) Sk))) Sk
abbrev BR1P (nv : Nat) : Command := .branch (cond1 nv) (Y1P nv) Sk
abbrev XBP (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (iU nv))) (.sequence (.primitive (.declare i32 true (iV nv))) (.sequence (BR1P nv) Sk))
/-- The two declarations `int u = from[e]; int v = to[e];` followed by `REST`. -/
theorem decl_uvP (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32)
    (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i e : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (fu : Nat) (REST : Command) (rr : PRM)
    (hrest : pexecM mv fu REST (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0), ci (T.getD e 0)])
      (VVP F T Cc D Pp) = some rr) :
    ∃ r : PRM, pexecM mv fu (.sequence (.primitive (.declare i32 true (iU mv.nv))) (.sequence (.primitive (.declare i32 true (iV mv.nv))) REST))
      (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e]) (VVP F T Cc D Pp) = some r ∧ r.ret = rr.ret ∧
      r.ps = rr.ps ∧ r.vv = rr.vv ∧ r.cost ≤ 20 + rr.cost ∧ r.need ≤ max (P.length + 40) rr.need ∧ r.wk = rr.wk := by
  have hu : F.getD e 0 < n := by
    have : F.getD e 0 = F[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, he]
    rw [this]; exact hFn _ (List.getElem_mem _)
  have hv : T.getD e 0 < n := by
    have : T.getD e 0 = T[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, he]
    rw [this]; exact hTn _ (List.getElem_mem _)
  have E5 := envs mv P [ci n, cs inf, ci m, ci rounds, ci i, ci e] 5 (ci e) rfl (Proofs.BellmanFordExec.i32_valid_nat e (by omega))
  have vu := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e])) 0 (by omega) i32
    hty0.symm (rdIdx mv.nv 5) rfl rfl e (cidx_den _ (mv.nv + 5) e E5 (by omega)) ((F.getD e 0 : Nat) : Int)
    (by rw [VVP_get0]; exact vec_getM F e (by omega)) (by rw [hty0]; exact Proofs.BellmanFordExec.i32_valid_nat _ (by omega))
  have d1 := gSM_decl mv P [ci n, cs inf, ci m, ci rounds, ci i, ci e] (VVP F T Cc D Pp) i32 _ _ _ vu
    (conv_signed i32 rfl rfl _ (Proofs.BellmanFordExec.i32_valid_nat _ (by omega)))
  have q1 := (pexecM_prim mv fu (.declare i32 true (iU mv.nv)) _ _).trans d1
  have E5' := envs mv P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0)] 5 (ci e) rfl (Proofs.BellmanFordExec.i32_valid_nat e (by omega))
  have vv' := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0)])) 1
    (by omega) i32 hty1.symm (rdIdx mv.nv 5) rfl rfl e (cidx_den _ (mv.nv + 5) e E5' (by omega)) ((T.getD e 0 : Nat) : Int)
    (by rw [VVP_get1]; exact vec_getM T e (by omega)) (by rw [hty1]; exact Proofs.BellmanFordExec.i32_valid_nat _ (by omega))
  have d2 := gSM_decl mv P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0)] (VVP F T Cc D Pp) i32 _ _ _ vv'
    (conv_signed i32 rfl rfl _ (Proofs.BellmanFordExec.i32_valid_nat _ (by omega)))
  have q2 := (pexecM_prim mv fu (.declare i32 true (iV mv.nv)) _ _).trans d2
  have q3 := seqM_some q2 rfl hrest
  have q4 := seqM_some q1 rfl q3
  refine ⟨_, q4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega
  · simp


/-- `dist[to[e]] = nd; parent[to[e]] = from[e];` inside two braces, with `nd < dist[v]` known. -/
theorem y2P_exec (mv : MV) (hnv : mv.nv = 5) (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32)
    (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i e u v : Nat) (inf nd : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < M31) (hu : u < M31) (hv : v < n)
    (hinf : s64.valid inf = true) (hnd : s64.valid nd = true) (hDl : D.length = n) (hPl : Pp.length = n) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Y2P mv.nv) (gS P (cD n m rounds i e u v inf nd)) (VVP F T Cc D Pp) = some r ∧ r.ret = none ∧
      r.ps = gS P (cD n m rounds i e u v inf nd) ∧ r.vv = VVP F T Cc (D.set v nd) (Pp.set v (u : Int)) ∧
      r.cost ≤ 200 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 2 := by
  have E6 := envs mv P (cD n m rounds i e u v inf nd) 6 (ci u) rfl (Proofs.BellmanFordExec.i32_valid_nat u (by omega))
  have E7 := envs mv P (cD n m rounds i e u v inf nd) 7 (ci v) rfl (Proofs.BellmanFordExec.i32_valid_nat v (by omega))
  have E8 := envs mv P (cD n m rounds i e u v inf nd) 8 (cs nd) rfl hnd
  have hp : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cD n m rounds i e u v inf nd))) (rdIdx mv.nv 7) = some (v : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 7) v E7 (by omega)
  have hx : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cD n m rounds i e u v inf nd))) (.variable s64 (mv.nv + 8)) = some nd := by
    rw [vdenM_scalar _ _ _ _ rfl]
    rw [den_variable]; exact E8
  have w := pstmtM_write_ok mv (gS P (cD n m rounds i e u v inf nd)) (VVP F T Cc D Pp) 3 (by omega) (rdIdx mv.nv 7)
    (.variable s64 (mv.nv + 8)) nd v hx hp (by rw [VVP_get3]; omega) (by rw [hty3]; exact hnd)
  rw [hty3, VVP_get3, VVP_write3] at w
  have a1 := (pexecM_prim mv fu (wrS mv.nv) _ _).trans w
  have hxu : vdenM mv (VVP F T Cc (D.set v nd) Pp) (penvN mv.nv (gS P (cD n m rounds i e u v inf nd)))
      (.variable i32 (mv.nv + 6)) = some (u : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E6
  have hp' : vdenM mv (VVP F T Cc (D.set v nd) Pp) (penvN mv.nv (gS P (cD n m rounds i e u v inf nd))) (rdIdx mv.nv 7) =
      some (v : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 7) v E7 (by omega)
  have w2 := pstmtM_write_ok mv (gS P (cD n m rounds i e u v inf nd)) (VVP F T Cc (D.set v nd) Pp) 4 (by omega) (rdIdx mv.nv 7)
    (.variable i32 (mv.nv + 6)) (u : Int) v hxu hp' (by rw [VVP_get4]; omega) (by rw [hty4]; exact Proofs.BellmanFordExec.i32_valid_nat u (by omega))
  rw [hty4, VVP_get4, VVP_write4] at w2
  have a1' := (pexecM_prim mv fu (wrP mv.nv) _ _).trans w2
  have a2 := seqM_some a1 rfl (seqM_some a1' rfl (pexecM_skip mv fu (gS P (cD n m rounds i e u v inf nd))
    (VVP F T Cc (D.set v nd) (Pp.set v (u : Int)))))
  have a3 := pexecM_scope mv fu _ _ _ _ a2
  have tk : (⟨(gS P (cD n m rounds i e u v inf nd)).mem.take (gS P (cD n m rounds i e u v inf nd)).mem.length,
      (gS P (cD n m rounds i e u v inf nd)).bs.take (gS P (cD n m rounds i e u v inf nd)).bs.length⟩ : PS) =
      gS P (cD n m rounds i e u v inf nd) := by simp
  simp only [tk] at a3
  have a4 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (cD n m rounds i e u v inf nd))
    (VVP F T Cc (D.set v nd) (Pp.set v (u : Int))))
  refine ⟨_, a4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


/-- `if (nd < dist[v]) dist[v] = nd;` after `long long nd = dist[u] + cost[e];` inside braces. -/
theorem y1P_exec (mv : MV) (hnv : mv.nv = 5) (hty2 : mv.ty 2 = s64) (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32)
    (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i e u v : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m) (hu : u < n) (hv : v < n)
    (hinf : s64.valid inf = true) (hDl : D.length = n) (hPl : Pp.length = n) (hCl : Cc.length = m)
    (hDv : ∀ x ∈ D, s64.valid x = true) (hCv : ∀ x ∈ Cc, s64.valid x = true)
    (hsum : s64.valid (D.getD u 0 + Cc.getD e 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Y1P mv.nv) (gS P (cC n m rounds i e u v inf)) (VVP F T Cc D Pp) = some r ∧ r.ret = none ∧
      r.ps = gS P (cC n m rounds i e u v inf) ∧
      r.vv = VVP F T Cc (if D.getD u 0 + Cc.getD e 0 < D.getD v 0 then D.set v (D.getD u 0 + Cc.getD e 0) else D)
        (if D.getD u 0 + Cc.getD e 0 < D.getD v 0 then Pp.set v (u : Int) else Pp) ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 := by
  have hDu : D.getD u 0 ∈ D := by
    have : D.getD u 0 = D[u]'(by omega) := by simp [List.getD_eq_getElem?_getD, hDl, hu]
    rw [this]; exact List.getElem_mem _
  have hDvv : D.getD v 0 ∈ D := by
    have : D.getD v 0 = D[v]'(by omega) := by simp [List.getD_eq_getElem?_getD, hDl, hv]
    rw [this]; exact List.getElem_mem _
  have hCe : Cc.getD e 0 ∈ Cc := by
    have : Cc.getD e 0 = Cc[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hCl, he]
    rw [this]; exact List.getElem_mem _
  obtain ⟨_, _, E5, E6, E7⟩ := envBF mv P n m rounds i e u v inf hn hm hr hi (by omega) (by omega) (by omega) hinf
  have vdu := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e u v inf))) 3 (by omega) s64 hty3.symm
    (rdIdx mv.nv 6) rfl rfl u (cidx_den _ (mv.nv + 6) u E6 (by omega)) (D.getD u 0)
    (by rw [VVP_get3]; exact vec_getI D u (by omega)) (by rw [hty3]; exact hDv _ hDu)
  have vce := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e u v inf))) 2 (by omega) s64 hty2.symm
    (rdIdx mv.nv 5) rfl rfl e (cidx_den _ (mv.nv + 5) e E5 (by omega)) (Cc.getD e 0)
    (by rw [VVP_get2]; exact vec_getI Cc e (by omega)) (by rw [hty2]; exact hCv _ hCe)
  have vnd : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e u v inf))) (ndE mv.nv) =
      some (D.getD u 0 + Cc.getD e 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdu, vce, Option.bind_some, Option.bind_some]
    exact conv_signed s64 rfl rfl _ hsum
  have d1 := gSM_decl mv P (cC n m rounds i e u v inf) (VVP F T Cc D Pp) s64 _ _ _ vnd (conv_signed s64 rfl rfl _ hsum)
  have q1 := (pexecM_prim mv fu (.declare s64 true (ndE mv.nv)) _ _).trans d1
  -- the state after the declaration
  have hpsD : gS P (cC n m rounds i e u v inf ++ [⟨s64, D.getD u 0 + Cc.getD e 0⟩]) =
      gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) := rfl
  rw [hpsD] at q1
  have hnd : s64.valid (D.getD u 0 + Cc.getD e 0) = true := hsum
  have E8 := envs mv P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) 8 (cs (D.getD u 0 + Cc.getD e 0)) rfl hnd
  have E7' := envs mv P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) 7 (ci v) rfl (Proofs.BellmanFordExec.i32_valid_nat v (by omega))
  have vdv := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)))) 3
    (by omega) s64 hty3.symm (rdIdx mv.nv 7) rfl rfl v (cidx_den _ (mv.nv + 7) v E7' (by omega)) (D.getD v 0)
    (by rw [VVP_get3]; exact vec_getI D v (by omega)) (by rw [hty3]; exact hDv _ hDvv)
  have vc2 : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)))) (cond2 mv.nv) =
      some (if D.getD u 0 + Cc.getD e 0 < D.getD v 0 then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdenM_scalar _ _ _ _ rfl, den_variable, E8, vdv, Option.bind_some, Option.bind_some]
    exact lt_conv _ _
  -- the inner branch
  obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ : ∃ rb : PRM,
      pexecM mv fu (.sequence (BR2P mv.nv) Sk) (gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0))) (VVP F T Cc D Pp) = some rb ∧
      rb.ret = none ∧ rb.ps = gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) ∧
      rb.vv = VVP F T Cc (if D.getD u 0 + Cc.getD e 0 < D.getD v 0 then D.set v (D.getD u 0 + Cc.getD e 0) else D)
        (if D.getD u 0 + Cc.getD e 0 < D.getD v 0 then Pp.set v (u : Int) else Pp) ∧
      rb.cost ≤ 250 ∧ rb.need ≤ P.length + 80 ∧ rb.wk ≤ 2 := by
    by_cases hlt : D.getD u 0 + Cc.getD e 0 < D.getD v 0
    · rw [if_pos hlt] at vc2
      obtain ⟨ry, hy, hyret, hyps, hyvv, hyc, hyn, hyw⟩ := y2P_exec mv hnv hty3 hty4 F T Cc D Pp P n m rounds i e u v inf
        (D.getD u 0 + Cc.getD e 0) hn hm hr hi (by omega) (by omega) hv hinf hnd hDl hPl fu
      have b1 := pexecM_branch_true mv fu (cond2 mv.nv) (Y2P mv.nv) Sk _ _ 1 vc2 (by decide) ry hy
      have b2 := seqM_some b1 hyret (pexecM_skip mv fu ry.ps ry.vv)
      have hl : ry.ps.mem.length + ry.ps.bs.length = P.length + 18 := by rw [hyps]; simp [gS_size]
      refine ⟨_, b2, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact hyps
      · rw [if_pos hlt, if_pos hlt]; exact hyvv
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hyc ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hyn ⊢; omega
      · simpa using hyw
    · rw [if_neg hlt] at vc2
      have b1 := pexecM_branch_false mv fu (cond2 mv.nv) (Y2P mv.nv) Sk _ _ vc2 _ (pexecM_skip mv fu _ _)
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · rw [if_neg hlt, if_neg hlt]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp
  have q2 := seqM_some q1 rfl hrb
  have q3 := pexecM_scope mv fu _ _ _ _ q2
  have tk := gS_takeC P (cC n m rounds i e u v inf) (cC n m rounds i e u v inf) [cs (D.getD u 0 + Cc.getD e 0)] rfl
  rw [hrbps] at q3
  have hpsD' : gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) =
      gS P (cC n m rounds i e u v inf ++ [cs (D.getD u 0 + Cc.getD e 0)]) := rfl
  rw [hpsD'] at q3
  simp only [tk] at q3
  have q4 := seqM_some q3 hrbret (pexecM_skip mv fu _ _)
  refine ⟨_, q4, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact hrbvv
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
  · simp at *; omega


/-- The parent list after relaxing edge `e` (the distance list is `D` before the relaxation). -/
def relaxPL (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D Pp : List Int) : List Int :=
  if D.getD (F.getD e 0) 0 ≠ inf ∧ D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
  then Pp.set (T.getD e 0) ((F.getD e 0 : Nat) : Int) else Pp

theorem relaxPL_eq (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D Pp : List Int) :
    relaxPL inf F T Cc e D Pp =
      if D.getD (F.getD e 0) 0 ≠ inf then
        (if D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
         then Pp.set (T.getD e 0) ((F.getD e 0 : Nat) : Int) else Pp)
      else Pp := by
  unfold relaxPL
  by_cases h1 : D.getD (F.getD e 0) 0 ≠ inf
  · rw [if_pos h1]
    by_cases h2 : D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
    · rw [if_pos ⟨h1, h2⟩, if_pos h2]
    · rw [if_neg (fun h => h2 h.2), if_neg h2]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

/-- `if (dist[u] != inf) { ... }` followed by the empty statement. -/
theorem br1P_exec (mv : MV) (hnv : mv.nv = 5) (hty2 : mv.ty 2 = s64) (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32)
    (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i e : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m)
    (hu : F.getD e 0 < n) (hv : T.getD e 0 < n)
    (hinf : s64.valid inf = true) (hDl : D.length = n) (hPl : Pp.length = n) (hCl : Cc.length = m)
    (hDv : ∀ x ∈ D, s64.valid x = true) (hCv : ∀ x ∈ Cc, s64.valid x = true)
    (hsum : s64.valid (D.getD (F.getD e 0) 0 + Cc.getD e 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (.sequence (BR1P mv.nv) Sk)
      (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)) (VVP F T Cc D Pp) = some r ∧ r.ret = none ∧
      r.ps = gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf) ∧ r.vv = VVP F T Cc (relaxL inf F T Cc e D) (relaxPL inf F T Cc e D Pp) ∧
      r.cost ≤ 500 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 := by
  have hDu : D.getD (F.getD e 0) 0 ∈ D := getD_mem D _ (by omega)
  obtain ⟨_, E1, E5, E6, E7⟩ := envBF mv P n m rounds i e (F.getD e 0) (T.getD e 0) inf hn hm hr hi (by omega) (by omega)
    (by omega) hinf
  have vdu := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) 3 (by omega) s64
    hty3.symm (rdIdx mv.nv 6) rfl rfl (F.getD e 0) (cidx_den _ (mv.nv + 6) _ E6 (by omega)) (D.getD (F.getD e 0) 0)
    (by rw [VVP_get3]; exact vec_getI D _ (by omega)) (by rw [hty3]; exact hDv _ hDu)
  have vc1 : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) (cond1 mv.nv) =
      some (if D.getD (F.getD e 0) 0 ≠ inf then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdu, vdenM_scalar _ _ _ _ rfl, den_variable, E1, Option.bind_some, Option.bind_some]
    exact ne_conv _ _
  rw [relaxL_eq, relaxPL_eq]
  by_cases hd : D.getD (F.getD e 0) 0 ≠ inf
  · rw [if_pos hd] at vc1
    obtain ⟨ry, hy, hyret, hyps, hyvv, hyc, hyn, hyw⟩ := y1P_exec mv hnv hty2 hty3 hty4 F T Cc D Pp P n m rounds i e (F.getD e 0)
      (T.getD e 0) inf hn hm hr hi he hu hv hinf hDl hPl hCl hDv hCv hsum fu
    have b1 := pexecM_branch_true mv fu (cond1 mv.nv) (Y1P mv.nv) Sk _ _ 1 vc1 (by decide) ry hy
    have b2 := seqM_some b1 hyret (pexecM_skip mv fu ry.ps ry.vv)
    have hl : ry.ps.mem.length + ry.ps.bs.length = P.length + 16 := by rw [hyps]; simp [gS_size]
    refine ⟨_, b2, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact hyps
    · rw [if_pos hd, if_pos hd]; exact hyvv
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hyc ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hyn ⊢; omega
    · simpa using hyw
  · rw [if_neg hd] at vc1
    have b1 := pexecM_branch_false mv fu (cond1 mv.nv) (Y1P mv.nv) Sk _ _ vc1 _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [if_neg hd, if_neg hd]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp


/-- The loop body: `int u = from[e]; int v = to[e]; if (dist[u] != inf) {...}`. -/
theorem e_bodyP (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i e : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D.length = n) (hPl : Pp.length = n)
    (hCv : ∀ x ∈ Cc, s64.valid x = true) (hDv : ∀ x ∈ D, s64.valid x = true)
    (hsum : s64.valid (D.getD (F.getD e 0) 0 + Cc.getD e 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (XBP mv.nv) (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e]) (VVP F T Cc D Pp) = some r ∧
      r.ret = none ∧
      r.ps = gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0), ci (T.getD e 0)] ∧
      r.vv = VVP F T Cc (relaxL inf F T Cc e D) (relaxPL inf F T Cc e D Pp) ∧ r.cost ≤ 550 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 := by
  have hu : F.getD e 0 < n := by
    have : F.getD e 0 = F[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, he]
    rw [this]; exact hFn _ (List.getElem_mem _)
  have hv : T.getD e 0 < n := by
    have : T.getD e 0 = T[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, he]
    rw [this]; exact hTn _ (List.getElem_mem _)
  obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ := br1P_exec mv hnv hty2 hty3 hty4 F T Cc D Pp P n m rounds i e inf hn hm hr hi he
    hu hv hinf hDl hPl hCl hDv hCv hsum fu
  obtain ⟨r, hrr, hret, hps, hvv, hc, hnd, hw⟩ := decl_uvP mv hnv hty0 hty1 F T Cc D Pp P n m rounds i e inf hn hm hr hi he hinf
    hFl hTl hFn hTn fu (.sequence (BR1P mv.nv) Sk) rb hrb
  refine ⟨r, hrr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hret]; exact hrbret
  · rw [hps]; exact hrbps
  · rw [hvv]; exact hrbvv
  · omega
  · omega
  · omega



/-- The parent list after relaxing the edges `0 .. t-1` in order (the distance list before edge `e` is `passPrefix e`). -/
def passPrefixP (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (D0 P0 : List Int) : List Int :=
  (List.range t).foldl (fun p e => relaxPL inf F T Cc e (passPrefix inf F T Cc e D0) p) P0

theorem passPrefixP_succ (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (D0 P0 : List Int) :
    passPrefixP inf F T Cc (t + 1) D0 P0 = relaxPL inf F T Cc t (passPrefix inf F T Cc t D0) (passPrefixP inf F T Cc t D0 P0) := by
  unfold passPrefixP
  rw [List.range_succ, List.foldl_append]
  rfl

theorem relaxPL_length (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D Pp : List Int) :
    (relaxPL inf F T Cc e D Pp).length = Pp.length := by
  unfold relaxPL
  split <;> simp

theorem passPrefixP_length (inf : Int) (F T : List Nat) (Cc : List Int) (D0 P0 : List Int) :
    ∀ t, (passPrefixP inf F T Cc t D0 P0).length = P0.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [passPrefixP_succ, relaxPL_length, ih]

/-- The inner loop `for (int e = 0; e < m; e++) {...}`: one pass over the edges. -/
theorem e_loopP (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (F T : List Nat) (Cc D0 P0 : List Int) (P : List Cell) (n m rounds i : Nat) (inf Cb lo : Int)
    (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hr : rounds < M31) (hi : i < M31)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) (hPl : P0.length = n) (b : Bnd inf Cb lo m Cc D0) (fu : Nat)
    (hfu : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 5 2 (XBP mv.nv)) (gS P [ci n, cs inf, ci m, ci rounds, ci i]) (VVP F T Cc D0 P0) =
      some res ∧ res.ps = gS P [ci n, cs inf, ci m, ci rounds, ci i] ∧
      res.vv = VVP F T Cc (passPrefix inf F T Cc m D0) (passPrefixP inf F T Cc m D0 P0) ∧ res.ret = none ∧ res.cost ≤ 570 * m + 30 ∧
      res.need ≤ P.length + 100 ∧ res.wk ≤ 2 * m := by
  have hm' : m < 2147483647 := hm2
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 5 2 m (by omega) hm' (XBP mv.nv)
    (fun t vv C => vv = VVP F T Cc (passPrefix inf F T Cc t D0) (passPrefixP inf F T Cc t D0 P0) ∧ C = [ci n, cs inf, ci m, ci rounds, ci i]) 550 100 2 0
    (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hbd := passPrefix_bound inf Cb lo F T Cc D0 n m hFl hTl hCl hFn hTn hDl b.cb0 b.cc b.d0 t (by omega)
      have hv := step_valid inf Cb lo m t Cc D0 b (by omega) _ hbd
      have hu : F.getD t 0 < n := by
        have : F.getD t 0 = F[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, ht]
        rw [this]; exact hFn _ (List.getElem_mem _)
      have hDlt : (passPrefix inf F T Cc t D0).length = n := by rw [passPrefix_length, hDl]
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := e_bodyP mv hnv hty0 hty1 hty2 hty3 hty4 F T Cc (passPrefix inf F T Cc t D0) (passPrefixP inf F T Cc t D0 P0) P n m
        rounds i t inf hn hm hr hi ht hinf hFl hTl hCl hFn hTn hDlt (by rw [passPrefixP_length, hPl]) hv.2.1 hv.1
        (hv.2.2 _ (getD_mem _ _ (by omega)) _ (getD_mem Cc t (by omega))) fu
      refine ⟨r, [ci (F.getD t 0), ci (T.getD t 0)], [ci n, cs inf, ci m, ci rounds, ci i], hr, hret, hps, rfl, rfl,
        ⟨?_, rfl⟩, hc, ?_, hwk⟩
      · rw [hvv, passPrefix_succ, passPrefixP_succ]
      · omega)
    (VVP F T Cc D0 P0) [ci n, cs inf, ci m, ci rounds, ci i] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI
  subst hC
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega



/-- The parent list after `r` full passes. -/
def roundsPL (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) : Nat → List Int → List Int → List Int
  | 0, _, P => P
  | r + 1, D, P => passPrefixP inf F T Cc m (roundsL inf F T Cc m r D) (roundsPL inf F T Cc m r D P)

theorem roundsPL_length (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (D0 P0 : List Int) :
    ∀ r, (roundsPL inf F T Cc m r D0 P0).length = P0.length := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih => simp only [roundsPL]; rw [passPrefixP_length, ih]

/-- One round of the outer loop. -/
theorem i_bodyP (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i : Nat) (inf Cb lo : Int)
    (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hr : rounds < M31) (hi : i < M31)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D.length = n) (hPl : Pp.length = n) (b : Bnd inf Cb lo m Cc D) (fu : Nat)
    (hfu : m + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (.sequence (forStmtB mv.nv 5 2 (XBP mv.nv)) Sk) (gS P [ci n, cs inf, ci m, ci rounds, ci i])
      (VVP F T Cc D Pp) = some r ∧ r.ret = none ∧ r.ps = gS P [ci n, cs inf, ci m, ci rounds, ci i] ∧
      r.vv = VVP F T Cc (passL inf F T Cc m D) (passPrefixP inf F T Cc m D Pp) ∧ r.cost ≤ 570 * m + 30 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 * m := by
  obtain ⟨res, hres, hps, hvv, hret, hc, hnd, hw⟩ := e_loopP mv hnv hty0 hty1 hty2 hty3 hty4 F T Cc D Pp P n m rounds i inf Cb lo hn hm hm2 hr
    hi hinf hFl hTl hCl hFn hTn hDl hPl b fu hfu
  have q := seqM_some hres hret (pexecM_skip mv fu res.ps res.vv)
  refine ⟨_, q, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact hps
  · exact hvv
  · simpa using hc
  · simp [gS_size] at hnd hps ⊢; rw [hps]; simp [gS_size]; omega
  · simpa using hw


/-- The outer loop `for (int i = 0; i < rounds; i++) {...}`. -/
theorem i_loopP (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (F T : List Nat) (Cc D0 P0 : List Int) (P : List Cell) (n m rounds : Nat) (inf Cb lo : Int)
    (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hr : rounds < 2147483647)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) (hPl : P0.length = n) (b : Bnd inf Cb lo m Cc D0)
    (hloR : -4611686018427387904 ≤ lo - (rounds : Int) * ((m : Int) * Cb)) (fu : Nat) (hfu : m + 1 + rounds + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 4 3 (.sequence (forStmtB mv.nv 5 2 (XBP mv.nv)) Sk))
      (gS P [ci n, cs inf, ci m, ci rounds]) (VVP F T Cc D0 P0) = some res ∧ res.ps = gS P [ci n, cs inf, ci m, ci rounds] ∧
      res.vv = VVP F T Cc (roundsL inf F T Cc m rounds D0) (roundsPL inf F T Cc m rounds D0 P0) ∧ res.ret = none ∧
      res.cost ≤ (570 * m + 50) * rounds + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ 2 * m * rounds := by
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 4 3 rounds (by omega) hr
    (.sequence (forStmtB mv.nv 5 2 (XBP mv.nv)) Sk)
    (fun t vv C => vv = VVP F T Cc (roundsL inf F T Cc m t D0) (roundsPL inf F T Cc m t D0 P0) ∧ C = [ci n, cs inf, ci m, ci rounds]) (570 * m + 30) 100 (2 * m) (m + 1)
    (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ hfu'
      subst hvv; subst hC
      have hK : 0 ≤ (m : Int) * Cb := Int.mul_nonneg (Int.natCast_nonneg m) b.cb0
      have hmul : ((t : Int) + 1) * ((m : Int) * Cb) ≤ (rounds : Int) * ((m : Int) * Cb) :=
        Int.mul_le_mul_of_nonneg_right (by omega) hK
      have hmul' : ((t : Int) + 1) * ((m : Int) * Cb) = (t : Int) * ((m : Int) * Cb) + (m : Int) * Cb := by
        rw [Int.add_mul, Int.one_mul]
      have bt : Bnd inf Cb (lo - (t : Int) * ((m : Int) * Cb)) m Cc (roundsL inf F T Cc m t D0) :=
        ⟨b.cb0, b.cbH, b.infH, by omega, b.cc, roundsL_bound inf Cb lo F T Cc D0 n m hFl hTl hCl hFn hTn hDl b.cb0 b.cc b.d0 t⟩
      have hlen : (roundsL inf F T Cc m t D0).length = n := by rw [roundsL_length, hDl]
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := i_bodyP mv hnv hty0 hty1 hty2 hty3 hty4 F T Cc (roundsL inf F T Cc m t D0) (roundsPL inf F T Cc m t D0 P0) P n m rounds t
        inf Cb (lo - (t : Int) * ((m : Int) * Cb)) hn hm hm2 (by show rounds < 2147483648; omega) (by show t < 2147483648; omega)
        hinf hFl hTl hCl hFn hTn hlen (by rw [roundsPL_length, hPl]) bt fu (by omega)
      refine ⟨r, [], [ci n, cs inf, ci m, ci rounds], hr, hret, hps, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      rw [hvv]; rfl)
    (VVP F T Cc D0 P0) [ci n, cs inf, ci m, ci rounds] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI
  subst hC
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega



-- ===== the marking passes =====
abbrev wDistNeg (nv : Nat) : NStmt := .write (.local 3) s64 (rdIdx nv 7) (.unary s64 .neg (.variable s64 (nv + 1)))
abbrev wParNeg (nv : Nat) : NStmt := .write (.local 4) i32 (rdIdx nv 7) (.unary i32 .neg (.literal i32 1))
abbrev ZN (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (wDistNeg nv)) (.sequence (.primitive (wParNeg nv)) Sk))) Sk
abbrev condEq (nv : Nat) : NExpr := .binary bT .eq (dU nv) (.unary s64 .neg (.variable s64 (nv + 1)))
abbrev elseM (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.declare s64 true (ndE nv))) (.sequence (.branch (cond2 nv) (ZN nv) Sk) Sk))) Sk
abbrev Y3 (nv : Nat) : Command := .sequence (.scope (.sequence (.branch (condEq nv) (ZN nv) (elseM nv)) Sk)) Sk
abbrev BR3 (nv : Nat) : Command := .branch (cond1 nv) (Y3 nv) Sk
abbrev XB3 (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (iU nv))) (.sequence (.primitive (.declare i32 true (iV nv))) (.sequence (BR3 nv) Sk))
abbrev bodyBFP (nv : Nat) : Command :=
  .sequence (.primitive declM) (.sequence (.primitive (declR nv))
    (.sequence (forStmtB nv 4 3 (.sequence (forStmtB nv 5 2 (XBP nv)) Sk))
      (.sequence (forStmtB nv 4 0 (.sequence (forStmtB nv 5 2 (XB3 nv)) Sk)) Sk)))

theorem body_eqBFP : Proofs.BellmanFordInstance.bellman_ford_std_vector_int.body = bodyBFP 5 := rfl

theorem den_unaryP (env : Nat → Ty → Option Int) (ty : Ty) (op : Unary) (e : NExpr) :
    (NExpr.unary ty op e).denote env = (e.denote env).bind fun v => ty.convert (unaryValue op v) := by
  simp [NExpr.denote]

theorem eq_convP (x y : Int) : bT.convert (binaryValue .eq x y) = some (if x = y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : (x == y) = false := by simp [h]
    simp [binaryValue, this, h, Ty.convert, bT, Ty.valid]

/-- The marking step for one edge whose start is neither unreached nor... (the inside of `if (dist[u] != inf)`). -/
def markIn (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (s : List Int × List Int) : List Int × List Int :=
  if s.1.getD (F.getD e 0) 0 = -inf then (s.1.set (T.getD e 0) (-inf), s.2.set (T.getD e 0) (-1))
  else if s.1.getD (F.getD e 0) 0 + Cc.getD e 0 < s.1.getD (T.getD e 0) 0
    then (s.1.set (T.getD e 0) (-inf), s.2.set (T.getD e 0) (-1)) else s

/-- The marking step for one edge. -/
def markEdge (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (s : List Int × List Int) : List Int × List Int :=
  if s.1.getD (F.getD e 0) 0 ≠ inf then markIn inf F T Cc e s else s

/-- `dist[to[e]] = -inf; parent[to[e]] = -1;` in braces. -/
theorem zn_exec (mv : MV) (hnv : mv.nv = 5) (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32)
    (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (cl : List Cell) (v : Nat) (inf : Int)
    (hv : v < D.length) (hPl : Pp.length = D.length) (h1 : cl[1]? = some (cs inf)) (h7 : cl[7]? = some (ci v))
    (hv31 : v < M31) (hinf : s64.valid inf = true) (hneg : s64.valid (-inf) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (ZN mv.nv) (gS P cl) (VVP F T Cc D Pp) = some r ∧ r.ret = none ∧ r.ps = gS P cl ∧
      r.vv = VVP F T Cc (D.set v (-inf)) (Pp.set v (-1)) ∧ r.cost ≤ 300 ∧ r.need ≤ P.length + 2 * cl.length + 60 ∧ r.wk ≤ 2 := by
  have E1 := envs mv P cl 1 (cs inf) h1 hinf
  have E7 := envs mv P cl 7 (ci v) h7 (Proofs.BellmanFordExec.i32_valid_nat v hv31)
  have hp : ∀ vv : Nat → List Int, vdenM mv vv (penvN mv.nv (gS P cl)) (rdIdx mv.nv 7) = some (v : Int) := by
    intro vv
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 7) v E7 hv31
  have hx : ∀ vv : Nat → List Int, vdenM mv vv (penvN mv.nv (gS P cl)) (.unary s64 .neg (.variable s64 (mv.nv + 1))) = some (-inf) := by
    intro vv
    rw [vdenM_scalar _ _ _ _ rfl, den_unaryP, den_variable, E1, Option.bind_some]
    exact conv_signed s64 rfl rfl _ hneg
  have hx2 : ∀ vv : Nat → List Int, vdenM mv vv (penvN mv.nv (gS P cl)) (.unary i32 .neg (.literal i32 1)) = some (-1) := by
    intro vv
    rw [vdenM_scalar _ _ _ _ rfl, den_unaryP, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
    exact conv_signed i32 rfl rfl _ rfl
  have w := pstmtM_write_ok mv (gS P cl) (VVP F T Cc D Pp) 3 (by omega) (rdIdx mv.nv 7)
    (.unary s64 .neg (.variable s64 (mv.nv + 1))) (-inf) v (hx _) (hp _) (by rw [VVP_get3]; exact hv) (by rw [hty3]; exact hneg)
  rw [hty3, VVP_get3, VVP_write3] at w
  have a1 := (pexecM_prim mv fu (wDistNeg mv.nv) _ _).trans w
  have w2 := pstmtM_write_ok mv (gS P cl) (VVP F T Cc (D.set v (-inf)) Pp) 4 (by omega) (rdIdx mv.nv 7)
    (.unary i32 .neg (.literal i32 1)) (-1) v (hx2 _) (hp _) (by rw [VVP_get4]; omega) (by rw [hty4]; rfl)
  rw [hty4, VVP_get4, VVP_write4] at w2
  have a1' := (pexecM_prim mv fu (wParNeg mv.nv) _ _).trans w2
  have a2 := seqM_some a1 rfl (seqM_some a1' rfl (pexecM_skip mv fu (gS P cl) (VVP F T Cc (D.set v (-inf)) (Pp.set v (-1)))))
  have a3 := pexecM_scope mv fu _ _ _ _ a2
  have tk : (⟨(gS P cl).mem.take (gS P cl).mem.length, (gS P cl).bs.take (gS P cl).bs.length⟩ : PS) = gS P cl := by simp
  simp only [tk] at a3
  have a4 := seqM_some a3 rfl (pexecM_skip mv fu (gS P cl) (VVP F T Cc (D.set v (-inf)) (Pp.set v (-1))))
  refine ⟨_, a4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp

/-- `{ if (dist[u] == -inf) {mark} else { long long nd = dist[u] + cost[e]; if (nd < dist[v]) {mark} } }`. -/
theorem y3_exec (mv : MV) (hnv : mv.nv = 5) (hty2 : mv.ty 2 = s64) (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32)
    (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i e : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m)
    (hu : F.getD e 0 < n) (hv : T.getD e 0 < n)
    (hinf : s64.valid inf = true) (hneg : s64.valid (-inf) = true) (hDl : D.length = n) (hPl : Pp.length = n)
    (hCl : Cc.length = m)
    (hDv : ∀ x ∈ D, s64.valid x = true) (hCv : ∀ x ∈ Cc, s64.valid x = true)
    (hsum : D.getD (F.getD e 0) 0 ≠ -inf → s64.valid (D.getD (F.getD e 0) 0 + Cc.getD e 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Y3 mv.nv) (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)) (VVP F T Cc D Pp) = some r ∧
      r.ret = none ∧ r.ps = gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf) ∧
      r.vv = VVP F T Cc (markIn inf F T Cc e (D, Pp)).1 (markIn inf F T Cc e (D, Pp)).2 ∧
      r.cost ≤ 800 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 := by
  have hDu : D.getD (F.getD e 0) 0 ∈ D := getD_mem D _ (by omega)
  have hDvv : D.getD (T.getD e 0) 0 ∈ D := getD_mem D _ (by omega)
  have hCe : Cc.getD e 0 ∈ Cc := getD_mem Cc _ (by omega)
  obtain ⟨_, E1, E5, E6, E7⟩ := envBF mv P n m rounds i e (F.getD e 0) (T.getD e 0) inf hn hm hr hi (by omega) (by omega)
    (by omega) hinf
  have vdu := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) 3 (by omega) s64
    hty3.symm (rdIdx mv.nv 6) rfl rfl (F.getD e 0) (cidx_den _ (mv.nv + 6) _ E6 (by omega)) (D.getD (F.getD e 0) 0)
    (by rw [VVP_get3]; exact vec_getI D _ (by omega)) (by rw [hty3]; exact hDv _ hDu)
  have hx : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)))
      (.unary s64 .neg (.variable s64 (mv.nv + 1))) = some (-inf) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_unaryP, den_variable, E1, Option.bind_some]
    exact conv_signed s64 rfl rfl _ hneg
  have vc : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) (condEq mv.nv) =
      some (if D.getD (F.getD e 0) 0 = -inf then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdu, hx, Option.bind_some, Option.bind_some]
    exact eq_convP _ _
  have hE7 := E7
  by_cases heq : D.getD (F.getD e 0) 0 = -inf
  · rw [if_pos heq] at vc
    obtain ⟨rz, hz, hzret, hzps, hzvv, hzc, hzn, hzw⟩ := zn_exec mv hnv hty3 hty4 F T Cc D Pp P
      (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf) (T.getD e 0) inf (by omega) (by omega) (by simp [cC]) (by simp [cC])
      (by omega) hinf hneg fu
    have b1 := pexecM_branch_true mv fu (condEq mv.nv) (ZN mv.nv) (elseM mv.nv) _ _ 1 vc (by decide) rz hz
    have b2 := seqM_some b1 hzret (pexecM_skip mv fu rz.ps rz.vv)
    have b3 := pexecM_scope mv fu _ _ _ _ b2
    have tk : (⟨(gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)).mem.take (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)).mem.length,
        (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)).bs.take (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)).bs.length⟩ : PS) =
        gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf) := by simp
    rw [hzps] at b3
    simp only [tk] at b3
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    have hl : rz.ps.mem.length + rz.ps.bs.length = P.length + 16 := by rw [hzps]; simp [gS_size]
    refine ⟨_, b4, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hzvv]; simp only [markIn, if_pos heq]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
    · simp at *; omega
  · rw [if_neg heq] at vc
    have hs := hsum heq
    have vce := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) 2 (by omega) s64 hty2.symm
      (rdIdx mv.nv 5) rfl rfl e (cidx_den _ (mv.nv + 5) e E5 (by omega)) (Cc.getD e 0)
      (by rw [VVP_get2]; exact vec_getI Cc e (by omega)) (by rw [hty2]; exact hCv _ hCe)
    have vnd : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) (ndE mv.nv) =
        some (D.getD (F.getD e 0) 0 + Cc.getD e 0) := by
      rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdu, vce, Option.bind_some, Option.bind_some]
      exact conv_signed s64 rfl rfl _ hs
    have d1 := gSM_decl mv P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf) (VVP F T Cc D Pp) s64 _ _ _ vnd (conv_signed s64 rfl rfl _ hs)
    have q1 := (pexecM_prim mv fu (.declare s64 true (ndE mv.nv)) _ _).trans d1
    have hpsD : gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf ++ [⟨s64, D.getD (F.getD e 0) 0 + Cc.getD e 0⟩]) =
        gS P (cD n m rounds i e (F.getD e 0) (T.getD e 0) inf (D.getD (F.getD e 0) 0 + Cc.getD e 0)) := rfl
    rw [hpsD] at q1
    have E8 := envs mv P (cD n m rounds i e (F.getD e 0) (T.getD e 0) inf (D.getD (F.getD e 0) 0 + Cc.getD e 0)) 8
      (cs (D.getD (F.getD e 0) 0 + Cc.getD e 0)) rfl hs
    have E7' := envs mv P (cD n m rounds i e (F.getD e 0) (T.getD e 0) inf (D.getD (F.getD e 0) 0 + Cc.getD e 0)) 7
      (ci (T.getD e 0)) rfl (Proofs.BellmanFordExec.i32_valid_nat _ (by omega))
    have vdv := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cD n m rounds i e (F.getD e 0) (T.getD e 0) inf
      (D.getD (F.getD e 0) 0 + Cc.getD e 0)))) 3 (by omega) s64 hty3.symm (rdIdx mv.nv 7) rfl rfl (T.getD e 0)
      (cidx_den _ (mv.nv + 7) _ E7' (by omega)) (D.getD (T.getD e 0) 0)
      (by rw [VVP_get3]; exact vec_getI D _ (by omega)) (by rw [hty3]; exact hDv _ hDvv)
    have vc2 : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cD n m rounds i e (F.getD e 0) (T.getD e 0) inf
        (D.getD (F.getD e 0) 0 + Cc.getD e 0)))) (cond2 mv.nv) =
        some (if D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0 then 1 else 0) := by
      rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdenM_scalar _ _ _ _ rfl, den_variable, E8, vdv, Option.bind_some, Option.bind_some]
      exact lt_conv _ _
    obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ : ∃ rb : PRM,
        pexecM mv fu (.sequence (.branch (cond2 mv.nv) (ZN mv.nv) Sk) Sk)
          (gS P (cD n m rounds i e (F.getD e 0) (T.getD e 0) inf (D.getD (F.getD e 0) 0 + Cc.getD e 0))) (VVP F T Cc D Pp) = some rb ∧
        rb.ret = none ∧ rb.ps = gS P (cD n m rounds i e (F.getD e 0) (T.getD e 0) inf (D.getD (F.getD e 0) 0 + Cc.getD e 0)) ∧
        rb.vv = VVP F T Cc (markIn inf F T Cc e (D, Pp)).1 (markIn inf F T Cc e (D, Pp)).2 ∧
        rb.cost ≤ 500 ∧ rb.need ≤ P.length + 100 ∧ rb.wk ≤ 2 := by
      by_cases hlt : D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
      · rw [if_pos hlt] at vc2
        obtain ⟨rz, hz, hzret, hzps, hzvv, hzc, hzn, hzw⟩ := zn_exec mv hnv hty3 hty4 F T Cc D Pp P
          (cD n m rounds i e (F.getD e 0) (T.getD e 0) inf (D.getD (F.getD e 0) 0 + Cc.getD e 0)) (T.getD e 0) inf (by omega) (by omega)
          (by simp [cD]) (by simp [cD]) (by omega) hinf hneg fu
        have b1 := pexecM_branch_true mv fu (cond2 mv.nv) (ZN mv.nv) Sk _ _ 1 vc2 (by decide) rz hz
        have b2 := seqM_some b1 hzret (pexecM_skip mv fu rz.ps rz.vv)
        have hl : rz.ps.mem.length + rz.ps.bs.length = P.length + 18 := by rw [hzps]; simp [gS_size]
        refine ⟨_, b2, rfl, hzps, ?_, ?_, ?_, ?_⟩
        · rw [hzvv]; simp only [markIn, if_neg heq, if_pos hlt]
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
        · simpa using hzw
      · rw [if_neg hlt] at vc2
        have b1 := pexecM_branch_false mv fu (cond2 mv.nv) (ZN mv.nv) Sk _ _ vc2 _ (pexecM_skip mv fu _ _)
        have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
        refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
        · simp only [markIn, if_neg heq, if_neg hlt]
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
        · simp
    have q2 := seqM_some q1 rfl hrb
    have q3 := pexecM_scope mv fu _ _ _ _ q2
    have tk := gS_takeC P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf) (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)
      [cs (D.getD (F.getD e 0) 0 + Cc.getD e 0)] rfl
    rw [hrbps] at q3
    have hpsD' : gS P (cD n m rounds i e (F.getD e 0) (T.getD e 0) inf (D.getD (F.getD e 0) 0 + Cc.getD e 0)) =
        gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf ++ [cs (D.getD (F.getD e 0) 0 + Cc.getD e 0)]) := rfl
    rw [hpsD'] at q3
    simp only [tk] at q3
    have q4 := seqM_some q3 hrbret (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_false mv fu (condEq mv.nv) (ZN mv.nv) (elseM mv.nv) _ _ vc _ q4
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := pexecM_scope mv fu _ _ _ _ b2
    have tk2 : (⟨(gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)).mem.take (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)).mem.length,
        (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)).bs.take (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)).bs.length⟩ : PS) =
        gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf) := by simp
    simp only [tk2] at b3
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b4, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact hrbvv
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
    · simp at *; omega


/-- The invariant of the marking passes: every entry is `-inf` or in `[lo1, inf]`. -/
def Inv2 (inf lo1 : Int) (D : List Int) : Prop := ∀ x ∈ D, x = -inf ∨ (lo1 ≤ x ∧ x ≤ inf)

theorem markIn_cases (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (s : List Int × List Int) :
    markIn inf F T Cc e s = s ∨ markIn inf F T Cc e s = (s.1.set (T.getD e 0) (-inf), s.2.set (T.getD e 0) (-1)) := by
  unfold markIn
  split
  · right; rfl
  · split
    · right; rfl
    · left; rfl

theorem markEdge_cases (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (s : List Int × List Int) :
    markEdge inf F T Cc e s = s ∨ markEdge inf F T Cc e s = (s.1.set (T.getD e 0) (-inf), s.2.set (T.getD e 0) (-1)) := by
  unfold markEdge
  split
  · exact markIn_cases inf F T Cc e s
  · left; rfl

theorem markEdge_len1 (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (s : List Int × List Int) :
    (markEdge inf F T Cc e s).1.length = s.1.length := by
  rcases markEdge_cases inf F T Cc e s with h | h <;> rw [h] <;> simp

theorem markEdge_len2 (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (s : List Int × List Int) :
    (markEdge inf F T Cc e s).2.length = s.2.length := by
  rcases markEdge_cases inf F T Cc e s with h | h <;> rw [h] <;> simp

theorem markEdge_inv (inf lo1 : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (s : List Int × List Int)
    (h : Inv2 inf lo1 s.1) : Inv2 inf lo1 (markEdge inf F T Cc e s).1 := by
  rcases markEdge_cases inf F T Cc e s with h' | h' <;> rw [h']
  · exact h
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hx | hx
    · exact h x hx
    · exact Or.inl hx

/-- The marking edges `0 .. t-1` in order. -/
def markPrefix (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (s : List Int × List Int) : List Int × List Int :=
  (List.range t).foldl (fun s e => markEdge inf F T Cc e s) s

theorem markPrefix_succ (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (s : List Int × List Int) :
    markPrefix inf F T Cc (t + 1) s = markEdge inf F T Cc t (markPrefix inf F T Cc t s) := by
  unfold markPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem markPrefix_len1 (inf : Int) (F T : List Nat) (Cc : List Int) (s : List Int × List Int) :
    ∀ t, (markPrefix inf F T Cc t s).1.length = s.1.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [markPrefix_succ, markEdge_len1, ih]

theorem markPrefix_len2 (inf : Int) (F T : List Nat) (Cc : List Int) (s : List Int × List Int) :
    ∀ t, (markPrefix inf F T Cc t s).2.length = s.2.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [markPrefix_succ, markEdge_len2, ih]

theorem markPrefix_inv (inf lo1 : Int) (F T : List Nat) (Cc : List Int) (s : List Int × List Int)
    (h : Inv2 inf lo1 s.1) : ∀ t, Inv2 inf lo1 (markPrefix inf F T Cc t s).1 := by
  intro t
  induction t with
  | zero => exact h
  | succ t ih => rw [markPrefix_succ]; exact markEdge_inv inf lo1 F T Cc t _ ih

/-- `r` full marking rounds. -/
def markRounds (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) : Nat → List Int × List Int → List Int × List Int
  | 0, s => s
  | r + 1, s => markPrefix inf F T Cc m (markRounds inf F T Cc m r s)

theorem markRounds_len1 (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (s : List Int × List Int) :
    ∀ r, (markRounds inf F T Cc m r s).1.length = s.1.length := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih => simp only [markRounds]; rw [markPrefix_len1, ih]

theorem markRounds_len2 (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (s : List Int × List Int) :
    ∀ r, (markRounds inf F T Cc m r s).2.length = s.2.length := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih => simp only [markRounds]; rw [markPrefix_len2, ih]

theorem markRounds_inv (inf lo1 : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (s : List Int × List Int)
    (h : Inv2 inf lo1 s.1) : ∀ r, Inv2 inf lo1 (markRounds inf F T Cc m r s).1 := by
  intro r
  induction r with
  | zero => exact h
  | succ r ih => simp only [markRounds]; exact markPrefix_inv inf lo1 F T Cc _ ih m

theorem inv2_valid (inf lo1 : Int) (D : List Int) (h : Inv2 inf lo1 D) (hlo : -4611686018427387904 ≤ lo1)
    (hinf0 : 0 ≤ inf) (hinfH : inf ≤ 4611686018427387904) : ∀ x ∈ D, s64.valid x = true := by
  intro x hx
  rcases h x hx with h | h
  · exact s64_valid_of x (by omega)
  · exact s64_valid_of x (by omega)

theorem inv2_sum (inf lo1 Cb : Int) (D Cc : List Int) (h : Inv2 inf lo1 D) (hlo : -4611686018427387904 ≤ lo1)
    (hinfH : inf ≤ 4611686018427387904) (hCb : Cb ≤ 2305843009213693952)
    (hc : ∀ x ∈ Cc, -Cb ≤ x ∧ x ≤ Cb) (x : Int) (hx : x ∈ D) (hne : x ≠ -inf) (c : Int) (hcm : c ∈ Cc) :
    s64.valid (x + c) = true := by
  have h1 := hc c hcm
  rcases h x hx with h | h
  · exact absurd h hne
  · exact s64_valid_of _ (by omega)

/-- `if (dist[u] != inf) {...}` of the marking passes, followed by the empty statement. -/
theorem br3_exec (mv : MV) (hnv : mv.nv = 5) (hty2 : mv.ty 2 = s64) (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32)
    (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i e : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m)
    (hu : F.getD e 0 < n) (hv : T.getD e 0 < n)
    (hinf : s64.valid inf = true) (hneg : s64.valid (-inf) = true) (hDl : D.length = n) (hPl : Pp.length = n)
    (hCl : Cc.length = m)
    (hDv : ∀ x ∈ D, s64.valid x = true) (hCv : ∀ x ∈ Cc, s64.valid x = true)
    (hsum : D.getD (F.getD e 0) 0 ≠ -inf → s64.valid (D.getD (F.getD e 0) 0 + Cc.getD e 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (.sequence (BR3 mv.nv) Sk)
      (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)) (VVP F T Cc D Pp) = some r ∧ r.ret = none ∧
      r.ps = gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf) ∧
      r.vv = VVP F T Cc (markEdge inf F T Cc e (D, Pp)).1 (markEdge inf F T Cc e (D, Pp)).2 ∧
      r.cost ≤ 900 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 := by
  have hDu : D.getD (F.getD e 0) 0 ∈ D := getD_mem D _ (by omega)
  obtain ⟨_, E1, E5, E6, E7⟩ := envBF mv P n m rounds i e (F.getD e 0) (T.getD e 0) inf hn hm hr hi (by omega) (by omega)
    (by omega) hinf
  have vdu := rdM_val mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) 3 (by omega) s64
    hty3.symm (rdIdx mv.nv 6) rfl rfl (F.getD e 0) (cidx_den _ (mv.nv + 6) _ E6 (by omega)) (D.getD (F.getD e 0) 0)
    (by rw [VVP_get3]; exact vec_getI D _ (by omega)) (by rw [hty3]; exact hDv _ hDu)
  have vc1 : vdenM mv (VVP F T Cc D Pp) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) (cond1 mv.nv) =
      some (if D.getD (F.getD e 0) 0 ≠ inf then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdu, vdenM_scalar _ _ _ _ rfl, den_variable, E1, Option.bind_some, Option.bind_some]
    exact ne_conv _ _
  by_cases hd : D.getD (F.getD e 0) 0 ≠ inf
  · rw [if_pos hd] at vc1
    obtain ⟨ry, hy, hyret, hyps, hyvv, hyc, hyn, hyw⟩ := y3_exec mv hnv hty2 hty3 hty4 F T Cc D Pp P n m rounds i e inf hn hm hr hi he
      hu hv hinf hneg hDl hPl hCl hDv hCv hsum fu
    have b1 := pexecM_branch_true mv fu (cond1 mv.nv) (Y3 mv.nv) Sk _ _ 1 vc1 (by decide) ry hy
    have b2 := seqM_some b1 hyret (pexecM_skip mv fu ry.ps ry.vv)
    have hl : ry.ps.mem.length + ry.ps.bs.length = P.length + 16 := by rw [hyps]; simp [gS_size]
    refine ⟨_, b2, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact hyps
    · rw [hyvv]; simp only [markEdge, if_pos hd]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hyc ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hyn ⊢; omega
    · simpa using hyw
  · rw [if_neg hd] at vc1
    have b1 := pexecM_branch_false mv fu (cond1 mv.nv) (Y3 mv.nv) Sk _ _ vc1 _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [markEdge, if_neg hd]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp


/-- The body of the marking loop. -/
theorem e_body3 (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i e : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m)
    (hinf : s64.valid inf = true) (hneg : s64.valid (-inf) = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D.length = n) (hPl : Pp.length = n)
    (hCv : ∀ x ∈ Cc, s64.valid x = true) (hDv : ∀ x ∈ D, s64.valid x = true)
    (hsum : D.getD (F.getD e 0) 0 ≠ -inf → s64.valid (D.getD (F.getD e 0) 0 + Cc.getD e 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (XB3 mv.nv) (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e]) (VVP F T Cc D Pp) = some r ∧
      r.ret = none ∧
      r.ps = gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0), ci (T.getD e 0)] ∧
      r.vv = VVP F T Cc (markEdge inf F T Cc e (D, Pp)).1 (markEdge inf F T Cc e (D, Pp)).2 ∧
      r.cost ≤ 950 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 := by
  have hu : F.getD e 0 < n := by
    have : F.getD e 0 = F[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, he]
    rw [this]; exact hFn _ (List.getElem_mem _)
  have hv : T.getD e 0 < n := by
    have : T.getD e 0 = T[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, he]
    rw [this]; exact hTn _ (List.getElem_mem _)
  obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ := br3_exec mv hnv hty2 hty3 hty4 F T Cc D Pp P n m rounds i e inf hn hm hr hi he
    hu hv hinf hneg hDl hPl hCl hDv hCv hsum fu
  obtain ⟨r, hrr, hret, hps, hvv, hc, hnd, hw⟩ := decl_uvP mv hnv hty0 hty1 F T Cc D Pp P n m rounds i e inf hn hm hr hi he hinf
    hFl hTl hFn hTn fu (.sequence (BR3 mv.nv) Sk) rb hrb
  refine ⟨r, hrr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hret]; exact hrbret
  · rw [hps]; exact hrbps
  · rw [hvv]; exact hrbvv
  · omega
  · omega
  · omega

/-- One marking pass over the edges. -/
theorem e_loop3 (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (F T : List Nat) (Cc D0 P0 : List Int) (P : List Cell) (n m rounds i : Nat)
    (inf Cb lo1 : Int)
    (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hr : rounds < M31) (hi : i < M31)
    (hinf : s64.valid inf = true) (hinf0 : 0 ≤ inf) (hinfH : inf ≤ 4611686018427387904)
    (hlo : -4611686018427387904 ≤ lo1) (hCb : Cb ≤ 2305843009213693952)
    (hcc : ∀ x ∈ Cc, -Cb ≤ x ∧ x ≤ Cb) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) (hPl : P0.length = n)
    (hI : Inv2 inf lo1 D0) (fu : Nat) (hfu : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 5 2 (XB3 mv.nv)) (gS P [ci n, cs inf, ci m, ci rounds, ci i]) (VVP F T Cc D0 P0) =
      some res ∧ res.ps = gS P [ci n, cs inf, ci m, ci rounds, ci i] ∧
      res.vv = VVP F T Cc (markPrefix inf F T Cc m (D0, P0)).1 (markPrefix inf F T Cc m (D0, P0)).2 ∧ res.ret = none ∧
      res.cost ≤ 970 * m + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ 2 * m := by
  have hneg : s64.valid (-inf) = true := s64_valid_of _ (by omega)
  have hm' : m < 2147483647 := hm2
  obtain ⟨res, C2, hr', hps, hC2, hI', hret, hc, hnd, hw⟩ := for_stmt_runB mv P 5 2 m (by omega) hm' (XB3 mv.nv)
    (fun t vv C => vv = VVP F T Cc (markPrefix inf F T Cc t (D0, P0)).1 (markPrefix inf F T Cc t (D0, P0)).2 ∧
      C = [ci n, cs inf, ci m, ci rounds, ci i]) 950 100 2 0
    (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hIt := markPrefix_inv inf lo1 F T Cc (D0, P0) hI t
      have hDlt : (markPrefix inf F T Cc t (D0, P0)).1.length = n := by rw [markPrefix_len1]; exact hDl
      have hPlt : (markPrefix inf F T Cc t (D0, P0)).2.length = n := by rw [markPrefix_len2]; exact hPl
      have hDvt := inv2_valid inf lo1 _ hIt hlo hinf0 hinfH
      have hCv : ∀ x ∈ Cc, s64.valid x = true := fun x hx => s64_valid_of x (by have := hcc x hx; omega)
      have hu : F.getD t 0 < n := by
        have : F.getD t 0 = F[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, ht]
        rw [this]; exact hFn _ (List.getElem_mem _)
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := e_body3 mv hnv hty0 hty1 hty2 hty3 hty4 F T Cc
        (markPrefix inf F T Cc t (D0, P0)).1 (markPrefix inf F T Cc t (D0, P0)).2 P n m rounds i t inf hn hm hr hi ht hinf hneg hFl hTl hCl
        hFn hTn hDlt hPlt hCv hDvt
        (fun hne => inv2_sum inf lo1 Cb _ Cc hIt hlo hinfH hCb hcc _ (getD_mem _ _ (by omega)) hne _ (getD_mem Cc t (by omega))) fu
      refine ⟨r, [ci (F.getD t 0), ci (T.getD t 0)], [ci n, cs inf, ci m, ci rounds, ci i], hr, hret, hps, rfl, rfl,
        ⟨?_, rfl⟩, hc, ?_, hwk⟩
      · rw [hvv, markPrefix_succ]
      · omega)
    (VVP F T Cc D0 P0) [ci n, cs inf, ci m, ci rounds, ci i] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI'
  subst hC
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- One round of the marking loop. -/
theorem i_body3 (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (F T : List Nat) (Cc D Pp : List Int) (P : List Cell) (n m rounds i : Nat)
    (inf Cb lo1 : Int)
    (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hr : rounds < M31) (hi : i < M31)
    (hinf : s64.valid inf = true) (hinf0 : 0 ≤ inf) (hinfH : inf ≤ 4611686018427387904)
    (hlo : -4611686018427387904 ≤ lo1) (hCb : Cb ≤ 2305843009213693952)
    (hcc : ∀ x ∈ Cc, -Cb ≤ x ∧ x ≤ Cb) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D.length = n) (hPl : Pp.length = n)
    (hI : Inv2 inf lo1 D) (fu : Nat) (hfu : m + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (.sequence (forStmtB mv.nv 5 2 (XB3 mv.nv)) Sk) (gS P [ci n, cs inf, ci m, ci rounds, ci i])
      (VVP F T Cc D Pp) = some r ∧ r.ret = none ∧ r.ps = gS P [ci n, cs inf, ci m, ci rounds, ci i] ∧
      r.vv = VVP F T Cc (markPrefix inf F T Cc m (D, Pp)).1 (markPrefix inf F T Cc m (D, Pp)).2 ∧
      r.cost ≤ 970 * m + 30 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 * m := by
  obtain ⟨res, hres, hps, hvv, hret, hc, hnd, hw⟩ := e_loop3 mv hnv hty0 hty1 hty2 hty3 hty4 F T Cc D Pp P n m rounds i inf Cb lo1 hn hm hm2 hr
    hi hinf hinf0 hinfH hlo hCb hcc hFl hTl hCl hFn hTn hDl hPl hI fu hfu
  have q := seqM_some hres hret (pexecM_skip mv fu res.ps res.vv)
  refine ⟨_, q, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact hps
  · exact hvv
  · simpa using hc
  · simp [gS_size] at hnd hps ⊢; rw [hps]; simp [gS_size]; omega
  · simpa using hw

/-- The marking loop `for (int i = 0; i < n; i++) {...}`. -/
theorem i_loop3 (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (F T : List Nat) (Cc D0 P0 : List Int) (P : List Cell) (n m rounds : Nat)
    (inf Cb lo1 : Int)
    (hn : n < M31) (hn2 : n < 2147483647) (hm : m < M31) (hm2 : m < 2147483647) (hr : rounds < M31)
    (hinf : s64.valid inf = true) (hinf0 : 0 ≤ inf) (hinfH : inf ≤ 4611686018427387904)
    (hlo : -4611686018427387904 ≤ lo1) (hCb : Cb ≤ 2305843009213693952)
    (hcc : ∀ x ∈ Cc, -Cb ≤ x ∧ x ≤ Cb) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) (hPl : P0.length = n)
    (hI : Inv2 inf lo1 D0) (fu : Nat) (hfu : m + 1 + n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 4 0 (.sequence (forStmtB mv.nv 5 2 (XB3 mv.nv)) Sk))
      (gS P [ci n, cs inf, ci m, ci rounds]) (VVP F T Cc D0 P0) = some res ∧ res.ps = gS P [ci n, cs inf, ci m, ci rounds] ∧
      res.vv = VVP F T Cc (markRounds inf F T Cc m n (D0, P0)).1 (markRounds inf F T Cc m n (D0, P0)).2 ∧ res.ret = none ∧
      res.cost ≤ (970 * m + 50) * n + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ 2 * m * n := by
  obtain ⟨res, C2, hr', hps, hC2, hI', hret, hc, hnd, hw⟩ := for_stmt_runB mv P 4 0 n (by omega) hn2
    (.sequence (forStmtB mv.nv 5 2 (XB3 mv.nv)) Sk)
    (fun t vv C => vv = VVP F T Cc (markRounds inf F T Cc m t (D0, P0)).1 (markRounds inf F T Cc m t (D0, P0)).2 ∧
      C = [ci n, cs inf, ci m, ci rounds]) (970 * m + 30) 100 (2 * m) (m + 1)
    (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ hfu'
      subst hvv; subst hC
      have hIt := markRounds_inv inf lo1 F T Cc m (D0, P0) hI t
      have hDlt : (markRounds inf F T Cc m t (D0, P0)).1.length = n := by rw [markRounds_len1]; exact hDl
      have hPlt : (markRounds inf F T Cc m t (D0, P0)).2.length = n := by rw [markRounds_len2]; exact hPl
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := i_body3 mv hnv hty0 hty1 hty2 hty3 hty4 F T Cc
        (markRounds inf F T Cc m t (D0, P0)).1 (markRounds inf F T Cc m t (D0, P0)).2 P n m rounds t inf Cb lo1 hn hm hm2 hr
        (by show t < 2147483648; omega) hinf hinf0 hinfH hlo hCb hcc hFl hTl hCl hFn hTn hDlt hPlt hIt fu (by omega)
      refine ⟨r, [], [ci n, cs inf, ci m, ci rounds], hr, hret, hps, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      rw [hvv]; rfl)
    (VVP F T Cc D0 P0) [ci n, cs inf, ci m, ci rounds] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI'
  subst hC
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega


theorem size_val0P (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (hn : (vv 0).length < 2147483648) :
    vdenM mv vv env (.cast i32 (.size (.integer i32) (.local 0))) = some ((vv 0).length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer i32) (.local 0))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer i32) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer i32) (.local 0)) = some ((vv 0).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨by omega, hty0.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

/-- The whole body of `bellman_ford` (for `n ≥ 1`). -/
theorem body_execP (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (F T : List Nat) (Cc D0 P0 : List Int) (P : List Cell) (n m : Nat)
    (inf Cb lo : Int)
    (hn : n < M31) (hn32 : n < 2147483647) (hn1 : 1 ≤ n) (hm2 : m < 2147483647)
    (hinf : s64.valid inf = true) (hinf0 : 0 ≤ inf) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) (hPl : P0.length = n)
    (b : Bnd inf Cb lo m Cc D0)
    (hloR : -4611686018427387904 ≤ lo - ((n - 1 : Nat) : Int) * ((m : Int) * Cb)) (fu : Nat)
    (hfu : m + 1 + n + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyBFP mv.nv) (gS P [ci n, cs inf]) (VVP F T Cc D0 P0) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, cs inf, ci m, ci (n - 1)] ∧
      r.vv = VVP F T Cc
        (markRounds inf F T Cc m n (roundsL inf F T Cc m (n - 1) D0, roundsPL inf F T Cc m (n - 1) D0 P0)).1
        (markRounds inf F T Cc m n (roundsL inf F T Cc m (n - 1) D0, roundsPL inf F T Cc m (n - 1) D0 P0)).2 ∧
      r.cost ≤ (970 * m + 50) * (n - 1) + (970 * m + 50) * n + 200 ∧ r.need ≤ P.length + 100 ∧
      r.wk ≤ 2 * m * (n - 1) + 2 * m * n := by
  have hm31 : m < M31 := by
    show m < 2147483648
    omega
  have hlen0 : (VVP F T Cc D0 P0 0).length = m := by rw [VVP_get0]; simp [hFl]
  have hsz := size_val0P mv hnv hty0 (VVP F T Cc D0 P0) (penvN mv.nv (gS P [ci n, cs inf])) (by rw [hlen0]; exact hm31)
  rw [hlen0] at hsz
  have d1 := gSM_decl mv P [ci n, cs inf] (VVP F T Cc D0 P0) i32 _ _ _ hsz (conv_signed i32 rfl rfl _ (validN m hm31))
  have q1 := (pexecM_prim mv fu declM _ _).trans d1
  have hE0 : penvN mv.nv (gS P [ci n, cs inf, ci m]) mv.nv i32 = some (n : Int) :=
    envs mv P [ci n, cs inf, ci m] 0 (ci n) rfl (validN n hn)
  have hsub : vdenM mv (VVP F T Cc D0 P0) (penvN mv.nv (gS P [ci n, cs inf, ci m]))
      (.binary i32 .sub (.variable i32 mv.nv) (.literal i32 1)) = some ((n - 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, hE0, Option.bind_some, den_literal,
      if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
    have : binaryValue .sub (n : Int) 1 = ((n - 1 : Nat) : Int) := by
      show (n : Int) - 1 = _
      omega
    rw [this]
    exact conv_signed i32 rfl rfl _ (validN _ (by have : n < 2147483648 := hn; omega))
  have d2 := gSM_decl mv P [ci n, cs inf, ci m] (VVP F T Cc D0 P0) i32 _ _ _ hsub
    (conv_signed i32 rfl rfl _ (validN _ (by have : n < 2147483648 := hn; omega)))
  have q2 := (pexecM_prim mv fu (declR mv.nv) _ _).trans d2
  have hn31 : n - 1 < 2147483647 := by have : n < 2147483648 := hn; omega
  obtain ⟨rl, hrl, hrlps, hrlvv, hrlret, hrlc, hrln, hrlw⟩ := i_loopP mv hnv hty0 hty1 hty2 hty3 hty4 F T Cc D0 P0 P n m (n - 1) inf Cb lo hn
    hm31 hm2 hn31 hinf hFl hTl hCl hFn hTn hDl hPl b hloR fu (by omega)
  have hlen1 : (roundsL inf F T Cc m (n - 1) D0).length = n := by rw [roundsL_length, hDl]
  have hlen2 : (roundsPL inf F T Cc m (n - 1) D0 P0).length = n := by rw [roundsPL_length, hPl]
  have hI : Inv2 inf (lo - ((n - 1 : Nat) : Int) * ((m : Int) * Cb)) (roundsL inf F T Cc m (n - 1) D0) := by
    intro x hx
    exact Or.inr (roundsL_bound inf Cb lo F T Cc D0 n m hFl hTl hCl hFn hTn hDl b.cb0 b.cc b.d0 (n - 1) x hx)
  obtain ⟨rm, hrm, hrmps, hrmvv, hrmret, hrmc, hrmn, hrmw⟩ := i_loop3 mv hnv hty0 hty1 hty2 hty3 hty4 F T Cc
    (roundsL inf F T Cc m (n - 1) D0) (roundsPL inf F T Cc m (n - 1) D0 P0) P n m (n - 1) inf Cb
    (lo - ((n - 1 : Nat) : Int) * ((m : Int) * Cb)) hn hn32 hm31 hm2 (by omega) hinf hinf0 b.infH hloR b.cbH b.cc hFl hTl hCl hFn hTn
    hlen1 hlen2 hI fu (by omega)
  have q3 := seqM_some hrm hrmret (pexecM_skip mv fu rm.ps rm.vv)
  have q4 := seqM_some hrl hrlret (by rw [hrlps, hrlvv]; exact q3)
  have q5 := seqM_some q2 rfl q4
  have q6 := seqM_some q1 rfl q5
  refine ⟨_, q6, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hrmps
  · exact hrmvv
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrlc hrmc ⊢
    have h570 : (570 * m + 50) * (n - 1) ≤ (970 * m + 50) * (n - 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrln hrmn ⊢
    have hl : rm.ps.mem.length + rm.ps.bs.length = P.length + 8 := by rw [hrmps]; simp [gS_size]
    omega
  · simp at hrlw hrmw ⊢
    omega


end Proofs.BellmanFordPExec
