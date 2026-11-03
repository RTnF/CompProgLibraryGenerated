import Proofs.LowlinkExec2

namespace Proofs.LowlinkExec3
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getM vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false)
open Proofs.DijkstraScan
open Proofs.DijkstraExec
open Proofs.LowlinkProg Proofs.LowlinkLists Proofs.LowlinkExec Proofs.LowlinkExec2

/-- `vector[k][cell j] = e;` -/
theorem step_write (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (k j : Nat) (vE : NExpr)
    (hk : k < mv.nv) (hty : mv.ty k = i32) {idx : Nat} (hj : cl[j]? = some (ci idx)) (hidx : idx < M31) (x : Int)
    (hx : vdenM mv vv (penvN mv.nv (gS P cl)) vE = some x) (hlt : idx < (vv k).length) (hv : i32.valid x = true) :
    pexecM mv fu (.primitive (wrv mv.nv k j vE)) (gS P cl) vv =
      some ⟨gS P cl, upd vv k ((vv k).set idx x), none, (vwp vE).1 + (vwp (ixc mv.nv j)).1 + 3,
        (gS P cl).mem.length + (gS P cl).bs.length + (ixc mv.nv j).nodes + vE.nodes + (vwp vE).2 +
          (vwp (ixc mv.nv j)).2 + 5, 1⟩ := by
  have hp := d_ixc mv vv P cl hj hidx
  have wr := pstmtM_write_ok mv (gS P cl) vv k hk (ixc mv.nv j) vE x idx hx hp hlt (by rw [hty]; exact hv)
  rw [hty] at wr
  exact (pexecM_prim mv fu _ _ _).trans wr

/-- `cell j = e;` (an `int` cell) -/
theorem step_assign (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (j : Nat) (e : NExpr) {y : Nat}
    (hj : cl[j]? = some (ci y)) (hy : y < M31) (z : Nat) (hz : z < M31)
    (he : vdenM mv vv (penvN mv.nv (gS P cl)) e = some (z : Int)) :
    pexecM mv fu (.primitive (.assign (mv.nv + j) i32 e)) (gS P cl) vv =
      some ⟨gS P (cl.set j (ci z)), vv, none, (vwp e).1 + 1,
        (gS P cl).mem.length + (gS P cl).bs.length + (vwp e).2 + 2, 0⟩ := by
  have hl : j < cl.length := (List.getElem?_eq_some_iff.mp hj).1
  have d := gSM_assign mv P cl vv j hl i32 e (z : Int) (z : Int) he (ci y) hj rfl (i32v y hy)
    (conv_signed i32 rfl rfl _ (i32v z hz))
  exact (pexecM_prim mv fu _ _ _).trans (by simpa [gS_size] using d)


/-- The arrays after the push branch. -/
def pushL (H : List Nat) (x : XS) (cnt sp v w : Nat) : XS :=
  { st := x.st
    Ol := x.Ol.set w (cnt : Int)
    Ll := x.Ll.set w (cnt : Int)
    Pl := x.Pl.set w (v : Int)
    Sl := x.Sl
    Il := x.Il.set w (H.getD w 0 : Int)
    Kl := x.Kl.set sp (w : Int) }

/-- The push branch: `par[w] = v; ord[w] = cnt; low[w] = cnt; cnt++; it[w] = head[w]; stk[sp] = w; sp++;` -/
theorem pushT_exec (mv : MV) (hnv : mv.nv = 8) (hty : ∀ k, k < 8 → mv.ty k = i32) (H T : List Nat) (x : XS) {n : Nat}
    (hO : x.Ol.length = n) (hL : x.Ll.length = n) (hP : x.Pl.length = n) (hI : x.Il.length = n) (hK : x.Kl.length = n)
    (hHl : H.length = n + 1) (P : List Cell) (cnt r sp v e w : Nat) (hn : n < M31) (hn1 : n + 1 < M31) (hcnt : cnt < n) (hsp : sp < n)
    (hvn : v < n) (hwn : w < n) (hhd : H.getD w 0 < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (PUSHT mv.nv) (gS P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w]) (VX H T x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci (cnt + 1), ci r, ci (sp + 1), ci v, ci e, ci w] ∧
      rr.vv = VX H T (pushL H x cnt sp v w) ∧
      rr.cost ≤ 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 5 := by
  have hvM : v < M31 := by omega
  have hwM : w < M31 := by omega
  have hcM : cnt < M31 := by omega
  have hsM : sp < M31 := by omega
  -- par[w] = v
  have s1 := step_write mv fu P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (VX H T x) 4 6 (vr mv.nv 4) (by omega)
    (hty 4 (by omega)) (idx := w) rfl hwM (v : Int) (d_vr mv _ P _ (j := 4) (x := v) rfl hvM)
    (by rw [VX_4, hP]; exact hwn) (i32v v hvM)
  obtain ⟨x1, hx1⟩ : ∃ x1 : XS, x1 = { x with Pl := x.Pl.set w (v : Int) } := ⟨_, rfl⟩
  rw [VX_4, VX_w4, ← hx1] at s1
  -- ord[w] = cnt
  have s2 := step_write mv fu P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (VX H T x1) 2 6 (vr mv.nv 1) (by omega)
    (hty 2 (by omega)) (idx := w) rfl hwM (cnt : Int) (d_vr mv _ P _ (j := 1) (x := cnt) rfl hcM)
    (by rw [VX_2, hx1]; exact (by rw [hO]; exact hwn)) (i32v cnt hcM)
  obtain ⟨x2, hx2⟩ : ∃ x2 : XS, x2 = { x1 with Ol := x1.Ol.set w (cnt : Int) } := ⟨_, rfl⟩
  rw [VX_2, VX_w2, ← hx2] at s2
  -- low[w] = cnt
  have s3 := step_write mv fu P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (VX H T x2) 3 6 (vr mv.nv 1) (by omega)
    (hty 3 (by omega)) (idx := w) rfl hwM (cnt : Int) (d_vr mv _ P _ (j := 1) (x := cnt) rfl hcM)
    (by rw [VX_3, hx2, hx1]; exact (by rw [hL]; exact hwn)) (i32v cnt hcM)
  obtain ⟨x3, hx3⟩ : ∃ x3 : XS, x3 = { x2 with Ll := x2.Ll.set w (cnt : Int) } := ⟨_, rfl⟩
  rw [VX_3, VX_w3, ← hx3] at s3
  -- cnt = cnt + 1
  have hc1 : cnt + 1 < M31 := by omega
  have s4 := step_assign mv fu P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (VX H T x3) 1
    (.binary i32 .add (vr mv.nv 1) one) (y := cnt) rfl hcM (cnt + 1) hc1 (by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact add1_den _ _ cnt (ev_cell mv P _ (j := 1) rfl hcM) hc1)
  -- it[w] = head[w]
  have hHw : (VX H T x3 0)[w]? = some ((H.getD w 0 : Nat) : Int) := by
    rw [VX_0]; exact vec_getM H w (by omega)
  have s5 := step_write mv fu P ([ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w].set 1 (ci (cnt + 1))) (VX H T x3) 6 6
    (rdv mv.nv 0 6) (by omega) (hty 6 (by omega)) (idx := w) rfl hwM ((H.getD w 0 : Nat) : Int)
    (d_rdv mv _ P _ (k := 0) (j := 6) (x := w) (by omega) (hty 0 (by omega)) rfl hwM _ hHw (i32v _ hhd))
    (by rw [VX_6, hx3, hx2, hx1]; exact (by rw [hI]; exact hwn)) (i32v _ hhd)
  obtain ⟨x5, hx5⟩ : ∃ x5 : XS, x5 = { x3 with Il := x3.Il.set w (H.getD w 0 : Int) } := ⟨_, rfl⟩
  rw [VX_6, VX_w6, ← hx5] at s5
  -- stk[sp] = w
  have s6 := step_write mv fu P ([ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w].set 1 (ci (cnt + 1))) (VX H T x5) 7 3
    (vr mv.nv 6) (by omega) (hty 7 (by omega)) (idx := sp) rfl hsM (w : Int)
    (d_vr mv _ P _ (j := 6) (x := w) rfl hwM) (by rw [VX_7, hx5, hx3, hx2, hx1]; exact (by rw [hK]; exact hsp))
    (i32v w hwM)
  obtain ⟨x6, hx6⟩ : ∃ x6 : XS, x6 = { x5 with Kl := x5.Kl.set sp (w : Int) } := ⟨_, rfl⟩
  rw [VX_7, VX_w7, ← hx6] at s6
  -- sp = sp + 1
  have hs1 : sp + 1 < M31 := by omega
  have s7 := step_assign mv fu P ([ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w].set 1 (ci (cnt + 1))) (VX H T x6) 3
    (.binary i32 .add (vr mv.nv 3) one) (y := sp) rfl hsM (sp + 1) hs1 (by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact add1_den _ _ sp (ev_cell mv P _ (j := 3) rfl hsM) hs1)
  have t7 := seqM_some s7 rfl (pexecM_skip mv fu _ _)
  have t6 := seqM_some s6 rfl t7
  have t5 := seqM_some s5 rfl t6
  have t4 := seqM_some s4 rfl t5
  have t3 := seqM_some s3 rfl t4
  have t2 := seqM_some s2 rfl t3
  have t1 := seqM_some s1 rfl t2
  have sc := scope_gS mv fu (PUSHB mv.nv) P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w]
    [ci n, ci (cnt + 1), ci r, ci (sp + 1), ci v, ci e, ci w] (VX H T x) _ rfl t1 rfl
  have fin := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, fin, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show VX H T x6 = _
    rw [hx6, hx5, hx3, hx2, hx1]
    rfl
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


/-- `if (ord[w] < low[v]) low[v] = ord[w];` -/
theorem cwLow_exec (mv : MV) (hnv : mv.nv = 8) (hty : ∀ k, k < 8 → mv.ty k = i32) (H T : List Nat) (x : XS) {n : Nat}
    (hO : x.Ol.length = n) (hL : x.Ll.length = n) (vO : ∀ y ∈ x.Ol, i32.valid y = true)
    (vL : ∀ y ∈ x.Ll, i32.valid y = true) (P cl : List Cell) {v w : Nat} (hv : cl[4]? = some (ci v))
    (hw : cl[6]? = some (ci w)) (hvn : v < n) (hwn : w < n) (hn : n < M31) (fu : Nat) :
    ∃ r1 : PRM, pexecM mv fu (CWb (cLow mv.nv) (sLowU mv.nv)) (gS P cl) (VX H T x) = some r1 ∧ r1.ret = none ∧
      r1.ps = gS P cl ∧
      r1.vv = VX H T { x with Ll := if x.Ol.getD w 0 < x.Ll.getD v 0 then x.Ll.set v (x.Ol.getD w 0) else x.Ll } ∧
      r1.cost ≤ 60 ∧ r1.need ≤ P.length + 2 * cl.length + 60 ∧ r1.wk ≤ 1 := by
  have hvM : v < M31 := by omega
  have hwM : w < M31 := by omega
  have hOw : (VX H T x 2)[w]? = some (x.Ol.getD w 0) := by
    rw [VX_2]; exact intList_get x.Ol w (by rw [hO]; exact hwn)
  have hLv : (VX H T x 3)[v]? = some (x.Ll.getD v 0) := by
    rw [VX_3]; exact intList_get x.Ll v (by rw [hL]; exact hvn)
  have dOw := d_rdv mv (VX H T x) P cl (k := 2) (j := 6) (x := w) (by omega) (hty 2 (by omega)) hw hwM _ hOw
    (rd_valid vO (by rw [hO]; exact hwn))
  have dLv := d_rdv mv (VX H T x) P cl (k := 3) (j := 4) (x := v) (by omega) (hty 3 (by omega)) hv hvM _ hLv
    (rd_valid vL (by rw [hL]; exact hvn))
  have hc := d_binb mv (VX H T x) P cl (op := .lt) (a := rdv mv.nv 2 6) (b := rdv mv.nv 3 4) rfl dOw dLv
  rw [bt_lt] at hc
  by_cases hlt : x.Ol.getD w 0 < x.Ll.getD v 0
  · rw [if_pos hlt] at hc
    have dI := d_ixc mv (VX H T x) P cl (j := 4) (x := v) hv hvM
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := cw_true mv fu (cLow mv.nv) (ixc mv.nv 4) (rdv mv.nv 2 6) 3 (by omega)
      (hty 3 (by omega)) (gS P cl) (VX H T x) 1 hc (by decide) _ v dOw dI (by rw [VX_3, hL]; exact hvn)
      (rd_valid vO (by rw [hO]; exact hwn))
    refine ⟨r1, h1, ret1, ps1, ?_, ?_, ?_, ?_⟩
    · rw [vv1, VX_w3, VX_3, if_pos hlt]
    · rw [c1]; simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at n1 ⊢; omega
    · omega
  · rw [if_neg hlt] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := cw_false mv fu (cLow mv.nv) (sLowU mv.nv) (gS P cl) (VX H T x) hc
    refine ⟨r1, h1, ret1, ps1, ?_, ?_, ?_, ?_⟩
    · rw [vv1, if_neg hlt]
    · rw [c1]; simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at n1 ⊢; omega
    · omega


/-- The arrays after the visited branch. -/
def backL (x : XS) (v w : Nat) : XS :=
  { st := x.st
    Ol := x.Ol
    Ll := if (w : Int) ≠ x.Pl.getD v 0 ∧ x.Ol.getD w 0 < x.Ll.getD v 0 then x.Ll.set v (x.Ol.getD w 0) else x.Ll
    Pl := x.Pl
    Sl := x.Sl
    Il := x.Il
    Kl := x.Kl }

/-- The visited branch: `if (w != par[v]) { if (ord[w] < low[v]) low[v] = ord[w]; }` -/
theorem backE_exec (mv : MV) (hnv : mv.nv = 8) (hty : ∀ k, k < 8 → mv.ty k = i32) (H T : List Nat) (x : XS) {n : Nat}
    (hO : x.Ol.length = n) (hL : x.Ll.length = n) (hP : x.Pl.length = n) (vO : ∀ y ∈ x.Ol, i32.valid y = true)
    (vL : ∀ y ∈ x.Ll, i32.valid y = true) (vP : ∀ y ∈ x.Pl, i32.valid y = true) (P : List Cell)
    (cnt r sp v e w : Nat) (hvn : v < n) (hwn : w < n) (hn : n < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (BACKE mv.nv) (gS P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w]) (VX H T x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] ∧
      rr.vv = VX H T (backL x v w) ∧ rr.cost ≤ 300 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 1 := by
  have hvM : v < M31 := by omega
  have hwM : w < M31 := by omega
  have hPv : (VX H T x 4)[v]? = some (x.Pl.getD v 0) := by
    rw [VX_4]; exact intList_get x.Pl v (by rw [hP]; exact hvn)
  have dW := d_vr mv (VX H T x) P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (j := 6) (x := w) rfl hwM
  have dPv := d_rdv mv (VX H T x) P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (k := 4) (j := 4) (x := v) (by omega)
    (hty 4 (by omega)) rfl hvM _ hPv (rd_valid vP (by rw [hP]; exact hvn))
  have hc := d_binb mv (VX H T x) P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (op := .ne) (a := vr mv.nv 6)
    (b := rdv mv.nv 4 4) rfl dW dPv
  rw [bt_ne] at hc
  by_cases hne : (w : Int) ≠ x.Pl.getD v 0
  · rw [if_pos hne] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := cwLow_exec mv hnv hty H T x hO hL vO vL P
      [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (v := v) (w := w) rfl rfl hvn hwn hn fu
    have s1 := seqM_some h1 ret1 (pexecM_skip mv fu r1.ps r1.vv)
    have sc := scope_gS mv fu (.sequence (CWb (cLow mv.nv) (sLowU mv.nv)) Sk) P
      [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (VX H T x) _ rfl s1 (by rw [ps1])
    have s2 := seqM_some sc rfl (pexecM_skip mv fu _ _)
    have br := pexecM_branch_true mv fu (cPar mv.nv) (BK2 mv.nv) Sk _ (VX H T x) 1 hc (by decide) _ s2
    have s3 := seqM_some br rfl (pexecM_skip mv fu _ _)
    have sc2 := scope_gS mv fu _ P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w]
      [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (VX H T x) _ rfl s3 rfl
    have fin := seqM_some sc2 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, fin, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · show r1.vv = VX H T (backL x v w)
      rw [vv1]
      refine VX_congr H T rfl ?_ rfl rfl rfl rfl
      show (if x.Ol.getD w 0 < x.Ll.getD v 0 then x.Ll.set v (x.Ol.getD w 0) else x.Ll) = (backL x v w).Ll
      by_cases hA : x.Ol.getD w 0 < x.Ll.getD v 0
      · simp only [backL]; rw [if_pos hA, if_pos ⟨hne, hA⟩]
      · simp only [backL]; rw [if_neg hA, if_neg (fun h => hA h.2)]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1]
      simp only [List.length_cons, List.length_nil] at n1
      omega
    · simp
      omega
  · rw [if_neg hne] at hc
    have br := pexecM_branch_false mv fu (cPar mv.nv) (BK2 mv.nv) Sk _ (VX H T x) hc _ (pexecM_skip mv fu _ _)
    have s3 := seqM_some br rfl (pexecM_skip mv fu _ _)
    have sc2 := scope_gS mv fu _ P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w]
      [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (VX H T x) _ rfl s3 rfl
    have fin := seqM_some sc2 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, fin, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · show VX H T x = VX H T (backL x v w)
      refine VX_congr H T rfl ?_ rfl rfl rfl rfl
      show x.Ll = (backL x v w).Ll
      simp only [backL]; rw [if_neg (fun h => hne h.1)]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp


/-- `int e = it[v]; int w = target[e]; it[v] = e + 1;` followed by `REST`. -/
theorem thens_prefix (mv : MV) (hnv : mv.nv = 8) (hty : ∀ k, k < 8 → mv.ty k = i32) (H T : List Nat) (x : XS)
    {n : Nat} (hI : x.Il.length = n) (vI : ∀ y ∈ x.Il, i32.valid y = true) (P : List Cell) (cnt r sp v e w : Nat)
    (hn : n < M31) (hvn : v < n) (hcnt : cnt < M31) (hr : r < M31) (hsp : sp < M31)
    (he : x.Il.getD v 0 = (e : Int)) (heT : e < T.length) (hTM : T.length < M31) (hwn : T.getD e 0 = w) (hwl : w < n)
    (he1 : e + 1 < M31) (REST : Command) (r1 : PRM) (fu : Nat)
    (hR : pexecM mv fu REST (gS P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w])
      (VX H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) = some r1) :
    ∃ rr : PRM, pexecM mv fu (.sequence (.primitive (dE mv.nv)) (.sequence (.primitive (LowlinkProg.dW mv.nv))
        (.sequence (.primitive (sIt1 mv.nv)) REST))) (gS P [ci n, ci cnt, ci r, ci sp, ci v]) (VX H T x) = some rr ∧
      rr.ps = r1.ps ∧ rr.vv = r1.vv ∧ rr.ret = r1.ret ∧ rr.cost ≤ r1.cost + 150 ∧ rr.need ≤ max (P.length + 80) r1.need ∧
      rr.wk ≤ r1.wk + 1 := by
  have hvM : v < M31 := by omega
  have heM : e < M31 := by omega
  have hwM : w < M31 := by omega
  -- int e = it[v]
  have hIv : (VX H T x 6)[v]? = some (x.Il.getD v 0) := by
    rw [VX_6]; exact intList_get x.Il v (by rw [hI]; exact hvn)
  have vE := d_rdv mv (VX H T x) P [ci n, ci cnt, ci r, ci sp, ci v] (k := 6) (j := 4) (x := v) (by omega)
    (hty 6 (by omega)) rfl hvM _ hIv (rd_valid vI (by rw [hI]; exact hvn))
  rw [he] at vE
  have dE' := gSM_decl mv P [ci n, ci cnt, ci r, ci sp, ci v] (VX H T x) i32 _ _ _ vE (conv_signed i32 rfl rfl _ (i32v e heM))
  have q1 := (pexecM_prim mv fu (dE mv.nv) _ _).trans dE'
  -- int w = target[e]
  have hTe : (VX H T x 1)[e]? = some ((T.getD e 0 : Nat) : Int) := by
    rw [VX_1]; exact vec_getM T e heT
  have vW := d_rdv mv (VX H T x) P [ci n, ci cnt, ci r, ci sp, ci v, ci e] (k := 1) (j := 5) (x := e) (by omega)
    (hty 1 (by omega)) rfl heM _ hTe (i32v _ (by omega))
  rw [hwn] at vW
  have dW' := gSM_decl mv P [ci n, ci cnt, ci r, ci sp, ci v, ci e] (VX H T x) i32 _ _ _ vW (conv_signed i32 rfl rfl _ (i32v w hwM))
  have q2 := (pexecM_prim mv fu (LowlinkProg.dW mv.nv) _ _).trans dW'
  -- it[v] = e + 1
  have s3 := step_write mv fu P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (VX H T x) 6 4 (.binary i32 .add (vr mv.nv 5) one)
    (by omega) (hty 6 (by omega)) (idx := v) rfl hvM ((e + 1 : Nat) : Int) (by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact add1_den _ _ e (ev_cell mv P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (j := 5) rfl heM) he1)
    (by rw [VX_6, hI]; exact hvn) (i32v _ he1)
  rw [VX_6, VX_w6] at s3
  have t3 := seqM_some s3 rfl hR
  have t2 := seqM_some q2 rfl t3
  have t1 := seqM_some q1 rfl t2
  refine ⟨_, t1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    omega
  · simp
    omega


/-- The arrays after `THENS`. -/
def thenL (H : List Nat) (x : XS) (cnt sp v e w : Nat) : XS :=
  if x.Ol.getD w 0 < 0 then pushL H { x with Il := x.Il.set v ((e + 1 : Nat) : Int) } cnt sp v w
  else backL { x with Il := x.Il.set v ((e + 1 : Nat) : Int) } v w

theorem thens_exec (mv : MV) (hnv : mv.nv = 8) (hty : ∀ k, k < 8 → mv.ty k = i32) (H T : List Nat) (x : XS) {n : Nat}
    (hO : x.Ol.length = n) (hL : x.Ll.length = n) (hP : x.Pl.length = n) (hI : x.Il.length = n) (hK : x.Kl.length = n)
    (vO : ∀ y ∈ x.Ol, i32.valid y = true) (vL : ∀ y ∈ x.Ll, i32.valid y = true) (vP : ∀ y ∈ x.Pl, i32.valid y = true)
    (vI : ∀ y ∈ x.Il, i32.valid y = true) (hHl : H.length = n + 1) (P : List Cell) (cnt r sp v e w : Nat)
    (hn : n < M31) (hn1 : n + 1 < M31) (hcnt : cnt < M31) (hsp : sp < M31)
    (hpush : x.Ol.getD w 0 < 0 → cnt < n ∧ sp < n) (hvn : v < n) (hr : r < M31)
    (he : x.Il.getD v 0 = (e : Int)) (heT : e < T.length) (hTM : T.length < M31) (hwn : T.getD e 0 = w) (hwl : w < n)
    (he1 : e + 1 < M31) (hhd : H.getD w 0 < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (THENS mv.nv) (gS P [ci n, ci cnt, ci r, ci sp, ci v]) (VX H T x) = some rr ∧
      rr.ret = none ∧
      rr.ps = gS P [ci n, ci (if x.Ol.getD w 0 < 0 then cnt + 1 else cnt), ci r,
        ci (if x.Ol.getD w 0 < 0 then sp + 1 else sp), ci v, ci e, ci w] ∧
      rr.vv = VX H T (thenL H x cnt sp v e w) ∧ rr.cost ≤ 800 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 7 := by
  have hcM : cnt < M31 := hcnt
  have hsM : sp < M31 := hsp
  have hwM : w < M31 := by omega
  have hOw : (VX H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) } 2)[w]? = some (x.Ol.getD w 0) := by
    rw [VX_2]; exact intList_get x.Ol w (by rw [hO]; exact hwl)
  have dOw := d_rdv mv (VX H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) P
    [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (k := 2) (j := 6) (x := w) (by omega) (hty 2 (by omega)) rfl hwM _ hOw
    (rd_valid vO (by rw [hO]; exact hwl))
  have hc := d_binb mv (VX H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) P
    [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w] (op := .lt) (a := rdv mv.nv 2 6) (b := lit0) rfl dOw (d_zero mv _ P _)
  rw [bt_lt] at hc
  by_cases hnew : x.Ol.getD w 0 < 0
  · rw [if_pos hnew] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := pushT_exec mv hnv hty H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }
      (n := n) hO hL hP (by simp [hI]) hK hHl P cnt r sp v e w hn hn1 (hpush hnew).1 (hpush hnew).2 hvn hwl hhd fu
    have br := pexecM_branch_true mv fu (cNew mv.nv) (PUSHT mv.nv) (BACKE mv.nv) _ _ 1 hc (by decide) _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    obtain ⟨rS, hS, hSps, hSvv, hSret, hScost, hSneed, hSwk⟩ : ∃ rS : PRM, pexecM mv fu (.sequence (.branch (cNew mv.nv)
        (PUSHT mv.nv) (BACKE mv.nv)) Sk) (gS P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w])
        (VX H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) = some rS ∧ rS.ps = r1.ps ∧ rS.vv = r1.vv ∧
        rS.ret = none ∧ rS.cost ≤ r1.cost + 20 ∧ rS.need ≤ P.length + 80 ∧ rS.wk ≤ r1.wk :=
      ⟨_, s2, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes],
        by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1] at n1 ⊢; omega, by simp⟩
    obtain ⟨rr, hrr, hps, hvv, hret, hcost, hneed, hwk⟩ := thens_prefix mv hnv hty H T x hI vI P cnt r sp v e w hn hvn hcM
      hr hsM he heT hTM hwn hwl he1 _ rS fu hS
    refine ⟨rr, hrr, by rw [hret, hSret], ?_, ?_, ?_, ?_, ?_⟩
    · rw [hps, hSps, if_pos hnew, if_pos hnew]; exact ps1
    · rw [hvv, hSvv, vv1]
      unfold thenL
      rw [if_pos hnew]
    · omega
    · omega
    · omega
  · rw [if_neg hnew] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := backE_exec mv hnv hty H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }
      (n := n) hO hL hP vO vL vP P cnt r sp v e w hvn hwl hn fu
    have br := pexecM_branch_false mv fu (cNew mv.nv) (PUSHT mv.nv) (BACKE mv.nv) _ _ hc _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    obtain ⟨rS, hS, hSps, hSvv, hSret, hScost, hSneed, hSwk⟩ : ∃ rS : PRM, pexecM mv fu (.sequence (.branch (cNew mv.nv)
        (PUSHT mv.nv) (BACKE mv.nv)) Sk) (gS P [ci n, ci cnt, ci r, ci sp, ci v, ci e, ci w])
        (VX H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) = some rS ∧ rS.ps = r1.ps ∧ rS.vv = r1.vv ∧
        rS.ret = none ∧ rS.cost ≤ r1.cost + 20 ∧ rS.need ≤ P.length + 80 ∧ rS.wk ≤ r1.wk :=
      ⟨_, s2, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes],
        by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1] at n1 ⊢; omega, by simp⟩
    obtain ⟨rr, hrr, hps, hvv, hret, hcost, hneed, hwk⟩ := thens_prefix mv hnv hty H T x hI vI P cnt r sp v e w hn hvn hcM
      hr hsM he heT hTM hwn hwl he1 _ rS fu hS
    refine ⟨rr, hrr, by rw [hret, hSret], ?_, ?_, ?_, ?_, ?_⟩
    · rw [hps, hSps, if_neg hnew, if_neg hnew]; exact ps1
    · rw [hvv, hSvv, vv1]
      unfold thenL
      rw [if_neg hnew]
    · omega
    · omega
    · omega

end Proofs.LowlinkExec3
