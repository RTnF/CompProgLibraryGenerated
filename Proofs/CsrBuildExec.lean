import Proofs.CsrBuildProg
import Proofs.CsrBuildMath
import Proofs.LowlinkExec3

namespace Proofs.CsrBuildExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.DoublingNested (i32 u64)
open Proofs.PowModStep (Sk)
open Proofs.BellmanFordExec (M31 rdM_val vec_getM vdenM_binary)
open Proofs.VectorSumCall (conv_signed)
open Proofs.PrefixSumsCall Proofs.IntSim Proofs.QuotientSearch
open Proofs.DijkstraOldScan
open Proofs.LowlinkExec Proofs.LowlinkExec2 Proofs.LowlinkExec3
open Proofs.CsrBuildMath
open Proofs.LowerBoundIndexCall (validN)

structure XB where
  Hd : List Int
  Tg : List Int
  Ps : List Int

/-- The vectors of `csr_build`: `from`, `to` (read-only), `head`, `target`, `pos`. -/
def VB (Fl Tl : List Nat) (x : XB) : Nat → List Int := fun k =>
  if k = 0 then Fl.map (fun a : Nat => (a : Int)) else if k = 1 then Tl.map (fun a : Nat => (a : Int))
  else if k = 2 then x.Hd else if k = 3 then x.Tg else if k = 4 then x.Ps else []

theorem VB_0 (Fl Tl x) : VB Fl Tl x 0 = Fl.map (fun a : Nat => (a : Int)) := by simp [VB]
theorem VB_1 (Fl Tl x) : VB Fl Tl x 1 = Tl.map (fun a : Nat => (a : Int)) := by simp [VB]
theorem VB_2 (Fl Tl x) : VB Fl Tl x 2 = x.Hd := by simp [VB]
theorem VB_3 (Fl Tl x) : VB Fl Tl x 3 = x.Tg := by simp [VB]
theorem VB_4 (Fl Tl x) : VB Fl Tl x 4 = x.Ps := by simp [VB]
theorem VB_w2 (Fl Tl x L') : Proofs.MultiVec.upd (VB Fl Tl x) 2 L' = VB Fl Tl { x with Hd := L' } := by
  funext j; simp only [Proofs.MultiVec.upd, VB]; split_ifs <;> simp_all
theorem VB_w3 (Fl Tl x L') : Proofs.MultiVec.upd (VB Fl Tl x) 3 L' = VB Fl Tl { x with Tg := L' } := by
  funext j; simp only [Proofs.MultiVec.upd, VB]; split_ifs <;> simp_all
theorem VB_w4 (Fl Tl x L') : Proofs.MultiVec.upd (VB Fl Tl x) 4 L' = VB Fl Tl { x with Ps := L' } := by
  funext j; simp only [Proofs.MultiVec.upd, VB]; split_ifs <;> simp_all


/-- Loop 1: `int f = from[i]; head[f + 1] = head[f + 1] + 1;` -/
theorem b1_body (mv : MV) (hnv : mv.nv = 5) (hty : ∀ k, k < 5 → mv.ty k = i32) (Fl Tl : List Nat) (x : XB)
    (P : List Cell) (n m i : Nat) (hn1 : n + 1 < M31) (hm : m < M31) (hi : i < Fl.length) (hFl : Fl.length = m)
    (hf : Fl.getD i 0 < n) (hHd : x.Hd.length = n + 1) (vHd : ∀ y ∈ x.Hd, i32.valid y = true)
    (hinc : i32.valid (x.Hd.getD (Fl.getD i 0 + 1) 0 + 1) = true) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Proofs.CsrBuildProg.B1 mv.nv) (gS P [ci n, ci m, ci i]) (VB Fl Tl x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci m, ci i, ci (Fl.getD i 0)] ∧
      rr.vv = VB Fl Tl { x with Hd := x.Hd.set (Fl.getD i 0 + 1) (x.Hd.getD (Fl.getD i 0 + 1) 0 + 1) } ∧
      rr.cost ≤ 300 ∧ rr.need ≤ P.length + 60 ∧ rr.wk ≤ 1 := by
  generalize hfd : Fl.getD i 0 = f at *
  have hiM : i < M31 := by omega
  have hfM : f < M31 := by omega
  have hf1 : f + 1 < M31 := by omega
  have hFi : (VB Fl Tl x 0)[i]? = some ((Fl.getD i 0 : Nat) : Int) := by
    rw [VB_0]; exact vec_getM Fl i hi
  rw [hfd] at hFi
  have vE := d_rdv mv (VB Fl Tl x) P [ci n, ci m, ci i] (k := 0) (j := 2) (x := i) (by omega) (hty 0 (by omega)) rfl hiM _ hFi
    (i32v _ hfM)
  have dF := gSM_decl mv P [ci n, ci m, ci i] (VB Fl Tl x) i32 _ _ _ vE (conv_signed i32 rfl rfl _ (i32v _ hfM))
  have q1 := (pexecM_prim mv fu (Proofs.CsrBuildProg.dF mv.nv) _ _).trans dF
  have hidx : (Proofs.CsrBuildProg.idxF1 mv.nv).denote (penvN mv.nv (gS P [ci n, ci m, ci i, ci f])) = some ((f + 1 : Nat) : Int) :=
    den_cast_u64 _ _ (f + 1) (add1_den _ (mv.nv + 3) f (ev_cell mv P [ci n, ci m, ci i, ci f] (j := 3) rfl hfM) hf1) hf1
  have hp : vdenM mv (VB Fl Tl x) (penvN mv.nv (gS P [ci n, ci m, ci i, ci f])) (Proofs.CsrBuildProg.idxF1 mv.nv) =
      some ((f + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact hidx
  have hHy : (VB Fl Tl x 2)[f + 1]? = some (x.Hd.getD (f + 1) 0) := by
    rw [VB_2]; exact intList_get x.Hd (f + 1) (by omega)
  have ha := rdM_val mv (VB Fl Tl x) (penvN mv.nv (gS P [ci n, ci m, ci i, ci f])) 2 (by omega) i32 (hty 2 (by omega)).symm
    (Proofs.CsrBuildProg.idxF1 mv.nv) rfl rfl (f + 1) hidx _ hHy (by rw [hty 2 (by omega)]; exact rd_valid vHd (by omega))
  have hx := d_add1I mv (VB Fl Tl x) P [ci n, ci m, ci i, ci f] (a := .read i32 (.local 2) (Proofs.CsrBuildProg.idxF1 mv.nv))
    rfl ha hinc
  have wr := pstmtM_write_ok mv (gS P [ci n, ci m, ci i, ci f]) (VB Fl Tl x) 2 (by omega) (Proofs.CsrBuildProg.idxF1 mv.nv)
    (.binary i32 .add (.read i32 (.local 2) (Proofs.CsrBuildProg.idxF1 mv.nv)) Proofs.CsrBuildProg.one) _ (f + 1) hx hp
    (by rw [VB_2]; omega) (by rw [hty 2 (by omega)]; exact hinc)
  rw [hty 2 (by omega), VB_2, VB_w2] at wr
  have a1 := (pexecM_prim mv fu (Proofs.CsrBuildProg.wH1 mv.nv) _ _).trans wr
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
  have a3 := seqM_some q1 rfl a2
  refine ⟨_, a3, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [Proofs.CsrBuildProg.dF, Proofs.CsrBuildProg.wH1, Proofs.CsrBuildProg.idxF1, Proofs.CsrBuildProg.one,
      Proofs.CsrBuildProg.vr, Proofs.CsrBuildProg.rdv, Proofs.CsrBuildProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes]
  · simp [Proofs.CsrBuildProg.dF, Proofs.CsrBuildProg.wH1, Proofs.CsrBuildProg.idxF1, Proofs.CsrBuildProg.one,
      Proofs.CsrBuildProg.vr, Proofs.CsrBuildProg.rdv, Proofs.CsrBuildProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes, gS_size]
  · simp


/-- Loop 2: `head[v + 1] = head[v + 1] + head[v];` -/
theorem b2_body (mv : MV) (hnv : mv.nv = 5) (hty : ∀ k, k < 5 → mv.ty k = i32) (Fl Tl : List Nat) (x : XB)
    (P : List Cell) (n m v : Nat) (hn1 : n + 1 < M31) (hm : m < M31) (hv : v < n) (hHd : x.Hd.length = n + 1)
    (vHd : ∀ y ∈ x.Hd, i32.valid y = true) (hsum : i32.valid (x.Hd.getD (v + 1) 0 + x.Hd.getD v 0) = true) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Proofs.CsrBuildProg.B2 mv.nv) (gS P [ci n, ci m, ci v]) (VB Fl Tl x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci m, ci v] ∧
      rr.vv = VB Fl Tl { x with Hd := x.Hd.set (v + 1) (x.Hd.getD (v + 1) 0 + x.Hd.getD v 0) } ∧
      rr.cost ≤ 300 ∧ rr.need ≤ P.length + 60 ∧ rr.wk ≤ 1 := by
  have hvM : v < M31 := by omega
  have hv1 : v + 1 < M31 := by omega
  have hidx : (Proofs.CsrBuildProg.idxV1 mv.nv).denote (penvN mv.nv (gS P [ci n, ci m, ci v])) = some ((v + 1 : Nat) : Int) :=
    den_cast_u64 _ _ (v + 1) (add1_den _ (mv.nv + 2) v (ev_cell mv P [ci n, ci m, ci v] (j := 2) rfl hvM) hv1) hv1
  have hp : vdenM mv (VB Fl Tl x) (penvN mv.nv (gS P [ci n, ci m, ci v])) (Proofs.CsrBuildProg.idxV1 mv.nv) =
      some ((v + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact hidx
  have hHy : (VB Fl Tl x 2)[v + 1]? = some (x.Hd.getD (v + 1) 0) := by
    rw [VB_2]; exact intList_get x.Hd (v + 1) (by omega)
  have ha := rdM_val mv (VB Fl Tl x) (penvN mv.nv (gS P [ci n, ci m, ci v])) 2 (by omega) i32 (hty 2 (by omega)).symm
    (Proofs.CsrBuildProg.idxV1 mv.nv) rfl rfl (v + 1) hidx _ hHy
    (by rw [hty 2 (by omega)]; exact rd_valid vHd (by omega))
  have hHv : (VB Fl Tl x 2)[v]? = some (x.Hd.getD v 0) := by
    rw [VB_2]; exact intList_get x.Hd v (by omega)
  have hb := d_rdv mv (VB Fl Tl x) P [ci n, ci m, ci v] (k := 2) (j := 2) (x := v) (by omega) (hty 2 (by omega)) rfl hvM _ hHv
    (rd_valid vHd (by omega))
  have hx : vdenM mv (VB Fl Tl x) (penvN mv.nv (gS P [ci n, ci m, ci v]))
      (.binary i32 .add (.read i32 (.local 2) (Proofs.CsrBuildProg.idxV1 mv.nv)) (Proofs.CsrBuildProg.rdv mv.nv 2 2)) =
      some (x.Hd.getD (v + 1) 0 + x.Hd.getD v 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, ha, Option.bind_some, hb, Option.bind_some]
    exact conv_signed i32 rfl rfl _ hsum
  have wr := pstmtM_write_ok mv (gS P [ci n, ci m, ci v]) (VB Fl Tl x) 2 (by omega) (Proofs.CsrBuildProg.idxV1 mv.nv)
    (.binary i32 .add (.read i32 (.local 2) (Proofs.CsrBuildProg.idxV1 mv.nv)) (Proofs.CsrBuildProg.rdv mv.nv 2 2)) _ (v + 1)
    hx hp (by rw [VB_2]; omega) (by rw [hty 2 (by omega)]; exact hsum)
  rw [hty 2 (by omega), VB_2, VB_w2] at wr
  have a1 := (pexecM_prim mv fu (Proofs.CsrBuildProg.wH2 mv.nv) _ _).trans wr
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, a2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [Proofs.CsrBuildProg.wH2, Proofs.CsrBuildProg.idxV1, Proofs.CsrBuildProg.one,
      Proofs.CsrBuildProg.vr, Proofs.CsrBuildProg.rdv, Proofs.CsrBuildProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes]
  · simp [Proofs.CsrBuildProg.wH2, Proofs.CsrBuildProg.idxV1, Proofs.CsrBuildProg.one,
      Proofs.CsrBuildProg.vr, Proofs.CsrBuildProg.rdv, Proofs.CsrBuildProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes, gS_size]
  · simp

/-- Loop 3: `pos[v] = head[v];` -/
theorem b3_body (mv : MV) (hnv : mv.nv = 5) (hty : ∀ k, k < 5 → mv.ty k = i32) (Fl Tl : List Nat) (x : XB)
    (P : List Cell) (n m v : Nat) (hn : n < M31) (hm : m < M31) (hv : v < n) (hHd : x.Hd.length = n + 1)
    (hPs : x.Ps.length = n) (vHd : ∀ y ∈ x.Hd, i32.valid y = true) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Proofs.CsrBuildProg.B3 mv.nv) (gS P [ci n, ci m, ci v]) (VB Fl Tl x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci m, ci v] ∧
      rr.vv = VB Fl Tl { x with Ps := x.Ps.set v (x.Hd.getD v 0) } ∧
      rr.cost ≤ 300 ∧ rr.need ≤ P.length + 60 ∧ rr.wk ≤ 1 := by
  have hvM : v < M31 := by omega
  have hHv : (VB Fl Tl x 2)[v]? = some (x.Hd.getD v 0) := by
    rw [VB_2]; exact intList_get x.Hd v (by omega)
  have step := step_write mv fu P [ci n, ci m, ci v] (VB Fl Tl x) 4 2 (Proofs.CsrBuildProg.rdv mv.nv 2 2) (by omega)
    (hty 4 (by omega)) (idx := v) rfl hvM (x.Hd.getD v 0)
    (d_rdv mv (VB Fl Tl x) P [ci n, ci m, ci v] (k := 2) (j := 2) (x := v) (by omega) (hty 2 (by omega)) rfl hvM _ hHv
      (rd_valid vHd (by omega)))
    (by rw [VB_4]; omega) (rd_valid vHd (by omega))
  rw [VB_4, VB_w4] at step
  have a2 := seqM_some step rfl (pexecM_skip mv fu _ _)
  refine ⟨_, a2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [Proofs.CsrBuildProg.vr, Proofs.CsrBuildProg.rdv, Proofs.CsrBuildProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes]
  · simp [Proofs.CsrBuildProg.vr, Proofs.CsrBuildProg.rdv, Proofs.CsrBuildProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes, gS_size]
  · simp


/-- The arrays after one round of the fourth loop. -/
def b4X (f p t : Nat) (x : XB) : XB :=
  { Hd := x.Hd
    Tg := x.Tg.set p (t : Int)
    Ps := x.Ps.set f ((p + 1 : Nat) : Int) }

/-- Loop 4: `int f = from[i]; int p = pos[f]; target[p] = to[i]; pos[f] = p + 1;` -/
theorem b4_body (mv : MV) (hnv : mv.nv = 5) (hty : ∀ k, k < 5 → mv.ty k = i32) (Fl Tl : List Nat) (x : XB)
    (P : List Cell) (n m i p : Nat) (hn : n < M31) (hm : m < M31) (hi : i < Fl.length) (hFl : Fl.length = m)
    (hTl : Tl.length = m) (hf : Fl.getD i 0 < n) (hPs : x.Ps.length = n) (hTg : x.Tg.length = m)
    (hp : x.Ps.getD (Fl.getD i 0) 0 = (p : Int)) (hpm : p < m) (hTv : Tl.getD i 0 < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Proofs.CsrBuildProg.B4 mv.nv) (gS P [ci n, ci m, ci i]) (VB Fl Tl x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci m, ci i, ci (Fl.getD i 0), ci p] ∧
      rr.vv = VB Fl Tl (b4X (Fl.getD i 0) p (Tl.getD i 0) x) ∧
      rr.cost ≤ 400 ∧ rr.need ≤ P.length + 60 ∧ rr.wk ≤ 2 := by
  generalize hfd : Fl.getD i 0 = f at *
  have hiM : i < M31 := by omega
  have hfM : f < M31 := by omega
  have hpM : p < M31 := by omega
  have hp1 : p + 1 < M31 := by omega
  -- int f = from[i]
  have hFi : (VB Fl Tl x 0)[i]? = some ((Fl.getD i 0 : Nat) : Int) := by
    rw [VB_0]; exact vec_getM Fl i hi
  rw [hfd] at hFi
  have vE := d_rdv mv (VB Fl Tl x) P [ci n, ci m, ci i] (k := 0) (j := 2) (x := i) (by omega) (hty 0 (by omega)) rfl hiM _ hFi
    (i32v _ hfM)
  have dF := gSM_decl mv P [ci n, ci m, ci i] (VB Fl Tl x) i32 _ _ _ vE (conv_signed i32 rfl rfl _ (i32v _ hfM))
  have q1 := (pexecM_prim mv fu (Proofs.CsrBuildProg.dF mv.nv) _ _).trans dF
  -- int p = pos[f]
  have hPy : (VB Fl Tl x 4)[f]? = some (x.Ps.getD f 0) := by
    rw [VB_4]; exact intList_get x.Ps f (by omega)
  rw [hp] at hPy
  have vP := d_rdv mv (VB Fl Tl x) P [ci n, ci m, ci i, ci f] (k := 4) (j := 3) (x := f) (by omega) (hty 4 (by omega)) rfl hfM _ hPy
    (i32v _ hpM)
  have dP := gSM_decl mv P [ci n, ci m, ci i, ci f] (VB Fl Tl x) i32 _ _ _ vP (conv_signed i32 rfl rfl _ (i32v _ hpM))
  have q2 := (pexecM_prim mv fu (Proofs.CsrBuildProg.dP mv.nv) _ _).trans dP
  -- target[p] = to[i]
  have hTy : (VB Fl Tl x 1)[i]? = some ((Tl.getD i 0 : Nat) : Int) := by
    rw [VB_1]; exact vec_getM Tl i (by omega)
  have s3 := step_write mv fu P [ci n, ci m, ci i, ci f, ci p] (VB Fl Tl x) 3 4 (Proofs.CsrBuildProg.rdv mv.nv 1 2) (by omega)
    (hty 3 (by omega)) (idx := p) rfl hpM ((Tl.getD i 0 : Nat) : Int)
    (d_rdv mv (VB Fl Tl x) P [ci n, ci m, ci i, ci f, ci p] (k := 1) (j := 2) (x := i) (by omega) (hty 1 (by omega)) rfl hiM _ hTy
      (i32v _ hTv))
    (by rw [VB_3]; omega) (i32v _ hTv)
  rw [VB_3, VB_w3] at s3
  obtain ⟨x1, hx1⟩ : ∃ x1 : XB, x1 = { x with Tg := x.Tg.set p ((Tl.getD i 0 : Nat) : Int) } := ⟨_, rfl⟩
  rw [← hx1] at s3
  -- pos[f] = p + 1
  have s4 := step_write mv fu P [ci n, ci m, ci i, ci f, ci p] (VB Fl Tl x1) 4 3
    (.binary i32 .add (Proofs.CsrBuildProg.vr mv.nv 4) Proofs.CsrBuildProg.one) (by omega) (hty 4 (by omega)) (idx := f) rfl hfM
    ((p + 1 : Nat) : Int) (by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact add1_den _ _ p (ev_cell mv P _ (j := 4) rfl hpM) hp1)
    (by rw [VB_4, hx1]; show f < x.Ps.length; omega) (i32v _ hp1)
  rw [VB_4, VB_w4] at s4
  have t4 := seqM_some s4 rfl (pexecM_skip mv fu _ _)
  have t3 := seqM_some s3 rfl t4
  have t2 := seqM_some q2 rfl t3
  have t1 := seqM_some q1 rfl t2
  refine ⟨_, t1, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hx1]; rfl
  · simp [Proofs.CsrBuildProg.dF, Proofs.CsrBuildProg.dP, Proofs.CsrBuildProg.wT, Proofs.CsrBuildProg.wP4, Proofs.CsrBuildProg.one,
      Proofs.CsrBuildProg.vr, Proofs.CsrBuildProg.rdv, Proofs.CsrBuildProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes]
  · simp [Proofs.CsrBuildProg.dF, Proofs.CsrBuildProg.dP, Proofs.CsrBuildProg.wT, Proofs.CsrBuildProg.wP4, Proofs.CsrBuildProg.one,
      Proofs.CsrBuildProg.vr, Proofs.CsrBuildProg.rdv, Proofs.CsrBuildProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes, gS_size]
  · simp


section Loops
variable (mv : MV) (hnv : mv.nv = 5) (hty : ∀ k, k < 5 → mv.ty k = i32) (Fl Tl : List Nat) (P : List Cell) (n m : Nat)
include hnv hty

/-- The loop `for (i = 0; i < m; i++) { f = from[i]; head[f + 1]++; }` -/
theorem loop1 (hn1 : n + 1 < M31) (hm : m < M31) (hm2 : m + 1 < M31) (hFl : Fl.length = m)
    (hF : ∀ j, j < m → Fl.getD j 0 < n) (Tg Ps Hd0 : List Int) (hHd : Hd0.length = n + 1) (hz : ∀ y ∈ Hd0, y = 0)
    (fu : Nat) (hfu : m + 1 ≤ fu) :
    ∃ (res : PRM) (Hd : List Int), pexecM mv fu (forStmtB mv.nv 2 1 (Proofs.CsrBuildProg.B1 mv.nv)) (gS P [ci n, ci m])
        (VB Fl Tl ⟨Hd0, Tg, Ps⟩) = some res ∧ res.ret = none ∧ res.ps = gS P [ci n, ci m] ∧ res.vv = VB Fl Tl ⟨Hd, Tg, Ps⟩ ∧
      Hd.length = n + 1 ∧ (∀ y ∈ Hd, i32.valid y = true) ∧
      (∀ v, Hd.getD v 0 = if 1 ≤ v ∧ v ≤ n then ((cnt (fun j => Fl.getD j 0) (v - 1) m : Nat) : Int) else 0) ∧
      res.cost ≤ 320 * m + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ m := by
  have hnv' := hnv
  have hmM : m < M31 := hm
  obtain ⟨res, C2, hres, hps, hC2, hIn, hret, hcost, hneed, hwk⟩ := for_stmt_runB mv P 2 1 m (by omega)
    (by unfold M31 at hm2; omega) (Proofs.CsrBuildProg.B1 mv.nv)
    (fun t vv C => ∃ Hd : List Int, vv = VB Fl Tl ⟨Hd, Tg, Ps⟩ ∧ C = [ci n, ci m] ∧ Hd.length = n + 1 ∧
      (∀ y ∈ Hd, i32.valid y = true) ∧
      (∀ v, Hd.getD v 0 = if 1 ≤ v ∧ v ≤ n then ((cnt (fun j => Fl.getD j 0) (v - 1) t : Nat) : Int) else 0))
    300 60 1 0 (by omega)
    (by
      intro t vv C fu' ht hCp hC0 hI hfu'
      obtain ⟨Hd, rfl, rfl, hlen, hval, hform⟩ := hI
      have hf := hF t ht
      have hHf : Hd.getD (Fl.getD t 0 + 1) 0 = ((cnt (fun j => Fl.getD j 0) (Fl.getD t 0) t : Nat) : Int) := by
        rw [hform]
        rw [if_pos (by omega)]
        simp
      have hcle := cnt_le (fun j => Fl.getD j 0) (Fl.getD t 0) t
      have hinc : i32.valid (Hd.getD (Fl.getD t 0 + 1) 0 + 1) = true := by
        rw [hHf, i32_valid_iff]; unfold M31 at hm; constructor <;> omega
      obtain ⟨rr, h1, ret1, ps1, vv1, c1, n1, w1⟩ := b1_body mv hnv hty Fl Tl ⟨Hd, Tg, Ps⟩ P n m t hn1 hm (by omega) hFl hf
        hlen hval hinc fu'
      refine ⟨rr, [ci (Fl.getD t 0)], [ci n, ci m], h1, ret1, by rw [ps1]; rfl, rfl, rfl, ?_, c1, n1, w1⟩
      refine ⟨_, vv1, rfl, by simp [hlen], Proofs.LowlinkLists.valid_set hval _ hinc, ?_⟩
      intro v
      rw [Proofs.LowlinkLists.getD_set_gen]
      by_cases hv : v = Fl.getD t 0 + 1
      · subst hv
        dsimp only; rw [if_pos ⟨rfl, by omega⟩, hHf]
        rw [if_pos (by omega)]
        have e1 : Fl.getD t 0 + 1 - 1 = Fl.getD t 0 := by omega
        rw [e1, cnt_succ]
        simp
      · rw [if_neg (fun h => hv h.1), hform v]
        by_cases hc : 1 ≤ v ∧ v ≤ n
        · rw [if_pos hc, if_pos hc, cnt_succ]
          have : (fun j => Fl.getD j 0) t ≠ v - 1 := by
            show Fl.getD t 0 ≠ v - 1
            omega
          rw [if_neg this]; simp
        · rw [if_neg hc, if_neg hc])
    (VB Fl Tl ⟨Hd0, Tg, Ps⟩) [ci n, ci m] rfl rfl
    ⟨Hd0, rfl, rfl, hHd, fun y hy => by rw [hz y hy]; decide, fun v => by
      rw [cnt_zero]
      by_cases hc : 1 ≤ v ∧ v ≤ n
      · rw [if_pos hc]
        have : Hd0.getD v 0 = 0 := by
          by_cases hv : v < Hd0.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]
            exact hz _ (List.getElem_mem _)
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
        rw [this]; simp
      · rw [if_neg hc]
        by_cases hv : v < Hd0.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]
          exact hz _ (List.getElem_mem _)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl⟩ fu (by omega)
  obtain ⟨Hd, hvv, hC, hlen, hval, hform⟩ := hIn
  refine ⟨res, Hd, hres, hret, by rw [hps, hC], hvv, hlen, hval, hform, ?_, hneed, ?_⟩
  · omega
  · omega


/-- The loop `for (v = 0; v < n; v++) head[v + 1] += head[v];` -/
theorem loop2 (hn1 : n + 1 < M31) (hm : m < M31)
    (hF : ∀ j, j < m → Fl.getD j 0 < n) (Tg Ps Hd0 : List Int) (hHd : Hd0.length = n + 1)
    (hval0 : ∀ y ∈ Hd0, i32.valid y = true)
    (hform0 : ∀ v, Hd0.getD v 0 = if 1 ≤ v ∧ v ≤ n then ((cnt (fun j => Fl.getD j 0) (v - 1) m : Nat) : Int) else 0)
    (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ (res : PRM) (Hd : List Int), pexecM mv fu (forStmtB mv.nv 2 0 (Proofs.CsrBuildProg.B2 mv.nv)) (gS P [ci n, ci m])
        (VB Fl Tl ⟨Hd0, Tg, Ps⟩) = some res ∧ res.ret = none ∧ res.ps = gS P [ci n, ci m] ∧ res.vv = VB Fl Tl ⟨Hd, Tg, Ps⟩ ∧
      Hd.length = n + 1 ∧ (∀ y ∈ Hd, i32.valid y = true) ∧
      (∀ v, Hd.getD v 0 = if v ≤ n then ((ocnt (fun j => Fl.getD j 0) m v : Nat) : Int) else 0) ∧
      res.cost ≤ 320 * n + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ n := by
  have hn : n < 2147483647 := by unfold M31 at hn1; omega
  obtain ⟨res, C2, hres, hps, hC2, hIn, hret, hcost, hneed, hwk⟩ := for_stmt_runB mv P 2 0 n (by omega)
    hn (Proofs.CsrBuildProg.B2 mv.nv)
    (fun t vv C => ∃ Hd : List Int, vv = VB Fl Tl ⟨Hd, Tg, Ps⟩ ∧ C = [ci n, ci m] ∧ Hd.length = n + 1 ∧
      (∀ y ∈ Hd, i32.valid y = true) ∧
      (∀ v, Hd.getD v 0 = if v ≤ t then ((ocnt (fun j => Fl.getD j 0) m v : Nat) : Int)
        else if v ≤ n then ((cnt (fun j => Fl.getD j 0) (v - 1) m : Nat) : Int) else 0))
    300 60 1 0 (by omega)
    (by
      intro t vv C fu' ht hCp hC0 hI hfu'
      obtain ⟨Hd, rfl, rfl, hlen, hval, hform⟩ := hI
      have h1 : Hd.getD (t + 1) 0 = ((cnt (fun j => Fl.getD j 0) t m : Nat) : Int) := by
        rw [hform, if_neg (by omega), if_pos (by omega)]
        simp
      have h2 : Hd.getD t 0 = ((ocnt (fun j => Fl.getD j 0) m t : Nat) : Int) := by
        rw [hform, if_pos (Nat.le_refl _)]
      have hs : Hd.getD (t + 1) 0 + Hd.getD t 0 = ((ocnt (fun j => Fl.getD j 0) m (t + 1) : Nat) : Int) := by
        rw [h1, h2]; simp only [ocnt]; push_cast; omega
      have hle : ocnt (fun j => Fl.getD j 0) m (t + 1) ≤ m := by
        have := ocnt_mono (fun j => Fl.getD j 0) m (show t + 1 ≤ n by omega)
        have := ocnt_total (fun j => Fl.getD j 0) n m hF
        omega
      have hsum : i32.valid (Hd.getD (t + 1) 0 + Hd.getD t 0) = true := by
        rw [hs, i32_valid_iff]; unfold M31 at hm; constructor <;> omega
      obtain ⟨rr, h3, ret1, ps1, vv1, c1, n1, w1⟩ := b2_body mv hnv hty Fl Tl ⟨Hd, Tg, Ps⟩ P n m t hn1 hm ht hlen hval
        hsum fu'
      refine ⟨rr, [], [ci n, ci m], h3, ret1, by rw [ps1]; rfl, rfl, rfl, ?_, c1, n1, w1⟩
      refine ⟨_, vv1, rfl, by simp [hlen], Proofs.LowlinkLists.valid_set hval _ hsum, ?_⟩
      intro v
      rw [Proofs.LowlinkLists.getD_set_gen]
      by_cases hv : v = t + 1
      · subst hv
        rw [if_pos ⟨rfl, by dsimp only; omega⟩, if_pos (Nat.le_refl _)]
        exact hs
      · rw [if_neg (fun h => hv h.1), hform v]
        by_cases hc : v ≤ t
        · rw [if_pos hc, if_pos (show v ≤ t + 1 by omega)]
        · have h' : ¬ v ≤ t + 1 := by omega
          rw [if_neg hc, if_neg h'])
    (VB Fl Tl ⟨Hd0, Tg, Ps⟩) [ci n, ci m] rfl rfl
    ⟨Hd0, rfl, rfl, hHd, hval0, fun v => by
      by_cases hc : v ≤ 0
      · have hv0 : v = 0 := by omega
        subst hv0
        rw [if_pos hc, hform0 0, if_neg (by omega)]
        simp [ocnt]
      · rw [if_neg hc, hform0 v]
        by_cases hc2 : 1 ≤ v ∧ v ≤ n
        · rw [if_pos hc2, if_pos hc2.2]
        · rw [if_neg hc2]
          by_cases hc3 : v ≤ n
          · exfalso; omega
          · rw [if_neg hc3]⟩ fu (by omega)
  obtain ⟨Hd, hvv, hC, hlen, hval, hform⟩ := hIn
  refine ⟨res, Hd, hres, hret, by rw [hps, hC], hvv, hlen, hval, ?_, ?_, hneed, ?_⟩
  · intro v
    rw [hform v]
    by_cases hc : v ≤ n
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, if_neg hc]
  · omega
  · omega

/-- The loop `for (v = 0; v < n; v++) pos[v] = head[v];` -/
theorem loop3 (hn1 : n + 1 < M31) (hm : m < M31) (Hd Tg Ps0 : List Int) (hHd : Hd.length = n + 1)
    (hval : ∀ y ∈ Hd, i32.valid y = true) (hPs : Ps0.length = n) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ (res : PRM) (Ps : List Int), pexecM mv fu (forStmtB mv.nv 2 0 (Proofs.CsrBuildProg.B3 mv.nv)) (gS P [ci n, ci m])
        (VB Fl Tl ⟨Hd, Tg, Ps0⟩) = some res ∧ res.ret = none ∧ res.ps = gS P [ci n, ci m] ∧ res.vv = VB Fl Tl ⟨Hd, Tg, Ps⟩ ∧
      Ps.length = n ∧ (∀ v, v < n → Ps.getD v 0 = Hd.getD v 0) ∧
      res.cost ≤ 320 * n + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ n := by
  have hn : n < 2147483647 := by unfold M31 at hn1; omega
  obtain ⟨res, C2, hres, hps, hC2, hIn, hret, hcost, hneed, hwk⟩ := for_stmt_runB mv P 2 0 n (by omega)
    hn (Proofs.CsrBuildProg.B3 mv.nv)
    (fun t vv C => ∃ Ps : List Int, vv = VB Fl Tl ⟨Hd, Tg, Ps⟩ ∧ C = [ci n, ci m] ∧ Ps.length = n ∧
      (∀ v, v < t → Ps.getD v 0 = Hd.getD v 0))
    300 60 1 0 (by omega)
    (by
      intro t vv C fu' ht hCp hC0 hI hfu'
      obtain ⟨Ps, rfl, rfl, hlen, hform⟩ := hI
      obtain ⟨rr, h3, ret1, ps1, vv1, c1, n1, w1⟩ := b3_body mv hnv hty Fl Tl ⟨Hd, Tg, Ps⟩ P n m t (by omega) hm ht hHd
        hlen hval fu'
      refine ⟨rr, [], [ci n, ci m], h3, ret1, by rw [ps1]; rfl, rfl, rfl, ?_, c1, n1, w1⟩
      refine ⟨_, vv1, rfl, by simp [hlen], ?_⟩
      intro v hv
      rw [Proofs.LowlinkLists.getD_set_gen]
      by_cases hvt : v = t
      · subst hvt
        rw [if_pos ⟨rfl, by dsimp only; omega⟩]
      · rw [if_neg (fun h => hvt h.1)]
        exact hform v (by omega))
    (VB Fl Tl ⟨Hd, Tg, Ps0⟩) [ci n, ci m] rfl rfl
    ⟨Ps0, rfl, rfl, hPs, fun v hv => absurd hv (by omega)⟩ fu (by omega)
  obtain ⟨Ps, hvv, hC, hlen, hform⟩ := hIn
  refine ⟨res, Ps, hres, hret, by rw [hps, hC], hvv, hlen, hform, ?_, hneed, ?_⟩
  · omega
  · omega

omit hnv hty in
theorem ocnt_step (F : Nat → Nat) (m a : Nat) : ocnt F m (a + 1) = ocnt F m a + cnt F a m := rfl

omit hnv hty in
/-- Two edges with different indices are written to different positions. -/
theorem pos_ne (F : Nat → Nat) (m : Nat) {j t : Nat} (hj : j < t) (htm : t < m) :
    ocnt F m (F j) + cnt F (F j) j ≠ ocnt F m (F t) + cnt F (F t) t := by
  have h1 := cnt_lt F (show j < m by omega)
  have h2 := cnt_lt F htm
  by_cases heq : F j = F t
  · rw [heq]
    have h3 := cnt_succ F (F t) j
    rw [heq, if_pos rfl] at h3
    have h4 := cnt_mono F (F t) (show j + 1 ≤ t by omega)
    omega
  · rcases Nat.lt_or_gt_of_ne heq with h | h
    · have := ocnt_mono F m (show F j + 1 ≤ F t by omega)
      rw [ocnt_step] at this
      omega
    · have := ocnt_mono F m (show F t + 1 ≤ F j by omega)
      rw [ocnt_step] at this
      omega

/-- The loop `for (i = 0; i < m; i++) { f = from[i]; p = pos[f]; target[p] = to[i]; pos[f] = p + 1; }` -/
theorem loop4 (hn1 : n + 1 < M31) (hm : m < M31) (hm2 : m + 1 < M31) (hFl : Fl.length = m) (hTl : Tl.length = m)
    (hF : ∀ j, j < m → Fl.getD j 0 < n) (hT : ∀ j, j < m → Tl.getD j 0 < M31)
    (Hd Tg0 Ps0 : List Int) (hTg : Tg0.length = m) (hPs : Ps0.length = n)
    (hPform : ∀ v, v < n → Ps0.getD v 0 = ((ocnt (fun j => Fl.getD j 0) m v : Nat) : Int))
    (fu : Nat) (hfu : m + 1 ≤ fu) :
    ∃ (res : PRM) (Tg Ps : List Int), pexecM mv fu (forStmtB mv.nv 2 1 (Proofs.CsrBuildProg.B4 mv.nv)) (gS P [ci n, ci m])
        (VB Fl Tl ⟨Hd, Tg0, Ps0⟩) = some res ∧ res.ret = none ∧ res.ps = gS P [ci n, ci m] ∧ res.vv = VB Fl Tl ⟨Hd, Tg, Ps⟩ ∧
      Tg.length = m ∧
      (∀ j, j < m → Tg.getD (ocnt (fun j => Fl.getD j 0) m (Fl.getD j 0) + cnt (fun j => Fl.getD j 0) (Fl.getD j 0) j) 0
        = ((Tl.getD j 0 : Nat) : Int)) ∧
      res.cost ≤ 420 * m + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ 2 * m := by
  have hn : m < 2147483647 := by unfold M31 at hm2; omega
  obtain ⟨res, C2, hres, hps, hC2, hIn, hret, hcost, hneed, hwk⟩ := for_stmt_runB mv P 2 1 m (by omega)
    hn (Proofs.CsrBuildProg.B4 mv.nv)
    (fun t vv C => ∃ Tg Ps : List Int, vv = VB Fl Tl ⟨Hd, Tg, Ps⟩ ∧ C = [ci n, ci m] ∧ Ps.length = n ∧
      Tg.length = m ∧
      (∀ v, v < n → Ps.getD v 0 = ((ocnt (fun j => Fl.getD j 0) m v + cnt (fun j => Fl.getD j 0) v t : Nat) : Int)) ∧
      (∀ j, j < t → Tg.getD (ocnt (fun j => Fl.getD j 0) m (Fl.getD j 0) +
        cnt (fun j => Fl.getD j 0) (Fl.getD j 0) j) 0 = ((Tl.getD j 0 : Nat) : Int)))
    400 60 2 0 (by omega)
    (by
      intro t vv C fu' ht hCp hC0 hI hfu'
      obtain ⟨Tg, Ps, rfl, rfl, hPl, hTgl, hPf, hTf⟩ := hI
      have hf := hF t ht
      have hFt : (fun j => Fl.getD j 0) t = Fl.getD t 0 := rfl
      have hlt := cnt_lt (fun j => Fl.getD j 0) ht
      have hlt' : cnt (fun j => Fl.getD j 0) (Fl.getD t 0) t < cnt (fun j => Fl.getD j 0) (Fl.getD t 0) m := hlt
      have hocm := ocnt_mono (fun j => Fl.getD j 0) m (show Fl.getD t 0 + 1 ≤ n by omega)
      have hocn := ocnt_total (fun j => Fl.getD j 0) n m hF
      rw [ocnt_step] at hocm
      have hpm : ocnt (fun j => Fl.getD j 0) m (Fl.getD t 0) + cnt (fun j => Fl.getD j 0) (Fl.getD t 0) t < m := by omega
      obtain ⟨rr, h3, ret1, ps1, vv1, c1, n1, w1⟩ := b4_body mv hnv hty Fl Tl ⟨Hd, Tg, Ps⟩ P n m t
        (ocnt (fun j => Fl.getD j 0) m (Fl.getD t 0) + cnt (fun j => Fl.getD j 0) (Fl.getD t 0) t)
        (by unfold M31 at hn1 ⊢; omega) hm (by omega) hFl hTl hf hPl hTgl (by rw [hPf _ hf]) hpm (hT t ht) fu'
      refine ⟨rr, [ci (Fl.getD t 0), ci (ocnt (fun j => Fl.getD j 0) m (Fl.getD t 0) +
        cnt (fun j => Fl.getD j 0) (Fl.getD t 0) t)], [ci n, ci m], h3, ret1, by rw [ps1]; rfl, rfl, rfl, ?_, c1, n1, w1⟩
      refine ⟨_, _, vv1, rfl, by simp [b4X, hPl], by simp [b4X, hTgl], ?_, ?_⟩
      · intro v hv
        show (Ps.set (Fl.getD t 0) _).getD v 0 = _
        rw [Proofs.LowlinkLists.getD_set_gen]
        by_cases hvf : v = Fl.getD t 0
        · subst hvf
          rw [if_pos ⟨rfl, by omega⟩, cnt_succ]
          simp only [hFt, if_pos]
          push_cast; omega
        · rw [if_neg (fun h => hvf h.1), hPf v hv, cnt_succ]
          have : (fun j => Fl.getD j 0) t ≠ v := fun h => hvf h.symm
          rw [if_neg this]; simp
      · intro j hj
        show (Tg.set _ _).getD _ 0 = _
        rw [Proofs.LowlinkLists.getD_set_gen]
        by_cases hjt : j = t
        · subst hjt
          rw [if_pos ⟨rfl, by omega⟩]
        · have hne := pos_ne (fun j => Fl.getD j 0) m (show j < t by omega) ht
          rw [if_neg (fun h => hne h.1)]
          exact hTf j (by omega))
    (VB Fl Tl ⟨Hd, Tg0, Ps0⟩) [ci n, ci m] rfl rfl
    ⟨Tg0, Ps0, rfl, rfl, hPs, hTg, fun v hv => by rw [hPform v hv, cnt_zero]; rfl, fun j hj => absurd hj (by omega)⟩
    fu (by omega)
  obtain ⟨Tg, Ps, hvv, hC, hPl, hTgl, hPf, hTf⟩ := hIn
  refine ⟨res, Tg, Ps, hres, hret, by rw [hps, hC], hvv, hTgl, hTf, ?_, hneed, ?_⟩
  · omega
  · omega

omit hnv hty in
theorem size_valC (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (hn : (vv 0).length < 2147483648) :
    vdenM mv vv env (.cast i32 (.size (.integer i32) (.local 0))) = some ((vv 0).length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer i32) (.local 0))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer i32) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer i32) (.local 0)) = some ((vv 0).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨by omega, hty0.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

/-- The whole body of `csr_build`. -/
theorem body_exec (hn1 : n + 1 < M31) (hm : m < M31) (hm2 : m + 1 < M31) (hFl : Fl.length = m) (hTl : Tl.length = m)
    (hF : ∀ j, j < m → Fl.getD j 0 < n) (hT : ∀ j, j < m → Tl.getD j 0 < M31)
    (Hd0 Tg0 Ps0 : List Int) (hHd : Hd0.length = n + 1) (hz : ∀ y ∈ Hd0, y = 0) (hTg : Tg0.length = m)
    (hPs : Ps0.length = n) (fu : Nat) (hfu : n + m + 2 ≤ fu) :
    ∃ (r : PRM) (Hd Tg Ps : List Int), pexecM mv fu (Proofs.CsrBuildProg.progCB mv.nv) (gS P [ci n])
        (VB Fl Tl ⟨Hd0, Tg0, Ps0⟩) = some r ∧ r.ret = none ∧ r.ps = gS P [ci n, ci m] ∧
      r.vv = VB Fl Tl ⟨Hd, Tg, Ps⟩ ∧ Hd.length = n + 1 ∧
      (∀ v, Hd.getD v 0 = if v ≤ n then ((ocnt (fun j => Fl.getD j 0) m v : Nat) : Int) else 0) ∧
      Tg.length = m ∧
      (∀ j, j < m → Tg.getD (ocnt (fun j => Fl.getD j 0) m (Fl.getD j 0) + cnt (fun j => Fl.getD j 0) (Fl.getD j 0) j) 0
        = ((Tl.getD j 0 : Nat) : Int)) ∧
      r.cost ≤ 800 * (n + m) + 400 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 3 * m + 2 * n := by
  have hlen0 : (VB Fl Tl ⟨Hd0, Tg0, Ps0⟩ 0).length = m := by rw [VB_0]; simp [hFl]
  have hsz := size_valC mv hnv (hty 0 (by omega)) (VB Fl Tl ⟨Hd0, Tg0, Ps0⟩) (penvN mv.nv (gS P [ci n]))
    (by rw [hlen0]; exact hm)
  rw [hlen0] at hsz
  have d1 := gSM_decl mv P [ci n] (VB Fl Tl ⟨Hd0, Tg0, Ps0⟩) i32 _ _ _ hsz (conv_signed i32 rfl rfl _ (validN m hm))
  have q1 := (pexecM_prim mv fu (Proofs.CsrBuildProg.dM mv.nv) _ _).trans d1
  obtain ⟨r1, Hd1, e1, ret1, ps1, vv1, hl1, hv1, hf1, c1, n1, w1⟩ := loop1 mv hnv hty Fl Tl P n m hn1 hm hm2 hFl hF Tg0 Ps0 Hd0 hHd hz fu
    (by omega)
  obtain ⟨r2, Hd2, e2, ret2, ps2, vv2, hl2, hv2, hf2, c2, n2, w2⟩ := loop2 mv hnv hty Fl Tl P n m hn1 hm hF Tg0 Ps0 Hd1 hl1 hv1 hf1 fu
    (by omega)
  obtain ⟨r3, Ps3, e3, ret3, ps3, vv3, hl3, hf3, c3, n3, w3⟩ := loop3 mv hnv hty Fl Tl P n m hn1 hm Hd2 Tg0 Ps0 hl2 hv2 hPs fu (by omega)
  obtain ⟨r4, Tg4, Ps4, e4, ret4, ps4, vv4, hl4, hf4, c4, n4, w4⟩ := loop4 mv hnv hty Fl Tl P n m hn1 hm hm2 hFl hTl hF hT Hd2 Tg0 Ps3
    hTg hl3 (fun v hv => by rw [hf3 v hv, hf2 v, if_pos (by omega)]) fu (by omega)
  have q4 := seqM_some e4 ret4 (pexecM_skip mv fu r4.ps r4.vv)
  have q3 := seqM_some e3 ret3 (by rw [ps3, vv3]; exact q4)
  have q2 := seqM_some e2 ret2 (by rw [ps2, vv2]; exact q3)
  have q1' := seqM_some e1 ret1 (by rw [ps1, vv1]; exact q2)
  have q0 := seqM_some q1 rfl q1'
  refine ⟨_, Hd2, Tg4, Ps4, q0, rfl, ?_, vv4, hl2, hf2, hl4, hf4, ?_, ?_, ?_⟩
  · exact ps4
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at c1 c2 c3 c4 ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at n1 n2 n3 n4 ⊢
    have : r4.ps.mem.length + r4.ps.bs.length = P.length + 4 := by rw [ps4]; simp [gS_size]
    omega
  · simp at w1 w2 w3 w4 ⊢; omega

end Loops

end Proofs.CsrBuildExec
