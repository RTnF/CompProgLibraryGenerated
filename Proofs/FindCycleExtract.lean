import Proofs.FindCycleOuter

namespace Proofs.FindCycleExtract
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.DoublingNested (i32 u64)
open Proofs.PowModStep (Sk)
open Proofs.BellmanFordExec (M31 rdM_val vec_getM pexecM_branch_true pexecM_branch_false)
open Proofs.VectorSumCall (conv_signed)
open Proofs.PrefixSumsCall Proofs.IntSim Proofs.QuotientSearch
open Proofs.DijkstraScan
open Proofs.LowlinkExec Proofs.LowlinkExec2 Proofs.LowlinkExec3
open Proofs.FindCycleLists Proofs.FindCycleExec Proofs.FindCycleOk Proofs.FindCycleIter Proofs.FindCycleOuter
open Proofs.FindCycleInv Proofs.FindCycleSpec

/-- The loop `while (stk[j] != fw) j--;` : it stops at the position `j0` of `fw` in the stack. -/
theorem wj_loopF {mv : MV} {n : Nat} (hnv : mv.nv = 6) (hty : ∀ k, k < 6 → mv.ty k = i32) {H T : List Nat} (x : XF)
    {fsp fw j0 : Nat} (F : FoundS n (hdF H) (tgF T) x fsp fw) (hj0 : j0 < fsp) (hfw : x.st.Sk j0 = fw) (P : List Cell)
    (hn : n < M31) (r k : Nat) (hk : k < M31) (hr : r < M31) (hfM : fsp < M31) :
    ∀ (m j : Nat), j = j0 + m → j < fsp → ∀ fu, m + 1 ≤ fu →
      ∃ rr : PRM, pexecM mv fu (Proofs.FindCycleProg.WJ mv.nv) (gS P [ci n, ci fsp, ci fw, ci k, ci j]) (VXF H T x) =
        some rr ∧ rr.ret = none ∧ rr.ps = gS P [ci n, ci fsp, ci fw, ci k, ci j0] ∧ rr.vv = VXF H T x ∧
        rr.cost ≤ 100 * m + 30 ∧ rr.need ≤ P.length + 100 ∧ rr.wk = 0 := by
  have hMn : n < M31 := hn
  have hfwM : fw < M31 := by
    have := F.fnd.lt j0 hj0
    rw [hfw] at this; omega
  have hcond : ∀ j, j < fsp → ∀ cl : List Cell, cl[4]? = some (ci j) → cl[2]? = some (ci fw) →
      vdenM mv (VXF H T x) (penvN mv.nv (gS P cl)) (Proofs.FindCycleProg.cJ mv.nv) =
        some (if x.st.Sk j = fw then 0 else 1) := by
    intro j hj cl hcj hcf
    have hjM : j < M31 := by omega
    have hKj : (VXF H T x 4)[j]? = some (x.Kl.getD j 0) := by
      rw [VXF_4]; exact intList_get x.Kl j (by rw [F.lK]; have := F.fnd.fsp_le; omega)
    have dK := d_rdv mv (VXF H T x) P cl (k := 4) (j := 4) (x := j) (by omega) (hty 4 (by omega)) hcj hjM _ hKj
      (rd_valid F.vK (by rw [F.lK]; have := F.fnd.fsp_le; omega))
    have dF := d_vr mv (VXF H T x) P cl (j := 2) (x := fw) hcf hfwM
    have hc := d_binb mv (VXF H T x) P cl (op := .ne) (a := Proofs.FindCycleProg.rdv mv.nv 4 4)
      (b := Proofs.FindCycleProg.vr mv.nv 2) rfl dK dF
    rw [bt_ne] at hc
    rw [hc, F.kl j hj]
    by_cases h : x.st.Sk j = fw
    · rw [if_pos h, if_neg]
      intro hh; apply hh; rw [h]
    · rw [if_neg h, if_pos]
      intro hh; apply h; exact_mod_cast hh
  intro m
  induction m with
  | zero =>
    intro j hj hjf fu hfu
    have hjj : j = j0 := by omega
    subst hjj
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := hcond j hjf [ci n, ci fsp, ci fw, ci k, ci j] rfl rfl
    rw [hfw, if_pos rfl] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [Proofs.FindCycleProg.cJ, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [gS_size, Proofs.FindCycleProg.cJ, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc,
        vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · rfl
  | succ m ih =>
    intro j hj hjf fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hne : x.st.Sk j ≠ fw := by
      intro h
      have := F.fnd.inj j j0 hjf hj0 (by rw [h, hfw])
      omega
    have hc := hcond j hjf [ci n, ci fsp, ci fw, ci k, ci j] rfl rfl
    rw [if_neg hne] at hc
    have hjM : j < M31 := by omega
    have s1 := step_assign mv (fu' + 1) P [ci n, ci fsp, ci fw, ci k, ci j] (VXF H T x) 4
      (.binary i32 .sub (Proofs.FindCycleProg.vr mv.nv 4) Proofs.FindCycleProg.one) (y := j) rfl hjM (j - 1) (by omega) (by
        rw [vdenM_scalar _ _ _ _ rfl]
        exact sub1_den _ _ j (ev_cell mv P _ (j := 4) rfl hjM) hjM (by omega))
    have t1 := seqM_some s1 rfl (pexecM_skip mv (fu' + 1) _ _)
    have sc := scope_gS mv (fu' + 1) (.sequence (.primitive (Proofs.FindCycleProg.aJd mv.nv)) Sk) P
      [ci n, ci fsp, ci fw, ci k, ci j] [ci n, ci fsp, ci fw, ci k, ci (j - 1)] (VXF H T x) _ rfl t1 rfl
    have t2 := seqM_some sc rfl (pexecM_skip mv (fu' + 1) _ _)
    obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := ih (j - 1) (by omega) (by omega) fu' (by omega)
    rw [pexecM_while, hc]
    have h2' : pexecM mv fu' (Proofs.FindCycleProg.WJ mv.nv) _ _ = some r2 := h2
    simp only [Bind.bind, Option.bind, if_neg (show (1 : Int) ≠ 0 by decide), t2, h2']
    refine ⟨_, rfl, ret2, ps2, vv2, ?_, ?_, ?_⟩
    · simp [Proofs.FindCycleProg.cJ, Proofs.FindCycleProg.aJd, Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr,
        Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [gS_size, Proofs.FindCycleProg.cJ, Proofs.FindCycleProg.aJd, Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr,
        Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp; omega


/-- The copy loop `for (t = 0; t < k; t++) cyc[t] = stk[j + t];`. -/
theorem wc_loopF {mv : MV} {n : Nat} (hnv : mv.nv = 6) (hty : ∀ k, k < 6 → mv.ty k = i32) {H T : List Nat} (x : XF)
    {fsp fw j k : Nat} (hfw : fw < M31) (hn : n < M31) (hjk : j + k ≤ n) (hKl : x.Kl.length = n)
    (vK : ∀ y ∈ x.Kl, i32.valid y = true) (P : List Cell) (r : Nat) :
    ∀ (m t : Nat) (Yl : List Int), t + m = k → Yl.length = n → (∀ y ∈ Yl, i32.valid y = true) →
      (∀ i, i < t → Yl.getD i 0 = x.Kl.getD (j + i) 0) → ∀ fu, m + 1 ≤ fu → fsp < M31 →
      ∃ (rr : PRM) (Yl' : List Int), pexecM mv fu (Proofs.FindCycleProg.WC mv.nv)
          (gS P [ci n, ci fsp, ci fw, ci k, ci j, ci t]) (VXF H T { x with Yl := Yl }) = some rr ∧ rr.ret = none ∧
        rr.ps = gS P [ci n, ci fsp, ci fw, ci k, ci j, ci k] ∧ rr.vv = VXF H T { x with Yl := Yl' } ∧
        Yl'.length = n ∧ (∀ y ∈ Yl', i32.valid y = true) ∧ (∀ i, i < k → Yl'.getD i 0 = x.Kl.getD (j + i) 0) ∧
        rr.cost ≤ 200 * m + 30 ∧ rr.need ≤ P.length + 100 ∧ rr.wk ≤ m := by
  have hkM : k < M31 := by have h := hn; unfold M31 at h ⊢; omega
  have hjM : j < M31 := by have h := hn; unfold M31 at h ⊢; omega
  intro m
  induction m with
  | zero =>
    intro t Yl hm hYl vYl hpre fu hfu hfsp
    have htk : t = k := by omega
    subst htk
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have htM : t < M31 := hkM
    have hc : vdenM mv (VXF H T { x with Yl := Yl }) (penvN mv.nv (gS P [ci n, ci fsp, ci fw, ci t, ci j, ci t]))
        (Proofs.FindCycleProg.cT mv.nv) = some 0 := by
      rw [vdenM_scalar _ _ _ _ rfl]
      show (NExpr.binary bT .lt (.variable i32 (mv.nv + 5)) (.variable i32 (mv.nv + 3))).denote _ = _
      rw [den_binary, den_variable, den_variable, ev_cell mv P _ (j := 5) rfl htM, Option.bind_some,
        ev_cell mv P _ (j := 3) rfl htM, Option.bind_some, bt_lt]
      simp
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, Yl, rfl, rfl, rfl, rfl, hYl, vYl, fun i hi => hpre i hi, ?_, ?_, ?_⟩
    · simp [Proofs.FindCycleProg.cT, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [gS_size, Proofs.FindCycleProg.cT, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp
  | succ m ih =>
    intro t Yl hm hYl vYl hpre fu hfu hfsp
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have htk : t < k := by omega
    have htM : t < M31 := by omega
    have htn : t < n := by omega
    have hc : vdenM mv (VXF H T { x with Yl := Yl }) (penvN mv.nv (gS P [ci n, ci fsp, ci fw, ci k, ci j, ci t]))
        (Proofs.FindCycleProg.cT mv.nv) = some 1 := by
      rw [vdenM_scalar _ _ _ _ rfl]
      show (NExpr.binary bT .lt (.variable i32 (mv.nv + 5)) (.variable i32 (mv.nv + 3))).denote _ = _
      rw [den_binary, den_variable, den_variable, ev_cell mv P _ (j := 5) rfl htM, Option.bind_some,
        ev_cell mv P _ (j := 3) rfl hkM, Option.bind_some, bt_lt]
      simp [htk]
    -- cyc[t] = stk[j + t]
    have hjt : j + t < n := by omega
    have hjtM : j + t < M31 := by have h := hn; unfold M31 at h ⊢; omega
    have hidx : (NExpr.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 4)) (.variable i32 (mv.nv + 5)))).denote
        (penvN mv.nv (gS P [ci n, ci fsp, ci fw, ci k, ci j, ci t])) = some ((j + t : Nat) : Int) :=
      Proofs.DijkstraExec.sumIdx_den _ (mv.nv + 4) (mv.nv + 5) j t (ev_cell mv P _ (j := 4) rfl hjM)
        (ev_cell mv P _ (j := 5) rfl htM) hjtM
    have hKj : (VXF H T { x with Yl := Yl } 4)[j + t]? = some (x.Kl.getD (j + t) 0) := by
      rw [VXF_4]; exact intList_get x.Kl (j + t) (by rw [hKl]; exact hjt)
    have vE : vdenM mv (VXF H T { x with Yl := Yl }) (penvN mv.nv (gS P [ci n, ci fsp, ci fw, ci k, ci j, ci t]))
        (.read i32 (.local 4) (.cast u64 (.binary i32 .add (Proofs.FindCycleProg.vr mv.nv 4) (Proofs.FindCycleProg.vr mv.nv 5)))) =
        some (x.Kl.getD (j + t) 0) :=
      rdM_val mv _ _ 4 (by omega) i32 (hty 4 (by omega)).symm _ rfl rfl (j + t) hidx _ hKj
        (by rw [hty 4 (by omega)]; exact rd_valid vK (by rw [hKl]; exact hjt))
    have s1 := step_write mv (fu' + 1) P [ci n, ci fsp, ci fw, ci k, ci j, ci t] (VXF H T { x with Yl := Yl }) 5 5 _ (by omega)
      (hty 5 (by omega)) (idx := t) rfl htM _ vE (by rw [VXF_5]; show t < Yl.length; omega)
      (rd_valid vK (by rw [hKl]; exact hjt))
    rw [VXF_5, VXF_w5] at s1
    have t1 := seqM_some s1 rfl (pexecM_skip mv (fu' + 1) _ _)
    have sc := scope_gS mv (fu' + 1) (.sequence (.primitive (Proofs.FindCycleProg.wCyc mv.nv)) Sk) P
      [ci n, ci fsp, ci fw, ci k, ci j, ci t] [ci n, ci fsp, ci fw, ci k, ci j, ci t]
      (VXF H T { x with Yl := Yl }) _ rfl t1 rfl
    have ht1 : t + 1 < M31 := by omega
    have s2 := step_assign mv (fu' + 1) P [ci n, ci fsp, ci fw, ci k, ci j, ci t]
      (VXF H T { x with Yl := Yl.set t (x.Kl.getD (j + t) 0) }) 5
      (.binary i32 .add (Proofs.FindCycleProg.vr mv.nv 5) Proofs.FindCycleProg.one) (y := t) rfl htM (t + 1) ht1 (by
        rw [vdenM_scalar _ _ _ _ rfl]
        exact add1_den _ _ t (ev_cell mv P _ (j := 5) rfl htM) ht1)
    have t2 := seqM_some s2 rfl (pexecM_skip mv (fu' + 1) _ _)
    have body := seqM_some sc rfl t2
    have hlenN : (Yl.set t (x.Kl.getD (j + t) 0)).length = n := by simp [hYl]
    have vN : ∀ y ∈ Yl.set t (x.Kl.getD (j + t) 0), i32.valid y = true :=
      Proofs.LowlinkLists.valid_set vYl _ (rd_valid vK (by rw [hKl]; exact hjt))
    have hpre' : ∀ i, i < t + 1 → (Yl.set t (x.Kl.getD (j + t) 0)).getD i 0 = x.Kl.getD (j + i) 0 := by
      intro i hi
      rw [Proofs.LowlinkLists.getD_set_gen]
      by_cases hit : i = t
      · subst hit; rw [if_pos ⟨rfl, by omega⟩]
      · rw [if_neg (fun h => hit h.1)]; exact hpre i (by omega)
    obtain ⟨r2, Yl', h2, ret2, ps2, vv2, hl2, v2, pre2, c2, n2, w2⟩ :=
      ih (t + 1) (Yl.set t (x.Kl.getD (j + t) 0)) (by omega) hlenN vN hpre' fu' (by omega) hfsp
    rw [pexecM_while, hc]
    have h2' : pexecM mv fu' (Proofs.FindCycleProg.WC mv.nv)
        (gS P ([ci n, ci fsp, ci fw, ci k, ci j, ci t].set 5 (ci (t + 1))))
        (VXF H T { x with Yl := Yl.set t (x.Kl.getD (j + t) 0) }) = some r2 := h2
    simp only [Bind.bind, Option.bind, if_neg (show (1 : Int) ≠ 0 by decide), body, h2']
    refine ⟨_, Yl', rfl, ret2, ps2, vv2, hl2, v2, pre2, ?_, ?_, ?_⟩
    · simp [Proofs.FindCycleProg.cT, Proofs.FindCycleProg.wCyc, Proofs.FindCycleProg.aT1, Proofs.FindCycleProg.one,
        Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
        Container.nodes]
      omega
    · simp [gS_size, Proofs.FindCycleProg.cT, Proofs.FindCycleProg.wCyc, Proofs.FindCycleProg.aT1, Proofs.FindCycleProg.one,
        Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
        Container.nodes]
      omega
    · simp
      omega


set_option maxHeartbeats 8000000 in
/-- The extraction of the cycle. -/
theorem ext_execF {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (x : XF) {fsp fw : Nat}
    (F : FoundS n (hdF H) (tgF T) x fsp fw) (P : List Cell) (hfw : fw < M31) (fu : Nat) (hfu : n + 3 ≤ fu) :
    ∃ (rr : PRM) (j0 : Nat) (Yl' : List Int), pexecM mv fu (Proofs.FindCycleProg.EXT mv.nv)
        (gS P [ci n, ci fsp, ci fw, ci 0]) (VXF H T x) = some rr ∧ rr.ret = none ∧ j0 < fsp ∧ x.st.Sk j0 = fw ∧
      rr.ps = gS P [ci n, ci fsp, ci fw, ci (fsp - j0)] ∧ rr.vv = VXF H T { x with Yl := Yl' } ∧
      Yl'.length = n ∧ (∀ y ∈ Yl', i32.valid y = true) ∧ (∀ i, i < fsp - j0 → Yl'.getD i 0 = x.Kl.getD (j0 + i) 0) ∧
      rr.cost ≤ 400 * n + 300 ∧ rr.need ≤ P.length + 100 ∧ rr.wk ≤ n := by
  have hnv := E.hnv
  have hn : n < M31 := by have := E.hn1; omega
  have hfn := F.fnd.fsp_le
  have hfsp0 := F.fnd.pos
  obtain ⟨j0, hj0, hjw⟩ := F.fnd.mem
  have hfM : fsp < M31 := by omega
  have hM0 : (0 : Nat) < M31 := by unfold M31; omega
  -- int j = fsp - 1
  have dJ := gSM_decl mv P [ci n, ci fsp, ci fw, ci 0] (VXF H T x) i32 (.binary i32 .sub (Proofs.FindCycleProg.vr mv.nv 1) Proofs.FindCycleProg.one) ((fsp - 1 : Nat) : Int) ((fsp - 1 : Nat) : Int)
    (by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact sub1_den _ _ fsp (ev_cell mv P [ci n, ci fsp, ci fw, ci 0] (j := 1) rfl hfM) hfM (by omega))
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q1 := (pexecM_prim mv fu (Proofs.FindCycleProg.dJ mv.nv) _ _).trans dJ
  -- while (stk[j] != fw) j--
  obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := wj_loopF hnv E.hty x F hj0 hjw P hn 0 0 hM0 hM0 hfM
    (fsp - 1 - j0) (fsp - 1) (by omega) (by omega) fu (by omega)
  rcases r2 with ⟨rps, rvv, rret, rcost, rneed, rwk⟩
  simp only at ps2 vv2 ret2 c2 n2 w2
  subst ps2 vv2 ret2
  have h2' : pexecM mv fu (Proofs.FindCycleProg.WJ mv.nv) (gS P ([ci n, ci fsp, ci fw, ci 0] ++ [(⟨i32, ((fsp - 1 : Nat) : Int)⟩ : Cell)]))
      (VXF H T x) = _ := h2
  -- k = fsp - j
  have hkM : fsp - j0 < M31 := by omega
  have s3 := step_assign mv fu P [ci n, ci fsp, ci fw, ci 0, ci j0] (VXF H T x) 3
    (.binary i32 .sub (Proofs.FindCycleProg.vr mv.nv 1) (Proofs.FindCycleProg.vr mv.nv 4)) (y := 0) rfl hM0 (fsp - j0) hkM (by
      rw [vdenM_scalar _ _ _ _ rfl]
      show (NExpr.binary i32 .sub (.variable i32 (mv.nv + 1)) (.variable i32 (mv.nv + 4))).denote _ = _
      rw [den_binary, den_variable, den_variable, ev_cell mv P _ (j := 1) rfl hfM, Option.bind_some,
        ev_cell mv P _ (j := 4) rfl (by omega), Option.bind_some]
      have e : binaryValue .sub (fsp : Int) (j0 : Int) = ((fsp - j0 : Nat) : Int) := by
        show (fsp : Int) - (j0 : Int) = _; omega
      rw [e]
      exact conv_signed i32 rfl rfl _ (i32v _ hkM))
  -- t = 0 and the copy loop
  have dT := gSM_decl mv P [ci n, ci fsp, ci fw, ci (fsp - j0), ci j0] (VXF H T x) i32 lit0 0 0 (d_zero mv _ P _)
    (conv_signed i32 rfl rfl _ (by decide))
  have q4 := (pexecM_prim mv fu Proofs.FindCycleProg.dT _ _).trans dT
  have hKl := F.lK
  obtain ⟨r5, Yl', h5, ret5, ps5, vv5, hl5, v5, pre5, c5, n5, w5⟩ := wc_loopF (H := H) (T := T) hnv E.hty x
    (fsp := fsp) (fw := fw) (j := j0) (k := fsp - j0) hfw hn (by omega) hKl F.vK P 0 (fsp - j0) 0 x.Yl (by omega) F.lY F.vY
    (fun i hi => by omega) fu (by omega) hfM
  have h5' : pexecM mv fu (Proofs.FindCycleProg.WC mv.nv)
      (gS P ([ci n, ci fsp, ci fw, ci (fsp - j0), ci j0] ++ [(⟨i32, ((0 : Nat) : Int)⟩ : Cell)]))
      (VXF H T { x with Yl := x.Yl }) = some r5 := h5
  have t5 := seqM_some h5' ret5 (pexecM_skip mv fu _ _)
  have t4 := seqM_some q4 rfl t5
  have sc1 := scope_drop mv fu (Proofs.FindCycleProg.CPB mv.nv) P [ci n, ci fsp, ci fw, ci (fsp - j0), ci j0]
    [ci n, ci fsp, ci fw, ci (fsp - j0), ci j0] [ci (fsp - j0)] (VXF H T x) _ rfl t4 (by rw [ps5]; rfl)
  have t6 := seqM_some sc1 rfl (pexecM_skip mv fu _ _)
  have t3 := seqM_some s3 rfl t6
  have t2 := seqM_some h2' rfl t3
  have t1 := seqM_some q1 rfl t2
  have sc2 := scope_drop mv fu (Proofs.FindCycleProg.EXB mv.nv) P [ci n, ci fsp, ci fw, ci 0]
    [ci n, ci fsp, ci fw, ci (fsp - j0)] [ci j0] (VXF H T x) _ rfl t1 (by rfl)
  have t7 := seqM_some sc2 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, j0, Yl', t7, rfl, hj0, hjw, rfl, by rw [vv5], hl5, v5, pre5, ?_, ?_, ?_⟩
  · simp [Proofs.FindCycleProg.dJ, Proofs.FindCycleProg.aK, Proofs.FindCycleProg.dT, Proofs.FindCycleProg.one,
      Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes]
    omega
  · simp [Proofs.FindCycleProg.dJ, Proofs.FindCycleProg.aK, Proofs.FindCycleProg.dT, Proofs.FindCycleProg.one,
      Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly,
      Container.nodes, gS_size, ps5]
    omega
  · simp
    omega

end Proofs.FindCycleExtract
