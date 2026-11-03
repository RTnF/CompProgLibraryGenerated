import Proofs.LowlinkExec

namespace Proofs.LowlinkExec2
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
open Proofs.LowlinkProg Proofs.LowlinkLists Proofs.LowlinkExec Proofs.LowlinkInv Proofs.LowlinkPop

theorem getD_dflt (l : List Int) (i : Nat) (h : i < l.length) (d d' : Int) : l.getD i d = l.getD i d' := by
  simp [List.getD_eq_getElem?_getD, h]

theorem set_getD_self (l : List Int) (p : Nat) (h : p < l.length) : l.set p (l.getD p 0) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_set]
    by_cases hi : p = i
    · subst hi; simp [List.getD_eq_getElem?_getD, h]
    · simp [hi]

/-- `if (low[v] < low[p]) low[p] = low[v];` -/
theorem cwLP_exec (mv : MV) (hnv : mv.nv = 8) (hty : ∀ k, k < 8 → mv.ty k = i32) (H T : List Nat) (x : XS) {n : Nat}
    (R : LR n x) (P cl : List Cell) {v p : Nat} (hv : cl[4]? = some (ci v)) (hp : cl[5]? = some (ci p))
    (hvn : v < n) (hpn : p < n) (hn : n < M31) (fu : Nat) :
    ∃ r1 : PRM, pexecM mv fu (CWb (cLP mv.nv) (sLowP mv.nv)) (gS P cl) (VX H T x) = some r1 ∧ r1.ret = none ∧
      r1.ps = gS P cl ∧ r1.vv = VX H T { x with Ll := x.Ll.set p (min (x.st.L p) (x.st.L v)) } ∧
      r1.cost ≤ 40 ∧ r1.need ≤ P.length + 2 * cl.length + 40 ∧ r1.wk ≤ 1 := by
  have hvM : v < M31 := by omega
  have hpM : p < M31 := by omega
  have hLv : (VX H T x 3)[v]? = some (x.Ll.getD v 0) := by
    rw [VX_3]; exact intList_get x.Ll v (by rw [R.lL]; exact hvn)
  have hLp : (VX H T x 3)[p]? = some (x.Ll.getD p 0) := by
    rw [VX_3]; exact intList_get x.Ll p (by rw [R.lL]; exact hpn)
  have dLv := d_rdv mv (VX H T x) P cl (k := 3) (j := 4) (x := v) (by omega) (hty 3 (by omega)) hv hvM _ hLv
    (rd_valid R.vL (by rw [R.lL]; exact hvn))
  have dLp := d_rdv mv (VX H T x) P cl (k := 3) (j := 5) (x := p) (by omega) (hty 3 (by omega)) hp hpM _ hLp
    (rd_valid R.vL (by rw [R.lL]; exact hpn))
  have hc := d_binb mv (VX H T x) P cl (op := .lt) (a := rdv mv.nv 3 4) (b := rdv mv.nv 3 5) rfl dLv dLp
  rw [bt_lt] at hc
  have hLeq : x.st.L v = x.Ll.getD v 0 := R.fL v
  have hLeq' : x.st.L p = x.Ll.getD p 0 := R.fL p
  by_cases hlt : x.Ll.getD v 0 < x.Ll.getD p 0
  · rw [if_pos hlt] at hc
    have dI := d_ixc mv (VX H T x) P cl (j := 5) (x := p) hp hpM
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := cw_true mv fu (cLP mv.nv) (ixc mv.nv 5) (rdv mv.nv 3 4) 3 (by omega)
      (hty 3 (by omega)) (gS P cl) (VX H T x) 1 hc (by decide) _ p dLv dI (by rw [VX_3, R.lL]; exact hpn)
      (rd_valid R.vL (by rw [R.lL]; exact hvn))
    refine ⟨r1, h1, ret1, ps1, ?_, ?_, ?_, ?_⟩
    · rw [vv1, VX_w3]
      congr 2
      rw [hLeq, hLeq', Int.min_eq_right (Int.le_of_lt hlt)]
      rw [VX_3]
    · rw [c1]; simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · rw [gS_size] at n1; simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at n1 ⊢; omega
    · omega
  · rw [if_neg hlt] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := cw_false mv fu (cLP mv.nv) (sLowP mv.nv) (gS P cl) (VX H T x) hc
    refine ⟨r1, h1, ret1, ps1, ?_, ?_, ?_, ?_⟩
    · rw [vv1]
      have : x.Ll.set p (min (x.st.L p) (x.st.L v)) = x.Ll := by
        rw [hLeq, hLeq', Int.min_eq_left (by omega)]
        exact set_getD_self x.Ll p (by rw [R.lL]; exact hpn)
      rw [this]
    · rw [c1]; simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at n1 ⊢; omega
    · omega

/-- `if (ord[p] <= low[v]) sep[p] = sep[p] + 1;` -/
theorem cwSep_exec (mv : MV) (hnv : mv.nv = 8) (hty : ∀ k, k < 8 → mv.ty k = i32) (H T : List Nat) (x : XS) {n : Nat}
    (hO : x.Ol.length = n) (hL : x.Ll.length = n) (hS : x.Sl.length = n) (vO : ∀ y ∈ x.Ol, i32.valid y = true)
    (vL : ∀ y ∈ x.Ll, i32.valid y = true) (vS : ∀ y ∈ x.Sl, i32.valid y = true)
    (P cl : List Cell) {v p : Nat} (hv : cl[4]? = some (ci v)) (hp : cl[5]? = some (ci p))
    (hvn : v < n) (hpn : p < n) (hn : n < M31) (hinc : i32.valid (x.Sl.getD p 0 + 1) = true) (fu : Nat) :
    ∃ r2 : PRM, pexecM mv fu (CWb (cSep mv.nv) (sSep mv.nv)) (gS P cl) (VX H T x) = some r2 ∧ r2.ret = none ∧
      r2.ps = gS P cl ∧
      r2.vv = VX H T { x with Sl := x.Sl.set p (x.Sl.getD p 0 + (if x.Ol.getD p 0 ≤ x.Ll.getD v 0 then 1 else 0)) } ∧
      r2.cost ≤ 60 ∧ r2.need ≤ P.length + 2 * cl.length + 60 ∧ r2.wk ≤ 1 := by
  have hvM : v < M31 := by omega
  have hpM : p < M31 := by omega
  have hOp : (VX H T x 2)[p]? = some (x.Ol.getD p 0) := by
    rw [VX_2]; exact intList_get x.Ol p (by rw [hO]; exact hpn)
  have hLv : (VX H T x 3)[v]? = some (x.Ll.getD v 0) := by
    rw [VX_3]; exact intList_get x.Ll v (by rw [hL]; exact hvn)
  have hSp : (VX H T x 5)[p]? = some (x.Sl.getD p 0) := by
    rw [VX_5]; exact intList_get x.Sl p (by rw [hS]; exact hpn)
  have dOp := d_rdv mv (VX H T x) P cl (k := 2) (j := 5) (x := p) (by omega) (hty 2 (by omega)) hp hpM _ hOp
    (rd_valid vO (by rw [hO]; exact hpn))
  have dLv := d_rdv mv (VX H T x) P cl (k := 3) (j := 4) (x := v) (by omega) (hty 3 (by omega)) hv hvM _ hLv
    (rd_valid vL (by rw [hL]; exact hvn))
  have dSp := d_rdv mv (VX H T x) P cl (k := 5) (j := 5) (x := p) (by omega) (hty 5 (by omega)) hp hpM _ hSp
    (rd_valid vS (by rw [hS]; exact hpn))
  have hc := d_binb mv (VX H T x) P cl (op := .le) (a := rdv mv.nv 2 5) (b := rdv mv.nv 3 4) rfl dOp dLv
  rw [bt_le] at hc
  by_cases hle : x.Ol.getD p 0 ≤ x.Ll.getD v 0
  · rw [if_pos hle] at hc
    have dI := d_ixc mv (VX H T x) P cl (j := 5) (x := p) hp hpM
    have dV := d_add1I mv (VX H T x) P cl (a := rdv mv.nv 5 5) rfl dSp hinc
    obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := cw_true mv fu (cSep mv.nv) (ixc mv.nv 5)
      (.binary i32 .add (rdv mv.nv 5 5) one) 5 (by omega) (hty 5 (by omega)) (gS P cl) (VX H T x) 1 hc (by decide) _ p
      dV dI (by rw [VX_5, hS]; exact hpn) hinc
    refine ⟨r2, h2, ret2, ps2, ?_, ?_, ?_, ?_⟩
    · rw [vv2, VX_w5, VX_5, if_pos hle]
    · rw [c2]; simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at n2 ⊢; omega
    · omega
  · rw [if_neg hle] at hc
    obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := cw_false mv fu (cSep mv.nv) (sSep mv.nv) (gS P cl) (VX H T x) hc
    refine ⟨r2, h2, ret2, ps2, ?_, ?_, ?_, ?_⟩
    · rw [vv2, if_neg hle]
      have : x.Sl.set p (x.Sl.getD p 0 + 0) = x.Sl := by
        rw [Int.add_zero]
        exact set_getD_self x.Sl p (by rw [hS]; exact hpn)
      rw [this]
    · rw [c2]; simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at n2 ⊢; omega
    · omega


theorem VX_congr (H T : List Nat) {a b : XS} (h2 : a.Ol = b.Ol) (h3 : a.Ll = b.Ll) (h4 : a.Pl = b.Pl) (h5 : a.Sl = b.Sl)
    (h6 : a.Il = b.Il) (h7 : a.Kl = b.Kl) : VX H T a = VX H T b := by
  funext j
  simp only [VX, h2, h3, h4, h5, h6, h7]

theorem pops_child (mv : MV) (hnv : mv.nv = 8) (hty : ∀ k, k < 8 → mv.ty k = i32) (H T : List Nat) (x : XS)
    {n : Nat} {hd tg : Nat → Nat} (I : MInv n hd tg x.st) (R : LR n x) (P : List Cell) (cnt r v : Nat)
    (hn : n < M31) (hn1 : n + 1 < M31) (hsp2 : 2 ≤ x.st.sp) (hv : x.st.Sk (x.st.sp - 1) = v) (hcnt : cnt < M31) (hr : r < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (POPS mv.nv) (gS P [ci n, ci cnt, ci r, ci x.st.sp, ci v]) (VX H T x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci cnt, ci r, ci (x.st.sp - 1), ci v] ∧ rr.vv = VX H T (popX x v) ∧
      rr.cost ≤ 300 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 2 := by
  set sp := x.st.sp with hspd
  have hspn : sp ≤ n := by
    have := I.sp_le
    have := I.vis_len_le
    omega
  have hspM : sp < M31 := by omega
  have hvm := I.sk_mem (sp - 1) (by omega)
  rw [hv] at hvm
  obtain ⟨hvV, hfv⟩ := hvm
  have hvn : v < n := I.vis_lt v hvV
  have hpm := I.sk_mem (sp - 2) (by omega)
  obtain ⟨hpV, hfp⟩ := hpm
  set p := x.st.Sk (sp - 2) with hpdef
  have hpn : p < n := I.vis_lt p hpV
  have hPv : x.st.P v = (p : Int) := (I.top_parent (by omega) hv).2 hsp2
  have hpv : p ≠ v := by
    intro e
    have := (I.par_ok p v hPv).2.2
    rw [e] at this
    omega
  have hvM : v < M31 := by omega
  have hpM : p < M31 := by omega
  -- sp = sp - 1
  have eA : vdenM mv (VX H T x) (penvN mv.nv (gS P [ci n, ci cnt, ci r, ci sp, ci v]))
      (.binary i32 .sub (vr mv.nv 3) one) = some ((sp - 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact sub1_den _ _ sp (ev_cell mv P [ci n, ci cnt, ci r, ci sp, ci v] (j := 3) rfl hspM) hspM (by omega)
  have dA := gSM_assign mv P [ci n, ci cnt, ci r, ci sp, ci v] (VX H T x) 3 (by simp) i32 _ _ _ eA (ci sp) rfl rfl
    (i32v sp hspM) (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have qA := (pexecM_prim mv fu (aSp0 mv.nv) _ _).trans dA
  -- the test sp > 0
  have cB : vdenM mv (VX H T x) (penvN mv.nv (gS P [ci n, ci cnt, ci r, ci (sp - 1), ci v])) (cSp mv.nv) = some 1 := by
    rw [d_cSp (VX H T x) P [ci n, ci cnt, ci r, ci (sp - 1), ci v] (y := sp - 1) rfl (by omega), if_pos (by omega)]
  -- int p = stk[sp - 1]
  have hKl : (VX H T x 7)[sp - 1 - 1]? = some (x.Kl.getD (sp - 2) 0) := by
    rw [VX_7]
    have e : sp - 1 - 1 = sp - 2 := by omega
    rw [e]
    exact intList_get x.Kl (sp - 2) (by rw [R.lK]; omega)
  have hKv : x.Kl.getD (sp - 2) 0 = (p : Int) := R.fK (sp - 2) (by omega)
  have vP := d_stk (VX H T x) P [ci n, ci cnt, ci r, ci (sp - 1), ci v] hnv (hty 7 (by omega)) (sp := sp - 1) rfl
    (by omega) (by omega) _ hKl (by rw [hKv]; exact i32v p hpM)
  rw [hKv] at vP
  have dC := gSM_decl mv P [ci n, ci cnt, ci r, ci (sp - 1), ci v] (VX H T x) i32 _ _ _ vP
    (conv_signed i32 rfl rfl _ (i32v p hpM))
  have qC := (pexecM_prim mv fu (dV mv.nv) _ _).trans dC
  -- the two conditional writes
  obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := cwLP_exec mv hnv hty H T x R P [ci n, ci cnt, ci r, ci (sp - 1), ci v, ci p]
    (v := v) (p := p) rfl rfl hvn hpn hn fu
  have hLvp : (x.Ll.set p (min (x.st.L p) (x.st.L v))).getD v 0 = x.Ll.getD v 0 := by
    rw [getD_set_gen]
    have : ¬ (v = p ∧ p < x.Ll.length) := fun h => hpv h.1.symm
    rw [if_neg this]
  have Rl : (x.Ll.set p (min (x.st.L p) (x.st.L v))).length = n := by simp [R.lL]
  have hminv : i32.valid (min (x.st.L p) (x.st.L v)) = true := by
    have a1 : i32.valid (x.st.L p) = true := by
      rw [R.fL p]; exact rd_valid R.vL (by rw [R.lL]; exact hpn)
    have a2 : i32.valid (x.st.L v) = true := by
      rw [R.fL v]; exact rd_valid R.vL (by rw [R.lL]; exact hvn)
    by_cases hle : x.st.L p ≤ x.st.L v
    · rw [Int.min_eq_left hle]; exact a1
    · rw [Int.min_eq_right (by omega)]; exact a2
  have hinc : i32.valid (x.Sl.getD p 0 + 1) = true := by
    have h1 := I.sep_le hpV
    have h2 := I.vis_len_le
    have h3 : x.st.Sp p = x.Sl.getD p 0 := R.fS p
    have h4 := (i32_valid_iff _).mp (rd_valid R.vS (i := p) (by rw [R.lS]; exact hpn))
    have : n + 1 < M31 := hn1
    unfold M31 at this
    exact (i32_valid_iff _).mpr ⟨by omega, by omega⟩
  obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := cwSep_exec mv hnv hty H T
    { x with Ll := x.Ll.set p (min (x.st.L p) (x.st.L v)) } (n := n) R.lO Rl R.lS R.vO (valid_set R.vL _ hminv) R.vS P
    [ci n, ci cnt, ci r, ci (sp - 1), ci v, ci p] (v := v) (p := p) rfl rfl hvn hpn hn hinc fu
  have h2' : pexecM mv fu (CWb (cSep mv.nv) (sSep mv.nv)) r1.ps r1.vv = some r2 := by
    rw [ps1, vv1]; exact h2
  have s2 := seqM_some h2' ret2 (pexecM_skip mv fu r2.ps r2.vv)
  have h1' : pexecM mv fu (.sequence (CWb (cLP mv.nv) (sLowP mv.nv))
      (.sequence (CWb (cSep mv.nv) (sSep mv.nv)) Sk)) (gS P [ci n, ci cnt, ci r, ci (sp - 1), ci v, ci p]) (VX H T x) =
      some _ := seqM_some h1 ret1 s2
  have pcs := seqM_some qC rfl h1'
  have sc := scope_drop mv fu (PCS mv.nv) P [ci n, ci cnt, ci r, ci (sp - 1), ci v] [ci n, ci cnt, ci r, ci (sp - 1), ci v]
    [ci p] (VX H T x) _ rfl pcs (by rw [ps2]; rfl)
  have popc := seqM_some sc rfl (pexecM_skip mv fu _ _)
  have br := pexecM_branch_true mv fu (cSp mv.nv) (POPC mv.nv) Sk _ (VX H T x) 1 cB (by decide) _ popc
  have s3 := seqM_some br rfl (pexecM_skip mv fu _ _)
  have fin := seqM_some qA rfl s3
  have hx1Ol : ({ x with Ll := x.Ll.set p (min (x.st.L p) (x.st.L v)) } : XS).Ol = x.Ol := rfl
  have hLv1 : x.st.L v = x.Ll.getD v 0 := R.fL v
  have hLp1 : x.st.L p = x.Ll.getD p 0 := R.fL p
  refine ⟨_, fin, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- the arrays
    have hP0 : 0 ≤ x.st.P v := by omega
    have ep : (x.st.P v).toNat = p := by omega
    show r2.vv = _
    rw [vv2]
    refine VX_congr H T ?_ ?_ ?_ ?_ ?_ ?_
    · rfl
    · show x.Ll.set p (min (x.st.L p) (x.st.L v)) = (popX x v).Ll
      simp only [popX, if_pos hP0, ep]
    · rfl
    · show x.Sl.set p (x.Sl.getD p 0 + if x.Ol.getD p 0 ≤ (x.Ll.set p (min (x.st.L p) (x.st.L v))).getD v 0 then 1 else 0) =
        (popX x v).Sl
      simp only [popX, if_pos hP0, ep]
      have hOp0 : x.st.O p = x.Ol.getD p 0 := by
        rw [R.fO p]; exact getD_dflt x.Ol p (by rw [R.lO]; exact hpn) _ _
      rw [hLvp, R.fS p, hOp0, hLv1]
    · rfl
    · rfl
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    omega
  · simp only [List.length_cons, List.length_nil] at n1 n2
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    refine ⟨by omega, by omega, ?_⟩
    rw [ps2, gS_size]
    simp
  · simp
    omega


theorem pops_root (mv : MV) (hnv : mv.nv = 8) (H T : List Nat) (x : XS)
    {n : Nat} {hd tg : Nat → Nat} (I : MInv n hd tg x.st) (R : LR n x) (P : List Cell) (cnt r v : Nat)
    (hn : n < M31) (hsp1 : x.st.sp = 1) (hv : x.st.Sk (x.st.sp - 1) = v) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (POPS mv.nv) (gS P [ci n, ci cnt, ci r, ci x.st.sp, ci v]) (VX H T x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci cnt, ci r, ci (x.st.sp - 1), ci v] ∧ rr.vv = VX H T (popX x v) ∧
      rr.cost ≤ 300 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 2 := by
  have hP : x.st.P v = -1 := (I.top_parent (by omega) hv).1 hsp1
  have hP0 : ¬ 0 ≤ x.st.P v := by omega
  rw [hsp1] at hv ⊢
  have eA : vdenM mv (VX H T x) (penvN mv.nv (gS P [ci n, ci cnt, ci r, ci 1, ci v]))
      (.binary i32 .sub (vr mv.nv 3) one) = some ((1 - 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact sub1_den _ _ 1 (ev_cell mv P [ci n, ci cnt, ci r, ci 1, ci v] (j := 3) rfl (by unfold M31; omega)) (by unfold M31; omega)
      (by omega)
  have dA := gSM_assign mv P [ci n, ci cnt, ci r, ci 1, ci v] (VX H T x) 3 (by simp) i32 _ _ _ eA (ci 1) rfl rfl
    (i32v 1 (by unfold M31; omega)) (conv_signed i32 rfl rfl _ (i32v _ (by unfold M31; omega)))
  have qA := (pexecM_prim mv fu (aSp0 mv.nv) _ _).trans dA
  have cB : vdenM mv (VX H T x) (penvN mv.nv (gS P [ci n, ci cnt, ci r, ci (1 - 1), ci v])) (cSp mv.nv) = some 0 := by
    rw [d_cSp (VX H T x) P [ci n, ci cnt, ci r, ci (1 - 1), ci v] (y := 1 - 1) rfl (by unfold M31; omega), if_neg (by omega)]
  have br := pexecM_branch_false mv fu (cSp mv.nv) (POPC mv.nv) Sk _ (VX H T x) cB _ (pexecM_skip mv fu _ _)
  have s3 := seqM_some br rfl (pexecM_skip mv fu _ _)
  have fin := seqM_some qA rfl s3
  refine ⟨_, fin, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show VX H T x = _
    apply VX_congr <;> simp only [popX, if_neg hP0]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp

end Proofs.LowlinkExec2
