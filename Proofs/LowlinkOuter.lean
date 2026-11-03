import Proofs.LowlinkIter

namespace Proofs.LowlinkOuter
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.DoublingNested (i32 u64)
open Proofs.PowModStep (Sk)
open Proofs.BellmanFordExec (M31 rdM_val vec_getM pexecM_branch_true pexecM_branch_false)
open Proofs.VectorSumCall (conv_signed)
open Proofs.PrefixSumsCall
open Proofs.DijkstraScan
open Proofs.LowlinkProg Proofs.LowlinkLists Proofs.LowlinkExec Proofs.LowlinkExec2 Proofs.LowlinkExec3 Proofs.LowlinkStep
open Proofs.LowlinkIter
open Proofs.LowlinkInv Proofs.LowlinkScan Proofs.LowlinkPop Proofs.LowlinkPush Proofs.LowlinkRoot Proofs.LowlinkPhi

structure RootOK (n : Nat) (hd tg : Nat → Nat) (r : Nat) (x x' : XS) : Prop where
  inv : MInv n hd tg x'.st
  lr : LR n x'
  sp0 : x'.st.sp = 0
  mem : r ∈ x'.st.Vis
  vis : ∀ a ∈ x.st.Vis, a ∈ x'.st.Vis
  phi : phi n hd x'.st ≤ phi n hd x.st


theorem rootT_exec {mv : MV} {n : Nat} {H T : List Nat} (E : XE mv n H T) (G : GH n (hdF H) (tgF T)) (x : XS)
    (I : MInv n (hdF H) (tgF T) x.st) (R : LR n x) (P : List Cell) {r : Nat} (hrn : r < n) (hsp0 : x.st.sp = 0)
    (hrU : x.st.O r < 0) (fu : Nat) (hfu : phi n (hdF H) x.st + 2 ≤ fu) :
    ∃ (rr : PRM) (x' : XS), pexecM mv fu (ROOTT mv.nv) (gS P [ci n, ci x.st.Vis.length, ci r]) (VX H T x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci x'.st.Vis.length, ci r] ∧ rr.vv = VX H T x' ∧
      RootOK n (hdF H) (tgF T) r x x' ∧ rr.cost + 1250 * phi n (hdF H) x'.st ≤ 1250 * phi n (hdF H) x.st + 800 ∧
      rr.need ≤ P.length + 80 ∧ rr.wk + 7 * phi n (hdF H) x'.st ≤ 7 * phi n (hdF H) x.st + 4 := by
  have hnv := E.hnv
  have hn : n < M31 := by have := E.hn1; omega
  have hrV : r ∉ x.st.Vis := fun h => by have := (I.ord_lt_len h).1; omega
  have hVl := I.vis_len_le
  have hlt : x.st.Vis.length < n := by
    have hnd : (x.st.Vis ++ [r]).Nodup := by
      rw [List.nodup_append]
      refine ⟨I.vis_nd, by simp, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      exact fun e => hrV (e ▸ ha)
    have hsub : (x.st.Vis ++ [r]) ⊆ List.range n := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact List.mem_range.mpr (I.vis_lt a h)
      · simp at h; subst h; exact List.mem_range.mpr hrn
    have := List.Nodup.length_le_of_subset hnd hsub
    simp at this
    omega
  have hrM : r < M31 := by omega
  have hcM : x.st.Vis.length < M31 := by omega
  have hc1 : x.st.Vis.length + 1 < M31 := by have := E.hn1; omega
  have hTM := E.hTM
  have hHr : H.getD r 0 < M31 := by have := E.hd_le r (by omega); omega
  -- ord[r] = cnt
  have s1 := step_write mv fu P [ci n, ci x.st.Vis.length, ci r] (VX H T x) 2 2 (vr mv.nv 1) (by omega)
    (E.hty 2 (by omega)) (idx := r) rfl hrM (x.st.Vis.length : Int)
    (d_vr mv _ P _ (j := 1) (x := x.st.Vis.length) rfl hcM) (by rw [VX_2, R.lO]; exact hrn) (i32v _ hcM)
  obtain ⟨x1, hx1⟩ : ∃ x1 : XS, x1 = { x with Ol := x.Ol.set r (x.st.Vis.length : Int) } := ⟨_, rfl⟩
  rw [VX_2, VX_w2, ← hx1] at s1
  have s2 := step_write mv fu P [ci n, ci x.st.Vis.length, ci r] (VX H T x1) 3 2 (vr mv.nv 1) (by omega)
    (E.hty 3 (by omega)) (idx := r) rfl hrM (x.st.Vis.length : Int)
    (d_vr mv _ P _ (j := 1) (x := x.st.Vis.length) rfl hcM) (by rw [VX_3, hx1]; exact (by rw [R.lL]; exact hrn)) (i32v _ hcM)
  obtain ⟨x2, hx2⟩ : ∃ x2 : XS, x2 = { x1 with Ll := x1.Ll.set r (x.st.Vis.length : Int) } := ⟨_, rfl⟩
  rw [VX_3, VX_w3, ← hx2] at s2
  have s3 := step_assign mv fu P [ci n, ci x.st.Vis.length, ci r] (VX H T x2) 1
    (.binary i32 .add (vr mv.nv 1) one) (y := x.st.Vis.length) rfl hcM (x.st.Vis.length + 1) hc1 (by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact add1_den _ _ x.st.Vis.length (ev_cell mv P _ (j := 1) rfl hcM) hc1)
  have hHd : (VX H T x2 0)[r]? = some ((H.getD r 0 : Nat) : Int) := by
    rw [VX_0]; exact vec_getM H r (by have := E.HK.len; omega)
  have s4 := step_write mv fu P ([ci n, ci x.st.Vis.length, ci r].set 1 (ci (x.st.Vis.length + 1))) (VX H T x2) 6 2
    (rdv mv.nv 0 2) (by omega) (E.hty 6 (by omega)) (idx := r) rfl hrM ((H.getD r 0 : Nat) : Int)
    (d_rdv mv _ P _ (k := 0) (j := 2) (x := r) (by omega) (E.hty 0 (by omega)) rfl hrM _ hHd (i32v _ hHr))
    (by rw [VX_6, hx2, hx1]; exact (by rw [R.lI]; exact hrn)) (i32v _ hHr)
  obtain ⟨x3, hx3⟩ : ∃ x3 : XS, x3 = { x2 with Il := x2.Il.set r (H.getD r 0 : Int) } := ⟨_, rfl⟩
  rw [VX_6, VX_w6, ← hx3] at s4
  -- stk[0] = r
  have hi0 : vdenM mv (VX H T x3) (penvN mv.nv (gS P ([ci n, ci x.st.Vis.length, ci r].set 1 (ci (x.st.Vis.length + 1)))))
      (.cast u64 lit0) = some ((0 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact den_cast_u64 _ _ 0 (zero_den _) (by unfold M31; omega)
  have wr := pstmtM_write_ok mv (gS P ([ci n, ci x.st.Vis.length, ci r].set 1 (ci (x.st.Vis.length + 1)))) (VX H T x3) 7
    (by omega) (.cast u64 lit0) (vr mv.nv 2) (r : Int) 0
    (d_vr mv _ P ([ci n, ci x.st.Vis.length, ci r].set 1 (ci (x.st.Vis.length + 1))) (j := 2) (x := r) rfl hrM) hi0
    (by rw [VX_7, hx3, hx2, hx1]; exact (by rw [R.lK]; omega)) (by rw [E.hty 7 (by omega)]; exact i32v r hrM)
  rw [E.hty 7 (by omega), VX_7, VX_w7] at wr
  obtain ⟨x4, hx4⟩ : ∃ x4 : XS, x4 = { x3 with Kl := x3.Kl.set 0 (r : Int) } := ⟨_, rfl⟩
  rw [← hx4] at wr
  have s5 := (pexecM_prim mv fu (sStk0 mv.nv) _ _).trans wr
  -- int sp = 1
  have dS := gSM_decl mv P ([ci n, ci x.st.Vis.length, ci r].set 1 (ci (x.st.Vis.length + 1))) (VX H T x4) i32 one 1 1
    (d_one mv _ P _) (conv_signed i32 rfl rfl _ (by decide))
  have s6 := (pexecM_prim mv fu dSp _ _).trans dS
  -- the loop
  have hxr : VX H T x4 = VX H T (rootX (hdF H) x r) := by
    apply VX_congr <;> simp [hx4, hx3, hx2, hx1, rootX]
  have hIr := inv_root G I hsp0 hrn hrU
  have hRr : LR n (rootX (hdF H) x r) := LR_root (hdF H) R hrn (i32v _ hcM) (i32v r hrM) (i32v _ hHr)
  have hlenr : (rootX (hdF H) x r).st.Vis.length = x.st.Vis.length + 1 := by simp [rootX, rootS]
  have hspr : (rootX (hdF H) x r).st.sp = 1 := rfl
  have hphir : phi n (hdF H) (rootX (hdF H) x r).st ≤ phi n (hdF H) x.st := phi_root n (hdF H) x.st r hrV hlt hsp0
  obtain ⟨r7, x', h7, ret7, ps7, vv7, I7, R7, hsp7, hsub7, hphi7, c7, n7, w7⟩ := wloop_exec E G P r hrM (phi n (hdF H) (rootX (hdF H) x r).st)
    (rootX (hdF H) x r) hIr hRr (Nat.le_refl _) (fu - 0) (by omega)
  have h7' : pexecM mv fu (WH mv.nv) (gS P ([ci n, ci x.st.Vis.length, ci r].set 1 (ci (x.st.Vis.length + 1)) ++ [(⟨i32, 1⟩ : Cell)]))
      (VX H T x4) = some r7 := by
    rw [hxr]
    have := h7
    rw [hlenr, hspr] at this
    exact this
  have t7 := seqM_some h7' ret7 (pexecM_skip mv fu _ _)
  have t6 := seqM_some s6 rfl t7
  have t5 := seqM_some s5 rfl t6
  have t4 := seqM_some s4 rfl t5
  have t3 := seqM_some s3 rfl t4
  have t2 := seqM_some s2 rfl t3
  have t1 := seqM_some s1 rfl t2
  have sc := scope_drop mv fu (ROOTB mv.nv) P [ci n, ci x.st.Vis.length, ci r] [ci n, ci x'.st.Vis.length, ci r]
    [ci x'.st.sp] (VX H T x) _ rfl t1 (by rw [ps7]; rfl)
  have t8 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  have hsr : r ∈ (rootX (hdF H) x r).st.Vis := by simp [rootX, rootS]
  refine ⟨_, x', t8, rfl, rfl, by rw [vv7], ⟨I7, R7, hsp7, hsub7 r hsr, fun a ha => hsub7 a (by simp [rootX, rootS, ha]),
    by omega⟩, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps7]
    omega
  · simp
    omega


/-- `if (ord[r] < 0) { ... }` : one round of the outer loop. -/
theorem bout_exec {mv : MV} {n : Nat} {H T : List Nat} (E : XE mv n H T) (G : GH n (hdF H) (tgF T)) (x : XS)
    (I : MInv n (hdF H) (tgF T) x.st) (R : LR n x) (P : List Cell) {r : Nat} (hrn : r < n) (hsp0 : x.st.sp = 0)
    (fu : Nat) (hfu : phi n (hdF H) x.st + 2 ≤ fu) :
    ∃ (rr : PRM) (x' : XS), pexecM mv fu (BOUT mv.nv) (gS P [ci n, ci x.st.Vis.length, ci r]) (VX H T x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci x'.st.Vis.length, ci r] ∧ rr.vv = VX H T x' ∧
      RootOK n (hdF H) (tgF T) r x x' ∧ rr.cost + 1250 * phi n (hdF H) x'.st ≤ 1250 * phi n (hdF H) x.st + 900 ∧
      rr.need ≤ P.length + 80 ∧ rr.wk + 7 * phi n (hdF H) x'.st ≤ 7 * phi n (hdF H) x.st + 4 := by
  have hnv := E.hnv
  have hn : n < M31 := by have := E.hn1; omega
  have hrM : r < M31 := by omega
  have hOr : (VX H T x 2)[r]? = some (x.Ol.getD r 0) := by
    rw [VX_2]; exact intList_get x.Ol r (by rw [R.lO]; exact hrn)
  have dO := d_rdv mv (VX H T x) P [ci n, ci x.st.Vis.length, ci r] (k := 2) (j := 2) (x := r) (by omega)
    (E.hty 2 (by omega)) rfl hrM _ hOr (rd_valid R.vO (by rw [R.lO]; exact hrn))
  have hc := d_binb mv (VX H T x) P [ci n, ci x.st.Vis.length, ci r] (op := .lt) (a := rdv mv.nv 2 2) (b := lit0) rfl dO
    (d_zero mv _ P _)
  rw [bt_lt] at hc
  have hOeq : x.st.O r = x.Ol.getD r 0 := by
    rw [R.fO r]; exact getD_dflt x.Ol r (by rw [R.lO]; exact hrn) _ _
  by_cases hrU : x.st.O r < 0
  · have hrU' : x.Ol.getD r 0 < 0 := by rw [← hOeq]; exact hrU
    rw [if_pos hrU'] at hc
    obtain ⟨r1, x', h1, ret1, ps1, vv1, hok, c1, n1, w1⟩ := rootT_exec E G x I R P hrn hsp0 hrU fu hfu
    have br := pexecM_branch_true mv fu (cRoot mv.nv) (ROOTT mv.nv) Sk _ _ 1 hc (by decide) _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    refine ⟨_, x', s2, rfl, by rw [ps1], by rw [vv1], hok, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1]
      omega
    · simp
      omega
  · have hrU' : ¬ x.Ol.getD r 0 < 0 := by rw [← hOeq]; exact hrU
    rw [if_neg hrU'] at hc
    have br := pexecM_branch_false mv fu (cRoot mv.nv) (ROOTT mv.nv) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    have s2 := seqM_some br rfl (pexecM_skip mv fu _ _)
    have hrV : r ∈ x.st.Vis := I.vis_of_nn (by omega)
    refine ⟨_, x, s2, rfl, rfl, rfl, ⟨I, R, hsp0, hrV, fun a ha => ha, Nat.le_refl _⟩, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp

end Proofs.LowlinkOuter
