import Proofs.LowlinkExec3
import Proofs.LowlinkStep

namespace Proofs.LowlinkIter
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.DoublingNested (i32)
open Proofs.PowModStep (Sk)
open Proofs.BellmanFordExec (M31 rdM_val vec_getM pexecM_branch_true pexecM_branch_false)
open Proofs.VectorSumCall (conv_signed)
open Proofs.PrefixSumsCall
open Proofs.DijkstraScan
open Proofs.LowlinkProg Proofs.LowlinkLists Proofs.LowlinkExec Proofs.LowlinkExec2 Proofs.LowlinkExec3 Proofs.LowlinkStep
open Proofs.LowlinkInv Proofs.LowlinkScan Proofs.LowlinkPop Proofs.LowlinkPush Proofs.LowlinkPhi

abbrev hdF (H : List Nat) : Nat → Nat := fun a => H.getD a 0
abbrev tgF (T : List Nat) : Nat → Nat := fun a => T.getD a 0

def thenX (hd : Nat → Nat) (x : XS) (v w : Nat) : XS :=
  if x.st.O w < 0 then pushX hd x v w else if x.st.P v = (w : Int) then advX x v else backX x v w

theorem thenL_vx (H T : List Nat) {n : Nat} {x : XS} (R : LR n x) {cnt sp v e w : Nat} (hcnt : cnt = x.st.Vis.length)
    (hsp : sp = x.st.sp) (he : x.st.It v = (e : Int)) (hvn : v < n) (hwn : w < n) :
    VX H T (thenL H x cnt sp v e w) = VX H T (thenX (hdF H) x v w) := by
  have hOw : x.st.O w = x.Ol.getD w 0 := by
    rw [R.fO w]; exact getD_dflt x.Ol w (by rw [R.lO]; exact hwn) _ _
  have hPv : x.st.P v = x.Pl.getD v 0 := by
    rw [R.fP v]; exact getD_dflt x.Pl v (by rw [R.lP]; exact hvn) _ _
  have hIl : x.Il.getD v 0 = (e : Int) := by rw [← R.fI v]; exact he
  subst hcnt hsp
  by_cases hnew : x.st.O w < 0
  · have hnew' : x.Ol.getD w 0 < 0 := by rw [← hOw]; exact hnew
    unfold thenL thenX
    rw [if_pos hnew', if_pos hnew]
    refine VX_congr H T rfl rfl rfl rfl ?_ rfl
    show (x.Il.set v ((e + 1 : Nat) : Int)).set w (H.getD w 0 : Int) = (x.Il.set v (x.st.It v + 1)).set w (hdF H w : Int)
    rw [he]
    push_cast
    rfl
  · have hnew' : ¬ x.Ol.getD w 0 < 0 := by rw [← hOw]; exact hnew
    unfold thenL thenX
    rw [if_neg hnew', if_neg hnew]
    have hIeq : (x.Il.set v ((e + 1 : Nat) : Int)) = x.Il.set v (x.st.It v + 1) := by
      rw [he]; push_cast; rfl
    by_cases hpar : x.st.P v = (w : Int)
    · rw [if_pos hpar]
      refine VX_congr H T rfl ?_ rfl rfl hIeq rfl
      show (backL { x with Il := x.Il.set v ((e + 1 : Nat) : Int) } v w).Ll = x.Ll
      simp only [backL]
      rw [if_neg (fun h => h.1 (by rw [← hPv]; exact hpar.symm))]
    · rw [if_neg hpar]
      refine VX_congr H T rfl ?_ rfl rfl hIeq rfl
      show (backL { x with Il := x.Il.set v ((e + 1 : Nat) : Int) } v w).Ll = x.Ll.set v (min (x.st.L v) (x.st.O w))
      simp only [backL]
      have hLv : x.st.L v = x.Ll.getD v 0 := R.fL v
      have hne : (w : Int) ≠ x.Pl.getD v 0 := by rw [← hPv]; exact fun h => hpar h.symm
      by_cases hA : x.Ol.getD w 0 < x.Ll.getD v 0
      · rw [if_pos ⟨hne, hA⟩, hLv, hOw, Int.min_eq_right (by omega)]
      · rw [if_neg (fun h => hA h.2), hLv, hOw, Int.min_eq_left (by omega)]
        exact (set_getD_self x.Ll v (by rw [R.lL]; exact hvn)).symm


/-- The standing hypotheses of the loops. -/
structure XE (mv : MV) (n : Nat) (H T : List Nat) : Prop where
  hnv : mv.nv = 8
  hty : ∀ k, k < 8 → mv.ty k = i32
  hn1 : n + 1 < M31
  HK : Proofs.TopoSortMath.HeadOK H T n
  hTM : T.length < M31
  hTn : ∀ y ∈ T, y < n

theorem XE.hd_le {mv : MV} {n : Nat} {H T : List Nat} (E : XE mv n H T) (a : Nat) (ha : a ≤ n) :
    H.getD a 0 ≤ T.length := by
  have := E.HK.le H T n n (Nat.le_refl _) a ha
  rw [E.HK.last] at this
  exact this

theorem then_exec {mv : MV} {n : Nat} {H T : List Nat} (E : XE mv n H T) (G : GH n (hdF H) (tgF T)) (x : XS)
    (I : MInv n (hdF H) (tgF T) x.st) (R : LR n x) (P : List Cell) (r : Nat) (hr : r < M31) (hsp : 0 < x.st.sp)
    {v : Nat} (hv : x.st.Sk (x.st.sp - 1) = v) (hit : x.st.It v < (H.getD (v + 1) 0 : Int)) (fu : Nat) :
    ∃ (rr : PRM) (x' : XS), pexecM mv fu (THENB mv.nv) (gS P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v]) (VX H T x) =
        some rr ∧ rr.ret = none ∧ rr.ps = gS P [ci n, ci x'.st.Vis.length, ci r, ci x'.st.sp, ci v] ∧
      rr.vv = VX H T x' ∧ StepOK n (hdF H) (tgF T) x x' ∧ rr.cost ≤ 900 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 7 := by
  have hvm := I.sk_mem (x.st.sp - 1) (by omega)
  rw [hv] at hvm
  obtain ⟨hvV, hfv⟩ := hvm
  have hvn := I.vis_lt v hvV
  have hrng := I.it_rng v hvV
  have hn : n < M31 := by have := E.hn1; omega
  have hvl := E.hd_le (v + 1) (by omega)
  -- the arc
  obtain ⟨e, he⟩ : ∃ e : Nat, x.st.It v = (e : Int) := ⟨(x.st.It v).toNat, by have : (hdF H v : Int) ≤ x.st.It v := hrng.1; omega⟩
  have heh : e < H.getD (v + 1) 0 := by
    have : x.st.It v < ((H.getD (v + 1) 0 : Nat) : Int) := hit
    omega
  have heT : e < T.length := by omega
  have hwn : T.getD e 0 < n := E.hTn _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem heT]
    exact List.getElem_mem _)
  obtain ⟨w, hw⟩ : ∃ w, w = T.getD e 0 := ⟨_, rfl⟩
  have hwl : w < n := by rw [hw]; exact hwn
  have hq : (e : Int) = x.st.It v := he.symm
  have hitq : (e : Int) < (hdF H (v + 1) : Int) := by rw [← he]; exact hit
  have hwtg : tgF T e = w := hw.symm
  have hVl := I.vis_len_le
  have hsn := I.sp_le
  have hTM := E.hTM
  have hn1 := E.hn1
  have hcnt : x.st.Vis.length < M31 := by omega
  have hsM : x.st.sp < M31 := by omega
  have he1 : e + 1 < M31 := by omega
  have hit1 : i32.valid (x.st.It v + 1) = true := by
    rw [i32_valid_iff]; unfold M31 at he1; constructor <;> omega
  have hhd : H.getD w 0 < M31 := by have := E.hd_le w (by omega); omega
  -- the execution of THENS
  obtain ⟨rr, hrr, hret, hps, hvv, hc, hnd, hwk⟩ := thens_exec mv E.hnv E.hty H T x R.lO R.lL R.lP R.lI R.lK R.vO R.vL R.vP R.vI
    E.HK.len P x.st.Vis.length r x.st.sp v e w hn E.hn1 hcnt hsM (by
      intro hneg
      have hO : x.st.O w < 0 := by
        rw [R.fO w, getD_dflt x.Ol w (by rw [R.lO]; exact hwl) _ _]; exact hneg
      have hwV : w ∉ x.st.Vis := fun h => by have := (I.ord_lt_len h).1; omega
      have hlt : x.st.Vis.length < n := by
        have hnd : (x.st.Vis ++ [w]).Nodup := by
          rw [List.nodup_append]
          refine ⟨I.vis_nd, by simp, ?_⟩
          intro a ha b hb
          simp at hb
          subst hb
          exact fun e => hwV (e ▸ ha)
        have hsub : (x.st.Vis ++ [w]) ⊆ List.range n := by
          intro a ha
          rcases List.mem_append.mp ha with h | h
          · exact List.mem_range.mpr (I.vis_lt a h)
          · simp at h; subst h; exact List.mem_range.mpr hwl
        have := List.Nodup.length_le_of_subset hnd hsub
        simp at this
        omega
      exact ⟨hlt, by omega⟩) hvn hr (by rw [← R.fI v, he]) heT E.hTM hw.symm hwl he1 hhd fu
  -- drop the two cells of THENS
  have hvx : rr.vv = VX H T (thenX (hdF H) x v w) := by
    rw [hvv]; exact thenL_vx H T R rfl rfl he hvn hwl
  have fin : ∀ (x' : XS) (c' s' : Nat), thenX (hdF H) x v w = x' → x'.st.Vis.length = c' → x'.st.sp = s' →
      rr.ps = gS P [ci n, ci c', ci r, ci s', ci v, ci e, ci w] → StepOK n (hdF H) (tgF T) x x' →
      ∃ (rr : PRM) (x' : XS), pexecM mv fu (THENB mv.nv) (gS P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v]) (VX H T x) =
        some rr ∧ rr.ret = none ∧ rr.ps = gS P [ci n, ci x'.st.Vis.length, ci r, ci x'.st.sp, ci v] ∧
      rr.vv = VX H T x' ∧ StepOK n (hdF H) (tgF T) x x' ∧ rr.cost ≤ 900 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 7 := by
    intro x' c' s' hx' hc' hs' hps' hso
    have sc := scope_drop mv fu (THENS mv.nv) P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v]
      [ci n, ci c', ci r, ci s', ci v] [ci e, ci w] (VX H T x) rr rfl hrr hps'
    have s2 := seqM_some sc (by simpa using hret) (pexecM_skip mv fu _ _)
    refine ⟨_, x', s2, rfl, ?_, ?_, hso, ?_, ?_, ?_⟩
    · rw [hc', hs']
    · rw [hvx, hx']
    · simp
      omega
    · simp [gS_size]
      omega
    · simp
      omega
  by_cases hnew : x.st.O w < 0
  · have hnew' : x.Ol.getD w 0 < 0 := by
      rw [← getD_dflt x.Ol w (by rw [R.lO]; exact hwl) (-1) 0, ← R.fO w]; exact hnew
    rw [if_pos hnew', if_pos hnew'] at hps
    have hso := step_push G I R hsp hv hq hitq hwtg hnew hn hit1 (by simpa using hhd)
    refine fin (pushX (hdF H) x v w) (x.st.Vis.length + 1) (x.st.sp + 1) ?_ (by simp [pushX, pushS]) rfl hps hso
    unfold thenX; rw [if_pos hnew]
  · have hnew' : ¬ x.Ol.getD w 0 < 0 := by
      rw [← getD_dflt x.Ol w (by rw [R.lO]; exact hwl) (-1) 0, ← R.fO w]; exact hnew
    rw [if_neg hnew', if_neg hnew'] at hps
    have hwv : 0 ≤ x.st.O w := by omega
    by_cases hpar : x.st.P v = (w : Int)
    · have hso := step_adv G I R hsp hv hq hitq hwtg hwv hpar hit1
      refine fin (advX x v) x.st.Vis.length x.st.sp ?_ rfl rfl hps hso
      unfold thenX; rw [if_neg hnew, if_pos hpar]
    · have hso := step_back G I R hsp hv hq hitq hwtg hwv hpar hit1
      refine fin (backX x v w) x.st.Vis.length x.st.sp ?_ rfl rfl hps hso
      unfold thenX; rw [if_neg hnew, if_neg hpar]


theorem pop_exec {mv : MV} {n : Nat} {H T : List Nat} (E : XE mv n H T) (x : XS)
    (I : MInv n (hdF H) (tgF T) x.st) (R : LR n x) (P : List Cell) (r : Nat) (hr : r < M31) (hsp : 0 < x.st.sp)
    {v : Nat} (hv : x.st.Sk (x.st.sp - 1) = v) (hit : x.st.It v = (H.getD (v + 1) 0 : Int)) (fu : Nat) :
    ∃ (rr : PRM) (x' : XS), pexecM mv fu (POPB mv.nv) (gS P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v]) (VX H T x) =
        some rr ∧ rr.ret = none ∧ rr.ps = gS P [ci n, ci x'.st.Vis.length, ci r, ci x'.st.sp, ci v] ∧
      rr.vv = VX H T x' ∧ StepOK n (hdF H) (tgF T) x x' ∧ rr.cost ≤ 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 2 := by
  have hn : n < M31 := by have := E.hn1; omega
  have hVl := I.vis_len_le
  have hcM : x.st.Vis.length < M31 := by omega
  have hso := step_pop I R hsp hv hit E.hn1
  by_cases h2 : 2 ≤ x.st.sp
  · obtain ⟨rr, hrr, hret, hps, hvv, hc, hnd, hwk⟩ := pops_child mv E.hnv E.hty H T x I R P x.st.Vis.length r v hn E.hn1 h2 hv
      hcM hr fu
    have sc := scope_gS mv fu (POPS mv.nv) P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v]
      [ci n, ci (popX x v).st.Vis.length, ci r, ci (popX x v).st.sp, ci v] (VX H T x) rr rfl hrr (by rw [hps]; rfl)
    have s2 := seqM_some sc (by simpa using hret) (pexecM_skip mv fu _ _)
    refine ⟨_, popX x v, s2, rfl, rfl, by rw [hvv], hso, ?_, ?_, ?_⟩
    · simp; omega
    · simp [gS_size]; omega
    · simp; omega
  · have h1 : x.st.sp = 1 := by omega
    obtain ⟨rr, hrr, hret, hps, hvv, hc, hnd, hwk⟩ := pops_root mv E.hnv H T x I R P x.st.Vis.length r v hn h1 hv fu
    have sc := scope_gS mv fu (POPS mv.nv) P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v]
      [ci n, ci (popX x v).st.Vis.length, ci r, ci (popX x v).st.sp, ci v] (VX H T x) rr rfl hrr (by rw [hps]; rfl)
    have s2 := seqM_some sc (by simpa using hret) (pexecM_skip mv fu _ _)
    refine ⟨_, popX x v, s2, rfl, rfl, by rw [hvv], hso, ?_, ?_, ?_⟩
    · simp; omega
    · simp [gS_size]; omega
    · simp; omega


/-- One iteration of the loop `while (sp > 0)`. -/
theorem wbody_exec {mv : MV} {n : Nat} {H T : List Nat} (E : XE mv n H T) (G : GH n (hdF H) (tgF T)) (x : XS)
    (I : MInv n (hdF H) (tgF T) x.st) (R : LR n x) (P : List Cell) (r : Nat) (hr : r < M31) (hsp : 0 < x.st.sp)
    (fu : Nat) :
    ∃ (rr : PRM) (x' : XS), pexecM mv fu (WBODY mv.nv) (gS P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp]) (VX H T x) =
        some rr ∧ rr.ret = none ∧ rr.ps = gS P [ci n, ci x'.st.Vis.length, ci r, ci x'.st.sp] ∧
      rr.vv = VX H T x' ∧ StepOK n (hdF H) (tgF T) x x' ∧ rr.cost ≤ 1200 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 7 := by
  have hnv := E.hnv
  have hn : n < M31 := by have := E.hn1; omega
  have hVl := I.vis_len_le
  have hsn := I.sp_le
  have hcM : x.st.Vis.length < M31 := by omega
  have hsM : x.st.sp < M31 := by omega
  obtain ⟨v, hv⟩ : ∃ v, x.st.Sk (x.st.sp - 1) = v := ⟨_, rfl⟩
  have hvm := I.sk_mem (x.st.sp - 1) (by omega)
  rw [hv] at hvm
  obtain ⟨hvV, hfv⟩ := hvm
  have hvn := I.vis_lt v hvV
  have hrng := I.it_rng v hvV
  have hvM : v < M31 := by omega
  -- int v = stk[sp - 1]
  have hKl : (VX H T x 7)[x.st.sp - 1]? = some (x.Kl.getD (x.st.sp - 1) 0) := by
    rw [VX_7]; exact intList_get x.Kl (x.st.sp - 1) (by rw [R.lK]; omega)
  have hKv : x.Kl.getD (x.st.sp - 1) 0 = (v : Int) := by rw [R.fK (x.st.sp - 1) (by omega), hv]
  have vV := d_stk (VX H T x) P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp] E.hnv (E.hty 7 (by omega)) (sp := x.st.sp)
    rfl hsM (by omega) _ hKl (by rw [hKv]; exact i32v v hvM)
  rw [hKv] at vV
  have dD := gSM_decl mv P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp] (VX H T x) i32 _ _ _ vV
    (conv_signed i32 rfl rfl _ (i32v v hvM))
  have q1 := (pexecM_prim mv fu (dV mv.nv) _ _).trans dD
  -- the test it[v] < head[v + 1]
  have hIv : (VX H T x 6)[v]? = some (x.Il.getD v 0) := by
    rw [VX_6]; exact intList_get x.Il v (by rw [R.lI]; exact hvn)
  have dIt := d_rdv mv (VX H T x) P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v] (k := 6) (j := 4) (x := v)
    (by omega) (E.hty 6 (by omega)) rfl hvM _ hIv (rd_valid R.vI (by rw [R.lI]; exact hvn))
  have hv1 : v + 1 < M31 := by have := E.hn1; omega
  have hHd : (VX H T x 0)[v + 1]? = some ((H.getD (v + 1) 0 : Nat) : Int) := by
    rw [VX_0]; exact vec_getM H (v + 1) (by have := E.HK.len; omega)
  have hvl := E.hd_le (v + 1) (by omega)
  have hTM := E.hTM
  have dHd : vdenM mv (VX H T x) (penvN mv.nv (gS P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v]))
      (.read i32 (.local 0) (idxV1 mv.nv)) = some ((H.getD (v + 1) 0 : Nat) : Int) :=
    rdM_val mv (VX H T x) _ 0 (by omega) i32 (E.hty 0 (by omega)).symm (idxV1 mv.nv) rfl rfl (v + 1)
      (den_cast_u64 _ _ (v + 1) (add1_den _ _ v (ev_cell mv P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v] (j := 4) rfl hvM)
        hv1) hv1) _ hHd (by rw [E.hty 0 (by omega)]; exact i32v _ (by omega))
  have hc := d_binb mv (VX H T x) P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp, ci v] (op := .lt) (a := rdv mv.nv 6 4)
    (b := .read i32 (.local 0) (idxV1 mv.nv)) rfl dIt dHd
  rw [bt_lt] at hc
  have hIv' : x.Il.getD v 0 = x.st.It v := (R.fI v).symm
  rw [hIv'] at hc
  by_cases hit : x.st.It v < ((H.getD (v + 1) 0 : Nat) : Int)
  · rw [if_pos hit] at hc
    obtain ⟨r1, x', h1, ret1, ps1, vv1, hso, c1, n1, w1⟩ := then_exec E G x I R P r hr hsp hv hit fu
    have br := pexecM_branch_true mv fu (cIt mv.nv) (THENB mv.nv) (POPB mv.nv) _ _ 1 hc (by decide) _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    have s3 := seqM_some q1 rfl s2
    have sc := scope_drop mv fu (WSC mv.nv) P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp]
      [ci n, ci x'.st.Vis.length, ci r, ci x'.st.sp] [ci v] (VX H T x) _ rfl s3 (by rw [ps1]; rfl)
    have s4 := seqM_some sc rfl (pexecM_skip mv fu _ _)
    refine ⟨_, x', s4, rfl, rfl, by rw [vv1], hso, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1]
      omega
    · simp
      omega
  · rw [if_neg hit] at hc
    have hit0 : x.st.It v = (H.getD (v + 1) 0 : Int) := by
      have : x.st.It v ≤ ((H.getD (v + 1) 0 : Nat) : Int) := hrng.2
      omega
    obtain ⟨r1, x', h1, ret1, ps1, vv1, hso, c1, n1, w1⟩ := pop_exec E x I R P r hr hsp hv hit0 fu
    have br := pexecM_branch_false mv fu (cIt mv.nv) (THENB mv.nv) (POPB mv.nv) _ _ hc _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    have s3 := seqM_some q1 rfl s2
    have sc := scope_drop mv fu (WSC mv.nv) P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp]
      [ci n, ci x'.st.Vis.length, ci r, ci x'.st.sp] [ci v] (VX H T x) _ rfl s3 (by rw [ps1]; rfl)
    have s4 := seqM_some sc rfl (pexecM_skip mv fu _ _)
    refine ⟨_, x', s4, rfl, rfl, by rw [vv1], hso, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1]
      omega
    · simp
      omega


theorem d_cSp_val {mv : MV} (vv : Nat → List Int) (P : List Cell) (n cnt r sp : Nat) (hsM : sp < M31) :
    vdenM mv vv (penvN mv.nv (gS P [ci n, ci cnt, ci r, ci sp])) (cSp mv.nv) = some (if (sp : Int) > 0 then 1 else 0) :=
  d_cSp vv P [ci n, ci cnt, ci r, ci sp] (y := sp) rfl hsM

/-- The loop `while (sp > 0) { ... }`. -/
theorem wloop_exec {mv : MV} {n : Nat} {H T : List Nat} (E : XE mv n H T) (G : GH n (hdF H) (tgF T)) (P : List Cell)
    (r : Nat) (hr : r < M31) :
    ∀ (k : Nat) (x : XS), MInv n (hdF H) (tgF T) x.st → LR n x → phi n (hdF H) x.st ≤ k → ∀ fu, k + 1 ≤ fu →
      ∃ (rr : PRM) (x' : XS), pexecM mv fu (WH mv.nv) (gS P [ci n, ci x.st.Vis.length, ci r, ci x.st.sp]) (VX H T x) =
          some rr ∧ rr.ret = none ∧ rr.ps = gS P [ci n, ci x'.st.Vis.length, ci r, ci x'.st.sp] ∧
        rr.vv = VX H T x' ∧ MInv n (hdF H) (tgF T) x'.st ∧ LR n x' ∧ x'.st.sp = 0 ∧ (∀ a ∈ x.st.Vis, a ∈ x'.st.Vis) ∧
        phi n (hdF H) x'.st ≤ phi n (hdF H) x.st ∧
        rr.cost + 1250 * phi n (hdF H) x'.st ≤ 1250 * phi n (hdF H) x.st + 30 ∧ rr.need ≤ P.length + 80 ∧
        rr.wk + 7 * phi n (hdF H) x'.st ≤ 7 * phi n (hdF H) x.st := by
  have hnv := E.hnv
  intro k
  induction k with
  | zero =>
    intro x I R hphi fu hfu
    have hsp0 : x.st.sp = 0 := by unfold phi at hphi; omega
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hsM : x.st.sp < M31 := by rw [hsp0]; unfold M31; omega
    have hc := d_cSp_val (mv := mv) (VX H T x) P n x.st.Vis.length r x.st.sp hsM
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, x, rfl, rfl, rfl, rfl, I, R, hsp0, fun a ha => ha, Nat.le_refl _, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      omega
    · simp [gS_size, vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp
  | succ k ih =>
    intro x I R hphi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hVl := I.vis_len_le
    have hsn := I.sp_le
    have hsM : x.st.sp < M31 := by have := E.hn1; unfold M31 at *; omega
    have hc := d_cSp_val (mv := mv) (VX H T x) P n x.st.Vis.length r x.st.sp hsM
    by_cases hsp : 0 < x.st.sp
    · rw [if_pos (by omega)] at hc
      obtain ⟨r1, x1, h1, ret1, ps1, vv1, hso, c1, n1, w1⟩ := wbody_exec E G x I R P r hr hsp (fu' + 1)
      have hphi1 := hso.phi
      obtain ⟨r2, x', h2, ret2, ps2, vv2, I2, R2, hsp2, hsub, hphi2, c2, n2, w2⟩ := ih x1 hso.inv hso.lr (by omega) fu'
        (by omega)
      rw [pexecM_while, hc]
      have h2' : pexecM mv fu' (WH mv.nv) r1.ps r1.vv = some r2 := by rw [ps1, vv1]; exact h2
      simp only [Bind.bind, Option.bind, if_neg (show (1 : Int) ≠ 0 by decide), h1, ret1, h2']
      refine ⟨_, x', rfl, ret2, ps2, vv2, I2, R2, hsp2, fun a ha => hsub a (hso.vis a ha), by omega, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
        omega
      · simp [gS_size, vwp, NExpr.nodes, NExpr.scalarOnly, ps1]
        omega
      · simp
        omega
    · have hsp0 : x.st.sp = 0 := by omega
      have hsM : x.st.sp < M31 := by rw [hsp0]; unfold M31; omega
      rw [if_neg (by omega)] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, x, rfl, rfl, rfl, rfl, I, R, hsp0, fun a ha => ha, Nat.le_refl _, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
        omega
      · simp [gS_size, vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp

end Proofs.LowlinkIter
