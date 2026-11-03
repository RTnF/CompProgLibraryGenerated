import Proofs.FindCycleLists

namespace Proofs.FindCycleExec
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
open Proofs.FindCycleLists

/-- `stk[sp - 1]` with `sp` in cell 4. -/
theorem d_stkF {mv : MV} (vv : Nat → List Int) (P cl : List Cell) (hnv : mv.nv = 6) (hty : mv.ty 4 = i32) {sp : Nat}
    (hj : cl[4]? = some (ci sp)) (hsp : sp < M31) (h1 : 1 ≤ sp) (y : Int) (hy : (vv 4)[sp - 1]? = some y)
    (hv : i32.valid y = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.read i32 (.local 4) (Proofs.FindCycleProg.idxTop mv.nv)) = some y := by
  have hidx : (Proofs.FindCycleProg.idxTop mv.nv).denote (penvN mv.nv (gS P cl)) = some ((sp - 1 : Nat) : Int) := by
    have : (Proofs.FindCycleProg.idxTop mv.nv) = NExpr.cast u64 (NExpr.binary i32 .sub (.variable i32 (mv.nv + 4))
      (.literal i32 1)) := rfl
    rw [this]
    refine den_cast_u64 _ _ _ ?_ (by omega)
    exact sub1_den _ (mv.nv + 4) sp (ev_cell mv P cl (j := 4) hj hsp) hsp h1
  exact rdM_val mv vv _ 4 (by omega) i32 hty.symm (Proofs.FindCycleProg.idxTop mv.nv) rfl rfl (sp - 1) hidx y hy
    (by rw [hty]; exact hv)

theorem d_cSpF {mv : MV} (vv : Nat → List Int) (P cl : List Cell) {y : Nat} (hj : cl[4]? = some (ci y)) (hy : y < M31) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (Proofs.FindCycleProg.cSp mv.nv) = some (if (y : Int) > 0 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  show (NExpr.binary bT .gt (.variable i32 (mv.nv + 4)) lit0).denote _ = _
  rw [den_binary, den_variable, ev_cell mv P cl (j := 4) hj hy, Option.bind_some, zero_den, Option.bind_some, bt_gt]


/-- The arrays after the push branch. -/
def pushLF (H : List Nat) (x : XF) (sp w : Nat) : XF :=
  { st := x.st, Cl := x.Cl.set w 1, Il := x.Il.set w (H.getD w 0 : Int), Kl := x.Kl.set sp (w : Int), Yl := x.Yl }

/-- The push branch: `state[w] = 1; it[w] = head[w]; stk[sp] = w; sp++;` -/
theorem pushT_execF (mv : MV) (hnv : mv.nv = 6) (hty : ∀ k, k < 6 → mv.ty k = i32) (H T : List Nat) (x : XF) {n : Nat}
    (hC : x.Cl.length = n) (hI : x.Il.length = n) (hK : x.Kl.length = n) (hHl : H.length = n + 1) (P : List Cell)
    (fsp fw r sp v e w : Nat) (hn : n < M31) (hn1 : n + 1 < M31) (hfsp : fsp < M31) (hfw : fw < M31) (hr : r < M31)
    (hsp : sp < n) (hvn : v < M31) (hwn : w < n) (hhd : H.getD w 0 < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Proofs.FindCycleProg.PUSHT mv.nv)
        (gS P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w]) (VXF H T x) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci fsp, ci fw, ci r, ci (sp + 1), ci v, ci e, ci w] ∧
      rr.vv = VXF H T (pushLF H x sp w) ∧ rr.cost ≤ 400 ∧ rr.need ≤ P.length + 100 ∧ rr.wk ≤ 3 := by
  have hwM : w < M31 := by omega
  have hsM : sp < M31 := by omega
  -- state[w] = 1
  have s1 := step_write mv fu P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] (VXF H T x) 2 7
    Proofs.FindCycleProg.one (by omega) (hty 2 (by omega)) (idx := w) rfl hwM 1 (d_one mv _ P _)
    (by rw [VXF_2, hC]; exact hwn) (by decide)
  obtain ⟨x1, hx1⟩ : ∃ x1 : XF, x1 = { x with Cl := x.Cl.set w 1 } := ⟨_, rfl⟩
  rw [VXF_2, VXF_w2, ← hx1] at s1
  -- it[w] = head[w]
  have hHw : (VXF H T x1 0)[w]? = some ((H.getD w 0 : Nat) : Int) := by
    rw [VXF_0]; exact vec_getM H w (by omega)
  have s2 := step_write mv fu P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] (VXF H T x1) 3 7
    (Proofs.FindCycleProg.rdv mv.nv 0 7) (by omega) (hty 3 (by omega)) (idx := w) rfl hwM ((H.getD w 0 : Nat) : Int)
    (d_rdv mv _ P _ (k := 0) (j := 7) (x := w) (by omega) (hty 0 (by omega)) rfl hwM _ hHw (i32v _ hhd))
    (by rw [VXF_3, hx1]; exact (by rw [hI]; exact hwn)) (i32v _ hhd)
  obtain ⟨x2, hx2⟩ : ∃ x2 : XF, x2 = { x1 with Il := x1.Il.set w (H.getD w 0 : Int) } := ⟨_, rfl⟩
  rw [VXF_3, VXF_w3, ← hx2] at s2
  -- stk[sp] = w
  have s3 := step_write mv fu P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] (VXF H T x2) 4 4
    (Proofs.FindCycleProg.vr mv.nv 7) (by omega) (hty 4 (by omega)) (idx := sp) rfl hsM (w : Int)
    (d_vr mv _ P _ (j := 7) (x := w) rfl hwM) (by rw [VXF_4, hx2, hx1]; exact (by rw [hK]; exact hsp)) (i32v w hwM)
  obtain ⟨x3, hx3⟩ : ∃ x3 : XF, x3 = { x2 with Kl := x2.Kl.set sp (w : Int) } := ⟨_, rfl⟩
  rw [VXF_4, VXF_w4, ← hx3] at s3
  -- sp = sp + 1
  have hs1 : sp + 1 < M31 := by omega
  have s4 := step_assign mv fu P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] (VXF H T x3) 4
    (.binary i32 .add (Proofs.FindCycleProg.vr mv.nv 4) Proofs.FindCycleProg.one) (y := sp) rfl hsM (sp + 1) hs1 (by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact add1_den _ _ sp (ev_cell mv P _ (j := 4) rfl hsM) hs1)
  have t4 := seqM_some s4 rfl (pexecM_skip mv fu _ _)
  have t3 := seqM_some s3 rfl t4
  have t2 := seqM_some s2 rfl t3
  have t1 := seqM_some s1 rfl t2
  have sc := scope_gS mv fu (Proofs.FindCycleProg.PUSHB mv.nv) P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w]
    [ci n, ci fsp, ci fw, ci r, ci (sp + 1), ci v, ci e, ci w] (VXF H T x) _ rfl t1 rfl
  have fin := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, fin, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show VXF H T x3 = _
    rw [hx3, hx2, hx1]
    rfl
  · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


/-- The found branch: `fsp = sp; fw = w; sp = 0;` -/
theorem found_execF (mv : MV) (hnv : mv.nv = 6) (vv : Nat → List Int) (P : List Cell) (n fsp fw r sp v e w : Nat)
    (hsp : sp < M31) (hwM : w < M31) (hfsp : fsp < M31) (hfw : fw < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Proofs.FindCycleProg.FND mv.nv) (gS P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w]) vv =
        some rr ∧ rr.ret = none ∧ rr.ps = gS P [ci n, ci sp, ci w, ci r, ci 0, ci v, ci e, ci w] ∧ rr.vv = vv ∧
      rr.cost ≤ 200 ∧ rr.need ≤ P.length + 100 ∧ rr.wk = 0 := by
  have s1 := step_assign mv fu P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] vv 1
    (Proofs.FindCycleProg.vr mv.nv 4) (y := fsp) rfl hfsp sp hsp (d_vr mv vv P _ (j := 4) (x := sp) rfl hsp)
  have s2 := step_assign mv fu P ([ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w].set 1 (ci sp)) vv 2
    (Proofs.FindCycleProg.vr mv.nv 7) (y := fw) rfl hfw w hwM (d_vr mv vv P _ (j := 7) (x := w) rfl hwM)
  have s3 := step_assign mv fu P (([ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w].set 1 (ci sp)).set 2 (ci w)) vv 4
    lit0 (y := sp) rfl hsp 0 (by unfold M31; omega) (d_zero mv vv P _)
  have t3 := seqM_some s3 rfl (pexecM_skip mv fu _ _)
  have t2 := seqM_some s2 rfl t3
  have t1 := seqM_some s1 rfl t2
  have sc := scope_gS mv fu (Proofs.FindCycleProg.FNB mv.nv) P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w]
    [ci n, ci sp, ci w, ci r, ci 0, ci v, ci e, ci w] vv _ rfl t1 rfl
  have fin := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, fin, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
  · simp [Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly, gS_size]
  · simp

theorem cGr_val {mv : MV} (hnv : mv.nv = 6) (hty : ∀ k, k < 6 → mv.ty k = i32) {H T : List Nat} {n : Nat}
    (vv : Nat → List Int) (P cl : List Cell) {w : Nat} (hw : cl[7]? = some (ci w)) (hwM : w < M31)
    (x : XF) (hvv : vv = VXF H T x) (hC : x.Cl.length = n) (hwn : w < n) (hvC : ∀ y ∈ x.Cl, i32.valid y = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (Proofs.FindCycleProg.cGr mv.nv) =
      some (if x.Cl.getD w 0 = 1 then 1 else 0) := by
  subst hvv
  have hCw : (VXF H T x 2)[w]? = some (x.Cl.getD w 0) := by
    rw [VXF_2]; exact intList_get x.Cl w (by rw [hC]; exact hwn)
  have dC := d_rdv mv (VXF H T x) P cl (k := 2) (j := 7) (x := w) (by omega) (hty 2 (by omega)) hw hwM _ hCw
    (rd_valid hvC (by rw [hC]; exact hwn))
  have hc := d_binb mv (VXF H T x) P cl (op := .eq) (a := Proofs.FindCycleProg.rdv mv.nv 2 7) (b := Proofs.FindCycleProg.one)
    rfl dC (d_one mv _ P _)
  rw [hc]
  exact eq_conv _ _


/-- `else { if (state[w] == 1) { fsp = sp; fw = w; sp = 0; } }` -/
theorem els_execF (mv : MV) (hnv : mv.nv = 6) (hty : ∀ k, k < 6 → mv.ty k = i32) (H T : List Nat) (x : XF) {n : Nat}
    (hC : x.Cl.length = n) (vC : ∀ y ∈ x.Cl, i32.valid y = true) (P : List Cell) (fsp fw r sp v e w : Nat)
    (hsp : sp < M31) (hwn : w < n) (hn : n < M31) (hfsp : fsp < M31) (hfw : fw < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Proofs.FindCycleProg.ELS mv.nv) (gS P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w])
        (VXF H T x) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P (if x.Cl.getD w 0 = 1 then [ci n, ci sp, ci w, ci r, ci 0, ci v, ci e, ci w]
        else [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w]) ∧ rr.vv = VXF H T x ∧
      rr.cost ≤ 300 ∧ rr.need ≤ P.length + 100 ∧ rr.wk = 0 := by
  have hwM : w < M31 := by omega
  have hc := cGr_val (H := H) (T := T) (n := n) hnv hty (mv := mv) (VXF H T x) P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w]
    (w := w) rfl hwM x rfl hC hwn vC
  by_cases hg : x.Cl.getD w 0 = 1
  · rw [if_pos hg] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := found_execF mv hnv (VXF H T x) P n fsp fw r sp v e w hsp hwM hfsp hfw fu
    have br := pexecM_branch_true mv fu (Proofs.FindCycleProg.cGr mv.nv) (Proofs.FindCycleProg.FND mv.nv) Sk _ _ 1 hc
      (by decide) _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    have sc := scope_gS mv fu (Proofs.FindCycleProg.ELB mv.nv) P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w]
      [ci n, ci sp, ci w, ci r, ci 0, ci v, ci e, ci w] (VXF H T x) _ rfl s2 (by rw [ps1])
    have fin := seqM_some sc rfl (pexecM_skip mv fu _ _)
    refine ⟨_, fin, rfl, by rw [if_pos hg], by rw [vv1], ?_, ?_, ?_⟩
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1]
      omega
    · simp
      omega
  · rw [if_neg hg] at hc
    have br := pexecM_branch_false mv fu (Proofs.FindCycleProg.cGr mv.nv) (Proofs.FindCycleProg.FND mv.nv) Sk _ _ hc _
      (pexecM_skip mv fu _ _)
    have s2 := seqM_some br rfl (pexecM_skip mv fu _ _)
    have sc := scope_gS mv fu (Proofs.FindCycleProg.ELB mv.nv) P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w]
      [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] (VXF H T x) _ rfl s2 rfl
    have fin := seqM_some sc rfl (pexecM_skip mv fu _ _)
    refine ⟨_, fin, rfl, by rw [if_neg hg], rfl, ?_, ?_, ?_⟩
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp


/-- `int e = it[v]; int w = target[e]; it[v] = e + 1;` followed by `REST`. -/
theorem thens_prefixF (mv : MV) (hnv : mv.nv = 6) (hty : ∀ k, k < 6 → mv.ty k = i32) (H T : List Nat) (x : XF)
    {n : Nat} (hI : x.Il.length = n) (vI : ∀ y ∈ x.Il, i32.valid y = true) (P : List Cell) (fsp fw r sp v e w : Nat)
    (hn : n < M31) (hvn : v < n) (hfsp : fsp < M31) (hfw : fw < M31) (hr : r < M31) (hsp : sp < M31)
    (he : x.Il.getD v 0 = (e : Int)) (heT : e < T.length) (hTM : T.length < M31) (hwn : T.getD e 0 = w) (hwl : w < n)
    (he1 : e + 1 < M31) (REST : Command) (r1 : PRM) (fu : Nat)
    (hR : pexecM mv fu REST (gS P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w])
      (VXF H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) = some r1) :
    ∃ rr : PRM, pexecM mv fu (.sequence (.primitive (Proofs.FindCycleProg.dE mv.nv))
        (.sequence (.primitive (Proofs.FindCycleProg.dW mv.nv))
        (.sequence (.primitive (Proofs.FindCycleProg.sIt1 mv.nv)) REST))) (gS P [ci n, ci fsp, ci fw, ci r, ci sp, ci v])
        (VXF H T x) = some rr ∧
      rr.ps = r1.ps ∧ rr.vv = r1.vv ∧ rr.ret = r1.ret ∧ rr.cost ≤ r1.cost + 150 ∧ rr.need ≤ max (P.length + 100) r1.need ∧
      rr.wk ≤ r1.wk + 1 := by
  have hvM : v < M31 := by omega
  have heM : e < M31 := by omega
  have hwM : w < M31 := by omega
  have hIv : (VXF H T x 3)[v]? = some (x.Il.getD v 0) := by
    rw [VXF_3]; exact intList_get x.Il v (by rw [hI]; exact hvn)
  have vE := d_rdv mv (VXF H T x) P [ci n, ci fsp, ci fw, ci r, ci sp, ci v] (k := 3) (j := 5) (x := v) (by omega)
    (hty 3 (by omega)) rfl hvM _ hIv (rd_valid vI (by rw [hI]; exact hvn))
  rw [he] at vE
  have dE' := gSM_decl mv P [ci n, ci fsp, ci fw, ci r, ci sp, ci v] (VXF H T x) i32 _ _ _ vE
    (conv_signed i32 rfl rfl _ (i32v e heM))
  have q1 := (pexecM_prim mv fu (Proofs.FindCycleProg.dE mv.nv) _ _).trans dE'
  have hTe : (VXF H T x 1)[e]? = some ((T.getD e 0 : Nat) : Int) := by
    rw [VXF_1]; exact vec_getM T e heT
  have vW := d_rdv mv (VXF H T x) P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e] (k := 1) (j := 6) (x := e) (by omega)
    (hty 1 (by omega)) rfl heM _ hTe (i32v _ (by omega))
  rw [hwn] at vW
  have dW' := gSM_decl mv P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e] (VXF H T x) i32 _ _ _ vW
    (conv_signed i32 rfl rfl _ (i32v w hwM))
  have q2 := (pexecM_prim mv fu (Proofs.FindCycleProg.dW mv.nv) _ _).trans dW'
  have s3 := step_write mv fu P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] (VXF H T x) 3 5
    (.binary i32 .add (Proofs.FindCycleProg.vr mv.nv 6) Proofs.FindCycleProg.one)
    (by omega) (hty 3 (by omega)) (idx := v) rfl hvM ((e + 1 : Nat) : Int) (by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact add1_den _ _ e (ev_cell mv P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] (j := 6) rfl heM) he1)
    (by rw [VXF_3, hI]; exact hvn) (i32v _ he1)
  rw [VXF_3, VXF_w3] at s3
  have t3 := seqM_some s3 rfl hR
  have t2 := seqM_some q2 rfl t3
  have t1 := seqM_some q1 rfl t2
  refine ⟨_, t1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
      NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    omega
  · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
      NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    omega
  · simp
    omega


/-- The cells after `THENS`. -/
def thenCells (n fsp fw r sp v e w : Nat) (c : Int) : List Cell :=
  if c = 0 then [ci n, ci fsp, ci fw, ci r, ci (sp + 1), ci v, ci e, ci w]
  else if c = 1 then [ci n, ci sp, ci w, ci r, ci 0, ci v, ci e, ci w]
  else [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w]

/-- The arrays after `THENS`. -/
def thenLF (H : List Nat) (x : XF) (sp v e w : Nat) : XF :=
  if x.Cl.getD w 0 = 0 then pushLF H { x with Il := x.Il.set v ((e + 1 : Nat) : Int) } sp w
  else { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }

theorem thens_execF (mv : MV) (hnv : mv.nv = 6) (hty : ∀ k, k < 6 → mv.ty k = i32) (H T : List Nat) (x : XF) {n : Nat}
    (hC : x.Cl.length = n) (hI : x.Il.length = n) (hK : x.Kl.length = n)
    (vC : ∀ y ∈ x.Cl, i32.valid y = true) (vI : ∀ y ∈ x.Il, i32.valid y = true) (hHl : H.length = n + 1)
    (P : List Cell) (fsp fw r sp v e w : Nat) (hn : n < M31) (hn1 : n + 1 < M31) (hfsp : fsp < M31) (hfw : fw < M31)
    (hr : r < M31) (hsp : sp < M31) (hpush : x.Cl.getD w 0 = 0 → sp < n) (hvn : v < n)
    (he : x.Il.getD v 0 = (e : Int)) (heT : e < T.length) (hTM : T.length < M31) (hwn : T.getD e 0 = w) (hwl : w < n)
    (he1 : e + 1 < M31) (hhd : H.getD w 0 < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Proofs.FindCycleProg.THENS mv.nv) (gS P [ci n, ci fsp, ci fw, ci r, ci sp, ci v])
        (VXF H T x) = some rr ∧ rr.ret = none ∧ rr.ps = gS P (thenCells n fsp fw r sp v e w (x.Cl.getD w 0)) ∧
      rr.vv = VXF H T (thenLF H x sp v e w) ∧ rr.cost ≤ 800 ∧ rr.need ≤ P.length + 100 ∧ rr.wk ≤ 4 := by
  have hwM : w < M31 := by omega
  have hsM : sp < M31 := hsp
  have hCw : (VXF H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) } 2)[w]? = some (x.Cl.getD w 0) := by
    rw [VXF_2]; exact intList_get x.Cl w (by rw [hC]; exact hwl)
  have dCw := d_rdv mv (VXF H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) P
    [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] (k := 2) (j := 7) (x := w) (by omega) (hty 2 (by omega)) rfl hwM _ hCw
    (rd_valid vC (by rw [hC]; exact hwl))
  have hc := d_binb mv (VXF H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) P
    [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w] (op := .eq) (a := Proofs.FindCycleProg.rdv mv.nv 2 7) (b := lit0)
    rfl dCw (d_zero mv _ P _)
  rw [eq_conv] at hc
  by_cases hwhite : x.Cl.getD w 0 = 0
  · rw [if_pos hwhite] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := pushT_execF mv hnv hty H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }
      (n := n) hC (by simp [hI]) hK hHl P fsp fw r sp v e w hn hn1 hfsp hfw hr (hpush hwhite) (by omega) hwl hhd fu
    have br := pexecM_branch_true mv fu (Proofs.FindCycleProg.cWh mv.nv) (Proofs.FindCycleProg.PUSHT mv.nv)
      (Proofs.FindCycleProg.ELS mv.nv) _ _ 1 hc (by decide) _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    obtain ⟨rS, hS, hSps, hSvv, hSret, hScost, hSneed, hSwk⟩ : ∃ rS : PRM, pexecM mv fu (.sequence (.branch (Proofs.FindCycleProg.cWh mv.nv)
        (Proofs.FindCycleProg.PUSHT mv.nv) (Proofs.FindCycleProg.ELS mv.nv)) Sk) (gS P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w])
        (VXF H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) = some rS ∧ rS.ps = r1.ps ∧ rS.vv = r1.vv ∧
        rS.ret = none ∧ rS.cost ≤ r1.cost + 20 ∧ rS.need ≤ P.length + 100 ∧ rS.wk ≤ r1.wk :=
      ⟨_, s2, rfl, rfl, rfl, by simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes],
        by simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1] at n1 ⊢; omega, by simp⟩
    obtain ⟨rr, hrr, hps, hvv, hret, hcost, hneed, hwk⟩ := thens_prefixF mv hnv hty H T x hI vI P fsp fw r sp v e w hn hvn hfsp hfw hr
      hsp he heT hTM hwn hwl he1 _ rS fu hS
    refine ⟨rr, hrr, by rw [hret, hSret], ?_, ?_, ?_, ?_, ?_⟩
    · rw [hps, hSps, ps1]; unfold thenCells; rw [if_pos hwhite]
    · rw [hvv, hSvv, vv1]; unfold thenLF; rw [if_pos hwhite]
    · omega
    · omega
    · omega
  · rw [if_neg hwhite] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := els_execF mv hnv hty H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }
      (n := n) hC vC P fsp fw r sp v e w hsp hwl hn hfsp hfw fu
    have br := pexecM_branch_false mv fu (Proofs.FindCycleProg.cWh mv.nv) (Proofs.FindCycleProg.PUSHT mv.nv)
      (Proofs.FindCycleProg.ELS mv.nv) _ _ hc _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    obtain ⟨rS, hS, hSps, hSvv, hSret, hScost, hSneed, hSwk⟩ : ∃ rS : PRM, pexecM mv fu (.sequence (.branch (Proofs.FindCycleProg.cWh mv.nv)
        (Proofs.FindCycleProg.PUSHT mv.nv) (Proofs.FindCycleProg.ELS mv.nv)) Sk) (gS P [ci n, ci fsp, ci fw, ci r, ci sp, ci v, ci e, ci w])
        (VXF H T { x with Il := x.Il.set v ((e + 1 : Nat) : Int) }) = some rS ∧ rS.ps = r1.ps ∧ rS.vv = r1.vv ∧
        rS.ret = none ∧ rS.cost ≤ r1.cost + 20 ∧ rS.need ≤ P.length + 100 ∧ rS.wk ≤ r1.wk :=
      ⟨_, s2, rfl, rfl, rfl, by simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes],
        by
          have hsz : r1.ps.mem.length + r1.ps.bs.length = P.length + 16 := by
            rw [ps1]; split <;> simp [gS_size]
          simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at n1 ⊢
          omega, by simp⟩
    obtain ⟨rr, hrr, hps, hvv, hret, hcost, hneed, hwk⟩ := thens_prefixF mv hnv hty H T x hI vI P fsp fw r sp v e w hn hvn hfsp hfw hr
      hsp he heT hTM hwn hwl he1 _ rS fu hS
    refine ⟨rr, hrr, by rw [hret, hSret], ?_, ?_, ?_, ?_, ?_⟩
    · rw [hps, hSps, ps1]; unfold thenCells
      by_cases h1' : x.Cl.getD w 0 = 1
      · rw [if_pos h1', if_neg hwhite]
      · rw [if_neg h1', if_neg hwhite]
    · rw [hvv, hSvv, vv1]; unfold thenLF; rw [if_neg hwhite]
    · omega
    · omega
    · omega

end Proofs.FindCycleExec
