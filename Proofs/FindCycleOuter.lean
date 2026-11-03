import Proofs.FindCycleIter

namespace Proofs.FindCycleOuter
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
open Proofs.FindCycleLists Proofs.FindCycleExec Proofs.FindCycleOk Proofs.FindCycleIter
open Proofs.FindCycleInv Proofs.FindCycleStep Proofs.FindCyclePhi

/-- The result of searching from a new root. -/
structure RootOKF (n : Nat) (hd tg : Nat → Nat) (r : Nat) (fw : Nat) (x x' : XF) (fsp' fw' : Nat) : Prop where
  res : (fsp' = 0 ∧ fw' = fw ∧ FInv n hd tg x'.st ∧ LRF n x' ∧ x'.st.sp = 0 ∧ x'.st.C r ≠ 0 ∧ (∀ a, x.st.C a ≠ 0 → x'.st.C a ≠ 0) ∧
      phiF n hd x'.st ≤ phiF n hd x.st) ∨ (0 < fsp' ∧ FoundS n hd tg x' fsp' fw')

set_option maxHeartbeats 8000000 in
theorem r2b_execF {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (G : FGH n (hdF H) (tgF T)) (x : XF)
    (I : FInv n (hdF H) (tgF T) x.st) (R : LRF n x) (P : List Cell) (fw : Nat) (hfw : fw < M31) {r : Nat} (hrn : r < n)
    (hsp0 : x.st.sp = 0) (hrc : x.st.C r = 0) (fu : Nat) (hfu : phiF n (hdF H) x.st + 2 ≤ fu) :
    ∃ (rr : PRM) (x' : XF) (fsp' fw' : Nat), pexecM mv fu (Proofs.FindCycleProg.R2 mv.nv) (gS P [ci n, ci 0, ci fw, ci r])
        (VXF H T x) = some rr ∧ rr.ret = none ∧ rr.ps = gS P [ci n, ci fsp', ci fw', ci r] ∧ rr.vv = VXF H T x' ∧
      RootOKF n (hdF H) (tgF T) r fw x x' fsp' fw' ∧
      rr.cost + 1350 * (if fsp' = 0 then phiF n (hdF H) x'.st else 0) ≤ 1350 * phiF n (hdF H) x.st + 800 ∧
      rr.need ≤ P.length + 100 ∧ rr.wk + 4 * (if fsp' = 0 then phiF n (hdF H) x'.st else 0) ≤ 4 * phiF n (hdF H) x.st + 4 := by
  have hnv := E.hnv
  have hn : n < M31 := by have := E.hn1; omega
  have hrM : r < M31 := by omega
  have hTM := E.hTM
  have hHr : H.getD r 0 < M31 := by have := E.hd_le r (by omega); omega
  have hfsp0 : (0 : Nat) < M31 := by unfold M31; omega
  -- state[r] = 1
  have s1 := step_write mv fu P [ci n, ci 0, ci fw, ci r] (VXF H T x) 2 3 Proofs.FindCycleProg.one (by omega)
    (E.hty 2 (by omega)) (idx := r) rfl hrM 1 (d_one mv _ P _) (by rw [VXF_2, R.lC]; exact hrn) (by decide)
  rw [VXF_2, VXF_w2] at s1
  obtain ⟨x1, hx1⟩ : ∃ x1 : XF, x1 = { x with Cl := x.Cl.set r 1 } := ⟨_, rfl⟩
  rw [← hx1] at s1
  -- it[r] = head[r]
  have hHd : (VXF H T x1 0)[r]? = some ((H.getD r 0 : Nat) : Int) := by
    rw [VXF_0]; exact vec_getM H r (by have := E.HK.len; omega)
  have s2 := step_write mv fu P [ci n, ci 0, ci fw, ci r] (VXF H T x1) 3 3 (Proofs.FindCycleProg.rdv mv.nv 0 3) (by omega)
    (E.hty 3 (by omega)) (idx := r) rfl hrM ((H.getD r 0 : Nat) : Int)
    (d_rdv mv _ P _ (k := 0) (j := 3) (x := r) (by omega) (E.hty 0 (by omega)) rfl hrM _ hHd (i32v _ hHr))
    (by rw [VXF_3, hx1]; exact (by rw [R.lI]; exact hrn)) (i32v _ hHr)
  rw [VXF_3, VXF_w3] at s2
  obtain ⟨x2, hx2⟩ : ∃ x2 : XF, x2 = { x1 with Il := x1.Il.set r (H.getD r 0 : Int) } := ⟨_, rfl⟩
  rw [← hx2] at s2
  -- stk[0] = r
  have hi0 : vdenM mv (VXF H T x2) (penvN mv.nv (gS P [ci n, ci 0, ci fw, ci r])) (.cast u64 lit0) = some ((0 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact den_cast_u64 _ _ 0 (zero_den _) (by unfold M31; omega)
  have wr := pstmtM_write_ok mv (gS P [ci n, ci 0, ci fw, ci r]) (VXF H T x2) 4 (by omega) (.cast u64 lit0)
    (Proofs.FindCycleProg.vr mv.nv 3) (r : Int) 0 (d_vr mv _ P [ci n, ci 0, ci fw, ci r] (j := 3) (x := r) rfl hrM) hi0
    (by rw [VXF_4, hx2, hx1]; exact (by rw [R.lK]; omega)) (by rw [E.hty 4 (by omega)]; exact i32v r hrM)
  rw [E.hty 4 (by omega), VXF_4, VXF_w4] at wr
  obtain ⟨x3, hx3⟩ : ∃ x3 : XF, x3 = { x2 with Kl := x2.Kl.set 0 (r : Int) } := ⟨_, rfl⟩
  rw [← hx3] at wr
  have s3 := (pexecM_prim mv fu (Proofs.FindCycleProg.sStk0 mv.nv) _ _).trans wr
  -- int sp = 1
  have dS := gSM_decl mv P [ci n, ci 0, ci fw, ci r] (VXF H T x3) i32 Proofs.FindCycleProg.one 1 1
    (d_one mv _ P _) (conv_signed i32 rfl rfl _ (by decide))
  have s4 := (pexecM_prim mv fu Proofs.FindCycleProg.dSp _ _).trans dS
  -- the loop
  have hxr : VXF H T x3 = VXF H T (rootXF (hdF H) x r) := by
    apply VXF_congr <;> simp [hx3, hx2, hx1, rootXF]
  have hIr := inv_root G I hsp0 hrn hrc
  have hRr : LRF n (rootXF (hdF H) x r) := LRF_root (hdF H) R hrn (i32v r hrM) (i32v _ hHr)
  have hphir : phiF n (hdF H) (rootXF (hdF H) x r).st ≤ phiF n (hdF H) x.st := phiF_root n (hdF H) x.st r hrn hrc hsp0
  obtain ⟨r5, x', fsp', fw', h5, ret5, ps5, vv5, hsp5, hres, n5⟩ := wloop_execF E G P 0 fw r hfsp0 hfw hrM
    (phiF n (hdF H) (rootXF (hdF H) x r).st) (rootXF (hdF H) x r) hIr hRr (Nat.le_refl _) fu (by omega)
  have h5' : pexecM mv fu (Proofs.FindCycleProg.WH mv.nv) (gS P ([ci n, ci 0, ci fw, ci r] ++ [(⟨i32, 1⟩ : Cell)]))
      (VXF H T x3) = some r5 := by
    rw [hxr]; exact h5
  have t5 := seqM_some h5' ret5 (pexecM_skip mv fu _ _)
  have t4 := seqM_some s4 rfl t5
  have t3 := seqM_some s3 rfl t4
  have t2 := seqM_some s2 rfl t3
  have t1 := seqM_some s1 rfl t2
  have sc := scope_drop mv fu (Proofs.FindCycleProg.R2B mv.nv) P [ci n, ci 0, ci fw, ci r] [ci n, ci fsp', ci fw', ci r]
    [ci x'.st.sp] (VXF H T x) _ rfl t1 (by rw [ps5]; rfl)
  have t6 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  have hrC : (rootXF (hdF H) x r).st.C r ≠ 0 := by
    show (fRoot (hdF H) x.st r).C r ≠ 0
    rw [show (fRoot (hdF H) x.st r).C r = 1 from Proofs.LowlinkInv.upd_same _ _ _]; omega
  have hvisr : ∀ a, x.st.C a ≠ 0 → (rootXF (hdF H) x r).st.C a ≠ 0 := by
    intro a ha
    have har : a ≠ r := by intro e; subst e; omega
    show (fRoot (hdF H) x.st r).C a ≠ 0
    rw [show (fRoot (hdF H) x.st r).C a = x.st.C a from Proofs.LowlinkInv.upd_ne _ _ _ _ har]; exact ha
  rcases hres with ⟨e1, e2, I2, R2, hvis2, hphi2, c2, w2⟩ | ⟨hpos2, hF2, c2, w2⟩
  · refine ⟨_, x', fsp', fw', t6, rfl, rfl, by rw [vv5], ⟨Or.inl ⟨by omega, e2, I2, R2, hsp5, hvis2 r hrC,
      fun a ha => hvis2 a (hvisr a ha), by omega⟩⟩, ?_, ?_, ?_⟩
    · rw [if_pos (by omega)]
      simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps5]
      omega
    · rw [if_pos (by omega)]
      simp
      omega
  · refine ⟨_, x', fsp', fw', t6, rfl, rfl, by rw [vv5], ⟨Or.inr ⟨hpos2, hF2⟩⟩, ?_, ?_, ?_⟩
    · rw [if_neg (by omega)]
      simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps5]
      omega
    · rw [if_neg (by omega)]
      simp
      omega


theorem cF0_val {mv : MV} (vv : Nat → List Int) (P cl : List Cell) {f : Nat} (hf : cl[1]? = some (ci f)) (hfM : f < M31) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (Proofs.FindCycleProg.cF0 mv.nv) = some (if (f : Int) = 0 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  show (NExpr.binary bT .eq (.variable i32 (mv.nv + 1)) lit0).denote _ = _
  rw [den_binary, den_variable, ev_cell mv P cl (j := 1) hf hfM, Option.bind_some, zero_den, Option.bind_some, eq_conv]

set_option maxHeartbeats 8000000 in
/-- `if (fsp == 0) { if (state[r] == 0) { ... } }` with `fsp == 0`: one round of the outer loop. -/
theorem bo_execA {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (G : FGH n (hdF H) (tgF T)) (x : XF)
    (I : FInv n (hdF H) (tgF T) x.st) (R : LRF n x) (P : List Cell) (fw : Nat) (hfw : fw < M31) {r : Nat} (hrn : r < n)
    (hsp0 : x.st.sp = 0) (fu : Nat) (hfu : phiF n (hdF H) x.st + 2 ≤ fu) :
    ∃ (rr : PRM) (x' : XF) (fsp' fw' : Nat), pexecM mv fu (Proofs.FindCycleProg.BO mv.nv) (gS P [ci n, ci 0, ci fw, ci r])
        (VXF H T x) = some rr ∧ rr.ret = none ∧ rr.ps = gS P [ci n, ci fsp', ci fw', ci r] ∧ rr.vv = VXF H T x' ∧
      RootOKF n (hdF H) (tgF T) r fw x x' fsp' fw' ∧
      rr.cost + 1350 * (if fsp' = 0 then phiF n (hdF H) x'.st else 0) ≤ 1350 * phiF n (hdF H) x.st + 900 ∧
      rr.need ≤ P.length + 100 ∧ rr.wk + 4 * (if fsp' = 0 then phiF n (hdF H) x'.st else 0) ≤ 4 * phiF n (hdF H) x.st + 4 := by
  have hnv := E.hnv
  have hn : n < M31 := by have := E.hn1; omega
  have hrM : r < M31 := by omega
  have hf0 : (0 : Nat) < M31 := by unfold M31; omega
  have hc0 := cF0_val (mv := mv) (VXF H T x) P [ci n, ci 0, ci fw, ci r] (f := 0) rfl hf0
  rw [if_pos (by simp)] at hc0
  have hCr : (VXF H T x 2)[r]? = some (x.Cl.getD r 0) := by
    rw [VXF_2]; exact intList_get x.Cl r (by rw [R.lC]; exact hrn)
  have dCr := d_rdv mv (VXF H T x) P [ci n, ci 0, ci fw, ci r] (k := 2) (j := 3) (x := r) (by omega) (E.hty 2 (by omega))
    rfl hrM _ hCr (rd_valid R.vC (by rw [R.lC]; exact hrn))
  have hcs := d_binb mv (VXF H T x) P [ci n, ci 0, ci fw, ci r] (op := .eq) (a := Proofs.FindCycleProg.rdv mv.nv 2 3) (b := lit0)
    rfl dCr (d_zero mv _ P _)
  rw [eq_conv] at hcs
  have hCeq : x.st.C r = x.Cl.getD r 0 := R.fC r
  by_cases hwhite : x.Cl.getD r 0 = 0
  · rw [if_pos hwhite] at hcs
    have hrc : x.st.C r = 0 := by rw [hCeq]; exact hwhite
    obtain ⟨r1, x', fsp', fw', h1, ret1, ps1, vv1, hok, c1, n1, w1⟩ := r2b_execF E G x I R P fw hfw hrn hsp0 hrc fu hfu
    have br2 := pexecM_branch_true mv fu (Proofs.FindCycleProg.cSt0 mv.nv) (Proofs.FindCycleProg.R2 mv.nv) Sk _ _ 1 hcs
      (by decide) _ h1
    have s2 := seqM_some br2 (by simpa using ret1) (pexecM_skip mv fu _ _)
    have sc := scope_gS mv fu (Proofs.FindCycleProg.R1B mv.nv) P [ci n, ci 0, ci fw, ci r] [ci n, ci fsp', ci fw', ci r]
      (VXF H T x) _ rfl s2 (by rw [ps1])
    have s3 := seqM_some sc rfl (pexecM_skip mv fu _ _)
    have br1 := pexecM_branch_true mv fu (Proofs.FindCycleProg.cF0 mv.nv) (Proofs.FindCycleProg.R1 mv.nv) Sk _ _ 1 hc0
      (by decide) _ s3
    have s4 := seqM_some br1 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, x', fsp', fw', s4, rfl, by rw [ps1], by rw [vv1], hok, ?_, ?_, ?_⟩
    · by_cases hf : fsp' = 0
      · rw [if_pos hf] at c1 ⊢
        simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
          NExpr.nodes, NExpr.scalarOnly, Container.nodes]
        omega
      · rw [if_neg hf] at c1 ⊢
        simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
          NExpr.nodes, NExpr.scalarOnly, Container.nodes]
        omega
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1]
      omega
    · by_cases hf : fsp' = 0
      · rw [if_pos hf] at w1 ⊢
        simp
        omega
      · rw [if_neg hf] at w1 ⊢
        simp
        omega
  · rw [if_neg hwhite] at hcs
    have br2 := pexecM_branch_false mv fu (Proofs.FindCycleProg.cSt0 mv.nv) (Proofs.FindCycleProg.R2 mv.nv) Sk _ _ hcs _
      (pexecM_skip mv fu _ _)
    have s2 := seqM_some br2 rfl (pexecM_skip mv fu _ _)
    have sc := scope_gS mv fu (Proofs.FindCycleProg.R1B mv.nv) P [ci n, ci 0, ci fw, ci r] [ci n, ci 0, ci fw, ci r]
      (VXF H T x) _ rfl s2 rfl
    have s3 := seqM_some sc rfl (pexecM_skip mv fu _ _)
    have br1 := pexecM_branch_true mv fu (Proofs.FindCycleProg.cF0 mv.nv) (Proofs.FindCycleProg.R1 mv.nv) Sk _ _ 1 hc0
      (by decide) _ s3
    have s4 := seqM_some br1 rfl (pexecM_skip mv fu _ _)
    have hrc : x.st.C r ≠ 0 := by rw [hCeq]; exact hwhite
    refine ⟨_, x, 0, fw, s4, rfl, rfl, rfl, ⟨Or.inl ⟨rfl, rfl, I, R, hsp0, hrc, fun a ha => ha, Nat.le_refl _⟩⟩, ?_, ?_, ?_⟩
    · rw [if_pos rfl]
      simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · rw [if_pos rfl]
      simp

/-- With `fsp > 0` the round does nothing. -/
theorem bo_execB {mv : MV} {vv : Nat → List Int} (P : List Cell) (n fsp fw r : Nat) (hfsp : 0 < fsp) (hfM : fsp < M31)
    (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Proofs.FindCycleProg.BO mv.nv) (gS P [ci n, ci fsp, ci fw, ci r]) vv = some rr ∧
      rr.ret = none ∧ rr.ps = gS P [ci n, ci fsp, ci fw, ci r] ∧ rr.vv = vv ∧ rr.cost ≤ 20 ∧
      rr.need ≤ P.length + 100 ∧ rr.wk = 0 := by
  have hc0 := cF0_val (mv := mv) vv P [ci n, ci fsp, ci fw, ci r] (f := fsp) rfl hfM
  rw [if_neg (by omega)] at hc0
  have br1 := pexecM_branch_false mv fu (Proofs.FindCycleProg.cF0 mv.nv) (Proofs.FindCycleProg.R1 mv.nv) Sk _ _ hc0 _
    (pexecM_skip mv fu _ _)
  have s4 := seqM_some br1 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, s4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
  · simp [Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly, gS_size]
  · simp

end Proofs.FindCycleOuter
