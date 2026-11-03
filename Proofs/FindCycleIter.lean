import Proofs.FindCycleExec
import Proofs.FindCycleOk

namespace Proofs.FindCycleIter
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
open Proofs.FindCycleLists Proofs.FindCycleExec Proofs.FindCycleOk
open Proofs.FindCycleInv Proofs.FindCycleStep Proofs.FindCyclePhi

/-- The standing hypotheses of the loops. -/
structure FE (mv : MV) (n : Nat) (H T : List Nat) : Prop where
  hnv : mv.nv = 6
  hty : ∀ k, k < 6 → mv.ty k = i32
  hn1 : n + 1 < M31
  HK : Proofs.TopoSortMath.HeadOK H T n
  hTM : T.length < M31
  hTn : ∀ y ∈ T, y < n

theorem FE.hd_le {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (a : Nat) (ha : a ≤ n) :
    H.getD a 0 ≤ T.length := by
  have := E.HK.le H T n n (Nat.le_refl _) a ha
  rw [E.HK.last] at this
  exact this

theorem then_execF {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (G : FGH n (hdF H) (tgF T)) (x : XF)
    (I : FInv n (hdF H) (tgF T) x.st) (R : LRF n x) (P : List Cell) (fsp fw r : Nat) (hfsp : fsp < M31) (hfw : fw < M31)
    (hr : r < M31) (hsp : 0 < x.st.sp) {v : Nat} (hv : x.st.Sk (x.st.sp - 1) = v)
    (hit : x.st.It v < (H.getD (v + 1) 0 : Int)) (fu : Nat) :
    ∃ (rr : PRM) (x' : XF) (fsp' fw' : Nat), pexecM mv fu (Proofs.FindCycleProg.THENB mv.nv)
        (gS P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v]) (VXF H T x) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P [ci n, ci fsp', ci fw', ci r, ci x'.st.sp, ci v] ∧ rr.vv = VXF H T x' ∧
      ((fsp' = fsp ∧ fw' = fw ∧ FStepOK n (hdF H) (tgF T) x x') ∨
        (0 < fsp' ∧ FoundS n (hdF H) (tgF T) x' fsp' fw' ∧ x'.st.sp = 0)) ∧
      rr.cost ≤ 900 ∧ rr.need ≤ P.length + 100 ∧ rr.wk ≤ 4 := by
  have hnv := E.hnv
  have hvg := top_gray I hsp hv
  have hvn := I.c_lt v (by omega)
  have hrng := I.it_rng v (by omega)
  have hn : n < M31 := by have := E.hn1; omega
  have hTM := E.hTM
  have hn1 := E.hn1
  have hVl := I.sp_le
  have hsM : x.st.sp < M31 := by omega
  obtain ⟨e, he⟩ : ∃ e : Nat, x.st.It v = (e : Int) :=
    ⟨(x.st.It v).toNat, by have : (hdF H v : Int) ≤ x.st.It v := hrng.1; omega⟩
  have heh : e < H.getD (v + 1) 0 := by
    have : x.st.It v < ((H.getD (v + 1) 0 : Nat) : Int) := hit
    omega
  have hvl := E.hd_le (v + 1) (by omega)
  have heT : e < T.length := by omega
  have hwn : T.getD e 0 < n := E.hTn _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem heT]
    exact List.getElem_mem _)
  obtain ⟨w, hw⟩ : ∃ w, w = T.getD e 0 := ⟨_, rfl⟩
  have hwl : w < n := by rw [hw]; exact hwn
  have hq : (e : Int) = x.st.It v := he.symm
  have hitq : e < hdF H (v + 1) := heh
  have hwtg : tgF T e = w := hw.symm
  have he1 : e + 1 < M31 := by omega
  have hit1 : i32.valid (x.st.It v + 1) = true := by
    rw [i32_valid_iff]; unfold M31 at he1; constructor <;> omega
  have hhd : H.getD w 0 < M31 := by have := E.hd_le w (by omega); omega
  have hIl : x.Il.getD v 0 = (e : Int) := by rw [← R.fI v]; exact he
  have hCw : x.st.C w = x.Cl.getD w 0 := R.fC w
  obtain ⟨rr, hrr, hret, hps, hvv, hc, hnd, hwk⟩ := thens_execF mv hnv E.hty H T x R.lC R.lI R.lK R.vC R.vI E.HK.len P fsp fw r
    x.st.sp v e w hn hn1 hfsp hfw hr hsM (by
      intro hz
      have hwc : x.st.C w = 0 := by rw [hCw]; exact hz
      have hspn : x.st.sp < n := by
        have := I.c_rng w
        exact (by
          -- the stack and the white vertex w are distinct vertices below n
          have hnd : ((List.range x.st.sp).map x.st.Sk ++ [w]).Nodup := by
            rw [List.nodup_append]
            refine ⟨?_, by simp, ?_⟩
            · apply Proofs.PrimMath.nodup_map_inj List.nodup_range
              intro a ha b hb h
              exact I.sk_inj a b (List.mem_range.mp ha) (List.mem_range.mp hb) h
            · intro a ha b hb
              simp at hb
              subst hb
              obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
              have := I.sk_gray i (List.mem_range.mp hi)
              intro e; rw [e] at this; omega
          have hsub : ((List.range x.st.sp).map x.st.Sk ++ [w]) ⊆ List.range n := by
            intro a ha
            rcases List.mem_append.mp ha with h | h
            · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
              have := I.sk_gray i (List.mem_range.mp hi)
              exact List.mem_range.mpr (I.c_lt _ (by omega))
            · simp at h; subst h; exact List.mem_range.mpr hwl
          have := List.Nodup.length_le_of_subset hnd hsub
          simp at this
          omega)
      exact hspn) hvn hIl heT hTM hw.symm hwl he1 hhd fu
  have fin : ∀ (x' : XF) (fsp' fw' : Nat), VXF H T (thenLF H x x.st.sp v e w) = VXF H T x' →
      thenCells n fsp fw r x.st.sp v e w (x.Cl.getD w 0) =
        [ci n, ci fsp', ci fw', ci r, ci x'.st.sp, ci v, ci e, ci w] →
      ((fsp' = fsp ∧ fw' = fw ∧ FStepOK n (hdF H) (tgF T) x x') ∨
        (0 < fsp' ∧ FoundS n (hdF H) (tgF T) x' fsp' fw' ∧ x'.st.sp = 0)) →
      ∃ (rr : PRM) (x' : XF) (fsp' fw' : Nat), pexecM mv fu (Proofs.FindCycleProg.THENB mv.nv)
        (gS P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v]) (VXF H T x) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P [ci n, ci fsp', ci fw', ci r, ci x'.st.sp, ci v] ∧ rr.vv = VXF H T x' ∧
      ((fsp' = fsp ∧ fw' = fw ∧ FStepOK n (hdF H) (tgF T) x x') ∨
        (0 < fsp' ∧ FoundS n (hdF H) (tgF T) x' fsp' fw' ∧ x'.st.sp = 0)) ∧
      rr.cost ≤ 900 ∧ rr.need ≤ P.length + 100 ∧ rr.wk ≤ 4 := by
    intro x' fsp' fw' hvx hcells hdisj
    have sc := scope_drop mv fu (Proofs.FindCycleProg.THENS mv.nv) P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v]
      [ci n, ci fsp', ci fw', ci r, ci x'.st.sp, ci v] [ci e, ci w] (VXF H T x) rr rfl hrr (by rw [hps, hcells]; rfl)
    have s2 := seqM_some sc (by simpa using hret) (pexecM_skip mv fu _ _)
    refine ⟨_, x', fsp', fw', s2, rfl, rfl, by show rr.vv = _; rw [hvv, hvx], hdisj, ?_, ?_, ?_⟩
    · simp; omega
    · simp [gS_size]; omega
    · simp; omega
  by_cases hc0 : x.Cl.getD w 0 = 0
  · have hwc : x.st.C w = 0 := by rw [hCw]; exact hc0
    have hso := step_pushF G I R hsp hv hq hitq hwtg hwc hn hit1 hhd
    refine fin (pushXF (hdF H) x v w) fsp fw ?_ ?_ (Or.inl ⟨rfl, rfl, hso⟩)
    · apply VXF_congr
      · unfold thenLF pushLF; rw [if_pos hc0]; rfl
      · unfold thenLF pushLF; rw [if_pos hc0]; simp only [pushXF]; rw [he]; push_cast; rfl
      · unfold thenLF pushLF; rw [if_pos hc0]; rfl
      · unfold thenLF pushLF; rw [if_pos hc0]; rfl
    · unfold thenCells; rw [if_pos hc0]; rfl
  · by_cases hc1 : x.Cl.getD w 0 = 1
    · have hwg : x.st.C w = 1 := by rw [hCw]; exact hc1
      have hF := found_ofF I R hsp hv hq hitq hwtg hwg hvn hit1
      refine fin (foundXF x v) x.st.sp w ?_ ?_ (Or.inr ⟨by omega, hF, rfl⟩)
      · apply VXF_congr
        · unfold thenLF; rw [if_neg hc0]; rfl
        · unfold thenLF; rw [if_neg hc0]; simp only [foundXF]; rw [he]; push_cast; rfl
        · unfold thenLF; rw [if_neg hc0]; rfl
        · unfold thenLF; rw [if_neg hc0]; rfl
      · unfold thenCells; rw [if_neg hc0, if_pos hc1]; rfl
    · have hwb : x.st.C w = 2 := by
        rw [hCw]
        rcases I.c_rng w with h | h | h
        · rw [hCw] at h; exact absurd h hc0
        · rw [hCw] at h; exact absurd h hc1
        · rw [hCw] at h; exact h
      have hso := step_skipF G I R hsp hv hq hitq hwtg hwb hit1
      refine fin (skipXF x v) fsp fw ?_ ?_ (Or.inl ⟨rfl, rfl, hso⟩)
      · apply VXF_congr
        · unfold thenLF; rw [if_neg hc0]; rfl
        · unfold thenLF; rw [if_neg hc0]; simp only [skipXF]; rw [he]; push_cast; rfl
        · unfold thenLF; rw [if_neg hc0]; rfl
        · unfold thenLF; rw [if_neg hc0]; rfl
      · unfold thenCells; rw [if_neg hc0, if_neg hc1]; rfl


theorem d_two {mv : MV} (vv : Nat → List Int) (P cl : List Cell) :
    vdenM mv vv (penvN mv.nv (gS P cl)) Proofs.FindCycleProg.two = some 2 := by
  rw [vdenM_scalar _ _ _ _ rfl]
  show (NExpr.literal i32 2).denote _ = some 2
  rw [den_literal, if_pos (show i32.valid 2 = true from rfl)]

theorem pop_execF {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (x : XF)
    (I : FInv n (hdF H) (tgF T) x.st) (R : LRF n x) (P : List Cell) (fsp fw r : Nat) (hfsp : fsp < M31)
    (hfw : fw < M31) (hr : r < M31) (hsp : 0 < x.st.sp) {v : Nat} (hv : x.st.Sk (x.st.sp - 1) = v)
    (hit : x.st.It v = (H.getD (v + 1) 0 : Int)) (fu : Nat) :
    ∃ (rr : PRM), pexecM mv fu (Proofs.FindCycleProg.POPB mv.nv)
        (gS P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v]) (VXF H T x) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P [ci n, ci fsp, ci fw, ci r, ci (popXF x v).st.sp, ci v] ∧ rr.vv = VXF H T (popXF x v) ∧
      FStepOK n (hdF H) (tgF T) x (popXF x v) ∧ rr.cost ≤ 400 ∧ rr.need ≤ P.length + 100 ∧ rr.wk ≤ 1 := by
  have hnv := E.hnv
  have hvg := top_gray I hsp hv
  have hvn := I.c_lt v (by omega)
  have hn : n < M31 := by have := E.hn1; omega
  have hVl := I.sp_le
  have hsM : x.st.sp < M31 := by omega
  have hvM : v < M31 := by omega
  have hso := step_popF I R hsp hv hit
  have s1 := step_write mv fu P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v] (VXF H T x) 2 5 Proofs.FindCycleProg.two
    (by omega) (E.hty 2 (by omega)) (idx := v) rfl hvM 2 (d_two _ P _) (by rw [VXF_2, R.lC]; exact hvn) (by decide)
  rw [VXF_2, VXF_w2] at s1
  have s2 := step_assign mv fu P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v]
    (VXF H T { x with Cl := x.Cl.set v 2 }) 4
    (.binary i32 .sub (Proofs.FindCycleProg.vr mv.nv 4) Proofs.FindCycleProg.one) (y := x.st.sp) rfl hsM (x.st.sp - 1)
    (by omega) (by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact sub1_den _ _ x.st.sp (ev_cell mv P _ (j := 4) rfl hsM) hsM (by omega))
  have t2 := seqM_some s2 rfl (pexecM_skip mv fu _ _)
  have t1 := seqM_some s1 rfl t2
  have sc := scope_gS mv fu (Proofs.FindCycleProg.POPS mv.nv) P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v]
    [ci n, ci fsp, ci fw, ci r, ci (popXF x v).st.sp, ci v] (VXF H T x) _ rfl t1 rfl
  have fin := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, fin, rfl, rfl, rfl, hso, ?_, ?_, ?_⟩
  · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.two, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv,
      Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.two, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv,
      Proofs.FindCycleProg.ixc, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


/-- One iteration of the loop `while (sp > 0)`. -/
theorem wbody_execF {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (G : FGH n (hdF H) (tgF T)) (x : XF)
    (I : FInv n (hdF H) (tgF T) x.st) (R : LRF n x) (P : List Cell) (fsp fw r : Nat) (hfsp : fsp < M31)
    (hfw : fw < M31) (hr : r < M31) (hsp : 0 < x.st.sp) (fu : Nat) :
    ∃ (rr : PRM) (x' : XF) (fsp' fw' : Nat), pexecM mv fu (Proofs.FindCycleProg.WBODY mv.nv)
        (gS P [ci n, ci fsp, ci fw, ci r, ci x.st.sp]) (VXF H T x) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P [ci n, ci fsp', ci fw', ci r, ci x'.st.sp] ∧ rr.vv = VXF H T x' ∧
      ((fsp' = fsp ∧ fw' = fw ∧ FStepOK n (hdF H) (tgF T) x x') ∨
        (0 < fsp' ∧ FoundS n (hdF H) (tgF T) x' fsp' fw' ∧ x'.st.sp = 0)) ∧
      rr.cost ≤ 1300 ∧ rr.need ≤ P.length + 100 ∧ rr.wk ≤ 4 := by
  have hnv := E.hnv
  have hn : n < M31 := by have := E.hn1; omega
  have hVl := I.sp_le
  have hsM : x.st.sp < M31 := by omega
  obtain ⟨v, hv⟩ : ∃ v, x.st.Sk (x.st.sp - 1) = v := ⟨_, rfl⟩
  have hvg := top_gray I hsp hv
  have hvn := I.c_lt v (by omega)
  have hrng := I.it_rng v (by omega)
  have hvM : v < M31 := by omega
  -- int v = stk[sp - 1]
  have hKl : (VXF H T x 4)[x.st.sp - 1]? = some (x.Kl.getD (x.st.sp - 1) 0) := by
    rw [VXF_4]; exact intList_get x.Kl (x.st.sp - 1) (by rw [R.lK]; omega)
  have hKv : x.Kl.getD (x.st.sp - 1) 0 = (v : Int) := by rw [R.fK (x.st.sp - 1) (by omega), hv]
  have vV := d_stkF (VXF H T x) P [ci n, ci fsp, ci fw, ci r, ci x.st.sp] hnv (E.hty 4 (by omega)) (sp := x.st.sp)
    rfl hsM (by omega) _ hKl (by rw [hKv]; exact i32v v hvM)
  rw [hKv] at vV
  have dD := gSM_decl mv P [ci n, ci fsp, ci fw, ci r, ci x.st.sp] (VXF H T x) i32 _ _ _ vV
    (conv_signed i32 rfl rfl _ (i32v v hvM))
  have q1 := (pexecM_prim mv fu (Proofs.FindCycleProg.dV mv.nv) _ _).trans dD
  -- the test it[v] < head[v + 1]
  have hIv : (VXF H T x 3)[v]? = some (x.Il.getD v 0) := by
    rw [VXF_3]; exact intList_get x.Il v (by rw [R.lI]; exact hvn)
  have dIt := d_rdv mv (VXF H T x) P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v] (k := 3) (j := 5) (x := v)
    (by omega) (E.hty 3 (by omega)) rfl hvM _ hIv (rd_valid R.vI (by rw [R.lI]; exact hvn))
  have hv1 : v + 1 < M31 := by have := E.hn1; omega
  have hHd : (VXF H T x 0)[v + 1]? = some ((H.getD (v + 1) 0 : Nat) : Int) := by
    rw [VXF_0]; exact vec_getM H (v + 1) (by have := E.HK.len; omega)
  have hvl := E.hd_le (v + 1) (by omega)
  have hTM := E.hTM
  have dHd : vdenM mv (VXF H T x) (penvN mv.nv (gS P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v]))
      (.read i32 (.local 0) (Proofs.FindCycleProg.idxV1 mv.nv)) = some ((H.getD (v + 1) 0 : Nat) : Int) :=
    rdM_val mv (VXF H T x) _ 0 (by omega) i32 (E.hty 0 (by omega)).symm (Proofs.FindCycleProg.idxV1 mv.nv) rfl rfl (v + 1)
      (den_cast_u64 _ _ (v + 1) (add1_den _ _ v (ev_cell mv P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v] (j := 5) rfl hvM)
        hv1) hv1) _ hHd (by rw [E.hty 0 (by omega)]; exact i32v _ (by omega))
  have hc := d_binb mv (VXF H T x) P [ci n, ci fsp, ci fw, ci r, ci x.st.sp, ci v] (op := .lt)
    (a := Proofs.FindCycleProg.rdv mv.nv 3 5) (b := .read i32 (.local 0) (Proofs.FindCycleProg.idxV1 mv.nv)) rfl dIt dHd
  rw [bt_lt] at hc
  have hIv' : x.Il.getD v 0 = x.st.It v := (R.fI v).symm
  rw [hIv'] at hc
  by_cases hit : x.st.It v < ((H.getD (v + 1) 0 : Nat) : Int)
  · rw [if_pos hit] at hc
    obtain ⟨r1, x', fsp', fw', h1, ret1, ps1, vv1, hdis, c1, n1, w1⟩ := then_execF E G x I R P fsp fw r hfsp hfw hr hsp hv hit fu
    have br := pexecM_branch_true mv fu (Proofs.FindCycleProg.cIt mv.nv) (Proofs.FindCycleProg.THENB mv.nv)
      (Proofs.FindCycleProg.POPB mv.nv) _ _ 1 hc (by decide) _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    have s3 := seqM_some q1 rfl s2
    have sc := scope_drop mv fu (Proofs.FindCycleProg.WSC mv.nv) P [ci n, ci fsp, ci fw, ci r, ci x.st.sp]
      [ci n, ci fsp', ci fw', ci r, ci x'.st.sp] [ci v] (VXF H T x) _ rfl s3 (by rw [ps1]; rfl)
    have s4 := seqM_some sc rfl (pexecM_skip mv fu _ _)
    refine ⟨_, x', fsp', fw', s4, rfl, rfl, by rw [vv1], hdis, ?_, ?_, ?_⟩
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1]
      omega
    · simp
      omega
  · rw [if_neg hit] at hc
    have hit0 : x.st.It v = (H.getD (v + 1) 0 : Int) := by
      have : x.st.It v ≤ ((H.getD (v + 1) 0 : Nat) : Int) := hrng.2
      omega
    obtain ⟨r1, h1, ret1, ps1, vv1, hso, c1, n1, w1⟩ := pop_execF E x I R P fsp fw r hfsp hfw hr hsp hv hit0 fu
    have br := pexecM_branch_false mv fu (Proofs.FindCycleProg.cIt mv.nv) (Proofs.FindCycleProg.THENB mv.nv)
      (Proofs.FindCycleProg.POPB mv.nv) _ _ hc _ h1
    have s2 := seqM_some br (by simpa using ret1) (pexecM_skip mv fu _ _)
    have s3 := seqM_some q1 rfl s2
    have sc := scope_drop mv fu (Proofs.FindCycleProg.WSC mv.nv) P [ci n, ci fsp, ci fw, ci r, ci x.st.sp]
      [ci n, ci fsp, ci fw, ci r, ci (popXF x v).st.sp] [ci v] (VXF H T x) _ rfl s3 (by rw [ps1]; rfl)
    have s4 := seqM_some sc rfl (pexecM_skip mv fu _ _)
    refine ⟨_, popXF x v, fsp, fw, s4, rfl, rfl, by rw [vv1], Or.inl ⟨rfl, rfl, hso⟩, ?_, ?_, ?_⟩
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      omega
    · simp [Proofs.FindCycleProg.one, Proofs.FindCycleProg.vr, Proofs.FindCycleProg.rdv, Proofs.FindCycleProg.ixc, vwp,
        NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, ps1]
      omega
    · simp
      omega


/-- The loop `while (sp > 0) { ... }`. -/
theorem wloop_execF {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (G : FGH n (hdF H) (tgF T)) (P : List Cell)
    (fsp fw r : Nat) (hfsp : fsp < M31) (hfw : fw < M31) (hr : r < M31) :
    ∀ (k : Nat) (x : XF), FInv n (hdF H) (tgF T) x.st → LRF n x → phiF n (hdF H) x.st ≤ k → ∀ fu, k + 1 ≤ fu →
      ∃ (rr : PRM) (x' : XF) (fsp' fw' : Nat), pexecM mv fu (Proofs.FindCycleProg.WH mv.nv)
          (gS P [ci n, ci fsp, ci fw, ci r, ci x.st.sp]) (VXF H T x) = some rr ∧ rr.ret = none ∧
        rr.ps = gS P [ci n, ci fsp', ci fw', ci r, ci x'.st.sp] ∧ rr.vv = VXF H T x' ∧ x'.st.sp = 0 ∧
        ((fsp' = fsp ∧ fw' = fw ∧ FInv n (hdF H) (tgF T) x'.st ∧ LRF n x' ∧ (∀ a, x.st.C a ≠ 0 → x'.st.C a ≠ 0) ∧
          phiF n (hdF H) x'.st ≤ phiF n (hdF H) x.st ∧
          rr.cost + 1350 * phiF n (hdF H) x'.st ≤ 1350 * phiF n (hdF H) x.st + 30 ∧
          rr.wk + 4 * phiF n (hdF H) x'.st ≤ 4 * phiF n (hdF H) x.st) ∨
        (0 < fsp' ∧ FoundS n (hdF H) (tgF T) x' fsp' fw' ∧ rr.cost ≤ 1350 * phiF n (hdF H) x.st + 30 ∧
          rr.wk ≤ 4 * phiF n (hdF H) x.st)) ∧ rr.need ≤ P.length + 100 := by
  have hnv := E.hnv
  intro k
  induction k with
  | zero =>
    intro x I R hphi fu hfu
    have hsp0 : x.st.sp = 0 := by unfold phiF at hphi; omega
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hsM : x.st.sp < M31 := by rw [hsp0]; unfold M31; omega
    have hc := d_cSpF (mv := mv) (VXF H T x) P [ci n, ci fsp, ci fw, ci r, ci x.st.sp] (y := x.st.sp) rfl hsM
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, x, fsp, fw, rfl, rfl, rfl, rfl, hsp0, Or.inl ⟨rfl, rfl, I, R, fun a ha => ha, Nat.le_refl _, ?_, ?_⟩, ?_⟩
    · simp [Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
      omega
    · simp
    · simp [gS_size, Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
  | succ k ih =>
    intro x I R hphi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hVl := I.sp_le
    have hn : n < M31 := by have := E.hn1; omega
    have hsM : x.st.sp < M31 := by omega
    have hc := d_cSpF (mv := mv) (VXF H T x) P [ci n, ci fsp, ci fw, ci r, ci x.st.sp] (y := x.st.sp) rfl hsM
    by_cases hsp : 0 < x.st.sp
    · rw [if_pos (by omega)] at hc
      obtain ⟨r1, x1, fsp1, fw1, h1, ret1, ps1, vv1, hdis, c1, n1, w1⟩ :=
        wbody_execF E G x I R P fsp fw r hfsp hfw hr hsp (fu' + 1)
      rcases hdis with ⟨hf1, hw1, hso⟩ | ⟨hpos, hF, hsp1⟩
      · subst hf1 hw1
        have hphi1 := hso.phi
        obtain ⟨r2, x', fsp', fw', h2, ret2, ps2, vv2, hsp2, hres, n2⟩ := ih x1 hso.inv hso.lr (by omega) fu' (by omega)
        rw [pexecM_while, hc]
        have h2' : pexecM mv fu' (Proofs.FindCycleProg.WH mv.nv) r1.ps r1.vv = some r2 := by rw [ps1, vv1]; exact h2
        simp only [Bind.bind, Option.bind, if_neg (show (1 : Int) ≠ 0 by decide), h1, ret1, h2']
        refine ⟨_, x', fsp', fw', rfl, ret2, ps2, vv2, hsp2, ?_, ?_⟩
        · rcases hres with ⟨e1, e2, I2, R2, hvis2, hphi2, c2, w2⟩ | ⟨hpos2, hF2, c2, w2⟩
          · refine Or.inl ⟨e1, e2, I2, R2, fun a ha => hvis2 a (hso.vis a ha), by omega, ?_, ?_⟩
            · simp [Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
              omega
            · simp
              omega
          · refine Or.inr ⟨hpos2, hF2, ?_, ?_⟩
            · simp [Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
              omega
            · simp
              omega
        · simp [gS_size, Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly, ps1]
          omega
      · -- a back arc: the loop ends
        have hsM1 : x1.st.sp < M31 := by rw [hsp1]; unfold M31; omega
        have hc1 := d_cSpF (mv := mv) (VXF H T x1) P [ci n, ci fsp1, ci fw1, ci r, ci x1.st.sp] (y := x1.st.sp) rfl hsM1
        rw [if_neg (by omega)] at hc1
        rw [pexecM_while, hc]
        have h2' : pexecM mv fu' (Proofs.FindCycleProg.WH mv.nv) r1.ps r1.vv =
            some ⟨gS P [ci n, ci fsp1, ci fw1, ci r, ci x1.st.sp], VXF H T x1, none, 4, P.length + 2 * 5 + 5, 0⟩ := by
          rw [ps1, vv1]
          obtain ⟨fu'', rfl⟩ : ∃ fu'', fu' = fu'' + 1 := ⟨fu' - 1, by omega⟩
          rw [pexecM_while, hc1]
          simp only [Bind.bind, Option.bind, ite_true]
          simp [gS_size, Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
        simp only [Bind.bind, Option.bind, if_neg (show (1 : Int) ≠ 0 by decide), h1, ret1, h2']
        have hphix : 1 ≤ phiF n (hdF H) x.st := by unfold phiF; omega
        refine ⟨_, x1, fsp1, fw1, rfl, rfl, rfl, rfl, hsp1, Or.inr ⟨hpos, hF, ?_, ?_⟩, ?_⟩
        · simp [Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
          omega
        · simp
          omega
        · simp [gS_size, Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly, ps1]
          omega
    · have hsp0 : x.st.sp = 0 := by omega
      have hsM : x.st.sp < M31 := by rw [hsp0]; unfold M31; omega
      rw [if_neg (by omega)] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, x, fsp, fw, rfl, rfl, rfl, rfl, hsp0, Or.inl ⟨rfl, rfl, I, R, fun a ha => ha, Nat.le_refl _, ?_, ?_⟩, ?_⟩
      · simp [Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
        omega
      · simp
      · simp [gS_size, Proofs.FindCycleProg.cSp, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]

end Proofs.FindCycleIter
