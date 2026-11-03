import Proofs.FindCycleExtract
import Proofs.LowlinkProgExec
import Proofs.PrimExec

namespace Proofs.FindCycleProgExec
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
open Proofs.FindCycleExtract Proofs.FindCycleInv Proofs.FindCycleStep Proofs.FindCyclePhi Proofs.FindCycleSpec
open Proofs.LowlinkInv (AdjH)

/-- The initial state: nothing is visited. -/
def initFS (It : Nat → Int) : FS :=
  { C := fun _ => 0, It := It, Fi := fun _ => -1, Sk := fun _ => 0, sp := 0, nb := 0 }

theorem inv_initF (n : Nat) (hd tg : Nat → Nat) (It : Nat → Int) : FInv n hd tg (initFS It) := by
  refine ⟨fun a => Or.inl rfl, fun a h => absurd rfl h, fun i hi => by simp [initFS] at hi,
    fun a h => by simp [initFS] at h, fun i j hi => by simp [initFS] at hi, fun i hi => by simp [initFS] at hi,
    fun a h => absurd rfl h, fun a h => absurd rfl h, fun i hi => by simp [initFS] at hi,
    fun a h => by simp [initFS] at h, fun a h => by simp [initFS] at h⟩

theorem sum_const_one (n : Nat) : ((List.range n).map (fun _ => 1)).sum = n := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp

theorem phi0F {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (It : Nat → Int) :
    phiF n (hdF H) (initFS It) ≤ T.length + n := by
  have hz : H.getD 0 0 = 0 := E.HK.zero
  have hun : unscF n (hdF H) (initFS It) = T.length := by
    unfold unscF
    have : ∀ a ∈ List.range n, hdF H (a + 1) - itNF (hdF H) (initFS It) a = hdF H (a + 1) - hdF H a := by
      intro a _
      unfold itNF
      simp [initFS]
    rw [List.map_congr_left this]
    rw [Proofs.LowlinkProgExec.tele_sum (hdF H) n (fun a ha => E.HK.mono a ha)]
    show H.getD n 0 - H.getD 0 0 = _
    rw [E.HK.last, hz]
    simp
  have hw : whiteF n (initFS It) = n := by
    unfold whiteF
    have : ∀ a ∈ List.range n, (if (initFS It).C a = 0 then 1 else 0) = 1 := by
      intro a _; simp [initFS]
    rw [List.map_congr_left this, sum_const_one]
  unfold phiF
  show unscF n (hdF H) (initFS It) + whiteF n (initFS It) + 0 ≤ T.length + n
  rw [hun, hw]
  omega

/-- The invariant of the outer loop. -/
def OInv (n : Nat) (H T : List Nat) (Phi0 : Nat) (t : Nat) (vv : Nat → List Int) (C : List Cell) (pot : Nat) : Prop :=
  (∃ x : XF, FInv n (hdF H) (tgF T) x.st ∧ LRF n x ∧ x.st.sp = 0 ∧ (∀ a, a < t → x.st.C a ≠ 0) ∧
    phiF n (hdF H) x.st ≤ Phi0 ∧ vv = VXF H T x ∧ C = [ci n, ci 0, ci 0] ∧ pot = 4 * phiF n (hdF H) x.st) ∨
  (∃ (x : XF) (fsp fw : Nat), 0 < fsp ∧ FoundS n (hdF H) (tgF T) x fsp fw ∧ vv = VXF H T x ∧
    C = [ci n, ci fsp, ci fw] ∧ pot = 0)


set_option maxHeartbeats 8000000 in
theorem outer_stepF {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (G : FGH n (hdF H) (tgF T)) (Phi0 : Nat)
    (P : List Cell) (t : Nat) (vv : Nat → List Int) (C : List Cell) (pot : Nat) (fu : Nat) (ht : t < n)
    (hI : OInv n H T Phi0 t vv C pot) (hfu : Phi0 + 2 ≤ fu) :
    ∃ (r : PRM) (cs' C' : List Cell) (pot' : Nat), pexecM mv fu (Proofs.FindCycleProg.BO mv.nv) (gS P (C ++ [ci t])) vv =
        some r ∧ r.ret = none ∧ r.ps = gS P (C' ++ [ci t] ++ cs') ∧ C'.length = 3 ∧ C'[0]? = some (ci n) ∧
      OInv n H T Phi0 (t + 1) r.vv C' pot' ∧ r.cost + 340 * pot' ≤ 900 + 340 * pot ∧ r.need ≤ P.length + 100 ∧
      r.wk + pot' ≤ 4 + pot := by
  have hn : n < M31 := by have := E.hn1; omega
  rcases hI with ⟨x, Ix, Rx, hsp, hvis, hphi, rfl, rfl, rfl⟩ | ⟨x, fsp, fw, hpos, F, rfl, rfl, rfl⟩
  · have hf0 : (0 : Nat) < M31 := by unfold M31; omega
    obtain ⟨r1, x', fsp', fw', h1, ret1, ps1, vv1, hok, c1, n1, w1⟩ :=
      bo_execA E G x Ix Rx P 0 hf0 ht hsp fu (by omega)
    have hphi1 : ∀ (hp : phiF n (hdF H) x'.st ≤ phiF n (hdF H) x.st), True := fun _ => trivial
    refine ⟨r1, [], [ci n, ci fsp', ci fw'], ?_, h1, ret1, by rw [ps1]; rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact if fsp' = 0 then 4 * phiF n (hdF H) x'.st else 0
    · rcases hok.res with ⟨e1, e2, I2, R2, hsp2, hr2, hvis2, hphi2⟩ | ⟨hpos2, hF2⟩
      · left
        refine ⟨x', I2, R2, hsp2, fun a ha => ?_, by omega, vv1, ?_, ?_⟩
        · by_cases hat : a = t
          · subst hat; exact hr2
          · exact hvis2 a (hvis a (by omega))
        · rw [e1, e2]
        · rw [if_pos e1]
      · right
        refine ⟨x', fsp', fw', hpos2, hF2, vv1, rfl, ?_⟩
        rw [if_neg (by omega)]
    · by_cases hf : fsp' = 0
      · rcases hok.res with ⟨e1, e2, I2, R2, hsp2, hr2, hvis2, hphi2⟩ | ⟨hpos2, hF2⟩
        · rw [if_pos hf] at c1 ⊢
          omega
        · omega
      · rw [if_neg hf] at c1 ⊢
        omega
    · exact n1
    · by_cases hf : fsp' = 0
      · rcases hok.res with ⟨e1, e2, I2, R2, hsp2, hr2, hvis2, hphi2⟩ | ⟨hpos2, hF2⟩
        · rw [if_pos hf] at w1 ⊢
          omega
        · omega
      · rw [if_neg hf] at w1 ⊢
        omega
  · have hfM : fsp < M31 := by have := F.fnd.fsp_le; omega
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := bo_execB (mv := mv) (vv := VXF H T x) P n fsp fw t hpos hfM fu
    refine ⟨r1, [], [ci n, ci fsp, ci fw], 0, h1, ret1, by rw [ps1]; rfl, rfl, rfl, ?_, ?_, n1, ?_⟩
    · right
      exact ⟨x, fsp, fw, hpos, F, vv1, rfl, rfl⟩
    · omega
    · omega


theorem cGt_val {mv : MV} (vv : Nat → List Int) (P cl : List Cell) {f : Nat} (hf : cl[1]? = some (ci f)) (hfM : f < M31) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (Proofs.FindCycleProg.gtE (Proofs.FindCycleProg.vr mv.nv 1) lit0) =
      some (if (f : Int) > 0 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  show (NExpr.binary bT .gt (.variable i32 (mv.nv + 1)) lit0).denote _ = _
  rw [den_binary, den_variable, ev_cell mv P cl (j := 1) hf hfM, Option.bind_some, zero_den, Option.bind_some, bt_gt]

/-- The meaning of the output of `find_cycle`. -/
def FCOut (n : Nat) (hd tg : Nat → Nat) (Yl : List Int) (kk : Nat) : Prop :=
  (kk = 0 ∧ ∀ u w, AdjH hd tg u w → ¬ Proofs.PrimMath.Rtc (AdjH hd tg) w u) ∨ CycOut n hd tg Yl kk

set_option maxHeartbeats 16000000 in
/-- The whole body of `find_cycle`. -/
theorem prog_execF {mv : MV} {n : Nat} {H T : List Nat} (E : FE mv n H T) (G : FGH n (hdF H) (tgF T)) (x0 : XF)
    (I0 : FInv n (hdF H) (tgF T) x0.st) (R0 : LRF n x0) (hsp0 : x0.st.sp = 0) (hC0 : ∀ a, x0.st.C a = 0)
    (hphi0 : phiF n (hdF H) x0.st ≤ T.length + n) (P : List Cell) (fu : Nat) (hfu : 400 * n + T.length + n + 400 ≤ fu) :
    ∃ (rr : PRM) (x' : XF) (kk : Nat) (cl : List Cell), pexecM mv fu (Proofs.FindCycleProg.progFC mv.nv) (gS P [ci n])
        (VXF H T x0) = some rr ∧ rr.ret = some (kk : Int) ∧ rr.ps = gS P cl ∧ rr.vv = VXF H T x' ∧
      FCOut n (hdF H) (tgF T) x'.Yl kk ∧ kk < M31 ∧
      rr.cost ≤ 4000 * n + 1360 * T.length + 1360 * n + 3000 ∧ rr.need ≤ P.length + 100 ∧
      rr.wk ≤ 4 * n + 4 * T.length + 4 * n + n := by
  have hnv := E.hnv
  have hn : n < M31 := by have := E.hn1; omega
  have hn2 : n < 2147483647 := by have := E.hn1; unfold M31 at this; omega
  have hf0 : (0 : Nat) < M31 := by unfold M31; omega
  -- int fsp = 0; int fw = 0;
  have d1 := gSM_decl mv P [ci n] (VXF H T x0) i32 lit0 0 0 (d_zero mv _ P _) (conv_signed i32 rfl rfl _ (by decide))
  have q1 := (pexecM_prim mv fu (.declare i32 true lit0) _ _).trans d1
  have d2 := gSM_decl mv P [ci n, ci 0] (VXF H T x0) i32 lit0 0 0 (d_zero mv _ P _) (conv_signed i32 rfl rfl _ (by decide))
  have q2 := (pexecM_prim mv fu (.declare i32 true lit0) _ _).trans d2
  obtain ⟨res, C2, pot2, hres, hps, hC2p, hIn, hret, hcost, hneed, hwk⟩ := Proofs.PrimExec.for_stmt_runP mv P 3 0 n
    (by omega) hn2 (Proofs.FindCycleProg.BO mv.nv)
    (fun t vv C pot => OInv n H T (T.length + n) t vv C pot) 900 100 4 (T.length + n + 2) 340 (by omega)
    (by
      intro t vv C pot fu' ht hCp hC0' hI hfu'
      exact outer_stepF E G (T.length + n) P t vv C pot fu' ht hI (by omega))
    (VXF H T x0) [ci n, ci 0, ci 0] (4 * phiF n (hdF H) x0.st) rfl rfl
    (Or.inl ⟨x0, I0, R0, hsp0, fun a ha => by omega, hphi0, rfl, rfl, rfl⟩) fu (by omega)
  have hres' : pexecM mv fu (forStmtB mv.nv 3 0 (Proofs.FindCycleProg.BO mv.nv))
      (gS P ([ci n, ci 0] ++ [ci 0])) (VXF H T x0) = some res := hres
  -- int k = 0;
  have hl2 := hC2p
  rcases hIn with ⟨x, Ix, Rx, hspx, hvis, hphix, hvv, hC2, hpot⟩ | ⟨x, fsp, fw, hpos, F, hvv, hC2, hpot⟩
  · -- no cycle
    rw [hC2] at hps
    have dK := gSM_decl mv P [ci n, ci 0, ci 0] res.vv i32 lit0 0 0 (d_zero mv _ P _) (conv_signed i32 rfl rfl _ (by decide))
    have q4 := (pexecM_prim mv fu (.declare i32 true lit0) _ _).trans dK
    have hc := cGt_val (mv := mv) res.vv P [ci n, ci 0, ci 0, ci 0] (f := 0) rfl hf0
    rw [if_neg (by simp)] at hc
    have br := pexecM_branch_false mv fu (Proofs.FindCycleProg.gtE (Proofs.FindCycleProg.vr mv.nv 1) lit0)
      (Proofs.FindCycleProg.EXT mv.nv) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    have hk3 : vdenM mv res.vv (penvN mv.nv (gS P [ci n, ci 0, ci 0, ci 0])) (Proofs.FindCycleProg.vr mv.nv 3) = some ((0 : Nat) : Int) :=
      d_vr mv _ P _ (j := 3) (x := 0) rfl hf0
    have rt := pstmtM_ret_ok mv (gS P [ci n, ci 0, ci 0, ci 0]) res.vv (Proofs.FindCycleProg.vr mv.nv 3) ((0 : Nat) : Int) hk3
    have t_ret := seqM_ret (b := Sk) ((pexecM_prim mv fu (.ret (Proofs.FindCycleProg.vr mv.nv 3)) _ _).trans rt) rfl
    have t_br := seqM_some br rfl t_ret
    have t_dk := seqM_some q4 rfl t_br
    have hres2 : pexecM mv fu (forStmtB mv.nv 3 0 (Proofs.FindCycleProg.BO mv.nv)) (gS P [ci n, ci 0, ci 0]) (VXF H T x0) =
        some res := hres
    have t_for := seqM_some hres2 hret (by rw [hps]; exact t_dk)
    have t_2 := seqM_some q2 rfl t_for
    have t_1 := seqM_some q1 rfl t_2
    refine ⟨_, x, 0, [ci n, ci 0, ci 0, ci 0], t_1, rfl, rfl, by rw [← hvv], Or.inl ⟨rfl, ?_⟩, by unfold M31; omega, ?_, ?_, ?_⟩
    · exact acyclic_of_done (G := G) Ix hspx (fun a ha => hvis a ha) 
    · simp [Proofs.FindCycleProg.gtE, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
      omega
    · simp [Proofs.FindCycleProg.gtE, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, hps]
      omega
    · simp
      omega
  · -- a cycle was found
    rw [hC2] at hps
    have hfn := F.fnd.fsp_le
    have hfM : fsp < M31 := by omega
    have hfw : fw < M31 := by
      obtain ⟨j, hj, hjw⟩ := F.fnd.mem
      have := F.fnd.lt j hj
      rw [hjw] at this; omega
    have dK := gSM_decl mv P [ci n, ci fsp, ci fw] res.vv i32 lit0 0 0 (d_zero mv _ P _) (conv_signed i32 rfl rfl _ (by decide))
    have q4 := (pexecM_prim mv fu (.declare i32 true lit0) _ _).trans dK
    have hc := cGt_val (mv := mv) res.vv P [ci n, ci fsp, ci fw, ci 0] (f := fsp) rfl hfM
    rw [if_pos (by omega)] at hc
    rw [hvv] at hc
    obtain ⟨r1, j0, Yl', h1, ret1, hj0, hjw, ps1, vv1, hlY, hvY, hpre, c1, n1, w1⟩ :=
      ext_execF E x F P hfw fu (by omega)
    have br := pexecM_branch_true mv fu (Proofs.FindCycleProg.gtE (Proofs.FindCycleProg.vr mv.nv 1) lit0)
      (Proofs.FindCycleProg.EXT mv.nv) Sk _ _ 1 hc (by decide) _ h1
    have hkM : fsp - j0 < M31 := by omega
    have hk3 : vdenM mv (VXF H T { x with Yl := Yl' }) (penvN mv.nv (gS P [ci n, ci fsp, ci fw, ci (fsp - j0)]))
        (Proofs.FindCycleProg.vr mv.nv 3) = some ((fsp - j0 : Nat) : Int) :=
      d_vr mv _ P _ (j := 3) (x := fsp - j0) rfl hkM
    have rt := pstmtM_ret_ok mv (gS P [ci n, ci fsp, ci fw, ci (fsp - j0)]) (VXF H T { x with Yl := Yl' })
      (Proofs.FindCycleProg.vr mv.nv 3) ((fsp - j0 : Nat) : Int) hk3
    have t_ret := seqM_ret (b := Sk) ((pexecM_prim mv fu (.ret (Proofs.FindCycleProg.vr mv.nv 3)) _ _).trans rt) rfl
    have t_br := seqM_some br (by simpa using ret1) (by rw [ps1, vv1]; exact t_ret)
    have t_dk := seqM_some q4 rfl (by rw [hvv]; exact t_br)
    have hres2 : pexecM mv fu (forStmtB mv.nv 3 0 (Proofs.FindCycleProg.BO mv.nv)) (gS P [ci n, ci 0, ci 0]) (VXF H T x0) =
        some res := hres
    have t_for := seqM_some hres2 hret (by rw [hps]; exact t_dk)
    have t_2 := seqM_some q2 rfl t_for
    have t_1 := seqM_some q1 rfl t_2
    have hCyc : CycOut n (hdF H) (tgF T) Yl' (fsp - j0) :=
      cycout_of_found F.fnd hj0 hjw Yl' (fun t ht => by
        rw [hpre t ht, F.kl (j0 + t) (by omega)])
    refine ⟨_, { x with Yl := Yl' }, fsp - j0, [ci n, ci fsp, ci fw, ci (fsp - j0)], t_1, rfl, rfl, rfl, Or.inr hCyc, hkM, ?_, ?_, ?_⟩
    · simp [Proofs.FindCycleProg.gtE, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly]
      omega
    · simp [Proofs.FindCycleProg.gtE, Proofs.FindCycleProg.vr, vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, hps, ps1]
      omega
    · simp
      omega

end Proofs.FindCycleProgExec
