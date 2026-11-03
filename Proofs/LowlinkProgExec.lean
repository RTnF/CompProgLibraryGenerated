import Proofs.LowlinkOuter
import Proofs.PrimExec

namespace Proofs.LowlinkProgExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.DoublingNested (i32 u64)
open Proofs.PowModStep (Sk)
open Proofs.BellmanFordExec (M31)
open Proofs.VectorSumCall (conv_signed)
open Proofs.DijkstraScan
open Proofs.LowlinkProg Proofs.LowlinkLists Proofs.LowlinkExec Proofs.LowlinkIter Proofs.LowlinkOuter
open Proofs.LowlinkInv Proofs.LowlinkPhi Proofs.LowlinkFinal

theorem tele_sum (hd : Nat → Nat) (k : Nat) (hm : ∀ a, a < k → hd a ≤ hd (a + 1)) :
    ((List.range k).map (fun a => hd (a + 1) - hd a)).sum = hd k - hd 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih (fun a ha => hm a (by omega))]
    simp
    have h1 := hm k (by omega)
    have h2 : ∀ j, j ≤ k → hd 0 ≤ hd j := by
      intro j
      induction j with
      | zero => intro _; exact Nat.le_refl _
      | succ j ihj => intro hj; exact Nat.le_trans (ihj (by omega)) (hm j (by omega))
    have := h2 k (Nat.le_refl _)
    omega

theorem phi0_le {mv : MV} {n : Nat} {H T : List Nat} (E : XE mv n H T) (L It : Nat → Int) (Sk : Nat → Nat) :
    phi n (hdF H) (initS L It Sk) ≤ T.length + n := by
  have hz : H.getD 0 0 = 0 := E.HK.zero
  have hun : unsc n (hdF H) (initS L It Sk) = T.length := by
    unfold unsc
    have : ∀ a ∈ List.range n, hdF H (a + 1) - itN (hdF H) (initS L It Sk) a = hdF H (a + 1) - hdF H a := by
      intro a _
      unfold itN
      simp [initS]
    rw [List.map_congr_left this]
    rw [tele_sum (hdF H) n (fun a ha => E.HK.mono a ha)]
    show H.getD n 0 - H.getD 0 0 = _
    rw [E.HK.last, hz]
    simp
  unfold phi
  show unsc n (hdF H) (initS L It Sk) + (n - 0) + 0 ≤ T.length + n
  rw [hun]
  omega


set_option maxHeartbeats 8000000 in
/-- The whole body of `lowlink`. -/
theorem prog_exec {mv : MV} {n : Nat} {H T : List Nat} (E : XE mv n H T) (G : GH n (hdF H) (tgF T)) (x0 : XS)
    (I0 : MInv n (hdF H) (tgF T) x0.st) (R0 : LR n x0) (hsp0 : x0.st.sp = 0) (hV0 : x0.st.Vis = [])
    (hphi0 : phi n (hdF H) x0.st ≤ T.length + n) (P : List Cell) (fu : Nat) (hfu : T.length + 2 * n + 3 ≤ fu) :
    ∃ (rr : PRM) (x' : XS), pexecM mv fu (progLL mv.nv) (gS P [ci n]) (VX H T x0) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P [ci n, ci x'.st.Vis.length] ∧ rr.vv = VX H T x' ∧ MInv n (hdF H) (tgF T) x'.st ∧ LR n x' ∧
      x'.st.sp = 0 ∧ (∀ a, a < n → a ∈ x'.st.Vis) ∧ rr.cost ≤ 2670 * n + 1750 * T.length + 100 ∧
      rr.need ≤ P.length + 80 ∧ rr.wk ≤ 11 * n + 7 * T.length + 10 := by
  have hnv := E.hnv
  have hn : n < M31 := by have := E.hn1; omega
  have hn2 : n < 2147483647 := by have := E.hn1; unfold M31 at this; omega
  -- int cnt = 0
  have dC := gSM_decl mv P [ci n] (VX H T x0) i32 lit0 0 0 (d_zero mv _ P _) (conv_signed i32 rfl rfl _ (by decide))
  have q1 := (pexecM_prim mv fu (.declare i32 true lit0) _ _).trans dC
  have hl0 : x0.st.Vis.length = 0 := by rw [hV0]; rfl
  obtain ⟨res, C2, pot2, hres, hps, hC2, hIn, hret, hcost, hneed, hwk⟩ := Proofs.PrimExec.for_stmt_runP mv P 2 0 n (by omega) hn2
    (BOUT mv.nv)
    (fun t vv C pot => ∃ x : XS, MInv n (hdF H) (tgF T) x.st ∧ LR n x ∧ x.st.sp = 0 ∧ (∀ a, a < t → a ∈ x.st.Vis) ∧
      phi n (hdF H) x.st ≤ T.length + n ∧ vv = VX H T x ∧ C = [ci n, ci x.st.Vis.length] ∧ pot = 7 * phi n (hdF H) x.st)
    900 80 4 (T.length + n + 2) 250 (by omega)
    (by
      intro t vv C pot fu' ht hCp hC0 hI hfu'
      obtain ⟨x, Ix, Rx, hspx, hvisx, hphix, rfl, rfl, rfl⟩ := hI
      obtain ⟨rr, x', h1, ret1, ps1, vv1, hok, c1, n1, w1⟩ := bout_exec E G x Ix Rx P (r := t) ht hspx fu' (by omega)
      refine ⟨rr, [], [ci n, ci x'.st.Vis.length], 7 * phi n (hdF H) x'.st, h1, ret1, by rw [ps1]; rfl, rfl, rfl,
        ⟨x', hok.inv, hok.lr, hok.sp0, ?_, by omega, vv1, rfl, rfl⟩, ?_, n1, ?_⟩
      · intro a ha
        by_cases hat : a = t
        · subst hat; exact hok.mem
        · exact hok.vis a (hvisx a (by omega))
      · have := hok.phi
        omega
      · have := hok.phi
        omega)
    (VX H T x0) [ci n, ci x0.st.Vis.length] (7 * phi n (hdF H) x0.st) rfl rfl
    ⟨x0, I0, R0, hsp0, fun a ha => by omega, hphi0, rfl, rfl, rfl⟩ fu (by omega)
  obtain ⟨x', Ix, Rx, hspx, hvisx, hphix, hvvx, hC2x, hpot2⟩ := hIn
  rw [hl0] at hres
  have t2 := seqM_some hres hret (pexecM_skip mv fu _ _)
  have t1 := seqM_some q1 rfl t2
  refine ⟨_, x', t1, rfl, ?_, ?_, Ix, Rx, hspx, fun a ha => hvisx a ha, ?_, ?_, ?_⟩
  · show res.ps = _
    rw [hps, hC2x]
  · show res.vv = _
    exact hvvx
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, hps, hC2x]
    omega
  · simp
    omega

end Proofs.LowlinkProgExec
