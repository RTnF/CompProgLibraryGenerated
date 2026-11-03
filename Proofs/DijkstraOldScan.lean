import Proofs.ForLoopB
import Proofs.DijkstraMath
import Proofs.BellmanFordExec

namespace Proofs.DijkstraOldScan
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getM vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false cs)

/-! ### The program (nv = 5): cells 0 = n, 1 = inf, 2 = it, 3 = best, 4 = bd, 5 = v / start, 6 = cnt, 7 = d, 8 = w, 9 = nd -/

abbrev ix (nv c : Nat) : NExpr := .cast u64 (.variable i32 (nv + c))
abbrev lit1 : NExpr := .literal i32 1
abbrev lit0 : NExpr := .literal i32 0
abbrev idxSD (nv : Nat) : NExpr := .cast u64 (.binary i32 .add (.variable i32 (nv + 5)) (.variable i32 (nv + 7)))
-- scan loop
abbrev cDone (nv : Nat) : NExpr := .binary bT .eq (.read i32 (.local 4) (ix nv 5)) lit0
abbrev cLess (nv : Nat) : NExpr := .binary bT .lt (.read s64 (.local 3) (ix nv 5)) (.variable s64 (nv + 4))
abbrev aBd (nv : Nat) : NStmt := .assign (nv + 4) s64 (.read s64 (.local 3) (ix nv 5))
abbrev aBest (nv : Nat) : NStmt := .assign (nv + 3) i32 (.variable i32 (nv + 5))
abbrev Y2s (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (aBd nv)) (.sequence (.primitive (aBest nv)) Sk))) Sk
abbrev Y1s (nv : Nat) : Command := .sequence (.scope (.sequence (.branch (cLess nv) (Y2s nv) Sk) Sk)) Sk
abbrev Bs (nv : Nat) : Command := .sequence (.branch (cDone nv) (Y1s nv) Sk) Sk
-- relaxation loop
abbrev dW (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 1) (idxSD nv))
abbrev dNd (nv : Nat) : NStmt :=
  .declare s64 true (.binary s64 .add (.variable s64 (nv + 4)) (.read s64 (.local 2) (idxSD nv)))
abbrev cRel (nv : Nat) : NExpr := .binary bT .lt (.variable s64 (nv + 9)) (.read s64 (.local 3) (ix nv 8))
abbrev wDist (nv : Nat) : NStmt := .write (.local 3) s64 (ix nv 8) (.variable s64 (nv + 9))
abbrev Yr (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (wDist nv)) Sk)) Sk
abbrev Xr (nv : Nat) : Command := .sequence (.primitive (dW nv)) (.sequence (.primitive (dNd nv)) (.sequence (.branch (cRel nv) (Yr nv) Sk) Sk))
-- the vertex branch
abbrev wDone (nv : Nat) : NStmt := .write (.local 4) i32 (ix nv 3) lit1
abbrev dStart (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 0) (ix nv 3))
abbrev dCnt (nv : Nat) : NStmt :=
  .declare i32 true (.binary i32 .sub (.read i32 (.local 0) (.cast u64 (.binary i32 .add (.variable i32 (nv + 3)) lit1)))
    (.variable i32 (nv + 5)))
abbrev Zb (nv : Nat) : Command :=
  .sequence (.primitive (wDone nv)) (.sequence (.primitive (dStart nv)) (.sequence (.primitive (dCnt nv))
    (.sequence (forStmtB nv 7 6 (Xr nv)) Sk)))
abbrev cBest (nv : Nat) : NExpr := .binary bT .ge (.variable i32 (nv + 3)) lit0
abbrev BRb (nv : Nat) : Command := .branch (cBest nv) (.sequence (.scope (Zb nv)) Sk) Sk
abbrev dBest : NStmt := .declare i32 true (.unary i32 .neg lit1)
abbrev dBd (nv : Nat) : NStmt := .declare s64 true (.variable s64 (nv + 1))
abbrev Bo (nv : Nat) : Command :=
  .sequence (.primitive dBest) (.sequence (.primitive (dBd nv)) (.sequence (forStmtB nv 5 0 (Bs nv)) (.sequence (BRb nv) Sk)))
abbrev bodyDJ (nv : Nat) : Command := .sequence (forStmtB nv 2 0 (Bo nv)) Sk



theorem i32v (x : Nat) (h : x < M31) : i32.valid (x : Int) = true := validN x h

/-- The contents of the vectors `head`, `target`, `cost`, `dist`, `done`. -/
def VD (H T : List Nat) (C Dd : List Int) (Dn : List Nat) : Nat → List Int := fun k =>
  if k = 0 then H.map (fun x : Nat => (x : Int)) else if k = 1 then T.map (fun x : Nat => (x : Int))
  else if k = 2 then C else if k = 3 then Dd else if k = 4 then Dn.map (fun x : Nat => (x : Int)) else []

theorem VD_get0 (H T C Dd Dn) : VD H T C Dd Dn 0 = H.map (fun x : Nat => (x : Int)) := by simp [VD]
theorem VD_get1 (H T C Dd Dn) : VD H T C Dd Dn 1 = T.map (fun x : Nat => (x : Int)) := by simp [VD]
theorem VD_get2 (H T C Dd Dn) : VD H T C Dd Dn 2 = C := by simp [VD]
theorem VD_get3 (H T C Dd Dn) : VD H T C Dd Dn 3 = Dd := by simp [VD]
theorem VD_get4 (H T C Dd Dn) : VD H T C Dd Dn 4 = Dn.map (fun x : Nat => (x : Int)) := by simp [VD]

theorem VD_write3 (H T C Dd Dn) (x : List Int) : upd (VD H T C Dd Dn) 3 x = VD H T C x Dn := by
  funext k
  unfold upd VD
  by_cases h3 : k = 3
  · subst h3; simp
  · simp [h3]

theorem VD_write4 (H T C Dd Dn) (p x : Nat) :
    upd (VD H T C Dd Dn) 4 ((VD H T C Dd Dn 4).set p (x : Int)) = VD H T C Dd (Dn.set p x) := by
  funext k
  unfold upd VD
  by_cases h4 : k = 4
  · subst h4; simp [List.map_set]
  · simp [h4]

theorem natList_get (l : List Nat) (j : Nat) (h : j < l.length) :
    (l.map (fun x : Nat => (x : Int)))[j]? = some ((l.getD j 0 : Nat) : Int) := by
  simp [List.getElem?_map, h, List.getD_eq_getElem?_getD]

theorem intList_get (l : List Int) (j : Nat) (h : j < l.length) : l[j]? = some (l.getD j 0) := by
  simp [h, List.getD_eq_getElem?_getD]

theorem one_den (env : Nat → Ty → Option Int) : lit1.denote env = some 1 := by
  rw [den_literal, if_pos (show i32.valid 1 = true from rfl)]
theorem zero_den (env : Nat → Ty → Option Int) : lit0.denote env = some 0 := by
  rw [den_literal, if_pos (show i32.valid 0 = true from rfl)]

theorem eq_conv (x y : Int) : bT.convert (binaryValue .eq x y) = some (if x = y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem lt_conv (x y : Int) : bT.convert (binaryValue .lt x y) = some (if x < y then 1 else 0) := by
  by_cases h : x < y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem ge_conv (x y : Int) : bT.convert (binaryValue .ge x y) = some (if x ≥ y then 1 else 0) := by
  by_cases h : x ≥ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

/-- A `{ ... }` block that neither declares nor removes cells: the scope leaves the state alone. -/
theorem scope_gS (mv : MV) (fu : Nat) (body : Command) (P cs cs' : List Cell) (vv : Nat → List Int) (r : PRM)
    (hl : cs.length = cs'.length) (hr : pexecM mv fu body (gS P cs) vv = some r) (hps : r.ps = gS P cs') :
    pexecM mv fu (.scope body) (gS P cs) vv = some ⟨gS P cs', r.vv, r.ret, r.cost + 1, r.need, r.wk⟩ := by
  have a := pexecM_scope mv fu body (gS P cs) vv r hr
  have tk := gS_takeC P cs cs' [] hl
  simp only [List.append_nil] at tk
  rw [hps, tk] at a
  exact a


/-- The value of the `best` cell: `-1` for "none". -/
def bI : Option Nat → Int
  | none => -1
  | some b => (b : Int)

abbrev cb (r : Option Nat) : Cell := ⟨i32, bI r⟩

/-- One step of the minimum scan, on the lists. -/
def scanStepL (Dn : List Nat) (Dd : List Int) (s : Option Nat × Int) (v : Nat) : Option Nat × Int :=
  if Dn.getD v 0 = 0 ∧ Dd.getD v 0 < s.2 then (some v, Dd.getD v 0) else s

theorem bI_valid (r : Option Nat) (h : ∀ b, r = some b → b < M31) : i32.valid (bI r) = true := by
  cases r with
  | none => show i32.valid (-1) = true; exact rfl
  | some b => exact i32v b (h b rfl)

set_option maxHeartbeats 8000000 in
/-- One iteration of the minimum scan. -/
theorem b_scan (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it v : Nat) (inf bd : Int) (r : Option Nat) (hn : n < M31) (hit : it < M31) (hv : v < n)
    (hDnl : Dn.length = n) (hDdl : Dd.length = n) (hdn : Dn.getD v 0 < M31) (hbd : s64.valid bd = true)
    (hinf : s64.valid inf = true) (hdv : s64.valid (Dd.getD v 0) = true) (hr : ∀ b, r = some b → b < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Bs mv.nv) (gS P [ci n, cs inf, ci it, cb r, cs bd, ci v]) (VD H T C Dd Dn) = some rr ∧
      rr.ret = none ∧
      rr.ps = gS P [ci n, cs inf, ci it, cb (scanStepL Dn Dd (r, bd) v).1, cs (scanStepL Dn Dd (r, bd) v).2, ci v] ∧
      rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 300 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 0 := by
  have hnM : n < 2147483648 := hn
  have E5 := envs mv P [ci n, cs inf, ci it, cb r, cs bd, ci v] 5 (ci v) rfl (i32v v (by omega))
  have vdone := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb r, cs bd, ci v])) 4 (by omega) i32
    (hty4).symm (ix mv.nv 5) rfl rfl v (cidx_den _ (mv.nv + 5) v E5 (by omega)) ((Dn.getD v 0 : Nat) : Int)
    (by rw [VD_get4]; exact natList_get Dn v (by omega)) (by rw [hty4]; exact i32v _ hdn)
  have vc : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb r, cs bd, ci v])) (cDone mv.nv) =
      some (if ((Dn.getD v 0 : Nat) : Int) = 0 then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdone, Option.bind_some, vdenM_scalar _ _ _ _ rfl, zero_den, Option.bind_some]
    exact eq_conv _ _
  by_cases h0 : Dn.getD v 0 = 0
  · have hc1 : (if ((Dn.getD v 0 : Nat) : Int) = 0 then (1 : Int) else 0) = 1 := by rw [h0]; simp
    rw [hc1] at vc
    have E4 := envs mv P [ci n, cs inf, ci it, cb r, cs bd, ci v] 4 (cs bd) rfl hbd
    have vdist := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb r, cs bd, ci v])) 3 (by omega) s64
      (hty3).symm (ix mv.nv 5) rfl rfl v (cidx_den _ (mv.nv + 5) v E5 (by omega)) (Dd.getD v 0)
      (by rw [VD_get3]; exact intList_get Dd v (by omega)) (by rw [hty3]; exact hdv)
    have vcl : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb r, cs bd, ci v])) (cLess mv.nv) =
        some (if Dd.getD v 0 < bd then 1 else 0) := by
      rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdist, Option.bind_some, vdenM_scalar _ _ _ _ rfl, den_variable, E4, Option.bind_some]
      exact lt_conv _ _
    by_cases hlt : Dd.getD v 0 < bd
    · have hc2 : (if Dd.getD v 0 < bd then (1 : Int) else 0) = 1 := by rw [if_pos hlt]
      rw [hc2] at vcl
      -- Y2s: bd = dist[v]; best = v
      have as1 := gSM_assign mv P [ci n, cs inf, ci it, cb r, cs bd, ci v] (VD H T C Dd Dn) 4 (by simp) s64 _ _ (Dd.getD v 0)
        vdist (cs bd) rfl rfl hbd (conv_signed s64 rfl rfl _ hdv)
      have a1 := (pexecM_prim mv fu (aBd mv.nv) _ _).trans as1
      have E5' := envs mv P [ci n, cs inf, ci it, cb r, cs (Dd.getD v 0), ci v] 5 (ci v) rfl (i32v v (by omega))
      have vv5 : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb r, cs (Dd.getD v 0), ci v]))
          (.variable i32 (mv.nv + 5)) = some (v : Int) := by
        rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E5'
      have as2 := gSM_assign mv P [ci n, cs inf, ci it, cb r, cs (Dd.getD v 0), ci v] (VD H T C Dd Dn) 3 (by simp) i32 _ _ (v : Int)
        vv5 (cb r) rfl rfl (bI_valid r hr) (conv_signed i32 rfl rfl _ (i32v v (by omega)))
      have a2 := (pexecM_prim mv fu (aBest mv.nv) _ _).trans as2
      have a3 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
      have a4 := seqM_some a1 rfl a3
      have a5 := scope_gS mv fu _ P [ci n, cs inf, ci it, cb r, cs bd, ci v]
        [ci n, cs inf, ci it, cb (some v), cs (Dd.getD v 0), ci v] (VD H T C Dd Dn) _ (by simp) a4 rfl
      have a6 := seqM_some a5 rfl (pexecM_skip mv fu _ _)
      have b1 := pexecM_branch_true mv fu (cLess mv.nv) (Y2s mv.nv) Sk _ _ 1 vcl (by decide) _ a6
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      have b3 := scope_gS mv fu _ P [ci n, cs inf, ci it, cb r, cs bd, ci v]
        [ci n, cs inf, ci it, cb (some v), cs (Dd.getD v 0), ci v] (VD H T C Dd Dn) _ (by simp) b2 rfl
      have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
      have c1 := pexecM_branch_true mv fu (cDone mv.nv) (Y1s mv.nv) Sk _ _ 1 vc (by decide) _ b4
      have c2 := seqM_some c1 rfl (pexecM_skip mv fu _ _)
      have hst : scanStepL Dn Dd (r, bd) v = (some v, Dd.getD v 0) := by
        unfold scanStepL; rw [if_pos ⟨h0, hlt⟩]
      obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (Bs mv.nv)
          (gS P [ci n, cs inf, ci it, cb r, cs bd, ci v]) (VD H T C Dd Dn) = some rr ∧
          rr.ps = gS P [ci n, cs inf, ci it, cb (some v), cs (Dd.getD v 0), ci v] ∧ rr.ret = none ∧
          rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 300 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 0 :=
        ⟨_, c2, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size],
          by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size], by simp⟩
      refine ⟨rr, hrr, hret, ?_, hvv, hcost, hneed, hwk⟩
      rw [hst]
      exact hps
    · have hc2 : (if Dd.getD v 0 < bd then (1 : Int) else 0) = 0 := by rw [if_neg hlt]
      rw [hc2] at vcl
      have b1 := pexecM_branch_false mv fu (cLess mv.nv) (Y2s mv.nv) Sk _ _ vcl _ (pexecM_skip mv fu _ _)
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      have b3 := scope_gS mv fu _ P [ci n, cs inf, ci it, cb r, cs bd, ci v]
        [ci n, cs inf, ci it, cb r, cs bd, ci v] (VD H T C Dd Dn) _ rfl b2 rfl
      have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
      have c1 := pexecM_branch_true mv fu (cDone mv.nv) (Y1s mv.nv) Sk _ _ 1 vc (by decide) _ b4
      have c2 := seqM_some c1 rfl (pexecM_skip mv fu _ _)
      have hst : scanStepL Dn Dd (r, bd) v = (r, bd) := by
        unfold scanStepL; rw [if_neg (fun h => hlt h.2)]
      refine ⟨_, c2, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · rw [hst]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp
  · have hc0 : (if ((Dn.getD v 0 : Nat) : Int) = 0 then (1 : Int) else 0) = 0 := by
      have : ((Dn.getD v 0 : Nat) : Int) ≠ 0 := by omega
      rw [if_neg this]
    rw [hc0] at vc
    have b1 := pexecM_branch_false mv fu (cDone mv.nv) (Y1s mv.nv) Sk _ _ vc _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have hst : scanStepL Dn Dd (r, bd) v = (r, bd) := by
      unfold scanStepL; rw [if_neg (fun h => h0 h.1)]
    refine ⟨_, b2, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · rw [hst]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp


/-- The state of the minimum scan after the first `t` vertices. -/
def scanSt (inf : Int) (Dn : List Nat) (Dd : List Int) (t : Nat) : Option Nat × Int :=
  (List.range t).foldl (scanStepL Dn Dd) (none, inf)

theorem scanSt_succ (inf : Int) (Dn : List Nat) (Dd : List Int) (t : Nat) :
    scanSt inf Dn Dd (t + 1) = scanStepL Dn Dd (scanSt inf Dn Dd t) t := by
  unfold scanSt
  rw [List.range_succ, List.foldl_append]
  rfl

theorem scanSt_shape (inf : Int) (Dn : List Nat) (Dd : List Int) :
    ∀ t, ((scanSt inf Dn Dd t).1 = none → (scanSt inf Dn Dd t).2 = inf) ∧
      ∀ b, (scanSt inf Dn Dd t).1 = some b → b < t ∧ (scanSt inf Dn Dd t).2 = Dd.getD b 0 := by
  intro t
  induction t with
  | zero => exact ⟨fun _ => rfl, fun b hb => by simp [scanSt] at hb⟩
  | succ t ih =>
    rw [scanSt_succ]
    generalize hs : scanSt inf Dn Dd t = s at ih ⊢
    unfold scanStepL
    by_cases hg : Dn.getD t 0 = 0 ∧ Dd.getD t 0 < s.2
    · rw [if_pos hg]
      refine ⟨fun h => by simp at h, fun b hb => ?_⟩
      simp only [Option.some.injEq] at hb
      subst hb
      exact ⟨by omega, rfl⟩
    · rw [if_neg hg]
      refine ⟨ih.1, fun b hb => ?_⟩
      have := ih.2 b hb
      exact ⟨by omega, this.2⟩

set_option maxHeartbeats 8000000 in
/-- The scan loop `for (int v = 0; v < n; v++) {...}`. -/
theorem l_scan (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it : Nat) (inf : Int) (hn : n < M31) (hn2 : n < 2147483647) (hit : it < M31) (hDnl : Dn.length = n)
    (hDdl : Dd.length = n) (hDnv : ∀ j, Dn.getD j 0 < M31) (hDdv : ∀ j, s64.valid (Dd.getD j 0) = true)
    (hinf : s64.valid inf = true) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 5 0 (Bs mv.nv)) (gS P [ci n, cs inf, ci it, cb none, cs inf])
      (VD H T C Dd Dn) = some res ∧
      res.ps = gS P [ci n, cs inf, ci it, cb (scanSt inf Dn Dd n).1, cs (scanSt inf Dn Dd n).2] ∧
      res.vv = VD H T C Dd Dn ∧ res.ret = none ∧ res.cost ≤ 320 * n + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ 0 := by
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 5 0 n (by omega) hn2 (Bs mv.nv)
    (fun t vv Cl => vv = VD H T C Dd Dn ∧
      Cl = [ci n, cs inf, ci it, cb (scanSt inf Dn Dd t).1, cs (scanSt inf Dn Dd t).2]) 300 80 0 0 (by omega)
    (by
      intro t vv Cl fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hsh := scanSt_shape inf Dn Dd t
      have hbdv : s64.valid (scanSt inf Dn Dd t).2 = true := by
        rcases hr : (scanSt inf Dn Dd t).1 with _ | b
        · rw [hsh.1 hr]; exact hinf
        · rw [(hsh.2 b hr).2]; exact hDdv b
      have hrM : ∀ b, (scanSt inf Dn Dd t).1 = some b → b < M31 := by
        intro b hb
        have := (hsh.2 b hb).1
        have : t < n := ht
        have : n < M31 := hn
        omega
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := b_scan mv hnv hty0 hty1 hty2 hty3 hty4 H T C Dd Dn P n it t inf
        (scanSt inf Dn Dd t).2 (scanSt inf Dn Dd t).1 hn hit ht hDnl hDdl (hDnv t) hbdv hinf (hDdv t) hrM fu
      refine ⟨r, [], [ci n, cs inf, ci it, cb (scanSt inf Dn Dd (t + 1)).1, cs (scanSt inf Dn Dd (t + 1)).2], hr, hret,
        ?_, rfl, rfl, ⟨hvv, rfl⟩, hc, hnd, hwk⟩
      rw [scanSt_succ]
      exact hps)
    (VD H T C Dd Dn) [ci n, cs inf, ci it, cb (scanSt inf Dn Dd 0).1, cs (scanSt inf Dn Dd 0).2] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hIn
  subst hC
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

end Proofs.DijkstraOldScan
