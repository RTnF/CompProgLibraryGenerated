import Proofs.DijkstraOldScan
import Proofs.TopoSortMath

namespace Proofs.DijkstraOldExec
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
open Proofs.DijkstraOldScan


abbrev c8 (n : Nat) (inf : Int) (it : Nat) (r : Option Nat) (bd : Int) (st cnt d : Nat) : List Cell :=
  [ci n, cs inf, ci it, cb r, cs bd, ci st, ci cnt, ci d]
abbrev c10 (n : Nat) (inf : Int) (it : Nat) (r : Option Nat) (bd : Int) (st cnt d w : Nat) (nd : Int) : List Cell :=
  [ci n, cs inf, ci it, cb r, cs bd, ci st, ci cnt, ci d, ci w, cs nd]

theorem sumIdx_den (env : Nat → Ty → Option Int) (ka kb x y : Nat) (ha : env ka i32 = some (x : Int))
    (hb : env kb i32 = some (y : Int)) (hxy : x + y < M31) :
    (NExpr.cast u64 (.binary i32 .add (.variable i32 ka) (.variable i32 kb))).denote env = some ((x + y : Nat) : Int) := by
  rw [den_cast, den_binary, den_variable, ha, Option.bind_some, den_variable, hb, Option.bind_some]
  have e : binaryValue .add (x : Int) (y : Int) = ((x + y : Nat) : Int) := by
    show (x : Int) + (y : Int) = _; push_cast; rfl
  rw [e, conv_signed i32 rfl rfl _ (i32v _ hxy), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have : x + y < 2147483648 := hxy; omega)

set_option maxHeartbeats 8000000 in
/-- One iteration of the relaxation loop: `w = target[start+d]; nd = bd + cost[start+d]; if (nd < dist[w]) dist[w] = nd;` -/
theorem xr_body (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it st cnt d : Nat) (inf bd : Int) (r : Option Nat) (hn : n < M31) (hit : it < M31) (hstM : st < M31)
    (hcM : cnt < M31) (hd : d < M31) (hsd : st + d < T.length) (hmT : T.length < M31) (hCl : C.length = T.length)
    (hDdl : Dd.length = n) (hw : T.getD (st + d) 0 < n) (hbd : s64.valid bd = true) (hinf : s64.valid inf = true)
    (hr : ∀ b, r = some b → b < M31) (hc : s64.valid (C.getD (st + d) 0) = true)
    (hnd : s64.valid (bd + C.getD (st + d) 0) = true) (hdw : s64.valid (Dd.getD (T.getD (st + d) 0) 0) = true)
    (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (Xr mv.nv) (gS P (c8 n inf it r bd st cnt d)) (VD H T C Dd Dn) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P (c10 n inf it r bd st cnt d (T.getD (st + d) 0) (bd + C.getD (st + d) 0)) ∧
      rr.vv = VD H T C (if bd + C.getD (st + d) 0 < Dd.getD (T.getD (st + d) 0) 0
        then Dd.set (T.getD (st + d) 0) (bd + C.getD (st + d) 0) else Dd) Dn ∧
      rr.cost ≤ 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 1 := by
  generalize hwdef : T.getD (st + d) 0 = w at *
  have hsum : st + d < M31 := by omega
  have E5 := envs mv P (c8 n inf it r bd st cnt d) 5 (ci st) rfl (i32v st hstM)
  have E7 := envs mv P (c8 n inf it r bd st cnt d) 7 (ci d) rfl (i32v d hd)
  have hidx := sumIdx_den (penvN mv.nv (gS P (c8 n inf it r bd st cnt d))) (mv.nv + 5) (mv.nv + 7) st d E5 E7 hsum
  have vw := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c8 n inf it r bd st cnt d))) 1 (by omega) i32 (hty1).symm
    (idxSD mv.nv) rfl rfl (st + d) hidx ((w : Nat) : Int)
    (by rw [VD_get1]; have := natList_get T (st + d) hsd; rw [hwdef] at this; exact this)
    (by rw [hty1]; exact i32v _ (by omega))
  have d1 := gSM_decl mv P (c8 n inf it r bd st cnt d) (VD H T C Dd Dn) i32 _ _ _ vw
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q1 := (pexecM_prim mv fu (dW mv.nv) _ _).trans d1
  -- nd = bd + cost[start + d]
  have E4 := envs mv P (c8 n inf it r bd st cnt d ++ [ci w]) 4 (cs bd) rfl hbd
  have E5' := envs mv P (c8 n inf it r bd st cnt d ++ [ci w]) 5 (ci st) rfl (i32v st hstM)
  have E7' := envs mv P (c8 n inf it r bd st cnt d ++ [ci w]) 7 (ci d) rfl (i32v d hd)
  have hidx' := sumIdx_den (penvN mv.nv (gS P (c8 n inf it r bd st cnt d ++ [ci w]))) (mv.nv + 5) (mv.nv + 7) st d E5' E7' hsum
  have vcost := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c8 n inf it r bd st cnt d ++ [ci w]))) 2 (by omega) s64
    (hty2).symm (idxSD mv.nv) rfl rfl (st + d) hidx' (C.getD (st + d) 0)
    (by rw [VD_get2]; exact intList_get C (st + d) (by omega)) (by rw [hty2]; exact hc)
  have vnd : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c8 n inf it r bd st cnt d ++ [ci w])))
      (.binary s64 .add (.variable s64 (mv.nv + 4)) (.read s64 (.local 2) (idxSD mv.nv))) = some (bd + C.getD (st + d) 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdenM_scalar _ _ _ _ rfl, den_variable, E4, Option.bind_some, vcost, Option.bind_some]
    exact conv_signed s64 rfl rfl _ hnd
  have d2 := gSM_decl mv P (c8 n inf it r bd st cnt d ++ [ci w]) (VD H T C Dd Dn) s64 _ _ _ vnd
    (conv_signed s64 rfl rfl _ hnd)
  have q2 := (pexecM_prim mv fu (dNd mv.nv) _ _).trans d2
  -- the test
  have E8 := envs mv P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0)) 8 (ci w) rfl (i32v w (by omega))
  have E9 := envs mv P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0)) 9 (cs (bd + C.getD (st + d) 0)) rfl hnd
  have vdw := rdM_val mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0)))) 3
    (by omega) s64 (hty3).symm (ix mv.nv 8) rfl rfl w (cidx_den _ (mv.nv + 8) w E8 (by omega)) (Dd.getD w 0)
    (by rw [VD_get3]; exact intList_get Dd w (by omega)) (by rw [hty3]; exact hdw)
  have vc : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0)))) (cRel mv.nv) =
      some (if bd + C.getD (st + d) 0 < Dd.getD w 0 then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdenM_scalar _ _ _ _ rfl, den_variable, E9, Option.bind_some, vdw, Option.bind_some]
    exact lt_conv _ _
  by_cases hlt : bd + C.getD (st + d) 0 < Dd.getD w 0
  · have hc1 : (if bd + C.getD (st + d) 0 < Dd.getD w 0 then (1 : Int) else 0) = 1 := by rw [if_pos hlt]
    rw [hc1] at vc
    have hp : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0))))
        (ix mv.nv 8) = some (w : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact cidx_den _ (mv.nv + 8) w E8 (by omega)
    have hx : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0))))
        (.variable s64 (mv.nv + 9)) = some (bd + C.getD (st + d) 0) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E9
    have wr := pstmtM_write_ok mv (gS P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0))) (VD H T C Dd Dn) 3 (by omega)
      (ix mv.nv 8) (.variable s64 (mv.nv + 9)) (bd + C.getD (st + d) 0) w hx hp
      (by rw [VD_get3]; omega) (by rw [hty3]; exact hnd)
    rw [hty3, VD_get3, VD_write3] at wr
    have a1 := (pexecM_prim mv fu (wDist mv.nv) _ _).trans wr
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
    have a3 := scope_gS mv fu _ P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0))
      (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0)) (VD H T C Dd Dn) _ rfl a2 rfl
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu (cRel mv.nv) (Yr mv.nv) Sk _ _ 1 vc (by decide) _ a4
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q2 rfl b2
    have b4 := seqM_some q1 rfl b3
    obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (Xr mv.nv) (gS P (c8 n inf it r bd st cnt d))
        (VD H T C Dd Dn) = some rr ∧ rr.ps = gS P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0)) ∧ rr.ret = none ∧
        rr.vv = VD H T C (Dd.set w (bd + C.getD (st + d) 0)) Dn ∧ rr.cost ≤ 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 1 :=
      ⟨_, b4, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size],
        by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size], by simp⟩
    refine ⟨rr, hrr, hret, hps, ?_, hcost, hneed, hwk⟩
    rw [if_pos hlt]; exact hvv
  · have hc0 : (if bd + C.getD (st + d) 0 < Dd.getD w 0 then (1 : Int) else 0) = 0 := by rw [if_neg hlt]
    rw [hc0] at vc
    have b1 := pexecM_branch_false mv fu (cRel mv.nv) (Yr mv.nv) Sk _ _ vc _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q2 rfl b2
    have b4 := seqM_some q1 rfl b3
    obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (Xr mv.nv) (gS P (c8 n inf it r bd st cnt d))
        (VD H T C Dd Dn) = some rr ∧ rr.ps = gS P (c10 n inf it r bd st cnt d w (bd + C.getD (st + d) 0)) ∧ rr.ret = none ∧
        rr.vv = VD H T C Dd Dn ∧ rr.cost ≤ 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 1 :=
      ⟨_, b4, rfl, rfl, rfl, by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size],
        by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size], by simp⟩
    refine ⟨rr, hrr, hret, hps, ?_, hcost, hneed, hwk⟩
    rw [if_neg hlt]; exact hvv


open Proofs.BellmanFordMath (Edge relax foldl_le)
open Proofs.DijkstraMath (relax_fold_cases relaxOut)

theorem getD_oob {α : Type} (l : List α) (d : α) (j : Nat) (h : l.length ≤ j) : l.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem getD_ltN (l : List Nat) (j : Nat) (h : j < l.length) : l.getD j 0 = l[j] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The distance function as a list of length `n`. -/
def ofFn (n : Nat) (f : Nat → Int) : List Int := (List.range n).map f

theorem ofFn_length (n : Nat) (f : Nat → Int) : (ofFn n f).length = n := by simp [ofFn]

theorem ofFn_getD (n : Nat) (f : Nat → Int) (j : Nat) (hj : j < n) : (ofFn n f).getD j 0 = f j := by
  simp [ofFn, List.getD_eq_getElem?_getD, hj]

theorem ofFn_set (n : Nat) (f : Nat → Int) (w : Nat) (x : Int) (hw : w < n) :
    (ofFn n f).set w x = ofFn n (Proofs.BellmanFordMath.upd f w x) := by
  apply List.ext_getElem
  · simp [ofFn]
  · intro j h1 h2
    have hj : j < n := by simpa [ofFn] using h1
    rw [List.getElem_set]
    simp only [ofFn, List.getElem_map, List.getElem_range]
    unfold Proofs.BellmanFordMath.upd
    by_cases h : w = j
    · subst h; simp
    · simp [h, Ne.symm h]

theorem ofFn_relax (n : Nat) (inf : Int) (f : Nat → Int) (e : Edge) (he : e.2.1 < n) (hf : f e.1 ≠ inf) :
    ofFn n (relax inf f e) =
      if f e.1 + e.2.2 < f e.2.1 then (ofFn n f).set e.2.1 (f e.1 + e.2.2) else ofFn n f := by
  unfold relax
  by_cases h : f e.1 + e.2.2 < f e.2.1
  · rw [if_pos ⟨hf, h⟩, if_pos h, ofFn_set n f _ _ he]
  · rw [if_neg (fun hh => h hh.2), if_neg h]

/-- The out-edges of vertex `b` in CSR order. -/
def outEdges (H T : List Nat) (C : List Int) (b : Nat) : List Edge :=
  (List.range (H.getD (b + 1) 0 - H.getD b 0)).map (fun d => (b, T.getD (H.getD b 0 + d) 0, C.getD (H.getD b 0 + d) 0))

theorem outEdges_length (H T : List Nat) (C : List Int) (b : Nat) :
    (outEdges H T C b).length = H.getD (b + 1) 0 - H.getD b 0 := by simp [outEdges]

theorem outEdges_get (H T : List Nat) (C : List Int) (b d : Nat) (hd : d < (outEdges H T C b).length) :
    (outEdges H T C b)[d] = (b, T.getD (H.getD b 0 + d) 0, C.getD (H.getD b 0 + d) 0) := by
  simp [outEdges]

theorem outEdges_mem (H T : List Nat) (C : List Int) (b : Nat) (e : Edge) (he : e ∈ outEdges H T C b) :
    e.1 = b ∧ ∃ d, d < H.getD (b + 1) 0 - H.getD b 0 ∧ e.2.1 = T.getD (H.getD b 0 + d) 0 ∧ e.2.2 = C.getD (H.getD b 0 + d) 0 := by
  unfold outEdges at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  exact ⟨rfl, d, List.mem_range.mp hd, rfl, rfl⟩


/-- Relaxing the first `d` edges of `L` in order. -/
def foldR (inf : Int) (L : List Edge) (f0 : Nat → Int) (d : Nat) : Nat → Int := (L.take d).foldl (relax inf) f0

theorem foldR_succ (inf : Int) (L : List Edge) (f0 : Nat → Int) (d : Nat) (hd : d < L.length) :
    foldR inf L f0 (d + 1) = relax inf (foldR inf L f0 d) L[d] := by
  unfold foldR
  have h : L.take (d + 1) = L.take d ++ [L[d]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hd]
    rfl
  rw [h, List.foldl_append]
  rfl

theorem foldR_full (inf : Int) (L : List Edge) (f0 : Nat → Int) : foldR inf L f0 L.length = L.foldl (relax inf) f0 := by
  unfold foldR; rw [List.take_length]

theorem relax_bounds (n : Nat) (inf lo : Int) (f : Nat → Int) (e : Edge) (hb : ∀ j, j < n → lo ≤ f j ∧ f j ≤ inf)
    (hs : lo ≤ f e.1) (hc : 0 ≤ e.2.2) (hw : e.2.1 < n) : ∀ j, j < n → lo ≤ relax inf f e j ∧ relax inf f e j ≤ inf := by
  intro j hj
  unfold relax
  by_cases hg : f e.1 ≠ inf ∧ f e.1 + e.2.2 < f e.2.1
  · rw [if_pos hg]
    by_cases hjw : j = e.2.1
    · subst hjw
      rw [Proofs.BellmanFordMath.upd_same]
      have := (hb _ hw).2
      constructor <;> omega
    · rw [Proofs.BellmanFordMath.upd_ne _ _ _ _ hjw]
      exact hb j hj
  · rw [if_neg hg]; exact hb j hj


abbrev c7 (n : Nat) (inf : Int) (it : Nat) (r : Option Nat) (bd : Int) (st cnt : Nat) : List Cell :=
  [ci n, cs inf, ci it, cb r, cs bd, ci st, ci cnt]

theorem outEdges_cls (H T : List Nat) (C : List Int) (b : Nat) (hC : ∀ x ∈ C, 0 ≤ x) :
    ∀ e ∈ outEdges H T C b, e.1 = b ∧ 0 ≤ e.2.2 := by
  intro e he
  obtain ⟨h1, d, hd, h2, h3⟩ := outEdges_mem H T C b e he
  refine ⟨h1, ?_⟩
  rw [h3]
  by_cases hlt : H.getD b 0 + d < C.length
  · exact hC _ (Proofs.BellmanFordExec.getD_mem C _ hlt)
  · have h0 : C.getD (H.getD b 0 + d) 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [h0]

set_option maxHeartbeats 8000000 in
/-- The relaxation loop `for (int d = 0; d < cnt; d++) {...}`. -/
theorem xr_loop (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C : List Int) (Dn : List Nat) (P : List Cell)
    (n it b : Nat) (inf bd lo : Int) (f0 : Nat → Int) (hn : n < M31) (hit : it < M31) (hb : b < n)
    (hn2 : n < 2147483647) (hTn : ∀ x ∈ T, x < n) (hTM : T.length < M31) (hCl : C.length = T.length)
    (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x ≤ 2305843009213693952) (hstc : H.getD b 0 + (outEdges H T C b).length ≤ T.length)
    (hbd0 : ∀ j, j < n → lo ≤ f0 j ∧ f0 j ≤ inf) (hlo : -4611686018427387904 ≤ lo) (hinfB : inf ≤ 4611686018427387904)
    (hbdE : bd = f0 b) (hbdlt : bd < inf) (hcnt2 : (outEdges H T C b).length < 2147483647)
    (fu : Nat) (hfu : (outEdges H T C b).length + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 7 6 (Xr mv.nv))
      (gS P (c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length)) (VD H T C (ofFn n f0) Dn) = some res ∧
      res.ps = gS P (c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length) ∧
      res.vv = VD H T C (ofFn n (relaxOut inf (outEdges H T C) b f0)) Dn ∧ res.ret = none ∧
      res.cost ≤ 420 * (outEdges H T C b).length + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ (outEdges H T C b).length := by
  have hCnn : ∀ x ∈ C, 0 ≤ x := fun x hx => (hC0 x hx).1
  have hcls := outEdges_cls H T C b hCnn
  have hnM : n < 2147483648 := hn
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 7 6 (outEdges H T C b).length (by omega) hcnt2
    (Xr mv.nv)
    (fun d vv Cl => vv = VD H T C (ofFn n (foldR inf (outEdges H T C b) f0 d)) Dn ∧
      Cl = c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length ∧
      (∀ j, j < n → lo ≤ foldR inf (outEdges H T C b) f0 d j ∧ foldR inf (outEdges H T C b) f0 d j ≤ inf) ∧
      foldR inf (outEdges H T C b) f0 d b = bd)
    400 80 1 0 (by omega)
    (by
      intro d vv Cl fu hd hCl' hC0' ⟨hvv, hC, hgb, hgbd⟩ _
      subst hvv; subst hC
      have hLb := outEdges_length H T C b
      have hdlt : d < (outEdges H T C b).length := hd
      obtain ⟨e, he⟩ : ∃ e, e = (outEdges H T C b)[d] := ⟨_, rfl⟩
      have he' : e = (b, T.getD (H.getD b 0 + d) 0, C.getD (H.getD b 0 + d) 0) := by
        rw [he]; exact outEdges_get H T C b d hdlt
      have hsd : H.getD b 0 + d < T.length := by omega
      have hwn : T.getD (H.getD b 0 + d) 0 < n := by
        rw [getD_ltN T _ hsd]; exact hTn _ (List.getElem_mem _)
      have hcmem : C.getD (H.getD b 0 + d) 0 ∈ C := Proofs.BellmanFordExec.getD_mem C _ (by omega)
      have hcb := hC0 _ hcmem
      have hg0 := hgb b hb
      have hgbE : foldR inf (outEdges H T C b) f0 d b = bd := hgbd
      have hbdv : s64.valid bd = true := Proofs.BellmanFordExec.s64_valid_of bd (by omega)
      have hndv : s64.valid (bd + C.getD (H.getD b 0 + d) 0) = true :=
        Proofs.BellmanFordExec.s64_valid_of _ (by omega)
      have hdwv : s64.valid ((ofFn n (foldR inf (outEdges H T C b) f0 d)).getD (T.getD (H.getD b 0 + d) 0) 0) = true := by
        rw [ofFn_getD n _ _ hwn]
        have := hgb _ hwn
        exact Proofs.BellmanFordExec.s64_valid_of _ (by omega)
      obtain ⟨rr, hrr, hret, hps, hvv, hcost, hneed, hwk⟩ := xr_body mv hnv hty0 hty1 hty2 hty3 hty4 H T C
        (ofFn n (foldR inf (outEdges H T C b) f0 d)) Dn P n it (H.getD b 0) (outEdges H T C b).length d inf bd (some b) hn hit
        (by omega) (by omega) (by omega) hsd hTM hCl (ofFn_length _ _) hwn hbdv
        (Proofs.BellmanFordExec.s64_valid_of inf (by omega)) (fun b' hb' => by simp at hb'; omega)
        (Proofs.BellmanFordExec.s64_valid_of _ (by omega)) hndv hdwv fu
      have hsucc : foldR inf (outEdges H T C b) f0 (d + 1) = relax inf (foldR inf (outEdges H T C b) f0 d) e := by
        rw [foldR_succ inf _ f0 d hdlt, he]
      have hbnd' := relax_bounds n inf lo (foldR inf (outEdges H T C b) f0 d) e hgb
        (by rw [he']; show lo ≤ foldR inf (outEdges H T C b) f0 d b; omega) (by rw [he']; exact hcb.1)
        (by rw [he']; exact hwn)
      have hstab : foldR inf (outEdges H T C b) f0 (d + 1) b = bd := by
        have hcl2 : ∀ e' ∈ (outEdges H T C b).take (d + 1), e'.1 = b ∧ 0 ≤ e'.2.2 :=
          fun e' he'' => hcls e' (List.mem_of_mem_take he'')
        have := (relax_fold_cases inf b _ f0 hcl2).1
        unfold foldR; rw [this, hbdE]
      have hvv' : rr.vv = VD H T C (ofFn n (foldR inf (outEdges H T C b) f0 (d + 1))) Dn := by
        rw [hvv, hsucc, ofFn_relax n inf _ e (by rw [he']; exact hwn) (by rw [he']; show _ ≠ inf; rw [hgbE]; omega),
          ofFn_getD n _ _ hwn]
        rw [he']
        show VD H T C (if bd + C.getD (H.getD b 0 + d) 0 < foldR inf (outEdges H T C b) f0 d (T.getD (H.getD b 0 + d) 0)
            then (ofFn n (foldR inf (outEdges H T C b) f0 d)).set (T.getD (H.getD b 0 + d) 0) (bd + C.getD (H.getD b 0 + d) 0)
            else ofFn n (foldR inf (outEdges H T C b) f0 d)) Dn = VD H T C
            (if foldR inf (outEdges H T C b) f0 d b + C.getD (H.getD b 0 + d) 0 <
              foldR inf (outEdges H T C b) f0 d (T.getD (H.getD b 0 + d) 0) then
              (ofFn n (foldR inf (outEdges H T C b) f0 d)).set (T.getD (H.getD b 0 + d) 0)
                (foldR inf (outEdges H T C b) f0 d b + C.getD (H.getD b 0 + d) 0)
            else ofFn n (foldR inf (outEdges H T C b) f0 d)) Dn
        rw [hgbE]
      refine ⟨rr, [ci (T.getD (H.getD b 0 + d) 0), cs (bd + C.getD (H.getD b 0 + d) 0)],
        c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length, hrr, hret, hps, rfl, rfl,
        ⟨hvv', rfl, by rw [hsucc]; exact hbnd', hstab⟩, hcost, hneed, hwk⟩)
    (VD H T C (ofFn n (foldR inf (outEdges H T C b) f0 0)) Dn) (c7 n inf it (some b) bd (H.getD b 0) (outEdges H T C b).length)
    rfl rfl ⟨rfl, rfl, by simpa [foldR] using hbd0, by simp [foldR, hbdE]⟩ fu (by omega)
  obtain ⟨hvv, hC, hgb, hgbd⟩ := hIn
  subst hC
  refine ⟨res, hr', hps, ?_, hret, ?_, ?_, ?_⟩
  · rw [hvv, foldR_full]; rfl
  · omega
  · omega
  · omega


abbrev dCntE (nv : Nat) : NExpr :=
  .binary i32 .sub (.read i32 (.local 0) (.cast u64 (.binary i32 .add (.variable i32 (nv + 3)) DijkstraOldScan.lit1)))
    (.variable i32 (nv + 5))

abbrev c5 (n : Nat) (inf : Int) (it : Nat) (r : Option Nat) (bd : Int) : List Cell :=
  [ci n, cs inf, ci it, cb r, cs bd]

theorem succIdx_den (env : Nat → Ty → Option Int) (k x : Nat) (h : env k i32 = some (x : Int)) (hx : x + 1 < M31) :
    (NExpr.cast u64 (.binary i32 .add (.variable i32 k) DijkstraOldScan.lit1)).denote env = some ((x + 1 : Nat) : Int) := by
  rw [den_cast, den_binary, den_variable, h, Option.bind_some, DijkstraOldScan.one_den, Option.bind_some]
  have e : binaryValue .add (x : Int) 1 = ((x + 1 : Nat) : Int) := by
    show (x : Int) + 1 = _; push_cast; rfl
  rw [e, conv_signed i32 rfl rfl _ (i32v _ hx), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have : x + 1 < 2147483648 := hx; omega)

set_option maxHeartbeats 8000000 in
/-- `if (best >= 0) {...}` when a vertex `b` was found. -/
theorem b_vertex_some (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C : List Int) (Dn : List Nat) (P : List Cell)
    (n it b : Nat) (inf bd lo : Int) (f0 : Nat → Int) (hn : n < M31) (hit : it < M31) (hb : b < n)
    (hn2 : n < 2147483647) (HK : Proofs.TopoSortMath.HeadOK H T n) (hDnl : Dn.length = n)
    (hTn : ∀ x ∈ T, x < n) (hTM : T.length < M31) (hCl : C.length = T.length)
    (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x ≤ 2305843009213693952)
    (hbd0 : ∀ j, j < n → lo ≤ f0 j ∧ f0 j ≤ inf) (hlo : -4611686018427387904 ≤ lo) (hinfB : inf ≤ 4611686018427387904)
    (hbdE : bd = f0 b) (hbdlt : bd < inf) (hcnt2 : (outEdges H T C b).length < 2147483647) (fu : Nat)
    (hfu : (outEdges H T C b).length + 2 ≤ fu) :
    ∃ rr : PRM, pexecM mv fu (BRb mv.nv) (gS P (c5 n inf it (some b) bd)) (VD H T C (ofFn n f0) Dn) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P (c5 n inf it (some b) bd) ∧
      rr.vv = VD H T C (ofFn n (relaxOut inf (outEdges H T C) b f0)) (Dn.set b 1) ∧
      rr.cost ≤ 420 * (outEdges H T C b).length + 200 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ (outEdges H T C b).length + 1 := by
  have hnM : n < 2147483648 := hn
  have hHl : H.length = n + 1 := HK.len
  have hHle : ∀ j, j ≤ n → H.getD j 0 ≤ T.length := by
    intro j hj
    have := Proofs.TopoSortMath.HeadOK.le H T n HK n (Nat.le_refl _) j hj
    rw [HK.last] at this
    exact this
  have hmono := HK.mono b hb
  have hcntE : (outEdges H T C b).length = H.getD (b + 1) 0 - H.getD b 0 := outEdges_length H T C b
  have hcM : H.getD (b + 1) 0 ≤ T.length := hHle (b + 1) (by omega)
  have hstM' : H.getD b 0 ≤ T.length := hHle b (by omega)
  have E3 := envs mv P (c5 n inf it (some b) bd) 3 (cb (some b)) rfl (i32v b (by omega))
  have hp : vdenM mv (VD H T C (ofFn n f0) Dn) (penvN mv.nv (gS P (c5 n inf it (some b) bd))) (ix mv.nv 3) = some (b : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 3) b E3 (by omega)
  have hx1 : vdenM mv (VD H T C (ofFn n f0) Dn) (penvN mv.nv (gS P (c5 n inf it (some b) bd))) DijkstraOldScan.lit1 =
      some (((1 : Nat) : Int)) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact DijkstraOldScan.one_den _
  have wr := pstmtM_write_ok mv (gS P (c5 n inf it (some b) bd)) (VD H T C (ofFn n f0) Dn) 4 (by omega) (ix mv.nv 3)
    DijkstraOldScan.lit1 ((1 : Nat) : Int) b hx1 hp (by rw [VD_get4]; simp [hDnl]; exact hb)
    (by rw [hty4]; exact i32v 1 (by decide))
  rw [hty4, VD_write4] at wr
  have w1 := (pexecM_prim mv fu (wDone mv.nv) _ _).trans wr
  -- start = head[b]
  have E3' := envs mv P (c5 n inf it (some b) bd) 3 (cb (some b)) rfl (i32v b (by omega))
  have vst := rdM_val mv (VD H T C (ofFn n f0) (Dn.set b 1)) (penvN mv.nv (gS P (c5 n inf it (some b) bd))) 0 (by omega) i32
    (hty0).symm (ix mv.nv 3) rfl rfl b (cidx_den _ (mv.nv + 3) b E3' (by omega)) ((H.getD b 0 : Nat) : Int)
    (by rw [VD_get0]; exact natList_get H b (by omega)) (by rw [hty0]; exact i32v _ (by omega))
  have d1 := gSM_decl mv P (c5 n inf it (some b) bd) (VD H T C (ofFn n f0) (Dn.set b 1)) i32 _ _ _ vst
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q1 := (pexecM_prim mv fu (dStart mv.nv) _ _).trans d1
  -- cnt = head[b+1] - start
  have E3'' := envs mv P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)]) 3 (cb (some b)) rfl (i32v b (by omega))
  have E5 := envs mv P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)]) 5 (ci (H.getD b 0)) rfl (i32v _ (by omega))
  have vh1 := rdM_val mv (VD H T C (ofFn n f0) (Dn.set b 1)) (penvN mv.nv (gS P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)]))) 0
    (by omega) i32 (hty0).symm (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 3)) DijkstraOldScan.lit1)) rfl rfl (b + 1)
    (succIdx_den _ (mv.nv + 3) b E3'' (by omega)) ((H.getD (b + 1) 0 : Nat) : Int)
    (by rw [VD_get0]; exact natList_get H (b + 1) (by omega)) (by rw [hty0]; exact i32v _ (by omega))
  have vcnt : vdenM mv (VD H T C (ofFn n f0) (Dn.set b 1)) (penvN mv.nv (gS P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)])))
      (dCntE mv.nv) = some ((H.getD (b + 1) 0 - H.getD b 0 : Nat) : Int) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vh1, Option.bind_some, vdenM_scalar _ _ _ _ rfl, den_variable, E5, Option.bind_some]
    have : binaryValue .sub ((H.getD (b + 1) 0 : Nat) : Int) ((H.getD b 0 : Nat) : Int) =
        ((H.getD (b + 1) 0 - H.getD b 0 : Nat) : Int) := by
      show _ - _ = _; omega
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ (by omega))
  have d2 := gSM_decl mv P (c5 n inf it (some b) bd ++ [ci (H.getD b 0)]) (VD H T C (ofFn n f0) (Dn.set b 1)) i32 _ _ _ vcnt
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q2 := (pexecM_prim mv fu (dCnt mv.nv) _ _).trans d2
  rw [← hcntE] at q2
  obtain ⟨rl, hrl, hrlps, hrlvv, hrlret, hrlc, hrln, hrlw⟩ := xr_loop mv hnv hty0 hty1 hty2 hty3 hty4 H T C (Dn.set b 1) P n it b inf bd lo
    f0 hn hit hb hn2 hTn hTM hCl hC0 (by omega) hbd0 hlo hinfB hbdE hbdlt hcnt2 fu (by omega)
  have f1 := seqM_some hrl hrlret (pexecM_skip mv fu _ _)
  have f2 := seqM_some q2 rfl f1
  have f3 := seqM_some q1 rfl f2
  have f4 := seqM_some w1 rfl f3
  have f5 := pexecM_scope mv fu _ _ _ _ f4
  have tk := gS_takeC P (c5 n inf it (some b) bd) (c5 n inf it (some b) bd) [ci (H.getD b 0), ci (outEdges H T C b).length] rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append] at tk
  rw [hrlps] at f5
  simp only [tk] at f5
  have f6 := seqM_some f5 rfl (pexecM_skip mv fu _ _)
  have vge : vdenM mv (VD H T C (ofFn n f0) Dn) (penvN mv.nv (gS P (c5 n inf it (some b) bd))) (cBest mv.nv) = some 1 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E3, Option.bind_some, DijkstraOldScan.zero_den, Option.bind_some]
    have : ((b : Nat) : Int) ≥ 0 := Int.natCast_nonneg b
    have h := ge_conv ((b : Nat) : Int) 0
    rw [if_pos this] at h
    exact h
  have g1 := pexecM_branch_true mv fu (cBest mv.nv) (.sequence (.scope (Zb mv.nv)) Sk) Sk _ _ 1 vge (by decide) _ f6
  obtain ⟨rr, hrr, hps, hret, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (BRb mv.nv) (gS P (c5 n inf it (some b) bd))
      (VD H T C (ofFn n f0) Dn) = some rr ∧ rr.ps = gS P (c5 n inf it (some b) bd) ∧ rr.ret = none ∧
      rr.vv = VD H T C (ofFn n (relaxOut inf (outEdges H T C) b f0)) (Dn.set b 1) ∧
      rr.cost ≤ 420 * (outEdges H T C b).length + 200 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ (outEdges H T C b).length + 1 := by
    refine ⟨_, g1, rfl, rfl, hrlvv, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrlc ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrln ⊢; omega
    · simp at hrlw ⊢; omega
  exact ⟨rr, hrr, hret, hps, hvv, hcost, hneed, hwk⟩


/-- `if (best >= 0) {...}` when no vertex was found. -/
theorem b_vertex_none (mv : MV) (hnv : mv.nv = 5) (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (P : List Cell)
    (n it : Nat) (inf bd : Int) (hn : n < M31) (fu : Nat) :
    ∃ rr : PRM, pexecM mv fu (BRb mv.nv) (gS P (c5 n inf it none bd)) (VD H T C Dd Dn) = some rr ∧
      rr.ret = none ∧ rr.ps = gS P (c5 n inf it none bd) ∧ rr.vv = VD H T C Dd Dn ∧
      rr.cost ≤ 20 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ 0 := by
  have E3 := envs mv P (c5 n inf it none bd) 3 (cb none) rfl (bI_valid none (fun b hb => by simp at hb))
  have vge : vdenM mv (VD H T C Dd Dn) (penvN mv.nv (gS P (c5 n inf it none bd))) (cBest mv.nv) = some 0 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E3, Option.bind_some, DijkstraOldScan.zero_den, Option.bind_some]
    have : ¬ ((-1 : Int) ≥ 0) := by omega
    have h := ge_conv (-1 : Int) 0
    rw [if_neg this] at h
    exact h
  have b1 := pexecM_branch_false mv fu (cBest mv.nv) (.sequence (.scope (Zb mv.nv)) Sk) Sk _ _ vge _ (pexecM_skip mv fu _ _)
  refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


/-- The `done` vector for the set `D` of finalized vertices. -/
def doneOf (n : Nat) (D : List Nat) : List Nat := (List.range n).map (fun v => if v ∈ D then 1 else 0)

theorem doneOf_length (n : Nat) (D : List Nat) : (doneOf n D).length = n := by simp [doneOf]

theorem doneOf_getD (n : Nat) (D : List Nat) (v : Nat) (hv : v < n) : (doneOf n D).getD v 0 = if v ∈ D then 1 else 0 := by
  simp [doneOf, List.getD_eq_getElem?_getD, hv]

theorem doneOf_push (n : Nat) (D : List Nat) (b : Nat) (hb : b < n) : (doneOf n D).set b 1 = doneOf n (D ++ [b]) := by
  apply List.ext_getElem
  · simp [doneOf]
  · intro j h1 h2
    have hj : j < n := by simpa [doneOf] using h1
    rw [List.getElem_set]
    simp only [doneOf, List.getElem_map, List.getElem_range]
    by_cases h : b = j
    · subst h; simp
    · simp [h, Ne.symm h]

open Proofs.DijkstraMath (scanStep scanRes)

theorem scan_eq (n : Nat) (inf : Int) (f : Nat → Int) (D : List Nat) (Dn : List Nat) (Dd : List Int)
    (hdn : ∀ v, v < n → (Dn.getD v 0 = 0 ↔ v ∉ D)) (hdd : ∀ v, v < n → Dd.getD v 0 = f v) :
    ∀ t, t ≤ n → scanSt inf Dn Dd t = (List.range t).foldl (scanStep inf f D) (none, inf) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [scanSt_succ, ih (by omega), List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize (List.range t).foldl (scanStep inf f D) (none, inf) = s
    unfold scanStepL Proofs.DijkstraMath.scanStep
    rw [hdd t (by omega)]
    have := hdn t (by omega)
    by_cases hg : t ∉ D ∧ f t < s.2
    · rw [if_pos hg, if_pos ⟨this.mpr hg.1, hg.2⟩]
    · rw [if_neg hg, if_neg (fun h => hg ⟨this.mp h.1, h.2⟩)]


theorem graph_of (H T : List Nat) (C : List Int) (n : Nat) (HK : Proofs.TopoSortMath.HeadOK H T n) (hTn : ∀ x ∈ T, x < n)
    (hC : ∀ x ∈ C, 0 ≤ x) : Proofs.DijkstraMath.Graph n (outEdges H T C) := by
  refine ⟨fun u hu e he => ?_⟩
  have hcls := outEdges_cls H T C u hC e he
  obtain ⟨h1, d, hd, h2, h3⟩ := outEdges_mem H T C u e he
  refine ⟨hcls.1, ?_, hcls.2⟩
  have hle : H.getD (u + 1) 0 ≤ T.length := by
    have := Proofs.TopoSortMath.HeadOK.le H T n HK n (Nat.le_refl _) (u + 1) (by omega)
    rw [HK.last] at this; exact this
  have hlt : H.getD u 0 + d < T.length := by omega
  rw [h2, getD_ltN T _ hlt]
  exact hTn _ (List.getElem_mem _)


open Proofs.DijkstraMath (djStep scan_inv PickInv)

theorem relaxOut_bounds (n : Nat) (inf lo : Int) (outE : Nat → List Edge) (b : Nat) (f : Nat → Int)
    (hcls : ∀ e ∈ outE b, e.1 = b ∧ 0 ≤ e.2.2) (hbnd : ∀ j, j < n → lo ≤ f j ∧ f j ≤ inf) (hb : b < n) :
    ∀ j, j < n → lo ≤ relaxOut inf outE b f j ∧ relaxOut inf outE b f j ≤ inf := by
  intro j hj
  have hle := foldl_le inf (outE b) f j
  have hcases := (relax_fold_cases inf b (outE b) f hcls).2 j
  have h1 := hbnd j hj
  have hbb := hbnd b hb
  refine ⟨?_, by have : relaxOut inf outE b f j ≤ f j := hle; omega⟩
  rcases hcases with h | ⟨e, he, _, h⟩
  · have h' : relaxOut inf outE b f j = f j := h
    omega
  · have h' : relaxOut inf outE b f j = f b + e.2.2 := h
    have := (hcls e he).2
    omega

set_option maxHeartbeats 8000000 in
/-- One iteration of the outer loop. -/
theorem b_outer (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C : List Int) (P : List Cell) (n it : Nat)
    (inf lo : Int) (f : Nat → Int) (D : List Nat) (hn : n < M31) (hn2 : n < 2147483647) (hit : it < M31)
    (HK : Proofs.TopoSortMath.HeadOK H T n) (hTn : ∀ x ∈ T, x < n) (hTM : T.length < 2147483647)
    (hCl : C.length = T.length) (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x ≤ 2305843009213693952)
    (hinfv : s64.valid inf = true) (hlo : -4611686018427387904 ≤ lo) (hinfB : inf ≤ 4611686018427387904)
    (hbnd : ∀ j, j < n → lo ≤ f j ∧ f j ≤ inf) (fu : Nat) (hfu : n + T.length + 4 ≤ fu) :
    ∃ (rr : PRM) (r0 : Option Nat) (bd0 : Int), pexecM mv fu (Bo mv.nv) (gS P [ci n, cs inf, ci it])
      (VD H T C (ofFn n f) (doneOf n D)) = some rr ∧ rr.ret = none ∧ rr.ps = gS P (c5 n inf it r0 bd0) ∧
      rr.vv = VD H T C (ofFn n (djStep inf (outEdges H T C) n (f, D) it).1) (doneOf n (djStep inf (outEdges H T C) n (f, D) it).2) ∧
      (∀ j, j < n → lo ≤ (djStep inf (outEdges H T C) n (f, D) it).1 j ∧ (djStep inf (outEdges H T C) n (f, D) it).1 j ≤ inf) ∧
      rr.cost ≤ 320 * n + 420 * T.length + 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ T.length + 1 := by
  have hnM : n < 2147483648 := hn
  have hCnn : ∀ x ∈ C, 0 ≤ x := fun x hx => (hC0 x hx).1
  have G := graph_of H T C n HK hTn hCnn
  have hDnl : (doneOf n D).length = n := doneOf_length n D
  have hDdl : (ofFn n f).length = n := ofFn_length n f
  have hDnv : ∀ j, (doneOf n D).getD j 0 < M31 := by
    intro j
    by_cases hj : j < n
    · rw [doneOf_getD n D j hj]; split <;> (show _ < 2147483648; omega)
    · have : (doneOf n D).getD j 0 = 0 := getD_oob _ _ _ (by rw [doneOf_length]; omega)
      rw [this]; show 0 < 2147483648; omega
  have hDdv : ∀ j, s64.valid ((ofFn n f).getD j 0) = true := by
    intro j
    by_cases hj : j < n
    · rw [ofFn_getD n f j hj]
      have := hbnd j hj
      exact Proofs.BellmanFordExec.s64_valid_of _ (by omega)
    · have : (ofFn n f).getD j 0 = 0 := getD_oob _ _ _ (by rw [ofFn_length]; omega)
      rw [this]; exact Proofs.BellmanFordExec.s64_valid_of _ (by omega)
  -- the two declarations
  have E1 := envs mv P [ci n, cs inf, ci it, cb none] 1 (cs inf) rfl hinfv
  have vneg : vdenM mv (VD H T C (ofFn n f) (doneOf n D)) (penvN mv.nv (gS P [ci n, cs inf, ci it])) (.unary i32 .neg DijkstraOldScan.lit1)
      = some (-1) := by
    rw [vdenM_scalar _ _ _ _ rfl]; rfl
  have d1 := gSM_decl mv P [ci n, cs inf, ci it] (VD H T C (ofFn n f) (doneOf n D)) i32 _ _ _ vneg
    (conv_signed i32 rfl rfl _ (show i32.valid (-1) = true from rfl))
  have q1 := (pexecM_prim mv fu dBest _ _).trans d1
  have vinf : vdenM mv (VD H T C (ofFn n f) (doneOf n D)) (penvN mv.nv (gS P [ci n, cs inf, ci it, cb none])) (.variable s64 (mv.nv + 1))
      = some inf := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1
  have d2 := gSM_decl mv P [ci n, cs inf, ci it, cb none] (VD H T C (ofFn n f) (doneOf n D)) s64 _ _ _ vinf
    (conv_signed s64 rfl rfl _ hinfv)
  have q2 := (pexecM_prim mv fu (dBd mv.nv) _ _).trans d2
  -- the scan
  obtain ⟨rs, hrs, hrsps, hrsvv, hrsret, hrsc, hrsn, hrsw⟩ := l_scan mv hnv hty0 hty1 hty2 hty3 hty4 H T C (ofFn n f) (doneOf n D) P
    n it inf hn hn2 hit hDnl hDdl hDnv hDdv hinfv fu (by omega)
  have hdn : ∀ v, v < n → ((doneOf n D).getD v 0 = 0 ↔ v ∉ D) := by
    intro v hv
    rw [doneOf_getD n D v hv]
    by_cases h : v ∈ D <;> simp [h]
  have hdd : ∀ v, v < n → (ofFn n f).getD v 0 = f v := fun v hv => ofFn_getD n f v hv
  have hscan := scan_eq n inf f D (doneOf n D) (ofFn n f) hdn hdd n (Nat.le_refl _)
  have PI := scan_inv inf f D n
  rw [← hscan] at PI
  unfold djStep
  unfold Proofs.DijkstraMath.scanRes
  rw [← hscan]
  rcases hr : (scanSt inf (doneOf n D) (ofFn n f) n).1 with _ | b
  · -- no vertex found
    rw [hr] at hrsps
    obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ := b_vertex_none mv hnv H T C (ofFn n f) (doneOf n D) P n it inf
      (scanSt inf (doneOf n D) (ofFn n f) n).2 hn fu
    have hl1 : rb.ps.mem.length + rb.ps.bs.length = P.length + 10 := by rw [hrbps]; simp [gS_size]
    have g1 := seqM_some hrb hrbret (pexecM_skip mv fu _ _)
    have g2 := seqM_some hrs hrsret (by rw [hrsps, hrsvv]; exact g1)
    have g3 := seqM_some q2 rfl g2
    have g4 := seqM_some q1 rfl g3
    obtain ⟨rr, hrr, hret, hps, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (Bo mv.nv) (gS P [ci n, cs inf, ci it])
        (VD H T C (ofFn n f) (doneOf n D)) = some rr ∧ rr.ret = none ∧
        rr.ps = gS P (c5 n inf it none (scanSt inf (doneOf n D) (ofFn n f) n).2) ∧
        rr.vv = VD H T C (ofFn n f) (doneOf n D) ∧ rr.cost ≤ 320 * n + 420 * T.length + 400 ∧ rr.need ≤ P.length + 80 ∧
        rr.wk ≤ T.length + 1 := by
      refine ⟨_, g4, rfl, hrbps, ?_, ?_, ?_, ?_⟩
      · exact hrbvv
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrsc hrbc ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrsn hrbn ⊢; omega
      · simp at hrsw hrbw ⊢; omega
    exact ⟨rr, none, (scanSt inf (doneOf n D) (ofFn n f) n).2, hrr, hret, hps, hvv, hbnd, hcost, hneed, hwk⟩
  · -- the vertex b was found
    rw [hr] at hrsps
    have hPI := PI.some b hr
    have hbn : b < n := hPI.1
    have hcls := outEdges_cls H T C b hCnn
    have hcnt : (outEdges H T C b).length ≤ T.length := by
      rw [outEdges_length]
      have := Proofs.TopoSortMath.HeadOK.le H T n HK n (Nat.le_refl _) (b + 1) (by omega)
      rw [HK.last] at this
      omega
    obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ := b_vertex_some mv hnv hty0 hty1 hty2 hty3 hty4 H T C (doneOf n D) P
      n it b inf (scanSt inf (doneOf n D) (ofFn n f) n).2 lo f hn hit hbn hn2 HK hDnl hTn (by show _ < 2147483648; omega) hCl
      hC0 hbnd hlo hinfB hPI.2.2.1.symm hPI.2.2.2.1 (by omega) fu (by omega)
    have hl1 : rb.ps.mem.length + rb.ps.bs.length = P.length + 10 := by rw [hrbps]; simp [gS_size]
    have g1 := seqM_some hrb hrbret (pexecM_skip mv fu _ _)
    have g2 := seqM_some hrs hrsret (by rw [hrsps, hrsvv]; exact g1)
    have g3 := seqM_some q2 rfl g2
    have g4 := seqM_some q1 rfl g3
    obtain ⟨rr, hrr, hret, hps, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (Bo mv.nv) (gS P [ci n, cs inf, ci it])
        (VD H T C (ofFn n f) (doneOf n D)) = some rr ∧ rr.ret = none ∧
        rr.ps = gS P (c5 n inf it (some b) (scanSt inf (doneOf n D) (ofFn n f) n).2) ∧
        rr.vv = VD H T C (ofFn n (relaxOut inf (outEdges H T C) b f)) ((doneOf n D).set b 1) ∧
        rr.cost ≤ 320 * n + 420 * T.length + 400 ∧ rr.need ≤ P.length + 80 ∧ rr.wk ≤ T.length + 1 := by
      refine ⟨_, g4, rfl, hrbps, ?_, ?_, ?_, ?_⟩
      · rw [hrbvv]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrsc hrbc ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrsn hrbn ⊢; omega
      · simp at hrsw hrbw ⊢; omega
    refine ⟨rr, some b, (scanSt inf (doneOf n D) (ofFn n f) n).2, hrr, hret, hps, ?_, ?_, hcost, hneed, hwk⟩
    · rw [hvv, doneOf_push n D b hbn]
    · exact relaxOut_bounds n inf lo (outEdges H T C) b f (fun e he => hcls e he) hbnd hbn


open Proofs.DijkstraMath (djIter djIter_succ)

set_option maxHeartbeats 8000000 in
/-- The outer loop `for (int it = 0; it < n; it++) {...}`. -/
theorem l_outer (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C : List Int) (P : List Cell) (n : Nat)
    (inf lo : Int) (f0 : Nat → Int) (hn : n < M31) (hn2 : n < 2147483647)
    (HK : Proofs.TopoSortMath.HeadOK H T n) (hTn : ∀ x ∈ T, x < n) (hTM : T.length < 2147483647)
    (hCl : C.length = T.length) (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x ≤ 2305843009213693952)
    (hinfv : s64.valid inf = true) (hlo : -4611686018427387904 ≤ lo) (hinfB : inf ≤ 4611686018427387904)
    (hbnd : ∀ j, j < n → lo ≤ f0 j ∧ f0 j ≤ inf) (fu : Nat) (hfu : 2 * n + T.length + 5 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 2 0 (Bo mv.nv)) (gS P [ci n, cs inf]) (VD H T C (ofFn n f0) (doneOf n [])) = some res ∧
      res.ps = gS P [ci n, cs inf] ∧
      res.vv = VD H T C (ofFn n (djIter inf (outEdges H T C) n f0 n).1) (doneOf n (djIter inf (outEdges H T C) n f0 n).2) ∧
      res.ret = none ∧ (∀ j, j < n → lo ≤ (djIter inf (outEdges H T C) n f0 n).1 j ∧ (djIter inf (outEdges H T C) n f0 n).1 j ≤ inf) ∧
      res.cost ≤ (320 * n + 420 * T.length + 420) * n + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ (T.length + 1) * n := by
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 2 0 n (by omega) hn2 (Bo mv.nv)
    (fun t vv Cl => vv = VD H T C (ofFn n (djIter inf (outEdges H T C) n f0 t).1) (doneOf n (djIter inf (outEdges H T C) n f0 t).2) ∧
      Cl = [ci n, cs inf] ∧
      ∀ j, j < n → lo ≤ (djIter inf (outEdges H T C) n f0 t).1 j ∧ (djIter inf (outEdges H T C) n f0 t).1 j ≤ inf)
    (320 * n + 420 * T.length + 400) 80 (T.length + 1) (n + T.length + 4) (by omega)
    (by
      intro t vv Cl fu ht hCl' hC0' ⟨hvv, hC, hb⟩ hfu'
      subst hvv; subst hC
      obtain ⟨rr, r0, bd0, hrr, hret, hps, hvv, hbn, hcost, hneed, hwk⟩ := b_outer mv hnv hty0 hty1 hty2 hty3 hty4 H T C P n t inf lo
        (djIter inf (outEdges H T C) n f0 t).1 (djIter inf (outEdges H T C) n f0 t).2 hn hn2 (by omega) HK hTn hTM hCl hC0 hinfv hlo
        hinfB hb fu hfu'
      refine ⟨rr, [cb r0, cs bd0], [ci n, cs inf], hrr, hret, hps, rfl, rfl, ⟨?_, rfl, ?_⟩, hcost, hneed, hwk⟩
      · rw [hvv, djIter_succ]
      · rw [djIter_succ]; exact hbn)
    (VD H T C (ofFn n (djIter inf (outEdges H T C) n f0 0).1) (doneOf n (djIter inf (outEdges H T C) n f0 0).2)) [ci n, cs inf]
    rfl rfl ⟨rfl, rfl, by simpa [djIter] using hbnd⟩ fu (by omega)
  obtain ⟨hvv, hC, hb⟩ := hIn
  subst hC
  refine ⟨res, ?_, hps, hvv, hret, hb, ?_, ?_, ?_⟩
  · simpa [djIter] using hr'
  · exact hc
  · omega
  · exact hw


set_option maxHeartbeats 8000000 in
/-- The whole body of `dijkstra`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 5) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (hty4 : mv.ty 4 = i32) (H T : List Nat) (C : List Int) (P : List Cell) (n : Nat)
    (inf lo : Int) (f0 : Nat → Int) (hn : n < M31) (hn2 : n < 2147483647)
    (HK : Proofs.TopoSortMath.HeadOK H T n) (hTn : ∀ x ∈ T, x < n) (hTM : T.length < 2147483647)
    (hCl : C.length = T.length) (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x ≤ 2305843009213693952)
    (hinfv : s64.valid inf = true) (hlo : -4611686018427387904 ≤ lo) (hinfB : inf ≤ 4611686018427387904)
    (hbnd : ∀ j, j < n → lo ≤ f0 j ∧ f0 j ≤ inf) (fu : Nat) (hfu : 2 * n + T.length + 6 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyDJ mv.nv) (gS P [ci n, cs inf]) (VD H T C (ofFn n f0) (doneOf n [])) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, cs inf] ∧
      r.vv = VD H T C (ofFn n (djIter inf (outEdges H T C) n f0 n).1) (doneOf n (djIter inf (outEdges H T C) n f0 n).2) ∧
      r.cost ≤ (320 * n + 420 * T.length + 420) * n + 40 ∧ r.need ≤ P.length + 80 ∧ r.wk ≤ (T.length + 1) * n := by
  obtain ⟨res, hres, hps, hvv, hret, hb, hc, hn', hw⟩ := l_outer mv hnv hty0 hty1 hty2 hty3 hty4 H T C P n inf lo f0 hn hn2 HK hTn hTM
    hCl hC0 hinfv hlo hinfB hbnd fu (by omega)
  have q := seqM_some hres hret (pexecM_skip mv fu _ _)
  obtain ⟨r, hr, hrret, hrps, hrvv, hcost, hneed, hwk⟩ : ∃ r : PRM, pexecM mv fu (bodyDJ mv.nv) (gS P [ci n, cs inf])
      (VD H T C (ofFn n f0) (doneOf n [])) = some r ∧ r.ret = none ∧ r.ps = gS P [ci n, cs inf] ∧
      r.vv = VD H T C (ofFn n (djIter inf (outEdges H T C) n f0 n).1) (doneOf n (djIter inf (outEdges H T C) n f0 n).2) ∧
      r.cost ≤ (320 * n + 420 * T.length + 420) * n + 40 ∧ r.need ≤ P.length + 80 ∧ r.wk ≤ (T.length + 1) * n := by
    have hl : res.ps.mem.length + res.ps.bs.length = P.length + 4 := by rw [hps]; simp [gS_size]
    refine ⟨_, q, rfl, hps, hvv, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hc ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hn' ⊢; omega
    · simp at hw ⊢; omega
  exact ⟨r, hr, hrret, hrps, hrvv, hcost, hneed, hwk⟩

end Proofs.DijkstraOldExec
