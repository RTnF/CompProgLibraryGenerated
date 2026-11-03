import Proofs.TreeFullDpExec

namespace Proofs.TreeFullDpTd
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.ForLoopC (gS_takeC)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs pexecM_branch_true pexecM_branch_false)
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (vS vr bnd v64)
open Proofs.RunLengthExec (inc_val)
open Proofs.SegmentTreeExec (AppBlk appblk_exec mx)
open Proofs.TreeFullDpBody
open Proofs.TreeDpAlg Proofs.TreeDpSpec Proofs.TreeDpMath
open Proofs.TreeFullDpExec

/-- The cells of `tree_full_dp` in the top-down loop after `full[v]` has been written. -/
abbrev CT (root n k v : Nat) (ux tot : Int) : List Cell :=
  [ci root, ci n, cs 0, ci k, ci v, cs tot, cs ux, cs tot, cs (mx ux tot), cs (mx ux tot), cs (mx ux tot), cs (mx ux tot + 1)]

abbrev CTt (v : Nat) (ux tot : Int) : List Cell :=
  [ci v, cs tot, cs ux, cs tot, cs (mx ux tot), cs (mx ux tot), cs (mx ux tot), cs (mx ux tot + 1)]

def tdval (ux pr sf : Int) : Int := mx (mx ux pr) sf + 1

def tdup (a : Arr) (v p : Nat) : List Int :=
  if a.pa.getD (a.tg.getD p 0).toNat 0 = (v : Int) then
    a.up.set (a.tg.getD p 0).toNat (tdval (a.up.getD v 0) (a.pre.getD p 0) (a.suf.getD p 0))
  else a.up

theorem s64vb (x : Int) (h0 : 0 ≤ x) (h1 : x < 4611686018427387904) : s64.valid x = true := by
  simp [Ty.valid, s64]; omega

theorem mx_valid (x y : Int) (hx : s64.valid x = true) (hy : s64.valid y = true) : s64.valid (mx x y) = true := by
  unfold mx; split <;> assumption

set_option maxHeartbeats 512000000 in
/-- One iteration of the top-down arc loop. -/
theorem td2_iter (mv : MV) (hnv : mv.nv = 9) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32) (ty5 : mv.ty 5 = s64)
    (ty6 : mv.ty 6 = s64) (ty7 : mv.ty 7 = s64) (P : List Cell) (fu : Nat) (head target : List Nat) (parent : List Int)
    (ord : List Nat) (n : Nat) (a : Arr) (R : Ro head target parent ord n a) (Ln : Lens n target.length a)
    (root k v p : Nat) (ux tot : Int) (hux : a.up.getD v 0 = ux)
    (hv : v < n) (hp : p ∈ arcs head v) (hk31 : k < 2147483648) (hrk : root < 2147483648)
    (hupv : ∀ x, s64.valid (a.up.getD x 0) = true) (htot : s64.valid tot = true)
    (hbd : (parent.getD (target.getD p 0) 0 = (v : Int)) →
      s64.valid (a.pre.getD p 0) = true ∧ s64.valid (a.suf.getD p 0) = true ∧
        s64.valid (tdval ux (a.pre.getD p 0) (a.suf.getD p 0)) = true) :
    ∃ r : PRM, pexecM mv fu (TD2body mv.nv) (gS P (CT root n k v ux tot ++ [ci p])) (VA a) = some r ∧ r.ret = none ∧
      r.ps = gS P (CT root n k v ux tot ++ [ci (p + 1)]) ∧ r.vv = VA { a with up := tdup a v p } ∧
      r.cost ≤ 3000 ∧ r.need ≤ P.length + 300 ∧ r.wk ≤ 3 := by
  have hpt : p < target.length := arc_lt head target parent ord n a R v hv p hp
  have hw : target.getD p 0 < n := R.tlt p hpt
  have hn31 := R.nb
  have hp31 : p + 1 < 2147483648 := by have := R.tlen; omega
  have hv31 : v < 2147483648 := by omega
  have hw31 : target.getD p 0 < 2147483648 := by omega
  have hkp : (CT root n k v ux tot ++ [ci p])[12]? = some (ci p) := by simp
  have hden : vdenM mv (VA a) (penvN mv.nv (gS P (CT root n k v ux tot ++ [ci p]))) (rdI 1 (vI mv.nv 12)) =
      some (target.getD p 0 : Int) :=
    rdv mv (VA a) P _ 1 12 p i32 (by omega) ty1.symm hkp (by omega) _
      (by rw [VA_get1]; exact tg_getq head target parent ord n a R p hpt) (by rw [ty1]; exact i32v _ hw31)
  have d1 := gSM_decl mv P (CT root n k v ux tot ++ [ci p]) (VA a) i32 (rdI 1 (vI mv.nv 12)) (target.getD p 0 : Int)
    (target.getD p 0 : Int) hden (conv_signed i32 rfl rfl _ (i32v _ hw31))
  have a1 := (pexecM_prim mv fu (.declare i32 true (rdI 1 (vI mv.nv 12))) _ _).trans d1
  have e8 : CT root n k v ux tot ++ [ci p] ++ [(⟨i32, (target.getD p 0 : Int)⟩ : Cell)] =
      CT root n k v ux tot ++ [ci p] ++ [ci (target.getD p 0)] := rfl
  rw [e8] at a1
  have hpw := pa_getq head target parent ord n a R (target.getD p 0) hw
  have hpwv : i32.valid (parent.getD (target.getD p 0) 0) = true := by
    obtain ⟨h0, h1⟩ := R.pav _ hw
    exact Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)
  have hc := ischild_val mv hnv ty2 P (CT root n k v ux tot ++ [ci p] ++ [ci (target.getD p 0)]) a 4 13 v (target.getD p 0)
    (by simp) (by simp) hv31 hw31 _ hpw hpwv
  have htd_eq : tdup a v p = if parent.getD (target.getD p 0) 0 = (v : Int) then
      a.up.set (target.getD p 0) (tdval ux (a.pre.getD p 0) (a.suf.getD p 0)) else a.up := by
    unfold tdup; rw [tg_get head target parent ord n a R p hpt, R.pa, hux]; simp
  have hinc : ∀ (vv : Nat → List Int),
      ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (incI mv.nv 12)) Sk) (gS P (CT root n k v ux tot ++ [ci p])) vv = some r2 ∧
        r2.ret = none ∧ r2.ps = gS P (CT root n k v ux tot ++ [ci (p + 1)]) ∧ r2.vv = vv ∧ r2.cost ≤ 100 ∧
        r2.need ≤ P.length + 100 ∧ r2.wk = 0 := by
    intro vv
    have e2 := inc_val mv vv _ (mv.nv + 12) p (envs mv P (CT root n k v ux tot ++ [ci p]) 12 (ci p) (by simp) (i32vn p (by omega))) hp31
    have s2 := gSM_assign mv P (CT root n k v ux tot ++ [ci p]) vv 12 (by simp) i32 _ _ _ e2 (ci p) (by simp) rfl
      (i32vn p (by omega)) (conv_signed i32 rfl rfl _ (i32vn (p + 1) (by omega)))
    have eB : (CT root n k v ux tot ++ [ci p]).set 12 ⟨i32, ((p + 1 : Nat) : Int)⟩ = CT root n k v ux tot ++ [ci (p + 1)] := rfl
    rw [eB] at s2
    have a2 := (pexecM_prim mv fu (incI mv.nv 12) _ _).trans s2
    have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  by_cases hch : parent.getD (target.getD p 0) 0 = (v : Int)
  · rw [if_pos hch] at hc
    obtain ⟨hprv, hsfv, htdv⟩ := hbd hch
    have hux_v : s64.valid ux = true := by rw [← hux]; exact hupv v
    have hm1 : s64.valid (mx ux (a.pre.getD p 0)) = true := mx_valid _ _ hux_v hprv
    have hm2 : s64.valid (mx (mx ux (a.pre.getD p 0)) (a.suf.getD p 0)) = true := mx_valid _ _ hm1 hsfv
    set cl0 := CT root n k v ux tot ++ [ci p] ++ [ci (target.getD p 0)] with hcl0
    have hup7 : ∀ cl : List Cell, ∀ c : Nat, cl[c]? = some (ci v) → c = 4 → True := fun _ _ _ _ => trivial
    -- first `apply`: max (up[v]) (pre[p])
    have hX1 : vdenM mv (VA a) (penvN mv.nv (gS P cl0)) (rdS 7 (vI mv.nv 4)) = some ux :=
      rdv mv (VA a) P cl0 7 4 v s64 (by omega) ty7.symm (by simp [hcl0]) hv31 ux
        (by rw [VA_get7, ← hux]; exact vec_getI a.up v (by rw [Ln.up]; exact hv)) (by rw [ty7, ← hux]; exact hupv v)
    have hY1 : vdenM mv (VA a) (penvN mv.nv (gS P (cl0 ++ [cs ux]))) (rdS 5 (vI mv.nv 12)) = some (a.pre.getD p 0) :=
      rdv mv (VA a) P _ 5 12 p s64 (by omega) ty5.symm (by simp [hcl0]) (by omega) _
        (by rw [VA_get5]; exact vec_getI a.pre p (by rw [Ln.pre]; exact hpt)) (by rw [ty5]; exact hprv)
    set cl1 := cl0 ++ [cs ux, cs (a.pre.getD p 0), cs (mx ux (a.pre.getD p 0)), cs (mx ux (a.pre.getD p 0))] with hcl1
    have hX2 : vdenM mv (VA a) (penvN mv.nv (gS P cl1)) (vS mv.nv 17) = some (mx ux (a.pre.getD p 0)) :=
      cellS mv _ P _ 17 _ (by simp [hcl1, hcl0]) hm1
    have hY2 : vdenM mv (VA a) (penvN mv.nv (gS P (cl1 ++ [cs (mx ux (a.pre.getD p 0))]))) (rdS 6 (vI mv.nv 12)) =
        some (a.suf.getD p 0) :=
      rdv mv (VA a) P _ 6 12 p s64 (by omega) ty6.symm (by simp [hcl1, hcl0]) (by omega) _
        (by rw [VA_get6]; exact vec_getI a.suf p (by rw [Ln.suf]; exact hpt)) (by rw [ty6]; exact hsfv)
    set m2 := mx (mx ux (a.pre.getD p 0)) (a.suf.getD p 0) with hm2d
    set cl2 := cl1 ++ [cs (mx ux (a.pre.getD p 0)), cs (a.suf.getD p 0), cs m2, cs m2] with hcl2
    have hl2 : cl2.length = 22 := by simp [hcl2, hcl1, hcl0]
    have hm2s : s64.valid (m2 + 1) = true := htdv
    have hdd : s64.valid m2 = true := hm2
    -- REST2
    have hd21 := gSM_decl mv P cl2 (VA a) s64 (vS mv.nv 21) m2 m2 (cellS mv _ P _ 21 m2 (by simp [hcl2, hcl1, hcl0]) hm2)
      (conv_signed s64 rfl rfl _ hm2)
    have ad21 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 21)) _ _).trans hd21
    have hd22 := gSM_decl mv P (cl2 ++ [cs m2]) (VA a) s64 (succS mv.nv 22) (m2 + 1) (m2 + 1)
      (succ_val mv _ P _ 22 m2 (by simp [hcl2, hcl1, hcl0]) hm2 hm2s) (conv_signed s64 rfl rfl _ hm2s)
    have ad22 := (pexecM_prim mv fu (.declare s64 true (succS mv.nv 22)) _ _).trans hd22
    have hx23 : vdenM mv (VA a) (penvN mv.nv (gS P (cl2 ++ [cs m2] ++ [cs (m2 + 1)]))) (vS mv.nv 23) = some (m2 + 1) :=
      cellS mv _ P _ 23 _ (by simp [hcl2, hcl1, hcl0]) hm2s
    have hi13 : vdenM mv (VA a) (penvN mv.nv (gS P (cl2 ++ [cs m2] ++ [cs (m2 + 1)]))) (.cast u64 (.variable i32 (mv.nv + 13))) =
        some ((target.getD p 0 : Nat) : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact cidx_den _ _ (target.getD p 0) (envs mv P (cl2 ++ [cs m2] ++ [cs (m2 + 1)]) 13 (ci (target.getD p 0))
        (by simp [hcl2, hcl1, hcl0]) (i32vn _ hw31)) hw31
    have hlt7 : target.getD p 0 < ((VA a) 7).length := by rw [VA_get7, Ln.up]; exact hw
    have hv7 : (mv.ty 7).valid (m2 + 1) = true := by rw [ty7]; exact hm2s
    have hw7 := pstmtM_write_ok mv (gS P (cl2 ++ [cs m2] ++ [cs (m2 + 1)])) (VA a) 7 (by omega)
      (.cast u64 (.variable i32 (mv.nv + 13))) (vS mv.nv 23) (m2 + 1) (target.getD p 0) hx23 hi13 hlt7 hv7
    rw [ty7, VA_get7, VA_set7] at hw7
    have aw7 := (pexecM_prim mv fu (wrS 7 (vI mv.nv 13) (vS mv.nv 23)) _ _).trans hw7
    have sw := seqM_some aw7 rfl (pexecM_skip mv fu _ _)
    have s22 := seqM_some ad22 rfl sw
    have s21 := seqM_some ad21 rfl s22
    -- second AppBlk
    obtain ⟨rB, hB, retB, psB, vvB, cB, nB, wB⟩ := appblk_exec mv P (VA a) fu cl1 18 (by simp [hcl1, hcl0]) (vS mv.nv 17)
      (rdS 6 (vI mv.nv 12)) (mx ux (a.pre.getD p 0)) (a.suf.getD p 0) hm1 hsfv hX2 hY2 _ _ s21
    -- first AppBlk
    obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P (VA a) fu cl0 14 (by simp [hcl0]) (rdS 7 (vI mv.nv 4))
      (rdS 5 (vI mv.nv 12)) ux (a.pre.getD p 0) hux_v hprv hX1 hY1 _ _ hB
    have sc := pexecM_scope mv fu _ _ _ _ hA
    rw [psA, psB] at sc
    have eq2 : cl2 ++ [cs m2] ++ [cs (m2 + 1)] = cl0 ++ [cs ux, cs (a.pre.getD p 0), cs (mx ux (a.pre.getD p 0)),
        cs (mx ux (a.pre.getD p 0)), cs (mx ux (a.pre.getD p 0)), cs (a.suf.getD p 0), cs m2, cs m2, cs m2, cs (m2 + 1)] := by
      simp [hcl2, hcl1]
    rw [eq2] at sc
    have tk := gS_takeC P cl0 cl0 [cs ux, cs (a.pre.getD p 0), cs (mx ux (a.pre.getD p 0)),
        cs (mx ux (a.pre.getD p 0)), cs (mx ux (a.pre.getD p 0)), cs (a.suf.getD p 0), cs m2, cs m2, cs m2, cs (m2 + 1)] rfl
    simp only [tk] at sc
    have b1 := seqM_some sc (by show rA.ret = none; rw [retA, retB]) (pexecM_skip mv fu _ _)
    have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b1
    have b4 := seqM_some b3 (by simp) (pexecM_skip mv fu _ _)
    have s1 := seqM_some a1 rfl b4
    have b5 := pexecM_scope mv fu _ _ _ _ s1
    have tk2 := gS_takeC P (CT root n k v ux tot ++ [ci p]) (CT root n k v ux tot ++ [ci p]) [ci (target.getD p 0)] rfl
    rw [hcl0] at b5
    simp only [tk2] at b5
    obtain ⟨r3, hr3, ret3, ps3, vv3, c3, n3, w3⟩ := hinc (VA { a with up := a.up.set (target.getD p 0) (m2 + 1) })
    have b6 := seqM_some b5 (by simp) (by rw [vvA, vvB]; exact hr3)
    refine ⟨_, b6, ret3, ps3, ?_, ?_, ?_, ?_⟩
    · rw [htd_eq, if_pos hch]; exact vv3
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA cB c3 ⊢; omega
    · have hB' := nB (P.length + 250) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]; omega)
        (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
      have hA' := nA (P.length + 250) hB' (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' n3 ⊢
      omega
    · simp at wA wB w3 ⊢; omega
  · rw [if_neg hch] at hc
    have b3 := pexecM_branch_false mv fu _ (.sequence (.scope (TD2act mv.nv)) Sk) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    have s1 := seqM_some a1 rfl b4
    have b5 := pexecM_scope mv fu _ _ _ _ s1
    have tk := gS_takeC P (CT root n k v ux tot ++ [ci p]) (CT root n k v ux tot ++ [ci p]) [ci (target.getD p 0)] rfl
    simp only [tk] at b5
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ := hinc (VA a)
    have b6 := seqM_some b5 (by simp) hr2
    refine ⟨_, b6, ret2, ps2, ?_, ?_, ?_, ?_⟩
    · rw [htd_eq, if_neg hch]; exact vv2
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n2 ⊢; omega
    · simp at w2 ⊢; omega

theorem Ro_updUp {head target : List Nat} {parent : List Int} {ord : List Nat} {n : Nat} {a : Arr}
    (R : Ro head target parent ord n a) (x : List Int) : Ro head target parent ord n { a with up := x } :=
  ⟨R.hd, R.tg, R.pa, R.od, R.hlen, R.hmono, R.hlast, R.tlen, R.tlt, R.nb, R.palen, R.pav, R.odlen, R.odlt⟩

/-- The condition `p < head[v + 1]` of the top-down arc loop. -/
theorem cond2t_val (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (P : List Cell) (cl : List Cell) (a : Arr)
    (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (R : Ro head target parent ord n a)
    (v p : Nat) (hv : v < n) (h4 : cl[4]? = some (ci v)) (h12 : cl[12]? = some (ci p)) (hp : p < 2147483648) :
    vdenM mv (VA a) (penvN mv.nv (gS P cl)) (TD2cond mv.nv) = some (if p < head.getD (v + 1) 0 then 1 else 0) := by
  have hh : i32.valid (head.getD (v + 1) 0 : Int) = true := by
    have := head_le head target parent ord n a R v hv
    have := R.tlen
    exact i32vn _ (by omega)
  have r := rdv1 mv (VA a) P cl 0 4 v i32 (by omega) ty0.symm h4 (by have := R.nb; omega) (head.getD (v + 1) 0 : Int)
    (by rw [VA_get0]; exact hd_getq head target parent ord n a R (v + 1) (by omega)) (by rw [ty0]; exact hh)
  have c := cellI mv (VA a) P cl 12 p h12 hp
  unfold TD2cond
  rw [vdenM_binary mv _ _ bT .lt _ _ rfl, c, Option.bind_some, r, Option.bind_some]
  generalize head.getD (v + 1) 0 = H
  by_cases h : p < H
  · have : (p : Int) < (H : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((p : Int) < (H : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

/-! ### The top-down arc loop: invariant -/

structure AT (head target : List Nat) (parent : List Int) (v p : Nat) (up0 up' : List Int) (ux : Int)
    (pre suf : List Int) (Bn : Int) : Prop where
  done : ∀ q ∈ kidArcs head target parent v, q < p → up'.getD (tgt target q) 0 = tdval ux (pre.getD q 0) (suf.getD q 0)
  rest : ∀ x, (∀ q ∈ kidArcs head target parent v, q < p → tgt target q ≠ x) → up'.getD x 0 = up0.getD x 0
  len : up'.length = up0.length
  bnd : ∀ x, 0 ≤ up'.getD x 0 ∧ up'.getD x 0 ≤ Bn + 1

theorem at_init (head target : List Nat) (parent : List Int) (v : Nat) (up0 : List Int) (ux : Int) (pre suf : List Int) (Bn : Int)
    (h : ∀ x, 0 ≤ up0.getD x 0 ∧ up0.getD x 0 ≤ Bn) :
    AT head target parent v (head.getD v 0) up0 up0 ux pre suf Bn :=
  ⟨fun q hq hlt => absurd hlt (by have := (kidArcs_ge head target parent v q hq).1; omega), fun _ _ => rfl, rfl,
    fun x => ⟨(h x).1, by have := (h x).2; omega⟩⟩

theorem tdval_bnd (ux pr sf Bn n : Int) (hu : 0 ≤ ux ∧ ux ≤ Bn) (hp : 0 ≤ pr ∧ pr ≤ n) (hs : 0 ≤ sf ∧ sf ≤ n)
    (hn : n ≤ Bn) : 0 ≤ tdval ux pr sf ∧ tdval ux pr sf ≤ Bn + 1 := by
  unfold tdval mx; split <;> split <;> omega

theorem at_child (head target : List Nat) (parent : List Int) (v p : Nat) (up0 up' : List Int) (ux : Int) (pre suf : List Int) (Bn : Int)
    (I : AT head target parent v p up0 up' ux pre suf Bn) (hpk : p ∈ kidArcs head target parent v)
    (hinj : ∀ q ∈ kidArcs head target parent v, ∀ q' ∈ kidArcs head target parent v, tgt target q = tgt target q' → q = q')
    (hl : tgt target p < up'.length) (hb : 0 ≤ tdval ux (pre.getD p 0) (suf.getD p 0) ∧ tdval ux (pre.getD p 0) (suf.getD p 0) ≤ Bn + 1) :
    AT head target parent v (p + 1) up0 (up'.set (tgt target p) (tdval ux (pre.getD p 0) (suf.getD p 0))) ux pre suf Bn := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq hqlt
    rw [Proofs.SegTreeMath.getD_setE]
    by_cases hqp : q = p
    · subst hqp; rw [if_pos ⟨rfl, hl⟩]
    · rw [if_neg (fun h => hqp (hinj q hq p hpk h.1))]
      exact I.done q hq (by omega)
  · intro x hx
    rw [Proofs.SegTreeMath.getD_setE]
    have hxp : x ≠ tgt target p := fun h => hx p hpk (by omega) h.symm
    rw [if_neg (fun h => hxp h.1)]
    exact I.rest x (fun q hq hqp => hx q hq (by omega))
  · simp [I.len]
  · intro x
    rw [Proofs.SegTreeMath.getD_setE]
    by_cases hx : x = tgt target p ∧ tgt target p < up'.length
    · rw [if_pos hx]; exact hb
    · rw [if_neg hx]; exact I.bnd x

theorem at_other (head target : List Nat) (parent : List Int) (v p : Nat) (up0 up' : List Int) (ux : Int) (pre suf : List Int) (Bn : Int)
    (I : AT head target parent v p up0 up' ux pre suf Bn) (hpk : p ∉ kidArcs head target parent v) :
    AT head target parent v (p + 1) up0 up' ux pre suf Bn := by
  refine ⟨?_, ?_, I.len, I.bnd⟩
  · intro q hq hqlt
    have : q < p := by
      have : q ≠ p := fun h => hpk (h ▸ hq)
      omega
    exact I.done q hq this
  · intro x hx
    exact I.rest x (fun q hq hqp => hx q hq (by
      have : q ≠ p := fun e => hpk (e ▸ hq)
      omega))

theorem td_eq (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (v p : Nat) (hv : v < n) (hp : p ∈ arcs head v) (ux : Int) (hux : a.up.getD v 0 = ux) :
    tdup a v p = if p ∈ kidArcs head target parent v then
      a.up.set (tgt target p) (tdval ux (a.pre.getD p 0) (a.suf.getD p 0)) else a.up := by
  have hpt : p < target.length := arc_lt head target parent ord n a R v hv p hp
  have h := i1_child_iff head target parent ord n a R v p hv hp
  have e : (a.tg.getD p 0).toNat = tgt target p := by
    rw [tg_get head target parent ord n a R p hpt]; simp [tgt]
  unfold tdup
  rw [e, hux]
  rw [e] at h
  by_cases hc : a.pa.getD (tgt target p) 0 = (v : Int)
  · rw [if_pos hc, if_pos (h.mp hc)]
  · rw [if_neg hc, if_neg (fun hk => hc (h.mpr hk))]


set_option maxHeartbeats 128000000 in
/-- The top-down arc loop, from the state at arc `p`. -/
theorem td2_loop (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = s64) (ty7 : mv.ty 7 = s64) (P : List Cell) (head target : List Nat)
    (parent : List Int) (ord : List Nat) (n : Nat) (a0 : Arr) (R : Ro head target parent ord n a0)
    (Ln : Lens n target.length a0) (root k v : Nat) (hv : v < n) (hrk : root < 2147483648) (hk31 : k < 2147483648)
    (ux tot : Int) (hux : a0.up.getD v 0 = ux) (htot : s64.valid tot = true) (Bn : Int)
    (hBn : (n : Int) ≤ Bn ∧ Bn + 1 < 4611686018427387904) (hux0 : 0 ≤ ux ∧ ux ≤ Bn)
    (hpre : ∀ q ∈ kidArcs head target parent v, 0 ≤ a0.pre.getD q 0 ∧ a0.pre.getD q 0 ≤ n)
    (hsuf : ∀ q ∈ kidArcs head target parent v, 0 ≤ a0.suf.getD q 0 ∧ a0.suf.getD q 0 ≤ n)
    (hinj : ∀ q ∈ kidArcs head target parent v, ∀ q' ∈ kidArcs head target parent v, tgt target q = tgt target q' → q = q')
    (hself : ∀ q ∈ kidArcs head target parent v, tgt target q ≠ v) :
    ∀ (d p : Nat) (up' : List Int) (fu : Nat), head.getD (v + 1) 0 - p = d → head.getD v 0 ≤ p →
      p ≤ head.getD (v + 1) 0 → AT head target parent v p a0.up up' ux a0.pre a0.suf Bn → d + 1 ≤ fu →
      ∃ (res : PRM) (up'' : List Int),
        pexecM mv fu (.whileLoop (TD2cond mv.nv) (TD2body mv.nv)) (gS P (CT root n k v ux tot ++ [ci p])) (VA { a0 with up := up' }) = some res ∧
        res.ret = none ∧ res.ps = gS P (CT root n k v ux tot ++ [ci (head.getD (v + 1) 0)]) ∧
        res.vv = VA { a0 with up := up'' } ∧
        AT head target parent v (head.getD (v + 1) 0) a0.up up'' ux a0.pre a0.suf Bn ∧
        res.cost ≤ 3100 * d + 30 ∧ res.need ≤ P.length + 300 ∧ res.wk ≤ 3 * d := by
  have hend := head_le head target parent ord n a0 R v hv
  have htl := R.tlen
  have hn31 := R.nb
  intro d
  induction d with
  | zero =>
    intro p up' fu hd hp0 hpe I hfu
    have hpeq : p = head.getD (v + 1) 0 := by omega
    subst hpeq
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond2t_val mv hnv ty0 P (CT root n k v ux tot ++ [ci (head.getD (v + 1) 0)]) { a0 with up := up' } head target parent ord n
      (Ro_updUp R up') v (head.getD (v + 1) 0) hv (by simp) (by simp) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, up', rfl, rfl, rfl, rfl, I, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro p up' fu hd hp0 hpe I hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hpin : p ∈ arcs head v := by
      unfold arcs; rw [List.mem_range'_1]; omega
    have hpt : p < target.length := arc_lt head target parent ord n a0 R v hv p hpin
    have hc := cond2t_val mv hnv ty0 P (CT root n k v ux tot ++ [ci p]) { a0 with up := up' } head target parent ord n
      (Ro_updUp R up') v p hv (by simp) (by simp) (by omega)
    rw [if_pos (by omega)] at hc
    have Ln' : Lens n target.length { a0 with up := up' } := ⟨Ln.dp, Ln.pre, Ln.suf, by rw [I.len]; exact Ln.up, Ln.fu⟩
    have huv : up'.getD v 0 = ux := by
      rw [I.rest v (fun q hq _ h => hself q hq h)]
      exact hux
    have hupv : ∀ x, s64.valid ((({ a0 with up := up' } : Arr)).up.getD x 0) = true :=
      fun x => s64vb (up'.getD x 0) (I.bnd x).1 (by have := (I.bnd x).2; have := hBn.2; omega)
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := td2_iter mv hnv ty1 ty2 ty5 ty6 ty7 P (fu' + 1) head target parent ord n
      { a0 with up := up' } (Ro_updUp R up') Ln' root k v p ux tot huv hv hpin hk31 hrk hupv htot (by
        intro hch
        have hk : p ∈ kidArcs head target parent v :=
          List.mem_filter.mpr ⟨hpin, by simpa [tgt] using hch⟩
        obtain ⟨h0, h1⟩ := hpre p hk
        obtain ⟨h2, h3⟩ := hsuf p hk
        have hb := tdval_bnd ux (a0.pre.getD p 0) (a0.suf.getD p 0) Bn n hux0 ⟨h0, h1⟩ ⟨h2, h3⟩ hBn.1
        exact ⟨s64vb (a0.pre.getD p 0) h0 (by omega), s64vb (a0.suf.getD p 0) h2 (by omega),
          s64vb (tdval ux (a0.pre.getD p 0) (a0.suf.getD p 0)) hb.1 (by omega)⟩)
    have hq := td_eq head target parent ord n { a0 with up := up' } (Ro_updUp R up') v p hv hpin ux huv
    have hI' : AT head target parent v (p + 1) a0.up (tdup { a0 with up := up' } v p) ux a0.pre a0.suf Bn := by
      rw [hq]
      by_cases hk : p ∈ kidArcs head target parent v
      · rw [if_pos hk]
        obtain ⟨h0, h1⟩ := hpre p hk
        obtain ⟨h2, h3⟩ := hsuf p hk
        exact at_child head target parent v p a0.up up' ux a0.pre a0.suf Bn I hk hinj
          (by rw [I.len, Ln.up]; exact R.tlt p hpt) (tdval_bnd ux (a0.pre.getD p 0) (a0.suf.getD p 0) Bn n hux0 ⟨h0, h1⟩ ⟨h2, h3⟩ hBn.1)
      · rw [if_neg hk]
        exact at_other head target parent v p a0.up up' ux a0.pre a0.suf Bn I hk
    obtain ⟨r2, up'', h2, ret2, ps2, vv2, hI2, c2, n2, w2⟩ :=
      ih (p + 1) (tdup { a0 with up := up' } v p) fu' (by omega) (by omega) (by omega) hI' (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
    rw [h1]
    simp only [ret1, ps1, vv1]
    rw [h2]
    simp only
    refine ⟨_, up'', rfl, ret2, ps2, vv2, hI2, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

set_option maxHeartbeats 512000000 in
/-- The body of the top-down loop for the vertex `v = ord[k]`. -/
theorem td_iter (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = s64) (ty7 : mv.ty 7 = s64) (ty8 : mv.ty 8 = s64)
    (P : List Cell) (fu : Nat) (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (Ln : Lens n target.length a) (root k v : Nat) (hk : k < n)
    (hvk : v = ord.getD k 0) (hrk : root < 2147483648) (ux tot : Int) (hux : a.up.getD v 0 = ux) (htote : a.fu.getD v 0 = tot)
    (Bn : Int) (hBn : (n : Int) ≤ Bn ∧ Bn + 1 < 4611686018427387904)
    (hup0 : ∀ x, 0 ≤ a.up.getD x 0 ∧ a.up.getD x 0 ≤ Bn) (htb : 0 ≤ tot ∧ tot ≤ n)
    (hpre : ∀ q ∈ kidArcs head target parent v, 0 ≤ a.pre.getD q 0 ∧ a.pre.getD q 0 ≤ n)
    (hsuf : ∀ q ∈ kidArcs head target parent v, 0 ≤ a.suf.getD q 0 ∧ a.suf.getD q 0 ≤ n)
    (hinj : ∀ q ∈ kidArcs head target parent v, ∀ q' ∈ kidArcs head target parent v, tgt target q = tgt target q' → q = q')
    (hself : ∀ q ∈ kidArcs head target parent v, tgt target q ≠ v)
    (hfu : head.getD (v + 1) 0 - head.getD v 0 + 1 ≤ fu) :
    ∃ (r : PRM) (up'' : List Int),
      pexecM mv fu (TDiter mv.nv) (gS P [ci root, ci n, cs 0, ci k]) (VA a) = some r ∧ r.ret = none ∧
      r.ps = gS P (CT root n k v ux tot) ∧
      r.vv = VA { a with fu := a.fu.set v (mx ux tot + 1), up := up'' } ∧
      AT head target parent v (head.getD (v + 1) 0) a.up up'' ux a.pre a.suf Bn ∧
      r.cost ≤ 3100 * (head.getD (v + 1) 0 - head.getD v 0) + 1000 ∧ r.need ≤ P.length + 350 ∧
      r.wk ≤ 3 * (head.getD (v + 1) 0 - head.getD v 0) + 3 := by
  have hn31 := R.nb
  have hvn : v < n := by
    rw [hvk]
    apply R.odlt
    have : ord.getD k 0 = ord[k]'(by rw [R.odlen]; exact hk) := by
      simp [List.getD_eq_getElem?_getD, show k < ord.length by rw [R.odlen]; exact hk]
    rw [this]; exact List.getElem_mem _
  have hv31 : v < 2147483648 := by omega
  have hk31 : k < 2147483648 := by omega
  have hend := head_le head target parent ord n a R v hvn
  have hmono := R.hmono v hvn
  have htl := R.tlen
  have hux0 : 0 ≤ ux ∧ ux ≤ Bn := by rw [← hux]; exact hup0 v
  have hux_v : s64.valid ux = true := s64vb ux hux0.1 (by omega)
  have htot_v : s64.valid tot = true := s64vb tot htb.1 (by omega)
  have hm : mx ux tot = ux ∨ mx ux tot = tot := by unfold mx; split <;> simp
  have hmb : 0 ≤ mx ux tot ∧ mx ux tot ≤ Bn := by unfold mx; split <;> omega
  have hm_v : s64.valid (mx ux tot) = true := mx_valid _ _ hux_v htot_v
  have hm1_v : s64.valid (mx ux tot + 1) = true := s64vb _ (by omega) (by omega)
  -- v = ord[k]
  have S0v : ([ci root, ci n, cs 0, ci k] : List Cell)[3]? = some (ci k) := by simp
  have hdv : vdenM mv (VA a) (penvN mv.nv (gS P [ci root, ci n, cs 0, ci k])) (rdI 3 (vI mv.nv 3)) = some (v : Int) :=
    rdv mv (VA a) P _ 3 3 k i32 (by omega) ty3.symm S0v hk31 (v : Int)
      (by rw [VA_get3, hvk]; exact od_getq head target parent ord n a R k hk) (by rw [ty3]; exact i32vn _ hv31)
  have d1 := gSM_decl mv P [ci root, ci n, cs 0, ci k] (VA a) i32 (rdI 3 (vI mv.nv 3)) (v : Int) (v : Int) hdv
    (conv_signed i32 rfl rfl _ (i32vn _ hv31))
  have a1 := (pexecM_prim mv fu (.declare i32 true (rdI 3 (vI mv.nv 3))) _ _).trans d1
  have e1 : [ci root, ci n, cs 0, ci k] ++ [(⟨i32, (v : Int)⟩ : Cell)] = [ci root, ci n, cs 0, ci k, ci v] := rfl
  rw [e1] at a1
  -- tot = full[v]
  have hdt : vdenM mv (VA a) (penvN mv.nv (gS P [ci root, ci n, cs 0, ci k, ci v])) (rdS 8 (vI mv.nv 4)) = some tot :=
    rdv mv (VA a) P _ 8 4 v s64 (by omega) ty8.symm (by simp) hv31 tot
      (by rw [VA_get8, ← htote]; exact vec_getI a.fu v (by rw [Ln.fu]; exact hvn)) (by rw [ty8]; exact htot_v)
  have d2 := gSM_decl mv P [ci root, ci n, cs 0, ci k, ci v] (VA a) s64 (rdS 8 (vI mv.nv 4)) tot tot hdt
    (conv_signed s64 rfl rfl _ htot_v)
  have a2 := (pexecM_prim mv fu (.declare s64 true (rdS 8 (vI mv.nv 4))) _ _).trans d2
  have e2 : [ci root, ci n, cs 0, ci k, ci v] ++ [(⟨s64, tot⟩ : Cell)] = [ci root, ci n, cs 0, ci k, ci v, cs tot] := rfl
  rw [e2] at a2
  -- the `apply` block
  have hX : vdenM mv (VA a) (penvN mv.nv (gS P [ci root, ci n, cs 0, ci k, ci v, cs tot])) (rdS 7 (vI mv.nv 4)) = some ux :=
    rdv mv (VA a) P _ 7 4 v s64 (by omega) ty7.symm (by simp) hv31 ux
      (by rw [VA_get7, ← hux]; exact vec_getI a.up v (by rw [Ln.up]; exact hvn)) (by rw [ty7]; exact hux_v)
  have hY : vdenM mv (VA a) (penvN mv.nv (gS P ([ci root, ci n, cs 0, ci k, ci v, cs tot] ++ [cs ux]))) (vS mv.nv 5) = some tot :=
    cellS mv _ P _ 5 tot (by simp) htot_v
  -- the rest of the block
  set a0 : Arr := { a with fu := a.fu.set v (mx ux tot + 1) } with ha0
  have R0 : Ro head target parent ord n a0 :=
    ⟨R.hd, R.tg, R.pa, R.od, R.hlen, R.hmono, R.hlast, R.tlen, R.tlt, R.nb, R.palen, R.pav, R.odlen, R.odlt⟩
  have Ln0 : Lens n target.length a0 :=
    ⟨Ln.dp, Ln.pre, Ln.suf, Ln.up, by show (a.fu.set v (mx ux tot + 1)).length = n; simp [Ln.fu]⟩
  have hCT : [ci root, ci n, cs 0, ci k, ci v, cs tot] ++ [cs ux, cs tot, cs (mx ux tot), cs (mx ux tot)] ++ [cs (mx ux tot)] ++
      [cs (mx ux tot + 1)] = CT root n k v ux tot := rfl
  have d10 := gSM_decl mv P ([ci root, ci n, cs 0, ci k, ci v, cs tot] ++ [cs ux, cs tot, cs (mx ux tot), cs (mx ux tot)]) (VA a) s64
    (vS mv.nv 9) (mx ux tot) (mx ux tot) (cellS mv _ P _ 9 _ (by simp) hm_v) (conv_signed s64 rfl rfl _ hm_v)
  have a10 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 9)) _ _).trans d10
  have d11 := gSM_decl mv P ([ci root, ci n, cs 0, ci k, ci v, cs tot] ++ [cs ux, cs tot, cs (mx ux tot), cs (mx ux tot)] ++ [cs (mx ux tot)])
    (VA a) s64 (succS mv.nv 10) (mx ux tot + 1) (mx ux tot + 1) (succ_val mv _ P _ 10 _ (by simp) hm_v hm1_v)
    (conv_signed s64 rfl rfl _ hm1_v)
  have a11 := (pexecM_prim mv fu (.declare s64 true (succS mv.nv 10)) _ _).trans d11
  rw [hCT] at a11
  have hx11 : vdenM mv (VA a) (penvN mv.nv (gS P (CT root n k v ux tot))) (vS mv.nv 11) = some (mx ux tot + 1) :=
    cellS mv _ P _ 11 _ (by simp) hm1_v
  have hi4 : vdenM mv (VA a) (penvN mv.nv (gS P (CT root n k v ux tot))) (.cast u64 (.variable i32 (mv.nv + 4))) = some (v : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ _ v (envs mv P (CT root n k v ux tot) 4 (ci v) (by simp) (i32vn v hv31)) (show v < 2147483648 by omega)
  have hlt8 : v < ((VA a) 8).length := by rw [VA_get8, Ln.fu]; exact hvn
  have hv8 : (mv.ty 8).valid (mx ux tot + 1) = true := by rw [ty8]; exact hm1_v
  have hw8 := pstmtM_write_ok mv (gS P (CT root n k v ux tot)) (VA a) 8 (by omega) (.cast u64 (.variable i32 (mv.nv + 4)))
    (vS mv.nv 11) (mx ux tot + 1) v hx11 hi4 hlt8 hv8
  rw [ty8, VA_get8, VA_set8] at hw8
  have aw8 := (pexecM_prim mv fu (wrS 8 (vI mv.nv 4) (vS mv.nv 11)) _ _).trans hw8
  -- the arc loop
  have hh : (CT root n k v ux tot)[4]? = some (ci v) := by simp
  have hhd : i32.valid (head.getD v 0 : Int) = true := i32vn _ (by omega)
  have hdp1 : vdenM mv (VA a0) (penvN mv.nv (gS P (CT root n k v ux tot))) (rdI 0 (vI mv.nv 4)) = some (head.getD v 0 : Int) :=
    rdv mv (VA a0) P _ 0 4 v i32 (by omega) ty0.symm hh hv31 _
      (by rw [VA_get0]; exact hd_getq head target parent ord n a0 R0 v (by omega)) (by rw [ty0]; exact hhd)
  have d4 := gSM_decl mv P (CT root n k v ux tot) (VA a0) i32 (rdI 0 (vI mv.nv 4)) (head.getD v 0 : Int) (head.getD v 0 : Int) hdp1
    (conv_signed i32 rfl rfl _ hhd)
  have a4 := (pexecM_prim mv fu (.declare i32 true (rdI 0 (vI mv.nv 4))) _ _).trans d4
  obtain ⟨rL, up'', hL, retL, psL, vvL, hAT, cL, nL, wL⟩ := td2_loop mv hnv ty0 ty1 ty2 ty5 ty6 ty7 P head target parent ord n a0 R0 Ln0
    root k v hvn hrk hk31 ux tot hux htot_v Bn hBn hux0 hpre hsuf hinj hself (head.getD (v + 1) 0 - head.getD v 0) (head.getD v 0)
    a0.up fu rfl (le_refl _) hmono (at_init head target parent v a0.up ux a0.pre a0.suf Bn hup0) hfu
  have hL' : pexecM mv fu (.whileLoop (TD2cond mv.nv) (TD2body mv.nv)) (gS P (CT root n k v ux tot ++ [ci (head.getD v 0)])) (VA a0) = some rL := hL
  have sL := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have s4 := seqM_some a4 rfl sL
  have sc4 := pexecM_scope mv fu _ _ _ _ s4
  have tk4 := gS_takeC P (CT root n k v ux tot) (CT root n k v ux tot) [ci (head.getD (v + 1) 0)] rfl
  rw [psL] at sc4
  simp only [tk4] at sc4
  have c5 := seqM_some sc4 (by simp) (pexecM_skip mv fu _ _)
  have c4 := seqM_some aw8 rfl c5
  have c3 := seqM_some a11 rfl c4
  have c2 := seqM_some a10 rfl c3
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P (VA a) fu [ci root, ci n, cs 0, ci k, ci v, cs tot] 6 (by simp)
    (rdS 7 (vI mv.nv 4)) (vS mv.nv 5) ux tot hux_v htot_v hX hY _ _ c2
  have b2 := seqM_some a2 rfl hA
  have b1 := seqM_some a1 rfl b2
  refine ⟨_, up'', b1, ?_, ?_, ?_, hAT, ?_, ?_, ?_⟩
  · show rA.ret = none
    rw [retA]
  · show rA.ps = _
    exact psA
  · show rA.vv = _
    rw [vvA]; exact vvL
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA cL ⊢; omega
  · have hA' := nA (P.length + 350) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nL ⊢; omega)
      (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' ⊢
    omega
  · simp at wA wL ⊢; omega

/-! ### The top-down loop: invariant -/

/-- The bottom-up value of `full[ord j]`. -/
def totf (head target : List Nat) (parent : List Int) (ord : List Nat) (dp : List Int) (j : Nat) : Int :=
  fold M0 ((kidT head target parent (ord.getD j 0)).map fun x => dp.getD x 0)

structure TDI (head target : List Nat) (parent : List Int) (ord : List Nat) (n root : Nat) (ab : Arr) (k : Nat)
    (F U : List Int) : Prop where
  upg : ∀ x, 0 ≤ U.getD x 0 ∧ U.getD x 0 ≤ (n : Int) + k
  uplen : U.length = n
  up0 : U.getD root 0 = 0
  updone : ∀ j, j < k → ∀ q ∈ kidArcs head target parent (ord.getD j 0),
    U.getD (tgt target q) 0 = tdval (U.getD (ord.getD j 0) 0) (ab.pre.getD q 0) (ab.suf.getD q 0)
  fudone : ∀ j, j < k → F.getD (ord.getD j 0) 0 =
    mx (U.getD (ord.getD j 0) 0) (totf head target parent ord ab.dp j) + 1
  futodo : ∀ j, k ≤ j → j < n → F.getD (ord.getD j 0) 0 = totf head target parent ord ab.dp j
  fulen : F.length = n

theorem td_step (M : TS head target parent ord n root) (ab : Arr) (k : Nat) (hk : k < n) (v : Nat) (hvk : v = ord.getD k 0)
    (F U : List Int) (I : TDI head target parent ord n root ab k F U) (up'' : List Int) (ux tot : Int)
    (hux : U.getD v 0 = ux) (htot : F.getD v 0 = tot)
    (hAT : AT head target parent v (head.getD (v + 1) 0) U up'' ux ab.pre ab.suf ((n : Int) + k)) :
    TDI head target parent ord n root ab (k + 1) (F.set v (mx ux tot + 1)) up'' := by
  have hordk : k < ord.length := by rw [M.ordlen]; exact hk
  have hvn : v < n := by
    rw [hvk]; apply M.ordlt
    have : ord.getD k 0 = ord[k]'hordk := by simp [List.getD_eq_getElem?_getD, hordk]
    rw [this]; exact List.getElem_mem _
  have hposv : pos ord v = k := by rw [hvk]; exact pos_ord M.ordnd k hordk
  have hkid : ∀ q ∈ kidArcs head target parent v, tgt target q < n ∧ tgt target q ≠ v ∧ tgt target q ≠ root ∧
      k < pos ord (tgt target q) ∧ parent.getD (tgt target q) 0 = (v : Int) := by
    intro q hq
    obtain ⟨_, hxn, hxr, _, _, hpos⟩ := M.kid_facts v hvn q hq
    have hch : parent.getD (tgt target q) 0 = (v : Int) := by simpa using (List.mem_filter.mp hq).2
    exact ⟨hxn, by intro h; rw [h] at hpos; omega, hxr, by omega, hch⟩
  have hr : ∀ x, (∀ q ∈ kidArcs head target parent v, tgt target q ≠ x) → up''.getD x 0 = U.getD x 0 :=
    fun x hx => hAT.rest x (fun q hq _ => hx q hq)
  -- positions before `k` are untouched
  have hA : ∀ j, j < k → ∀ q ∈ kidArcs head target parent v, tgt target q ≠ ord.getD j 0 := by
    intro j hj q hq h
    have h1 := pos_ord M.ordnd j (by rw [M.ordlen]; omega)
    rw [← h] at h1
    have := (hkid q hq).2.2.2.1
    omega
  have hB : ∀ j, j < k → ∀ q' ∈ kidArcs head target parent (ord.getD j 0), ∀ q ∈ kidArcs head target parent v,
      tgt target q ≠ tgt target q' := by
    intro j hj q' hq' q hq h
    have h1 := (hkid q hq).2.2.2.2
    have h2 : parent.getD (tgt target q') 0 = ((ord.getD j 0 : Nat) : Int) := by simpa using (List.mem_filter.mp hq').2
    rw [h] at h1
    rw [h1] at h2
    have h3 : v = ord.getD j 0 := by exact_mod_cast h2
    rw [hvk] at h3
    have := ord_inj M.ordnd k j hordk (by rw [M.ordlen]; omega) h3
    omega
  have hne : ∀ j, j < n → j ≠ k → ord.getD j 0 ≠ v := by
    intro j hj hjk h
    rw [hvk] at h
    exact hjk (ord_inj M.ordnd j k (by rw [M.ordlen]; exact hj) hordk h)
  have hfl : v < F.length := by rw [I.fulen]; exact hvn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have := hAT.bnd x
    push_cast
    constructor
    · exact this.1
    · omega
  · rw [hAT.len]; exact I.uplen
  · rw [hr root (fun q hq => (hkid q hq).2.2.1)]; exact I.up0
  · intro j hj q hq
    by_cases hjk : j = k
    · subst hjk
      rw [← hvk] at hq ⊢
      have hqa : q < head.getD (v + 1) 0 := (kidArcs_ge head target parent v q hq).2
      rw [hAT.done q hq hqa, hr v (fun q' hq' => (hkid q' hq').2.1), hux]
    · have hj' : j < k := by omega
      rw [hr _ (fun q' hq' => hB j hj' q hq q' hq'), hr _ (fun q' hq' => hA j hj' q' hq')]
      exact I.updone j hj' q hq
  · intro j hj
    rw [Proofs.SegTreeMath.getD_setE]
    by_cases hjk : j = k
    · subst hjk
      rw [← hvk, if_pos ⟨rfl, hfl⟩, hr v (fun q' hq' => (hkid q' hq').2.1), hux]
      have : totf head target parent ord ab.dp j = tot := by
        rw [← htot, hvk]; exact (I.futodo j (le_refl _) hk).symm
      rw [this]
    · have hj' : j < k := by omega
      rw [if_neg (fun h => hne j (by omega) hjk h.1), hr _ (fun q' hq' => hA j hj' q' hq')]
      exact I.fudone j hj'
  · intro j hj hjn
    rw [Proofs.SegTreeMath.getD_setE, if_neg (fun h => hne j hjn (by omega) h.1)]
    exact I.futodo j (by omega) hjn
  · simp [I.fulen]

theorem inj_of_nodup_map (f : Nat → Nat) (l : List Nat) (h : (l.map f).Nodup) : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx y hy hxy
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨y, hy', hxy.symm⟩) h1
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd (List.mem_map.mpr ⟨x, hx', hxy⟩) h1
      · exact ih h2 x hx' y hy' hxy

theorem kid_self_ne (M : TS head target parent ord n root) (v : Nat) (hv : v < n) (q : Nat)
    (hq : q ∈ kidArcs head target parent v) : tgt target q ≠ v := by
  obtain ⟨_, _, _, _, _, hpos⟩ := M.kid_facts v hv q hq
  intro h; rw [h] at hpos; omega

theorem kid_inj (M : TS head target parent ord n root) (v : Nat) (hv : v < n) :
    ∀ q ∈ kidArcs head target parent v, ∀ q' ∈ kidArcs head target parent v, tgt target q = tgt target q' → q = q' := by
  intro q hq q' hq' h
  have hnd := kidT_nodup M v hv
  unfold kidT at hnd
  exact inj_of_nodup_map _ _ hnd q hq q' hq' h

theorem tot_bound {n : Nat} (head target : List Nat) (parent : List Int) (ab : Arr) (hg : ∀ x, 0 ≤ ab.dp.getD x 0 ∧ ab.dp.getD x 0 ≤ n) (v : Nat) :
    0 ≤ fold M0 ((kidT head target parent v).map fun x => ab.dp.getD x 0) ∧
      fold M0 ((kidT head target parent v).map fun x => ab.dp.getD x 0) ≤ n := by
  apply fold_le _ (n : Int) (Int.natCast_nonneg n)
  intro y hy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
  exact hg x

set_option maxHeartbeats 512000000 in
/-- One pass of the top-down loop body. -/
theorem td_body (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = s64) (ty7 : mv.ty 7 = s64) (ty8 : mv.ty 8 = s64)
    (P : List Cell) (fu : Nat) (head target : List Nat) (parent : List Int) (ord : List Nat) (n root : Nat)
    (M : TS head target parent ord n root) (ab : Arr) (Rb : Ro head target parent ord n ab) (Lb : Lens n target.length ab)
    (B0 : BUI head target parent ord n 0 ab) (root' k : Nat) (hk : k < n) (hrk : root' < 2147483648)
    (F U : List Int) (I : TDI head target parent ord n root ab k F U)
    (hfu : head.getD (ord.getD k 0 + 1) 0 - head.getD (ord.getD k 0) 0 + 1 ≤ fu) :
    ∃ (r : PRM) (up'' : List Int),
      pexecM mv fu (TDbody mv.nv) (gS P [ci root', ci n, cs 0, ci k]) (VA { ab with fu := F, up := U }) = some r ∧
      r.ret = none ∧ r.ps = gS P [ci root', ci n, cs 0, ci (k + 1)] ∧
      r.vv = VA { ab with fu := F.set (ord.getD k 0) (mx (U.getD (ord.getD k 0) 0) (F.getD (ord.getD k 0) 0) + 1), up := up'' } ∧
      TDI head target parent ord n root ab (k + 1)
        (F.set (ord.getD k 0) (mx (U.getD (ord.getD k 0) 0) (F.getD (ord.getD k 0) 0) + 1)) up'' ∧
      r.cost ≤ 3100 * (head.getD (ord.getD k 0 + 1) 0 - head.getD (ord.getD k 0) 0) + 1200 ∧ r.need ≤ P.length + 400 ∧
      r.wk ≤ 3 * (head.getD (ord.getD k 0 + 1) 0 - head.getD (ord.getD k 0) 0) + 3 := by
  have hn31 := Rb.nb
  have hordk : k < ord.length := by rw [Rb.odlen]; exact hk
  have hvn : ord.getD k 0 < n := by
    apply Rb.odlt
    have : ord.getD k 0 = ord[k]'hordk := by simp [List.getD_eq_getElem?_getD, hordk]
    rw [this]; exact List.getElem_mem _
  have hk31 : k < 2147483648 := by omega
  let a : Arr := { ab with fu := F, up := U }
  have Ra : Ro head target parent ord n a :=
    ⟨Rb.hd, Rb.tg, Rb.pa, Rb.od, Rb.hlen, Rb.hmono, Rb.hlast, Rb.tlen, Rb.tlt, Rb.nb, Rb.palen, Rb.pav, Rb.odlen, Rb.odlt⟩
  have La : Lens n target.length a := ⟨Lb.dp, Lb.pre, Lb.suf, I.uplen, I.fulen⟩
  have hBn : (n : Int) ≤ (n : Int) + k ∧ (n : Int) + k + 1 < 4611686018427387904 := by omega
  have hup0 : ∀ x, 0 ≤ a.up.getD x 0 ∧ a.up.getD x 0 ≤ (n : Int) + k := fun x => I.upg x
  have htb : 0 ≤ a.fu.getD (ord.getD k 0) 0 ∧ a.fu.getD (ord.getD k 0) 0 ≤ n := by
    show 0 ≤ F.getD (ord.getD k 0) 0 ∧ F.getD (ord.getD k 0) 0 ≤ n
    rw [I.futodo k (le_refl _) hk]
    exact tot_bound head target parent ab B0.glob _
  have hpre : ∀ q ∈ kidArcs head target parent (ord.getD k 0), 0 ≤ a.pre.getD q 0 ∧ a.pre.getD q 0 ≤ n := by
    intro q hq
    show 0 ≤ ab.pre.getD q 0 ∧ ab.pre.getD q 0 ≤ n
    rw [B0.pre k (Nat.zero_le _) hk q hq]
    apply fold_le _ (n : Int) (Int.natCast_nonneg n)
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact B0.glob x
  have hsuf : ∀ q ∈ kidArcs head target parent (ord.getD k 0), 0 ≤ a.suf.getD q 0 ∧ a.suf.getD q 0 ≤ n := by
    intro q hq
    show 0 ≤ ab.suf.getD q 0 ∧ ab.suf.getD q 0 ≤ n
    rw [B0.suf k (Nat.zero_le _) hk q hq]
    apply fold_le _ (n : Int) (Int.natCast_nonneg n)
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact B0.glob x
  obtain ⟨r1, up'', h1, ret1, ps1, vv1, hAT, c1, n1, w1⟩ := td_iter mv hnv ty0 ty1 ty2 ty3 ty5 ty6 ty7 ty8 P fu head target parent ord n a
    Ra La root' k (ord.getD k 0) hk rfl hrk (U.getD (ord.getD k 0) 0) (F.getD (ord.getD k 0) 0) rfl rfl ((n : Int) + k) hBn hup0 htb
    hpre hsuf (kid_inj M _ hvn) (kid_self_ne M _ hvn) hfu
  have hT := td_step M ab k hk (ord.getD k 0) rfl F U I up'' (U.getD (ord.getD k 0) 0) (F.getD (ord.getD k 0) 0) rfl rfl hAT
  have sc := pexecM_scope mv fu _ _ _ _ h1
  have eqCT : CT root' n k (ord.getD k 0) (U.getD (ord.getD k 0) 0) (F.getD (ord.getD k 0) 0) =
      [ci root', ci n, cs 0, ci k] ++ CTt (ord.getD k 0) (U.getD (ord.getD k 0) 0) (F.getD (ord.getD k 0) 0) := rfl
  rw [ps1, eqCT] at sc
  have tk := gS_takeC P [ci root', ci n, cs 0, ci k] [ci root', ci n, cs 0, ci k]
    (CTt (ord.getD k 0) (U.getD (ord.getD k 0) 0) (F.getD (ord.getD k 0) 0)) rfl
  simp only [tk] at sc
  -- the increment
  have e2 := inc_val mv (VA { ab with fu := F.set (ord.getD k 0) (mx (U.getD (ord.getD k 0) 0) (F.getD (ord.getD k 0) 0) + 1), up := up'' })
    (penvN mv.nv (gS P [ci root', ci n, cs 0, ci k])) (mv.nv + 3) k
    (envs mv P [ci root', ci n, cs 0, ci k] 3 (ci k) (by simp) (i32vn k hk31)) (by omega)
  have s2 := gSM_assign mv P [ci root', ci n, cs 0, ci k] (VA { ab with fu := F.set (ord.getD k 0) (mx (U.getD (ord.getD k 0) 0) (F.getD (ord.getD k 0) 0) + 1), up := up'' })
    3 (by simp) i32 _ _ _ e2 (ci k) (by simp) rfl (i32vn k hk31) (conv_signed i32 rfl rfl _ (i32vn (k + 1) (by omega)))
  have eB : ([ci root', ci n, cs 0, ci k] : List Cell).set 3 ⟨i32, ((k + 1 : Nat) : Int)⟩ = [ci root', ci n, cs 0, ci (k + 1)] := rfl
  rw [eB] at s2
  have a2 := (pexecM_prim mv fu (incI mv.nv 3) _ _).trans s2
  have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  have b1 := seqM_some sc (by show r1.ret = none; rw [ret1]) (by rw [vv1]; exact b2)
  refine ⟨_, up'', b1, rfl, rfl, ?_, hT, ?_, ?_, ?_⟩
  · rfl
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 ⊢; omega
  · simp at w1 ⊢; omega

theorem condTD_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (k n : Nat)
    (h3 : cl[3]? = some (ci k)) (h1 : cl[1]? = some (ci n)) (hk : k < 2147483648) (hn : n < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .lt (vI mv.nv 3) (vI mv.nv 1)) = some (if k < n then 1 else 0) := by
  have e3 := envs mv P cl 3 (ci k) h3 (i32vn k hk)
  have e1 := envs mv P cl 1 (ci n) h1 (i32vn n hn)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary]
  have e3' : (vI mv.nv 3).denote (penvN mv.nv (gS P cl)) = some (k : Int) := by
    show (NExpr.variable i32 (mv.nv + 3)).denote _ = some (k : Int)
    rw [den_variable]; exact e3
  have e1' : (vI mv.nv 1).denote (penvN mv.nv (gS P cl)) = some (n : Int) := by
    show (NExpr.variable i32 (mv.nv + 1)).denote _ = some (n : Int)
    rw [den_variable]; exact e1
  rw [e3', Option.bind_some, e1', Option.bind_some]
  by_cases h : k < n
  · have : (k : Int) < (n : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((k : Int) < (n : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 512000000 in
/-- The top-down loop `for (int k = 0; k < n; k++)`. -/
theorem td_loop (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = s64) (ty7 : mv.ty 7 = s64) (ty8 : mv.ty 8 = s64)
    (P : List Cell) (head target : List Nat) (parent : List Int) (ord : List Nat) (n root : Nat)
    (M : TS head target parent ord n root) (ab : Arr) (Rb : Ro head target parent ord n ab) (Lb : Lens n target.length ab)
    (B0 : BUI head target parent ord n 0 ab) (root' : Nat) (hrk : root' < 2147483648) :
    ∀ (d k : Nat) (F U : List Int) (fuel : Nat), n - k = d → k ≤ n → TDI head target parent ord n root ab k F U →
      d + target.length + 3 ≤ fuel →
      ∃ (res : PRM) (F' U' : List Int),
        pexecM mv fuel (.whileLoop (.binary bT .lt (vI mv.nv 3) (vI mv.nv 1)) (TDbody mv.nv))
          (gS P [ci root', ci n, cs 0, ci k]) (VA { ab with fu := F, up := U }) = some res ∧ res.ret = none ∧
        res.ps = gS P [ci root', ci n, cs 0, ci n] ∧ res.vv = VA { ab with fu := F', up := U' } ∧
        TDI head target parent ord n root ab n F' U' ∧
        res.cost + 3100 * degSum head ord k ≤ 3100 * degSum head ord n + 1300 * d + 30 ∧ res.need ≤ P.length + 400 ∧
        res.wk + 3 * degSum head ord k ≤ 3 * degSum head ord n + 3 * d := by
  have hn31 := Rb.nb
  intro d
  induction d with
  | zero =>
    intro k F U fuel hd hkn I hfu
    have hkn' : k = n := by omega
    subst hkn'
    obtain ⟨fu', rfl⟩ : ∃ fu', fuel = fu' + 1 := ⟨fuel - 1, by omega⟩
    have hc := condTD_val mv P (VA { ab with fu := F, up := U }) [ci root', ci k, cs 0, ci k] k k (by simp) (by simp) (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, F, U, rfl, rfl, rfl, rfl, I, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro k F U fuel hd hkn I hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fuel = fu' + 1 := ⟨fuel - 1, by omega⟩
    have hk : k < n := by omega
    have hc := condTD_val mv P (VA { ab with fu := F, up := U }) [ci root', ci n, cs 0, ci k] k n (by simp) (by simp) (by omega) (by omega)
    rw [if_pos hk] at hc
    have hvn : ord.getD k 0 < n := by
      apply Rb.odlt
      have hordk : k < ord.length := by rw [Rb.odlen]; exact hk
      have : ord.getD k 0 = ord[k]'hordk := by simp [List.getD_eq_getElem?_getD, hordk]
      rw [this]; exact List.getElem_mem _
    have hdeg := head_le head target parent ord n ab Rb _ hvn
    obtain ⟨r1, up'', h1, ret1, ps1, vv1, hI1, c1, n1, w1⟩ :=
      td_body mv hnv ty0 ty1 ty2 ty3 ty5 ty6 ty7 ty8 P (fu' + 1) head target parent ord n root M ab Rb Lb B0 root' k hk hrk F U I (by omega)
    obtain ⟨r2, F2, U2, h2, ret2, ps2, vv2, hI2, c2, n2, w2⟩ :=
      ih (k + 1) _ up'' fu' (by omega) (by omega) hI1 (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
    rw [h1]
    simp only [ret1, ps1, vv1]
    rw [h2]
    simp only
    refine ⟨_, F2, U2, rfl, ret2, ps2, vv2, hI2, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢
      rw [degSum_succ] at c2
      simp only [List.getD_eq_getElem?_getD] at *
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢
      rw [degSum_succ] at w2
      simp only [List.getD_eq_getElem?_getD] at *
      omega

theorem tdi_init (M : TS head target parent ord n root) (a : Arr) (Ln : Lens n target.length a) (B0 : BUI head target parent ord n 0 a)
    (hup : ∀ x, 0 ≤ a.up.getD x 0 ∧ a.up.getD x 0 ≤ n) :
    TDI head target parent ord n root a 0 a.fu (a.up.set root 0) := by
  have hr : root < a.up.length := by rw [Ln.up]; exact M.rootlt
  refine ⟨?_, ?_, ?_, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega), ?_, Ln.fu⟩
  · intro x
    rw [Proofs.SegTreeMath.getD_setE]
    by_cases h : x = root ∧ root < a.up.length
    · rw [if_pos h]; exact ⟨le_refl _, by push_cast; omega⟩
    · rw [if_neg h]; have := hup x; exact ⟨this.1, by push_cast; omega⟩
  · simp [Ln.up]
  · rw [Proofs.SegTreeMath.getD_setE, if_pos ⟨rfl, hr⟩]
  · intro j _ hj
    exact B0.tot j (Nat.zero_le _) hj

set_option maxHeartbeats 512000000 in
/-- The whole body of `tree_full_dp`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (ty4 : mv.ty 4 = s64) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = s64) (ty7 : mv.ty 7 = s64)
    (ty8 : mv.ty 8 = s64) (P : List Cell) (head target : List Nat) (parent : List Int) (ord : List Nat) (n root : Nat)
    (M : TS head target parent ord n root) (a0 : Arr) (R : Ro head target parent ord n a0) (Ln0 : Lens n target.length a0)
    (hdp : ∀ x, 0 ≤ a0.dp.getD x 0 ∧ a0.dp.getD x 0 ≤ n) (hup : ∀ x, 0 ≤ a0.up.getD x 0 ∧ a0.up.getD x 0 ≤ n)
    (fuel : Nat) (hfuel : 2 * n + target.length + 6 ≤ fuel) :
    ∃ (res : PRM) (a' : Arr) (F' U' : List Int),
      pexecM mv fuel (bodyFD mv.nv) (gS P [ci root, ci n]) (VA a0) = some res ∧ res.ret = none ∧
      res.ps = gS P [ci root, ci n, cs 0] ∧ res.vv = VA { a' with fu := F', up := U' } ∧
      BUI head target parent ord n 0 a' ∧ a'.up = a0.up ∧ TDI head target parent ord n root a' n F' U' ∧
      res.cost ≤ 5500 * target.length + 2400 * n + 600 ∧ res.need ≤ P.length + 450 ∧
      res.wk ≤ 5 * target.length + 5 * n + 8 := by
  have hn31 := R.nb
  have hrn := M.rootlt
  have hrk : root < 2147483648 := by omega
  have hnk : n < 2147483648 := by omega
  -- n - 1
  have e1 := envs mv P [ci root, ci n] 1 (ci n) (by simp) (i32vn n hnk)
  have h1 : vdenM mv (VA a0) (penvN mv.nv (gS P [ci root, ci n]))
      (.binary i32 .sub (.variable i32 (mv.nv + 1)) Proofs.TreeFullDpBody.lit1) = some ((n : Int) - 1) :=
    sub1_val mv _ _ (mv.nv + 1) n e1 hnk
  have hn1 : i32.valid ((n : Int) - 1) = true := Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)
  have d1 := gSM_decl mv P [ci root, ci n] (VA a0) i32 (.binary i32 .sub (.variable i32 (mv.nv + 1)) Proofs.TreeFullDpBody.lit1)
    ((n : Int) - 1) ((n : Int) - 1) h1 (conv_signed i32 rfl rfl _ hn1)
  have a1 := (pexecM_prim mv fuel (.declare i32 true (.binary i32 .sub (vI mv.nv 1) Proofs.TreeFullDpBody.lit1)) _ _).trans d1
  obtain ⟨rB, a', hB, retB, psB, vvB, hI0, R', Ln', cB, nB, wB, hupB⟩ := bu_loop mv hnv ty0 ty1 ty2 ty3 ty4 ty5 ty6 ty8 P M a0 R Ln0 root hrk
    n a0 fuel (le_refl _) R Ln0 (bui_init head target parent ord n a0 hdp) (by omega)
  have hL' : pexecM mv fuel (.whileLoop (.binary bT .ge (vI mv.nv 2) (.literal i32 0)) (BUbody mv.nv))
      (gS P ([ci root, ci n] ++ [(⟨i32, (n : Int) - 1⟩ : Cell)])) (VA a0) = some rB := hB
  have sL := seqM_some hL' retB (pexecM_skip mv fuel rB.ps rB.vv)
  have s1 := seqM_some a1 rfl sL
  have sc1 := pexecM_scope mv fuel _ _ _ _ s1
  have tk1 : (⟨(gS P [ci root, ci n, cpI ((0 : Int) - 1)]).mem.take (gS P [ci root, ci n]).mem.length,
      (gS P [ci root, ci n, cpI ((0 : Int) - 1)]).bs.take (gS P [ci root, ci n]).bs.length⟩ : PS) = gS P [ci root, ci n] :=
    gS_takeC P [ci root, ci n] [ci root, ci n] [cpI ((0 : Int) - 1)] rfl
  rw [psB] at sc1
  simp only [tk1] at sc1
  -- e() and `up[root] = e()`
  have d2 := gSM_decl mv P [ci root, ci n] (VA a') s64 zeroS 0 0 (zeroS_val mv _ _) (conv_signed s64 rfl rfl _ (show s64.valid 0 = true from rfl))
  have a2 := (pexecM_prim mv fuel (.declare s64 true zeroS) _ _).trans d2
  have e2 : [ci root, ci n] ++ [(⟨s64, 0⟩ : Cell)] = [ci root, ci n, cs 0] := rfl
  rw [e2] at a2
  have hx : vdenM mv (VA a') (penvN mv.nv (gS P [ci root, ci n, cs 0])) (vS mv.nv 2) = some 0 :=
    cellS mv _ P _ 2 0 (by simp) (show s64.valid 0 = true from rfl)
  have hi : vdenM mv (VA a') (penvN mv.nv (gS P [ci root, ci n, cs 0])) (.cast u64 (.variable i32 (mv.nv + 0))) = some (root : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ _ root (envs mv P [ci root, ci n, cs 0] 0 (ci root) (by simp) (i32vn root hrk)) hrk
  have hlt : root < ((VA a') 7).length := by rw [VA_get7, Ln'.up]; exact hrn
  have hw := pstmtM_write_ok mv (gS P [ci root, ci n, cs 0]) (VA a') 7 (by omega) (.cast u64 (.variable i32 (mv.nv + 0)))
    (vS mv.nv 2) 0 root hx hi hlt (by rw [ty7]; exact (show s64.valid 0 = true from rfl))
  rw [ty7, VA_get7, VA_set7] at hw
  have aw := (pexecM_prim mv fuel (wrS 7 (vI mv.nv 0) (vS mv.nv 2)) _ _).trans hw
  -- the top-down loop
  have hz : vdenM mv (VA { a' with up := a'.up.set root 0 }) (penvN mv.nv (gS P [ci root, ci n, cs 0])) (.literal i32 0) = some 0 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]
  have d3 := gSM_decl mv P [ci root, ci n, cs 0] (VA { a' with up := a'.up.set root 0 }) i32 (.literal i32 0) 0 0 hz
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a3 := (pexecM_prim mv fuel (.declare i32 true (.literal i32 0)) _ _).trans d3
  have e3 : [ci root, ci n, cs 0] ++ [(⟨i32, (0 : Int)⟩ : Cell)] = [ci root, ci n, cs 0, ci 0] := rfl
  rw [e3] at a3
  have hupa : ∀ x, 0 ≤ a'.up.getD x 0 ∧ a'.up.getD x 0 ≤ n := by rw [hupB]; exact hup
  have I0 := tdi_init M a' Ln' hI0 hupa
  obtain ⟨rT, F', U', hT, retT, psT, vvT, hIT, cT, nT, wT⟩ := td_loop mv hnv ty0 ty1 ty2 ty3 ty5 ty6 ty7 ty8 P head target parent ord n root M a' R' Ln' hI0
    root hrk n 0 a'.fu (a'.up.set root 0) fuel (by omega) (by omega) I0 (by omega)
  have hT' : pexecM mv fuel (.whileLoop (.binary bT .lt (vI mv.nv 3) (vI mv.nv 1)) (TDbody mv.nv))
      (gS P ([ci root, ci n, cs 0] ++ [ci 0])) (VA { a' with up := a'.up.set root 0 }) = some rT := hT
  have sT := seqM_some hT' retT (pexecM_skip mv fuel rT.ps rT.vv)
  have s3 := seqM_some a3 rfl sT
  have sc3 := pexecM_scope mv fuel _ _ _ _ s3
  have tk3 : (⟨(gS P [ci root, ci n, cs 0, ci n]).mem.take (gS P [ci root, ci n, cs 0]).mem.length,
      (gS P [ci root, ci n, cs 0, ci n]).bs.take (gS P [ci root, ci n, cs 0]).bs.length⟩ : PS) = gS P [ci root, ci n, cs 0] :=
    gS_takeC P [ci root, ci n, cs 0] [ci root, ci n, cs 0] [ci n] rfl
  rw [psT] at sc3
  simp only [tk3] at sc3
  have c3 := seqM_some sc3 (by simp) (pexecM_skip mv fuel _ _)
  have c2 := seqM_some aw rfl c3
  have c1 := seqM_some a2 rfl c2
  have c0 := seqM_some sc1 (by simp) (by rw [vvB]; exact c1)
  have hdeg := degSum_le M R n (le_refl _)
  have hd0 : degSum head ord 0 = 0 := by simp [degSum]
  refine ⟨_, a', F', U', c0, ?_, ?_, ?_, hI0, hupB, hIT, ?_, ?_, ?_⟩
  · simp
  · rfl
  · show rT.vv = _
    exact vvT
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cB cT ⊢
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nB nT ⊢
    omega
  · simp at wB wT ⊢
    omega

/-- The final correctness statement: the arrays hold the rerooting DP values. -/
theorem full_correct (M : TS head target parent ord n root) (a : Arr) (F U : List Int)
    (B0 : BUI head target parent ord n 0 a) (I : TDI head target parent ord n root a n F U) :
    (∀ v, v < n → ∃ f, Ef M0 head target f (pp parent n root v) v = some (a.dp.getD v 0)) ∧
    (∀ w, w < n → w ≠ root → ∃ f, Ef M0 head target f w (par parent w) = some (U.getD w 0)) ∧
    (∀ v, v < n → ∃ f, Ef M0 head target f n v = some (F.getD v 0)) := by
  have hj : ∀ v, v < n → ∃ j, j < n ∧ ord.getD j 0 = v := fun v hv =>
    ⟨pos ord v, M.pos_lt v hv, ord_pos_get v (M.ordmem v hv)⟩
  have hdp : ∀ v, v < n → a.dp.getD v 0 = M0.su (fold M0 ((kidT head target parent v).map fun x => a.dp.getD x 0)) := by
    intro v hv
    obtain ⟨j, hjn, rfl⟩ := hj v hv
    show _ = fold M0 _ + 1
    rw [B0.dpE j (Nat.zero_le _) hjn, B0.tot j (Nat.zero_le _) hjn]
  have hVdp : ∀ x, x < n → M0.V (a.dp.getD x 0) := fun x _ => (B0.glob x).1
  have hVup : ∀ x, x < n → M0.V (U.getD x 0) := fun x _ => (I.upg x).1
  have hpre : ∀ v, v < n → ∀ p ∈ kidArcs head target parent v,
      a.pre.getD p 0 = fold M0 ((kb head target parent v p).map fun x => a.dp.getD x 0) := by
    intro v hv p hp
    obtain ⟨j, hjn, rfl⟩ := hj v hv
    exact B0.pre j (Nat.zero_le _) hjn p hp
  have hsuf : ∀ v, v < n → ∀ p ∈ kidArcs head target parent v,
      a.suf.getD p 0 = fold M0 ((ka head target parent v p).map fun x => a.dp.getD x 0) := by
    intro v hv p hp
    obtain ⟨j, hjn, rfl⟩ := hj v hv
    exact B0.suf j (Nat.zero_le _) hjn p hp
  have hupe : ∀ v, v < n → ∀ p ∈ kidArcs head target parent v,
      U.getD (tgt target p) 0 = M0.su (M0.op (M0.op (U.getD v 0) (a.pre.getD p 0)) (a.suf.getD p 0)) := by
    intro v hv p hp
    obtain ⟨j, hjn, rfl⟩ := hj v hv
    exact I.updone j hjn p hp
  have hup0 : U.getD root 0 = M0.e := I.up0
  have hU := up_deriv M0 M a.dp U a.pre a.suf hdp hVdp hVup hup0 hpre hsuf hupe
  have hfull : ∀ v, v < n → F.getD v 0 = M0.su (M0.op (U.getD v 0) (fold M0 ((kidT head target parent v).map fun x => a.dp.getD x 0))) := by
    intro v hv
    obtain ⟨j, hjn, rfl⟩ := hj v hv
    exact I.fudone j hjn
  exact ⟨dp_deriv M0 M a.dp hdp, hU, full_deriv M0 M a.dp U F hdp hVdp hVup hup0 hU hfull⟩

end Proofs.TreeFullDpTd
