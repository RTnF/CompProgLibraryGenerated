import Proofs.TreeOrderBody
import Proofs.TreeOrderMath
import Proofs.TreeFullDpExec

namespace Proofs.TreeOrderExec
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
open Proofs.RunLengthExec (inc_val)
open Proofs.TreeOrderBody
open Proofs.TreeFullDpBody (vI rdI incI isChild)
open Proofs.TreeDpSpec Proofs.TreeDpMath Proofs.TreeOrderMath
open Proofs.TreeFullDpExec (rdv rdv1 cellI i32vn filter_lt_succ kidArcs_ge)

/-- The four vectors of `tree_order`. -/
structure Arr where
  hd : List Int
  tg : List Int
  pa : List Int
  od : List Int

def VA (a : Arr) : Nat → List Int := fun k =>
  if k = 0 then a.hd else if k = 1 then a.tg else if k = 2 then a.pa else if k = 3 then a.od else []

theorem VA_get0 (a : Arr) : VA a 0 = a.hd := by simp [VA]
theorem VA_get1 (a : Arr) : VA a 1 = a.tg := by simp [VA]
theorem VA_get2 (a : Arr) : VA a 2 = a.pa := by simp [VA]
theorem VA_get3 (a : Arr) : VA a 3 = a.od := by simp [VA]
theorem VA_set3 (a : Arr) (x : List Int) : upd (VA a) 3 x = VA { a with od := x } := by
  funext k; unfold upd VA; split <;> simp_all

structure Ro (head target : List Nat) (parent : List Int) (n : Nat) (a : Arr) : Prop where
  hd : a.hd = head.map (fun x : Nat => (x : Int))
  tg : a.tg = target.map (fun x : Nat => (x : Int))
  pa : a.pa = parent
  hlen : head.length = n + 1
  hmono : ∀ v, v < n → head.getD v 0 ≤ head.getD (v + 1) 0
  hlast : head.getD n 0 = target.length
  tlen : target.length < 2147483647
  tlt : ∀ q, q < target.length → target.getD q 0 < n
  nb : n + 2 < 2147483648
  palen : parent.length = n
  pav : ∀ w, w < n → 0 ≤ parent.getD w 0 ∧ parent.getD w 0 < n

theorem Ro.updOd {head target : List Nat} {parent : List Int} {n : Nat} {a : Arr}
    (R : Ro head target parent n a) (x : List Int) : Ro head target parent n { a with od := x } :=
  ⟨R.hd, R.tg, R.pa, R.hlen, R.hmono, R.hlast, R.tlen, R.tlt, R.nb, R.palen, R.pav⟩

theorem head_le (head target : List Nat) (parent : List Int) (n : Nat) (a : Arr)
    (R : Ro head target parent n a) (v : Nat) (hv : v < n) : head.getD (v + 1) 0 ≤ target.length := by
  rw [← R.hlast]
  have : ∀ d, v + 1 + d ≤ n → head.getD (v + 1) 0 ≤ head.getD (v + 1 + d) 0 := by
    intro d
    induction d with
    | zero => intro _; exact le_refl _
    | succ d ih => intro hd; exact le_trans (ih (by omega)) (R.hmono (v + 1 + d) (by omega))
  have := this (n - (v + 1)) (by omega)
  rwa [show v + 1 + (n - (v + 1)) = n by omega] at this

theorem arc_lt (head target : List Nat) (parent : List Int) (n : Nat) (a : Arr)
    (R : Ro head target parent n a) (v : Nat) (hv : v < n) (p : Nat) (hp : p ∈ arcs head v) :
    p < target.length := by
  have h1 := head_le head target parent n a R v hv
  unfold arcs at hp
  rw [List.mem_range'_1] at hp
  omega

theorem hd_getq (head target : List Nat) (parent : List Int) (n : Nat) (a : Arr)
    (R : Ro head target parent n a) (i : Nat) (hi : i ≤ n) :
    a.hd[i]? = some (head.getD i 0 : Int) := by
  have hl : i < a.hd.length := by rw [R.hd]; simp [R.hlen]; omega
  rw [vec_getI a.hd i hl, R.hd]; simp [List.getD_eq_getElem?_getD, show i < head.length by rw [R.hlen]; omega]

theorem tg_getq (head target : List Nat) (parent : List Int) (n : Nat) (a : Arr)
    (R : Ro head target parent n a) (p : Nat) (hp : p < target.length) :
    a.tg[p]? = some (target.getD p 0 : Int) := by
  have hl : p < a.tg.length := by rw [R.tg]; simp [hp]
  rw [vec_getI a.tg p hl, R.tg]; simp [List.getD_eq_getElem?_getD, hp]

theorem pa_getq (head target : List Nat) (parent : List Int) (n : Nat) (a : Arr)
    (R : Ro head target parent n a) (w : Nat) (hw : w < n) :
    a.pa[w]? = some (parent.getD w 0) := by
  rw [vec_getI a.pa w (by rw [R.pa, R.palen]; exact hw), R.pa]

/-- The cells of `tree_order` inside the loop over `i`, with `v = ord[i]`. -/
abbrev TB (root n cnt i v : Nat) : List Cell := [ci root, ci n, ci cnt, ci i, ci v]

/-- The child test on an arc. -/
theorem ischild_val (mv : MV) (hnv : mv.nv = 4) (ty2 : mv.ty 2 = i32) (P : List Cell) (cl : List Cell) (a : Arr)
    (vc wc v w : Nat) (hv : cl[vc]? = some (ci v)) (hw : cl[wc]? = some (ci w)) (hv31 : v < 2147483648)
    (hw31 : w < 2147483648) (pw : Int) (hpw : a.pa[w]? = some pw) (hpwv : i32.valid pw = true) :
    vdenM mv (VA a) (penvN mv.nv (gS P cl)) (isChild mv.nv vc wc) = some (if pw = (v : Int) then 1 else 0) := by
  have r := rdv mv (VA a) P cl 2 wc w i32 (by omega) ty2.symm hw hw31 pw (by rw [VA_get2]; exact hpw) (by rw [ty2]; exact hpwv)
  have c := cellI mv (VA a) P cl vc v hv hv31
  unfold isChild
  rw [vdenM_binary mv _ _ bT .eq _ _ rfl, r, Option.bind_some, c, Option.bind_some]
  by_cases h : pw = (v : Int)
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

def toc (a : Arr) (v p cnt : Nat) : Nat :=
  if a.pa.getD (a.tg.getD p 0).toNat 0 = (v : Int) then cnt + 1 else cnt

def tod (a : Arr) (v p cnt : Nat) : List Int :=
  if a.pa.getD (a.tg.getD p 0).toNat 0 = (v : Int) then a.od.set cnt (a.tg.getD p 0) else a.od

set_option maxHeartbeats 128000000 in
/-- One iteration of the arc loop. -/
theorem to_iter (mv : MV) (hnv : mv.nv = 4) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32) (ty3 : mv.ty 3 = i32)
    (P : List Cell) (fu : Nat) (head target : List Nat) (parent : List Int) (n : Nat) (a : Arr)
    (R : Ro head target parent n a) (Ln : a.od.length = n) (root cnt i v p : Nat)
    (hv : v < n) (hp : p ∈ arcs head v) (hrk : root < 2147483648) (hi31 : i < 2147483648) (hcn : cnt + 1 < 2147483648)
    (hcap : parent.getD (target.getD p 0) 0 = (v : Int) → cnt < n) :
    ∃ r : PRM, pexecM mv fu (TObody mv.nv) (gS P (TB root n cnt i v ++ [ci p])) (VA a) = some r ∧ r.ret = none ∧
      r.ps = gS P (TB root n (toc a v p cnt) i v ++ [ci (p + 1)]) ∧ r.vv = VA { a with od := tod a v p cnt } ∧
      r.cost ≤ 1000 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 1 := by
  have hpt : p < target.length := arc_lt head target parent n a R v hv p hp
  have hw : target.getD p 0 < n := R.tlt p hpt
  have hn31 := R.nb
  have hp31 : p + 1 < 2147483648 := by have := R.tlen; omega
  have hv31 : v < 2147483648 := by omega
  have hw31 : target.getD p 0 < 2147483648 := by omega
  have hkp : (TB root n cnt i v ++ [ci p])[5]? = some (ci p) := by simp
  have hden : vdenM mv (VA a) (penvN mv.nv (gS P (TB root n cnt i v ++ [ci p]))) (rdI 1 (vI mv.nv 5)) =
      some (target.getD p 0 : Int) :=
    rdv mv (VA a) P _ 1 5 p i32 (by omega) ty1.symm hkp (by omega) _
      (by rw [VA_get1]; exact tg_getq head target parent n a R p hpt) (by rw [ty1]; exact i32vn _ hw31)
  have d1 := gSM_decl mv P (TB root n cnt i v ++ [ci p]) (VA a) i32 (rdI 1 (vI mv.nv 5)) (target.getD p 0 : Int)
    (target.getD p 0 : Int) hden (conv_signed i32 rfl rfl _ (i32vn _ hw31))
  have a1 := (pexecM_prim mv fu (.declare i32 true (rdI 1 (vI mv.nv 5))) _ _).trans d1
  have e8 : TB root n cnt i v ++ [ci p] ++ [(⟨i32, (target.getD p 0 : Int)⟩ : Cell)] =
      TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)] := rfl
  rw [e8] at a1
  have hpw := pa_getq head target parent n a R (target.getD p 0) hw
  have hpwv : i32.valid (parent.getD (target.getD p 0) 0) = true := by
    obtain ⟨h0, h1⟩ := R.pav _ hw
    exact Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)
  have hc := ischild_val mv hnv ty2 P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)]) a 4 6 v (target.getD p 0)
    (by simp) (by simp) hv31 hw31 _ hpw hpwv
  have tgv : a.tg.getD p 0 = (target.getD p 0 : Int) := by rw [R.tg]; simp [List.getD_eq_getElem?_getD, hpt]
  have hcnt_eq : toc a v p cnt = if parent.getD (target.getD p 0) 0 = (v : Int) then cnt + 1 else cnt := by
    unfold toc; rw [tgv, R.pa]; simp
  have hod_eq : tod a v p cnt = if parent.getD (target.getD p 0) 0 = (v : Int) then a.od.set cnt (target.getD p 0 : Int) else a.od := by
    unfold tod; rw [tgv, R.pa]; simp
  have hinc : ∀ (cnt' : Nat) (vv : Nat → List Int), cnt' + 1 < 2147483648 →
      ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (incI mv.nv 5)) Sk) (gS P (TB root n cnt' i v ++ [ci p])) vv = some r2 ∧
        r2.ret = none ∧ r2.ps = gS P (TB root n cnt' i v ++ [ci (p + 1)]) ∧ r2.vv = vv ∧ r2.cost ≤ 100 ∧
        r2.need ≤ P.length + 100 ∧ r2.wk = 0 := by
    intro cnt' vv _
    have e2 := inc_val mv vv _ (mv.nv + 5) p (envs mv P (TB root n cnt' i v ++ [ci p]) 5 (ci p) (by simp) (i32vn p (by omega))) hp31
    have s2 := gSM_assign mv P (TB root n cnt' i v ++ [ci p]) vv 5 (by simp) i32 _ _ _ e2 (ci p) (by simp) rfl
      (i32vn p (by omega)) (conv_signed i32 rfl rfl _ (i32vn (p + 1) (by omega)))
    have eB : (TB root n cnt' i v ++ [ci p]).set 5 ⟨i32, ((p + 1 : Nat) : Int)⟩ = TB root n cnt' i v ++ [ci (p + 1)] := rfl
    rw [eB] at s2
    have a2 := (pexecM_prim mv fu (incI mv.nv 5) _ _).trans s2
    have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  by_cases hch : parent.getD (target.getD p 0) 0 = (v : Int)
  · rw [if_pos hch] at hc
    have hcn' := hcap hch
    have hx : vdenM mv (VA a) (penvN mv.nv (gS P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)]))) (vI mv.nv 6) =
        some (target.getD p 0 : Int) := cellI mv _ P _ 6 _ (by simp) hw31
    have hi : vdenM mv (VA a) (penvN mv.nv (gS P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)])))
        (.cast u64 (.variable i32 (mv.nv + 2))) = some (cnt : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact cidx_den _ _ cnt (envs mv P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)]) 2 (ci cnt) (by simp)
        (i32vn cnt (by omega))) (show cnt < 2147483648 by omega)
    have hlt : cnt < ((VA a) 3).length := by rw [VA_get3, Ln]; exact hcn'
    have hv3 : (mv.ty 3).valid (target.getD p 0 : Int) = true := by rw [ty3]; exact i32vn _ hw31
    have hw3 := pstmtM_write_ok mv (gS P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)])) (VA a) 3 (by omega)
      (.cast u64 (.variable i32 (mv.nv + 2))) (vI mv.nv 6) (target.getD p 0 : Int) cnt hx hi hlt hv3
    rw [ty3, VA_get3, VA_set3] at hw3
    have aw := (pexecM_prim mv fu (.write (.local 3) i32 (.cast u64 (vI mv.nv 2)) (vI mv.nv 6)) _ _).trans hw3
    have e2 := inc_val mv (VA { a with od := a.od.set cnt (target.getD p 0 : Int) }) _ (mv.nv + 2) cnt
      (envs mv P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)]) 2 (ci cnt) (by simp) (i32vn cnt (by omega))) hcn
    have s2 := gSM_assign mv P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)])
      (VA { a with od := a.od.set cnt (target.getD p 0 : Int) }) 2 (by simp) i32 _ _ _ e2 (ci cnt) (by simp) rfl
      (i32vn cnt (by omega)) (conv_signed i32 rfl rfl _ (i32vn (cnt + 1) hcn))
    have eB : (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)]).set 2 ⟨i32, ((cnt + 1 : Nat) : Int)⟩ =
        TB root n (cnt + 1) i v ++ [ci p] ++ [ci (target.getD p 0)] := rfl
    rw [eB] at s2
    have a2 := (pexecM_prim mv fu (incI mv.nv 2) _ _).trans s2
    have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
    have sA := seqM_some aw rfl b2
    have sc := pexecM_scope mv fu _ _ _ _ sA
    have tk : (⟨(gS P (TB root n (cnt + 1) i v ++ [ci p] ++ [ci (target.getD p 0)])).mem.take
          (gS P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)])).mem.length,
        (gS P (TB root n (cnt + 1) i v ++ [ci p] ++ [ci (target.getD p 0)])).bs.take
          (gS P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)])).bs.length⟩ : PS) =
        gS P (TB root n (cnt + 1) i v ++ [ci p] ++ [ci (target.getD p 0)]) := by
      simpa using gS_takeC P (TB root n cnt i v ++ [ci p] ++ [ci (target.getD p 0)])
        (TB root n (cnt + 1) i v ++ [ci p] ++ [ci (target.getD p 0)]) [] rfl
    simp only [tk] at sc
    have b1 := seqM_some sc (by simp) (pexecM_skip mv fu _ _)
    have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b1
    have b4 := seqM_some b3 (by simp) (pexecM_skip mv fu _ _)
    have s1 := seqM_some a1 rfl b4
    have b5 := pexecM_scope mv fu _ _ _ _ s1
    have tk2 := gS_takeC P (TB root n cnt i v ++ [ci p]) (TB root n (cnt + 1) i v ++ [ci p]) [ci (target.getD p 0)] rfl
    simp only [tk2] at b5
    obtain ⟨r3, hr3, ret3, ps3, vv3, c3, n3, w3⟩ := hinc (cnt + 1) (VA { a with od := a.od.set cnt (target.getD p 0 : Int) }) (by omega)
    have b6 := seqM_some b5 (by simp) hr3
    refine ⟨_, b6, ret3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcnt_eq, if_pos hch]; exact ps3
    · rw [hod_eq, if_pos hch]; exact vv3
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c3 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n3 ⊢; omega
    · simp at w3 ⊢; omega
  · rw [if_neg hch] at hc
    have b3 := pexecM_branch_false mv fu _ (.sequence (.scope (TOact mv.nv)) Sk) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    have s1 := seqM_some a1 rfl b4
    have b5 := pexecM_scope mv fu _ _ _ _ s1
    have tk := gS_takeC P (TB root n cnt i v ++ [ci p]) (TB root n cnt i v ++ [ci p]) [ci (target.getD p 0)] rfl
    simp only [tk] at b5
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ := hinc cnt (VA a) hcn
    have b6 := seqM_some b5 (by simp) hr2
    refine ⟨_, b6, ret2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcnt_eq, if_neg hch]; exact ps2
    · rw [hod_eq, if_neg hch]; exact vv2
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n2 ⊢; omega
    · simp at w2 ⊢; omega

theorem od_set (Q : List Nat) (od0 : List Int) (w : Nat) (h : Q.length < od0.length) :
    (Q.map (fun x : Nat => (x : Int)) ++ od0.drop Q.length).set Q.length (w : Int) =
      (Q ++ [w]).map (fun x : Nat => (x : Int)) ++ od0.drop (Q.length + 1) := by
  rw [List.set_append_right _ _ (by simp)]
  simp only [List.length_map, Nat.sub_self]
  have hne : od0.drop Q.length ≠ [] := by
    intro h'
    have := congrArg List.length h'
    simp at this; omega
  obtain ⟨x, t, ht⟩ := List.exists_cons_of_ne_nil hne
  have h2 : od0.drop (Q.length + 1) = t := by
    have : od0.drop (Q.length + 1) = (od0.drop Q.length).drop 1 := by
      rw [List.drop_drop]
    rw [this, ht]; rfl
  rw [ht, h2]
  simp

theorem child_iff (head target : List Nat) (parent : List Int) (n : Nat) (a : Arr)
    (R : Ro head target parent n a) (v p : Nat) (hv : v < n) (hp : p ∈ arcs head v) :
    (a.pa.getD (a.tg.getD p 0).toNat 0 = (v : Int)) ↔ p ∈ kidArcs head target parent v := by
  have hpt : p < target.length := arc_lt head target parent n a R v hv p hp
  have tgv : a.tg.getD p 0 = (target.getD p 0 : Int) := by rw [R.tg]; simp [List.getD_eq_getElem?_getD, hpt]
  rw [tgv, R.pa]
  simp only [Int.toNat_natCast]
  unfold kidArcs
  rw [List.mem_filter]
  simp [hp, tgt]

/-- The condition `p < head[v + 1]` of the arc loop. -/
theorem condO_val (mv : MV) (hnv : mv.nv = 4) (ty0 : mv.ty 0 = i32) (P : List Cell) (cl : List Cell) (a : Arr)
    (head target : List Nat) (parent : List Int) (n : Nat) (R : Ro head target parent n a)
    (v p : Nat) (hv : v < n) (h4 : cl[4]? = some (ci v)) (h5 : cl[5]? = some (ci p)) (hp : p < 2147483648) :
    vdenM mv (VA a) (penvN mv.nv (gS P cl)) (TOcond mv.nv) = some (if p < head.getD (v + 1) 0 then 1 else 0) := by
  have hh : i32.valid (head.getD (v + 1) 0 : Int) = true := by
    have := head_le head target parent n a R v hv
    have := R.tlen
    exact i32vn _ (by omega)
  have r := rdv1 mv (VA a) P cl 0 4 v i32 (by omega) ty0.symm h4 (by have := R.nb; omega) (head.getD (v + 1) 0 : Int)
    (by rw [VA_get0]; exact hd_getq head target parent n a R (v + 1) (by omega)) (by rw [ty0]; exact hh)
  have c := cellI mv (VA a) P cl 5 p h5 hp
  unfold TOcond
  rw [vdenM_binary mv _ _ bT .lt _ _ rfl, c, Option.bind_some, r, Option.bind_some]
  generalize head.getD (v + 1) 0 = H
  by_cases h : p < H
  · have : (p : Int) < (H : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((p : Int) < (H : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

theorem kid_count_lt (head target : List Nat) (parent : List Int) (v p : Nat) (hpk : p ∈ kidArcs head target parent v) :
    (((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length <
      (kidT head target parent v).length := by
  have hK := kidArcs_pairwise head target parent v
  have h1 := filter_lt_succ _ hK p
  rw [if_pos hpk] at h1
  have h2 : ((kidArcs head target parent v).filter fun x => decide (x < p + 1)).length ≤ (kidArcs head target parent v).length :=
    List.length_filter_le _ _
  rw [h1] at h2
  simp only [List.length_append, List.length_singleton] at h2
  simp only [List.length_map, kidT]
  omega

set_option maxHeartbeats 128000000 in
/-- The arc loop `for (p = head[v]; p < head[v + 1]; p++) ...`, from the state at arc `p`. -/
theorem to_loop (mv : MV) (hnv : mv.nv = 4) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (P : List Cell) (head target : List Nat) (parent : List Int) (n : Nat) (a0 : Arr)
    (R : Ro head target parent n a0) (od0 : List Int) (Lod : od0.length = n) (root i v : Nat) (q : List Nat)
    (hv : v < n) (hrk : root < 2147483648) (hi31 : i < 2147483648)
    (hfin : (q ++ kidT head target parent v).length ≤ n) :
    ∀ (d p : Nat) (od' : List Int) (fu : Nat), head.getD (v + 1) 0 - p = d → head.getD v 0 ≤ p →
      p ≤ head.getD (v + 1) 0 →
      od' = (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).map (fun x : Nat => (x : Int)) ++
        od0.drop (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length →
      d + 1 ≤ fu →
      ∃ (res : PRM) (od'' : List Int),
        pexecM mv fu (.whileLoop (TOcond mv.nv) (TObody mv.nv))
          (gS P (TB root n (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length i v ++ [ci p]))
          (VA { a0 with od := od' }) = some res ∧
        res.ret = none ∧
        res.ps = gS P (TB root n (q ++ kidT head target parent v).length i v ++ [ci (head.getD (v + 1) 0)]) ∧
        res.vv = VA { a0 with od := od'' } ∧
        od'' = (q ++ kidT head target parent v).map (fun x : Nat => (x : Int)) ++ od0.drop (q ++ kidT head target parent v).length ∧
        res.cost ≤ 1100 * d + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ d := by
  have hend := head_le head target parent n a0 R v hv
  have htl := R.tlen
  have hn31 := R.nb
  have hfilt_end : (kidArcs head target parent v).filter (fun x => decide (x < head.getD (v + 1) 0)) = kidArcs head target parent v := by
    rw [List.filter_eq_self]
    intro x hx
    have := (kidArcs_ge head target parent v x hx).2
    simpa using this
  intro d
  induction d with
  | zero =>
    intro p od' fu hd hp0 hpe hod hfu
    have hpeq : p = head.getD (v + 1) 0 := by omega
    subst hpeq
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hlen : (q ++ ((kidArcs head target parent v).filter fun x => decide (x < head.getD (v + 1) 0)).map (tgt target)).length ≤ n := by
      rw [hfilt_end]; exact hfin
    have hc := condO_val mv hnv ty0 P (TB root n (q ++ ((kidArcs head target parent v).filter fun x => decide (x < head.getD (v + 1) 0)).map (tgt target)).length i v ++ [ci (head.getD (v + 1) 0)])
      { a0 with od := od' } head target parent n (R.updOd od') v (head.getD (v + 1) 0) hv (by simp) (by simp) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    rw [hfilt_end] at hod ⊢
    refine ⟨_, od', rfl, rfl, rfl, rfl, by rw [hod]; rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro p od' fu hd hp0 hpe hod hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hpin : p ∈ arcs head v := by
      unfold arcs; rw [List.mem_range'_1]; omega
    have hlenQ : (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length ≤ n := by
      have : List.Sublist (((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)) (kidT head target parent v) :=
        (List.filter_sublist).map _
      have := this.length_le
      simp only [List.length_append] at hfin ⊢
      omega
    have hc := condO_val mv hnv ty0 P (TB root n (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length i v ++ [ci p])
      { a0 with od := od' } head target parent n (R.updOd od') v p hv (by simp) (by simp) (by omega)
    rw [if_pos (by omega)] at hc
    have hodlen : od'.length = n := by
      rw [hod]
      simp only [List.length_append, List.length_map, List.length_drop] at hlenQ ⊢
      omega
    have hchild := child_iff head target parent n { a0 with od := od' } (R.updOd od') v p hv hpin
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := to_iter mv hnv ty1 ty2 ty3 P (fu' + 1) head target parent n { a0 with od := od' }
      (R.updOd od') hodlen root (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length i v p hv hpin hrk hi31 (by omega) (by
        intro hch
        have hk : p ∈ kidArcs head target parent v := List.mem_filter.mpr ⟨hpin, by simpa [tgt] using hch⟩
        have := kid_count_lt head target parent v p hk
        simp only [List.length_append, List.length_map] at hfin this ⊢
        omega)
    have hK := kidArcs_pairwise head target parent v
    have hQ1 : q ++ ((kidArcs head target parent v).filter fun x => decide (x < p + 1)).map (tgt target) =
        if p ∈ kidArcs head target parent v then
          (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)) ++ [tgt target p]
        else q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target) := by
      rw [filter_lt_succ _ hK p]
      by_cases hk : p ∈ kidArcs head target parent v
      · simp [hk]
      · simp [hk]
    have tgv : (({ a0 with od := od' } : Arr)).tg.getD p 0 = (target.getD p 0 : Int) := by
      show a0.tg.getD p 0 = _
      have hpt : p < target.length := arc_lt head target parent n a0 R v hv p hpin
      rw [R.tg]; simp [List.getD_eq_getElem?_getD, hpt]
    have hcnt_eq : toc { a0 with od := od' } v p
        (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length =
        (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p + 1)).map (tgt target)).length := by
      unfold toc
      rw [hQ1]
      by_cases hk : p ∈ kidArcs head target parent v
      · rw [if_pos (hchild.mpr hk), if_pos hk]; simp; omega
      · rw [if_neg (fun h => hk (hchild.mp h)), if_neg hk]
    have hod_eq : tod { a0 with od := od' } v p
        (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length =
        (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p + 1)).map (tgt target)).map (fun x : Nat => (x : Int)) ++
          od0.drop (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p + 1)).map (tgt target)).length := by
      unfold tod
      rw [hQ1]
      by_cases hk : p ∈ kidArcs head target parent v
      · rw [if_pos (hchild.mpr hk), if_pos hk, tgv]
        have hlt : (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length < od0.length := by
          have := kid_count_lt head target parent v p hk
          simp only [List.length_append, List.length_map] at hfin this ⊢
          omega
        have := od_set (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)) od0 (tgt target p) hlt
        have e : (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target) ++ [tgt target p]).length =
            (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length + 1 := by simp; omega
        rw [e, hod]
        exact this
      · rw [if_neg (fun h => hk (hchild.mp h)), if_neg hk]
        exact hod
    obtain ⟨r2, od'', h2, ret2, ps2, vv2, hod2, c2, n2, w2⟩ :=
      ih (p + 1) (tod { a0 with od := od' } v p
        (q ++ ((kidArcs head target parent v).filter fun x => decide (x < p)).map (tgt target)).length) fu' (by omega) (by omega) (by omega)
        (by rw [hod_eq]) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
    rw [h1]
    simp only [ret1, ps1, vv1]
    rw [hcnt_eq]
    rw [h2]
    simp only
    refine ⟨_, od'', rfl, ret2, ps2, vv2, hod2, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

theorem condLT_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (c1 c2 x y : Nat)
    (h1 : cl[c1]? = some (ci x)) (h2 : cl[c2]? = some (ci y)) (hx : x < 2147483648) (hy : y < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .lt (vI mv.nv c1) (vI mv.nv c2)) = some (if x < y then 1 else 0) := by
  have e1 := envs mv P cl c1 (ci x) h1 (i32vn x hx)
  have e2 := envs mv P cl c2 (ci y) h2 (i32vn y hy)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary]
  have e1' : (vI mv.nv c1).denote (penvN mv.nv (gS P cl)) = some (x : Int) := by
    show (NExpr.variable i32 (mv.nv + c1)).denote _ = some (x : Int)
    rw [den_variable]; exact e1
  have e2' : (vI mv.nv c2).denote (penvN mv.nv (gS P cl)) = some (y : Int) := by
    show (NExpr.variable i32 (mv.nv + c2)).denote _ = some (y : Int)
    rw [den_variable]; exact e2
  rw [e1', Option.bind_some, e2', Option.bind_some]
  by_cases h : x < y
  · have : (x : Int) < (y : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((x : Int) < (y : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

/-- The arrays when the queue is `Q` (the rest of `ord` is the old contents `od0`). -/
def qarr (a0 : Arr) (od0 : List Int) (Q : List Nat) : Arr :=
  { a0 with od := Q.map (fun x : Nat => (x : Int)) ++ od0.drop Q.length }

/-- The degree of the vertex processed at the step `i` (zero when the queue is exhausted). -/
def delta (head : List Nat) (Q : List Nat) (i : Nat) : Nat :=
  if i < Q.length then head.getD (Q.getD i 0 + 1) 0 - head.getD (Q.getD i 0) 0 else 0

theorem hinc3 (mv : MV) (hnv : mv.nv = 4) (P : List Cell) (fu : Nat) (root n c i : Nat) (hi : i + 1 < 2147483648)
    (vv : Nat → List Int) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (incI mv.nv 3)) Sk) (gS P [ci root, ci n, ci c, ci i]) vv = some r2 ∧
      r2.ret = none ∧ r2.ps = gS P [ci root, ci n, ci c, ci (i + 1)] ∧ r2.vv = vv ∧ r2.cost ≤ 100 ∧
      r2.need ≤ P.length + 100 ∧ r2.wk = 0 := by
  have e2 := inc_val mv vv _ (mv.nv + 3) i (envs mv P [ci root, ci n, ci c, ci i] 3 (ci i) (by simp) (i32vn i (by omega))) hi
  have s2 := gSM_assign mv P [ci root, ci n, ci c, ci i] vv 3 (by simp) i32 _ _ _ e2 (ci i) (by simp) rfl
    (i32vn i (by omega)) (conv_signed i32 rfl rfl _ (i32vn (i + 1) hi))
  have eB : ([ci root, ci n, ci c, ci i] : List Cell).set 3 ⟨i32, ((i + 1 : Nat) : Int)⟩ = [ci root, ci n, ci c, ci (i + 1)] := rfl
  rw [eB] at s2
  have a2 := (pexecM_prim mv fu (incI mv.nv 3) _ _).trans s2
  have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, b2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

set_option maxHeartbeats 512000000 in
/-- One pass of the outer loop (the vertex `Q[i]` is expanded when it exists). -/
theorem to_pass (mv : MV) (hnv : mv.nv = 4) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (P : List Cell) (fu : Nat) (head target : List Nat) (parent : List Int) (n root : Nat)
    (H : TO head target parent n root) (a0 : Arr) (R : Ro head target parent n a0) (od0 : List Int) (Lod : od0.length = n)
    (i : Nat) (hi : i < n) (Q : List Nat) (I : QI head target parent n root i Q) (hfu : delta head Q i + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (TOouterBody mv.nv) (gS P [ci root, ci n, ci Q.length, ci i])
        (VA (qarr a0 od0 Q)) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci root, ci n, ci (qstep head target parent Q i).length, ci (i + 1)] ∧
      r.vv = VA (qarr a0 od0 (qstep head target parent Q i)) ∧
      r.cost ≤ 1100 * delta head Q i + 1500 ∧ r.need ≤ P.length + 300 ∧ r.wk ≤ delta head Q i + 2 := by
  have hn31 := R.nb
  have hrk : root < 2147483648 := by have := H.rootlt; omega
  have hQn : Q.length ≤ n := len_le_n Q I.nd I.lt
  have R' : Ro head target parent n (qarr a0 od0 Q) := R.updOd _
  have hc := condLT_val mv P (VA (qarr a0 od0 Q))
    [ci root, ci n, ci Q.length, ci i] 3 2 i Q.length (by simp) (by simp) (by omega) (by omega)
  obtain ⟨r3, hr3, ret3, ps3, vv3, c3, n3, w3⟩ := hinc3 mv hnv P fu root n (qstep head target parent Q i).length i (by omega)
    (VA (qarr a0 od0 (qstep head target parent Q i)))
  by_cases h : i < Q.length
  · rw [if_pos h] at hc
    have hvq := getD_mem_of_lt Q i h
    have hvn : Q.getD i 0 < n := I.lt _ hvq
    have hv31 : Q.getD i 0 < 2147483648 := by omega
    have hqs : qstep head target parent Q i = Q ++ kidT head target parent (Q.getD i 0) := by unfold qstep; rw [if_pos h]
    have hI1 := qi_step H i Q I
    rw [hqs] at hI1
    have hfin : (Q ++ kidT head target parent (Q.getD i 0)).length ≤ n := len_le_n _ hI1.nd hI1.lt
    have hend := head_le head target parent n a0 R _ hvn
    have hmono := R.hmono _ hvn
    have htl := R.tlen
    -- v = ord[i]
    have hvec : (VA (qarr a0 od0 Q) 3)[i]? = some (Q.getD i 0 : Int) := by
      rw [VA_get3]
      show (Q.map (fun x : Nat => (x : Int)) ++ od0.drop Q.length)[i]? = _
      rw [List.getElem?_append_left (by simpa using h)]
      simp [List.getD_eq_getElem?_getD, h]
    have hdv : vdenM mv (VA (qarr a0 od0 Q)) (penvN mv.nv (gS P [ci root, ci n, ci Q.length, ci i])) (rdI 3 (vI mv.nv 3)) =
        some (Q.getD i 0 : Int) :=
      rdv mv (VA (qarr a0 od0 Q)) P _ 3 3 i i32 (by omega) ty3.symm (by simp) (by omega) _ hvec (by rw [ty3]; exact i32vn _ hv31)
    have d1 := gSM_decl mv P [ci root, ci n, ci Q.length, ci i] (VA (qarr a0 od0 Q)) i32 (rdI 3 (vI mv.nv 3)) (Q.getD i 0 : Int)
      (Q.getD i 0 : Int) hdv (conv_signed i32 rfl rfl _ (i32vn _ hv31))
    have a1 := (pexecM_prim mv fu (.declare i32 true (rdI 3 (vI mv.nv 3))) _ _).trans d1
    have e1 : [ci root, ci n, ci Q.length, ci i] ++ [(⟨i32, (Q.getD i 0 : Int)⟩ : Cell)] =
        TB root n Q.length i (Q.getD i 0) := rfl
    rw [e1] at a1
    -- p = head[v]
    have hhd : i32.valid (head.getD (Q.getD i 0) 0 : Int) = true := i32vn _ (by omega)
    have hdp1 : vdenM mv (VA (qarr a0 od0 Q)) (penvN mv.nv (gS P (TB root n Q.length i (Q.getD i 0)))) (rdI 0 (vI mv.nv 4)) =
        some (head.getD (Q.getD i 0) 0 : Int) :=
      rdv mv (VA (qarr a0 od0 Q)) P _ 0 4 (Q.getD i 0) i32 (by omega) ty0.symm (by simp) hv31 _
        (by rw [VA_get0]; exact hd_getq head target parent n (qarr a0 od0 Q) R' _ (by omega)) (by rw [ty0]; exact hhd)
    have d4 := gSM_decl mv P (TB root n Q.length i (Q.getD i 0)) (VA (qarr a0 od0 Q)) i32 (rdI 0 (vI mv.nv 4))
      (head.getD (Q.getD i 0) 0 : Int) (head.getD (Q.getD i 0) 0 : Int) hdp1 (conv_signed i32 rfl rfl _ hhd)
    have a4 := (pexecM_prim mv fu (.declare i32 true (rdI 0 (vI mv.nv 4))) _ _).trans d4
    have hfilt0 : (kidArcs head target parent (Q.getD i 0)).filter (fun x => decide (x < head.getD (Q.getD i 0) 0)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro q hq
      have := (kidArcs_ge head target parent _ q hq).1
      rw [decide_eq_false (by omega)]
      simp
    obtain ⟨rL, od'', hL, retL, psL, vvL, hod'', cL, nL, wL⟩ := to_loop mv hnv ty0 ty1 ty2 ty3 P head target parent n a0 R od0 Lod
      root i (Q.getD i 0) Q hvn hrk (by omega) hfin (head.getD (Q.getD i 0 + 1) 0 - head.getD (Q.getD i 0) 0)
      (head.getD (Q.getD i 0) 0) (Q.map (fun x : Nat => (x : Int)) ++ od0.drop Q.length) fu rfl (le_refl _) hmono
      (by rw [hfilt0]; simp) (by unfold delta at hfu; rw [if_pos h] at hfu; omega)
    rw [hfilt0] at hL
    simp only [List.map_nil, List.append_nil] at hL
    have hL' : pexecM mv fu (.whileLoop (TOcond mv.nv) (TObody mv.nv))
        (gS P (TB root n Q.length i (Q.getD i 0) ++ [ci (head.getD (Q.getD i 0) 0)])) (VA (qarr a0 od0 Q)) = some rL := hL
    have sL := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
    have s4 := seqM_some a4 rfl sL
    have sc4 := pexecM_scope mv fu _ _ _ _ s4
    have tk4 := gS_takeC P (TB root n Q.length i (Q.getD i 0)) (TB root n (Q ++ kidT head target parent (Q.getD i 0)).length i (Q.getD i 0))
      [ci (head.getD (Q.getD i 0 + 1) 0)] rfl
    rw [psL] at sc4
    simp only [tk4] at sc4
    have c5 := seqM_some sc4 (by simp) (pexecM_skip mv fu _ _)
    have s6 := seqM_some a1 rfl c5
    have sc6 := pexecM_scope mv fu _ _ _ _ s6
    have tk6 : (⟨(gS P (TB root n (Q ++ kidT head target parent (Q.getD i 0)).length i (Q.getD i 0))).mem.take
          (gS P [ci root, ci n, ci Q.length, ci i]).mem.length,
        (gS P (TB root n (Q ++ kidT head target parent (Q.getD i 0)).length i (Q.getD i 0))).bs.take
          (gS P [ci root, ci n, ci Q.length, ci i]).bs.length⟩ : PS) =
        gS P [ci root, ci n, ci (Q ++ kidT head target parent (Q.getD i 0)).length, ci i] :=
      gS_takeC P [ci root, ci n, ci Q.length, ci i] [ci root, ci n, ci (Q ++ kidT head target parent (Q.getD i 0)).length, ci i]
        [ci (Q.getD i 0)] rfl
    simp only [tk6] at sc6
    have b1 := seqM_some sc6 (by simp) (pexecM_skip mv fu _ _)
    have br := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b1
    have b2 := seqM_some br (by simp) (pexecM_skip mv fu _ _)
    have sc7 := pexecM_scope mv fu _ _ _ _ b2
    have tk7 : (⟨(gS P [ci root, ci n, ci (Q ++ kidT head target parent (Q.getD i 0)).length, ci i]).mem.take
          (gS P [ci root, ci n, ci Q.length, ci i]).mem.length,
        (gS P [ci root, ci n, ci (Q ++ kidT head target parent (Q.getD i 0)).length, ci i]).bs.take
          (gS P [ci root, ci n, ci Q.length, ci i]).bs.length⟩ : PS) =
        gS P [ci root, ci n, ci (Q ++ kidT head target parent (Q.getD i 0)).length, ci i] := by
      simpa using gS_takeC P [ci root, ci n, ci Q.length, ci i] [ci root, ci n, ci (Q ++ kidT head target parent (Q.getD i 0)).length, ci i] [] rfl
    simp only [tk7] at sc7
    rw [hqs] at hr3 ps3 vv3 ⊢
    have b6 := seqM_some sc7 (by simp) (by rw [vvL, hod'']; exact hr3)
    refine ⟨_, b6, ret3, ps3, ?_, ?_, ?_, ?_⟩
    · exact vv3
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, delta, h] at cL c3 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nL n3 ⊢; omega
    · simp [delta, h] at wL w3 ⊢; omega
  · rw [if_neg h] at hc
    have hq : qstep head target parent Q i = Q := by unfold qstep; rw [if_neg h]
    rw [hq] at hr3 ps3 vv3 ⊢
    have b3 := pexecM_branch_false mv fu _ (.sequence (.scope (TOstep mv.nv)) Sk) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    have sc := pexecM_scope mv fu _ _ _ _ b4
    have tk : (⟨(gS P [ci root, ci n, ci Q.length, ci i]).mem.take (gS P [ci root, ci n, ci Q.length, ci i]).mem.length,
        (gS P [ci root, ci n, ci Q.length, ci i]).bs.take (gS P [ci root, ci n, ci Q.length, ci i]).bs.length⟩ : PS) =
        gS P [ci root, ci n, ci Q.length, ci i] := by simp
    simp only [tk] at sc
    have b6 := seqM_some sc (by simp) hr3
    refine ⟨_, b6, ret3, ps3, vv3, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, delta, h] at c3 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n3 ⊢; omega
    · simp [delta, h] at w3 ⊢; omega

/-- The degrees of the first `i` queued vertices. -/
def Dsum (head : List Nat) (Q : List Nat) (i : Nat) : Nat :=
  ((Q.take i).map fun x => head.getD (x + 1) 0 - head.getD x 0).sum

theorem Dsum_step (head target : List Nat) (parent : List Int) (Q : List Nat) (i : Nat) :
    Dsum head (qstep head target parent Q i) (i + 1) = Dsum head Q i + delta head Q i := by
  unfold qstep delta Dsum
  by_cases h : i < Q.length
  · rw [if_pos h, if_pos h, List.take_append_of_le_length (by omega)]
    have : Q.take (i + 1) = Q.take i ++ [Q.getD i 0] := by
      rw [List.take_succ]
      simp [List.getD_eq_getElem?_getD, h]
    rw [this]
    simp
  · rw [if_neg h, if_neg h, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    simp

theorem Dsum_le (M : TO head target parent n root) (R : Ro head target parent n a0) (Q : List Nat) (i : Nat)
    (hnd : Q.Nodup) (hlt : ∀ x ∈ Q, x < n) : Dsum head Q i ≤ target.length := by
  have hnd' : (Q.take i).Nodup := hnd.sublist (List.take_sublist _ _)
  have hlt' : ∀ x ∈ Q.take i, x < n := fun x hx => hlt x (List.mem_of_mem_take hx)
  have h1 := Proofs.TreeRootMath.sum_nodup_le (fun x => head.getD (x + 1) 0 - head.getD x 0) n _ hnd' hlt'
  have h2 := Proofs.TreeRootMath.sum_outdeg head n R.hmono
  unfold Dsum
  have := R.hlast
  omega

set_option maxHeartbeats 512000000 in
/-- The outer loop `for (int i = 0; i < n; i++)`. -/
theorem to_outer (mv : MV) (hnv : mv.nv = 4) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (P : List Cell) (head target : List Nat) (parent : List Int) (n root : Nat)
    (H : TO head target parent n root) (a0 : Arr) (R : Ro head target parent n a0) (od0 : List Int) (Lod : od0.length = n) :
    ∀ (d i : Nat) (fuel : Nat), n - i = d → i ≤ n → d + target.length + 3 ≤ fuel →
      ∃ res : PRM,
        pexecM mv fuel (.whileLoop (.binary bT .lt (vI mv.nv 3) (vI mv.nv 1)) (TOouterBody mv.nv))
          (gS P [ci root, ci n, ci (qrun head target parent [root] i).length, ci i])
          (VA (qarr a0 od0 (qrun head target parent [root] i))) = some res ∧ res.ret = none ∧
        res.ps = gS P [ci root, ci n, ci (qrun head target parent [root] n).length, ci n] ∧
        res.vv = VA (qarr a0 od0 (qrun head target parent [root] n)) ∧
        res.cost + 1100 * Dsum head (qrun head target parent [root] i) i ≤
          1100 * Dsum head (qrun head target parent [root] n) n + 1600 * d + 30 ∧
        res.need ≤ P.length + 300 ∧
        res.wk + Dsum head (qrun head target parent [root] i) i ≤ Dsum head (qrun head target parent [root] n) n + 2 * d := by
  have hn31 := R.nb
  intro d
  induction d with
  | zero =>
    intro i fuel hd hin hfu
    have hi : i = n := by omega
    subst hi
    obtain ⟨fu', rfl⟩ : ∃ fu', fuel = fu' + 1 := ⟨fuel - 1, by omega⟩
    have hc := condLT_val mv P (VA (qarr a0 od0 (qrun head target parent [root] i)))
      [ci root, ci i, ci (qrun head target parent [root] i).length, ci i] 3 1 i i (by simp) (by simp) (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro i fuel hd hin hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fuel = fu' + 1 := ⟨fuel - 1, by omega⟩
    have hi : i < n := by omega
    have I := qrun_inv H i
    have hc := condLT_val mv P (VA (qarr a0 od0 (qrun head target parent [root] i)))
      [ci root, ci n, ci (qrun head target parent [root] i).length, ci i] 3 1 i n (by simp) (by simp) (by omega) (by omega)
    rw [if_pos hi] at hc
    have hdl : delta head (qrun head target parent [root] i) i ≤ target.length := by
      unfold delta
      by_cases h : i < (qrun head target parent [root] i).length
      · rw [if_pos h]
        have hvn := I.lt _ (getD_mem_of_lt _ i h)
        have := head_le head target parent n a0 R _ hvn
        omega
      · rw [if_neg h]; omega
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := to_pass mv hnv ty0 ty1 ty2 ty3 P (fu' + 1) head target parent n root H a0 R od0 Lod i hi
      _ I (by omega)
    obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := ih (i + 1) fu' (by omega) (by omega) (by omega)
    have hq : qrun head target parent [root] (i + 1) = qstep head target parent (qrun head target parent [root] i) i := rfl
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
    rw [h1]
    simp only [ret1, ps1, vv1]
    rw [← hq]
    rw [h2]
    simp only
    have hDs := Dsum_step head target parent (qrun head target parent [root] i) i
    rw [← hq] at hDs
    refine ⟨_, rfl, ret2, ps2, vv2, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

set_option maxHeartbeats 512000000 in
/-- The whole body of `tree_order`. -/
theorem to_body (mv : MV) (hnv : mv.nv = 4) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (P : List Cell) (fuel : Nat) (head target : List Nat) (parent : List Int) (n root : Nat)
    (H : TO head target parent n root) (a0 : Arr) (R : Ro head target parent n a0) (Lod : a0.od.length = n)
    (hfuel : n + target.length + 6 ≤ fuel) :
    ∃ (res : PRM) (Qf : List Nat),
      pexecM mv fuel (bodyTO mv.nv) (gS P [ci root, ci n]) (VA a0) = some res ∧ res.ret = none ∧
      res.ps = gS P [ci root, ci n, ci n] ∧ res.vv = VA { a0 with od := Qf.map (fun x : Nat => (x : Int)) } ∧
      Qf = qrun head target parent [root] n ∧ Qf.length = n ∧ Qf.Nodup ∧ (∀ x ∈ Qf, x < n) ∧ Qf.getD 0 0 = root ∧
      (∀ j, 1 ≤ j → j < n → ∃ j', j' < j ∧ Qf.getD j' 0 = par parent (Qf.getD j 0)) ∧
      res.cost ≤ 1100 * target.length + 1600 * n + 600 ∧ res.need ≤ P.length + 400 ∧
      res.wk ≤ target.length + 2 * n + 6 := by
  have hn31 := R.nb
  have hrn := H.rootlt
  have hrk : root < 2147483648 := by omega
  -- ord[0] = root
  have hx : vdenM mv (VA a0) (penvN mv.nv (gS P [ci root, ci n])) (vI mv.nv 0) = some (root : Int) :=
    cellI mv _ P _ 0 root (by simp) hrk
  have hi0 : vdenM mv (VA a0) (penvN mv.nv (gS P [ci root, ci n])) (.cast u64 (.literal i32 0)) = some ((0 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
    rfl
  have hlt : 0 < ((VA a0) 3).length := by rw [VA_get3, Lod]; omega
  have hv3 : (mv.ty 3).valid (root : Int) = true := by rw [ty3]; exact i32vn _ hrk
  have hw := pstmtM_write_ok mv (gS P [ci root, ci n]) (VA a0) 3 (by omega) (.cast u64 (.literal i32 0)) (vI mv.nv 0)
    (root : Int) 0 hx hi0 hlt hv3
  rw [ty3, VA_get3, VA_set3] at hw
  have aw := (pexecM_prim mv fuel (.write (.local 3) i32 (.cast u64 (.literal i32 0)) (vI mv.nv 0)) _ _).trans hw
  -- the two declarations
  have hz1 : vdenM mv (VA { a0 with od := a0.od.set 0 (root : Int) }) (penvN mv.nv (gS P [ci root, ci n])) (.literal i32 1) = some 1 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 1 = true from rfl)]
  have d1 := gSM_decl mv P [ci root, ci n] (VA { a0 with od := a0.od.set 0 (root : Int) }) i32 (.literal i32 1) 1 1 hz1
    (conv_signed i32 rfl rfl _ (show i32.valid 1 = true from rfl))
  have a1 := (pexecM_prim mv fuel (.declare i32 true (.literal i32 1)) _ _).trans d1
  have e1 : [ci root, ci n] ++ [(⟨i32, (1 : Int)⟩ : Cell)] = [ci root, ci n, ci 1] := rfl
  rw [e1] at a1
  have hz0 : vdenM mv (VA { a0 with od := a0.od.set 0 (root : Int) }) (penvN mv.nv (gS P [ci root, ci n, ci 1])) (.literal i32 0) = some 0 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]
  have d2 := gSM_decl mv P [ci root, ci n, ci 1] (VA { a0 with od := a0.od.set 0 (root : Int) }) i32 (.literal i32 0) 0 0 hz0
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a2 := (pexecM_prim mv fuel (.declare i32 true (.literal i32 0)) _ _).trans d2
  have e2 : [ci root, ci n, ci 1] ++ [(⟨i32, (0 : Int)⟩ : Cell)] = [ci root, ci n, ci 1, ci 0] := rfl
  rw [e2] at a2
  -- the state is the queue [root]
  have hq0 : a0.od.set 0 (root : Int) = [root].map (fun x : Nat => (x : Int)) ++ a0.od.drop 1 := by
    cases hod : a0.od with
    | nil => rw [hod] at Lod; simp at Lod; omega
    | cons x t => simp
  have hvv0 : (VA { a0 with od := a0.od.set 0 (root : Int) }) = VA (qarr a0 a0.od [root]) := by
    unfold qarr; rw [hq0]; rfl
  obtain ⟨rL, hL, retL, psL, vvL, cL, nL, wL⟩ := to_outer mv hnv ty0 ty1 ty2 ty3 P head target parent n root H a0 R a0.od Lod
    n 0 fuel (by omega) (by omega) (by omega)
  have hL' : pexecM mv fuel (.whileLoop (.binary bT .lt (vI mv.nv 3) (vI mv.nv 1)) (TOouterBody mv.nv))
      (gS P ([ci root, ci n, ci 1] ++ [ci 0])) (VA { a0 with od := a0.od.set 0 (root : Int) }) = some rL := by
    rw [hvv0]; exact hL
  have sL := seqM_some hL' retL (pexecM_skip mv fuel rL.ps rL.vv)
  have s2 := seqM_some a2 rfl sL
  have sc2 := pexecM_scope mv fuel _ _ _ _ s2
  obtain ⟨hlen, hnd, hlt', hhd, hpar⟩ := order_spec H
  have tk2 : (⟨(gS P [ci root, ci n, ci (qrun head target parent [root] n).length, ci n]).mem.take
        (gS P [ci root, ci n, ci 1]).mem.length,
      (gS P [ci root, ci n, ci (qrun head target parent [root] n).length, ci n]).bs.take
        (gS P [ci root, ci n, ci 1]).bs.length⟩ : PS) =
      gS P [ci root, ci n, ci (qrun head target parent [root] n).length] :=
    gS_takeC P [ci root, ci n, ci 1] [ci root, ci n, ci (qrun head target parent [root] n).length] [ci n] rfl
  rw [psL] at sc2
  simp only [tk2] at sc2
  rw [hlen] at sc2
  have c3 := seqM_some sc2 (by simp) (pexecM_skip mv fuel _ _)
  have c2 := seqM_some a1 rfl c3
  have c1 := seqM_some aw rfl c2
  have hD := Dsum_le H R (qrun head target parent [root] n) n hnd hlt'
  have hD0 : Dsum head (qrun head target parent [root] 0) 0 = 0 := by simp [Dsum]
  refine ⟨_, qrun head target parent [root] n, c1, ?_, ?_, ?_, rfl, hlen, hnd, hlt', hhd, hpar, ?_, ?_, ?_⟩
  · simp
  · rfl
  · show rL.vv = _
    rw [vvL]
    unfold qarr
    rw [hlen, List.drop_eq_nil_of_le (by omega), List.append_nil]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL ⊢
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nL ⊢
    omega
  · simp at wL ⊢
    omega

end Proofs.TreeOrderExec




