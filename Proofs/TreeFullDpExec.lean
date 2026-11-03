import Proofs.TreeFullDpBody
import Proofs.TreeDpMath
import Proofs.TreeRootMath

namespace Proofs.TreeFullDpExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.ForLoopC (gS_takeC)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs pexecM_branch_true pexecM_branch_false)
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (vS vr bnd v64)
open Proofs.RunLengthExec (inc_val)
open Proofs.SegmentTreeExec (AppBlk appblk_exec mx)
open Proofs.TreeFullDpBody
open Proofs.TreeDpAlg Proofs.TreeDpSpec Proofs.TreeDpMath

/-- The nine vectors of `tree_full_dp`. -/
structure Arr where
  hd : List Int
  tg : List Int
  pa : List Int
  od : List Int
  dp : List Int
  pre : List Int
  suf : List Int
  up : List Int
  fu : List Int

def VA (a : Arr) : Nat → List Int := fun k =>
  if k = 0 then a.hd else if k = 1 then a.tg else if k = 2 then a.pa else if k = 3 then a.od else if k = 4 then a.dp
  else if k = 5 then a.pre else if k = 6 then a.suf else if k = 7 then a.up else if k = 8 then a.fu else []

theorem VA_get0 (a : Arr) : VA a 0 = a.hd := by simp [VA]
theorem VA_get1 (a : Arr) : VA a 1 = a.tg := by simp [VA]
theorem VA_get2 (a : Arr) : VA a 2 = a.pa := by simp [VA]
theorem VA_get3 (a : Arr) : VA a 3 = a.od := by simp [VA]
theorem VA_get4 (a : Arr) : VA a 4 = a.dp := by simp [VA]
theorem VA_get5 (a : Arr) : VA a 5 = a.pre := by simp [VA]
theorem VA_get6 (a : Arr) : VA a 6 = a.suf := by simp [VA]
theorem VA_get7 (a : Arr) : VA a 7 = a.up := by simp [VA]
theorem VA_get8 (a : Arr) : VA a 8 = a.fu := by simp [VA]

theorem VA_set4 (a : Arr) (x : List Int) : upd (VA a) 4 x = VA { a with dp := x } := by
  funext k; unfold upd VA; split <;> simp_all
theorem VA_set5 (a : Arr) (x : List Int) : upd (VA a) 5 x = VA { a with pre := x } := by
  funext k; unfold upd VA; split <;> simp_all
theorem VA_set6 (a : Arr) (x : List Int) : upd (VA a) 6 x = VA { a with suf := x } := by
  funext k; unfold upd VA; split <;> simp_all
theorem VA_set7 (a : Arr) (x : List Int) : upd (VA a) 7 x = VA { a with up := x } := by
  funext k; unfold upd VA; split <;> simp_all
theorem VA_set8 (a : Arr) (x : List Int) : upd (VA a) 8 x = VA { a with fu := x } := by
  funext k; unfold upd VA; split <;> simp_all

/-! ### Reading a vector at a cell index -/

theorem rdv (mv : MV) (vv : Nat → List Int) (P : List Cell) (cl : List Cell) (j c idx : Nat) (t : Ty)
    (hj : j < mv.nv) (ht : t = mv.ty j) (hc : cl[c]? = some (ci idx)) (hidx : idx < 2147483648) (x : Int)
    (hx : (vv j)[idx]? = some x) (hxv : (mv.ty j).valid x = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.read t (.local j) (.cast u64 (.variable i32 (mv.nv + c)))) = some x :=
  rdM_val mv vv _ j hj t ht (.cast u64 (.variable i32 (mv.nv + c))) rfl rfl idx
    (cidx_den _ _ idx (envs mv P cl c (ci idx) hc (i32v idx hidx)) hidx) x hx hxv

/-- `cell + 1` as an `int` expression. -/
theorem add1_den (mv : MV) (vv : Nat → List Int) (P : List Cell) (cl : List Cell) (c idx : Nat)
    (hc : cl[c]? = some (ci idx)) (h : idx + 1 < 2147483648) :
    (NExpr.binary i32 .add (.variable i32 (mv.nv + c)) Proofs.TreeFullDpBody.lit1).denote (penvN mv.nv (gS P cl)) = some ((idx + 1 : Nat) : Int) := by
  have hidx0 : idx < M31 := by
    have h2 : idx < 2147483648 := by omega
    exact h2
  have e := envs mv P cl c (ci idx) hc (i32v idx hidx0)
  rw [den_binary, den_variable, e, Option.bind_some, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .add (idx : Int) 1 = ((idx + 1 : Nat) : Int) := by
    show (idx : Int) + 1 = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32v _ h)

/-- Reading at `cell + 1`. -/
theorem rdv1 (mv : MV) (vv : Nat → List Int) (P : List Cell) (cl : List Cell) (j c idx : Nat) (t : Ty)
    (hj : j < mv.nv) (ht : t = mv.ty j) (hc : cl[c]? = some (ci idx)) (hidx : idx + 1 < 2147483648) (x : Int)
    (hx : (vv j)[idx + 1]? = some x) (hxv : (mv.ty j).valid x = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.read t (.local j) (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + c)) Proofs.TreeFullDpBody.lit1))) = some x := by
  have hd := add1_den mv vv P cl c idx hc hidx
  have hd' : (NExpr.cast u64 (.binary i32 .add (.variable i32 (mv.nv + c)) Proofs.TreeFullDpBody.lit1)).denote (penvN mv.nv (gS P cl)) =
      some ((idx + 1 : Nat) : Int) := by
    rw [den_cast, hd, Option.bind_some, convert_u64]
    congr 1
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have : idx + 1 < 2147483648 := hidx; omega)
  exact rdM_val mv vv _ j hj t ht _ rfl rfl (idx + 1) hd' x hx hxv

/-- A cell holding an `int`. -/
theorem cellI (mv : MV) (vv : Nat → List Int) (P : List Cell) (cl : List Cell) (c x : Nat)
    (hc : cl[c]? = some (ci x)) (hx : x < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (vI mv.nv c) = some (x : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_variable]
  exact envs mv P cl c (ci x) hc (i32v x hx)

/-- A cell holding a `long long`. -/
theorem cellS (mv : MV) (vv : Nat → List Int) (P : List Cell) (cl : List Cell) (c : Nat) (x : Int)
    (hc : cl[c]? = some (cs x)) (hx : s64.valid x = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (vS mv.nv c) = some x := by
  rw [vdenM_scalar _ _ _ _ rfl]
  exact vr mv P cl c x hc hx

theorem i32vn (x : Nat) (h : x < 2147483648) : i32.valid (x : Int) = true := i32v x h

/-! ### The instance: maximum, identity `0`, `sum_up(x) = x + 1` -/

def M0 : CM where
  V := fun x => 0 ≤ x
  op := mx
  e := 0
  su := fun x => x + 1
  he := le_refl _
  closed := by intro a b ha hb; unfold mx; split <;> assumption
  suV := by intro a ha; omega
  assoc := by intro a b c _ _ _; unfold mx; split_ifs <;> omega
  comm := by intro a b _ _; unfold mx; split_ifs <;> omega
  lid := by intro a ha; unfold mx; split_ifs <;> omega

/-- Read-only facts about the arrays. -/
structure Ro (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr) : Prop where
  hd : a.hd = head.map (fun x : Nat => (x : Int))
  tg : a.tg = target.map (fun x : Nat => (x : Int))
  pa : a.pa = parent
  od : a.od = ord.map (fun x : Nat => (x : Int))
  hlen : head.length = n + 1
  hmono : ∀ v, v < n → head.getD v 0 ≤ head.getD (v + 1) 0
  hlast : head.getD n 0 = target.length
  tlen : target.length < 2147483647
  tlt : ∀ q, q < target.length → target.getD q 0 < n
  nb : n + 2 < 2147483648
  palen : parent.length = n
  pav : ∀ w, w < n → 0 ≤ parent.getD w 0 ∧ parent.getD w 0 < n
  odlen : ord.length = n
  odlt : ∀ x ∈ ord, x < n

/-- Lengths of the writable arrays. -/
structure Lens (n m : Nat) (a : Arr) : Prop where
  dp : a.dp.length = n
  pre : a.pre.length = m
  suf : a.suf.length = m
  up : a.up.length = n
  fu : a.fu.length = n

theorem filter_lt_succ (l : List Nat) (hl : l.Pairwise (· < ·)) (p : Nat) :
    l.filter (fun q => decide (q < p + 1)) = l.filter (fun q => decide (q < p)) ++ (if p ∈ l then [p] else []) := by
  by_cases hp : p ∈ l
  · rw [if_pos hp]
    have h := pairwise_split l hl p hp
    have hA : (l.filter (fun q => decide (q < p))).filter (fun q => decide (q < p + 1)) = l.filter (fun q => decide (q < p)) := by
      rw [List.filter_eq_self]
      intro q hq
      have := (List.mem_filter.mp hq).2
      simp at this ⊢; omega
    have hB : (l.filter (fun q => decide (p < q))).filter (fun q => decide (q < p + 1)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro q hq
      have := (List.mem_filter.mp hq).2
      simp at this ⊢; omega
    conv_lhs => rw [h]
    rw [List.filter_append, hA, List.filter_cons_of_pos (by simp), hB]
  · rw [if_neg hp, List.append_nil]
    apply List.filter_congr
    intro q hq
    have : q ≠ p := fun e => hp (e ▸ hq)
    simp; omega

/-! ### The forward arc loop (`pre`): math -/

structure AI1 (head target : List Nat) (parent : List Int) (v p : Nat) (dp pre0 pre' : List Int) (acc : Int) : Prop where
  accE : acc = fold M0 ((((kidArcs head target parent v).filter fun q => decide (q < p)).map (tgt target)).map
    fun x => dp.getD x 0)
  done : ∀ q ∈ kidArcs head target parent v, q < p →
    pre'.getD q 0 = fold M0 ((kb head target parent v q).map fun x => dp.getD x 0)
  rest : ∀ q, ¬ (q ∈ kidArcs head target parent v ∧ q < p) → pre'.getD q 0 = pre0.getD q 0
  len : pre'.length = pre0.length

theorem kidArcs_ge (head target : List Nat) (parent : List Int) (v q : Nat) (hq : q ∈ kidArcs head target parent v) :
    head.getD v 0 ≤ q ∧ q < head.getD (v + 1) 0 := by
  have := (List.mem_filter.mp hq).1
  unfold arcs at this
  rw [List.mem_range'_1] at this
  omega

theorem ai1_init (head target : List Nat) (parent : List Int) (v : Nat) (dp pre0 : List Int) :
    AI1 head target parent v (head.getD v 0) dp pre0 pre0 0 := by
  refine ⟨?_, fun q hq hlt => ?_, fun q _ => rfl, rfl⟩
  · have : (kidArcs head target parent v).filter (fun q => decide (q < head.getD v 0)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro q hq
      have := (kidArcs_ge head target parent v q hq).1
      rw [decide_eq_false (by omega)]
      simp
    rw [this]; rfl
  · exact absurd hlt (by have := (kidArcs_ge head target parent v q hq).1; omega)

theorem ai1_child (head target : List Nat) (parent : List Int) (v p : Nat) (dp pre0 pre' : List Int) (acc : Int)
    (I : AI1 head target parent v p dp pre0 pre' acc) (hpk : p ∈ kidArcs head target parent v)
    (hdp : ∀ x, 0 ≤ dp.getD x 0) (hpl : p < pre'.length) :
    AI1 head target parent v (p + 1) dp pre0 (pre'.set p acc) (mx acc (dp.getD (tgt target p) 0)) := by
  have hK := kidArcs_pairwise head target parent v
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [filter_lt_succ _ hK p, if_pos hpk, List.map_append, List.map_append]
    simp only [List.map_cons, List.map_nil]
    have hA : ∀ y ∈ (((kidArcs head target parent v).filter fun q => decide (q < p)).map (tgt target)).map
        (fun x => dp.getD x 0), M0.V y := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      exact hdp x
    rw [fold_append M0 _ _ hA (by intro y hy; simp at hy; rw [hy]; exact hdp _)]
    have h1 : fold M0 [dp.getD (tgt target p) 0] = dp.getD (tgt target p) 0 := fold_single M0 _ (hdp _)
    rw [h1, ← I.accE]
    rfl
  · intro q hq hqlt
    rw [Proofs.SegTreeMath.getD_setE]
    by_cases hqp : q = p
    · subst hqp
      rw [if_pos ⟨rfl, hpl⟩]
      rw [I.accE]; rfl
    · rw [if_neg (fun h => hqp h.1)]
      exact I.done q hq (by omega)
  · intro q hq
    rw [Proofs.SegTreeMath.getD_setE]
    have hqp : q ≠ p := fun h => hq ⟨h ▸ hpk, by omega⟩
    rw [if_neg (fun h => hqp h.1)]
    exact I.rest q (fun h => hq ⟨h.1, by omega⟩)
  · simp [I.len]

theorem ai1_other (head target : List Nat) (parent : List Int) (v p : Nat) (dp pre0 pre' : List Int) (acc : Int)
    (I : AI1 head target parent v p dp pre0 pre' acc) (hpk : p ∉ kidArcs head target parent v) :
    AI1 head target parent v (p + 1) dp pre0 pre' acc := by
  have hK := kidArcs_pairwise head target parent v
  refine ⟨?_, ?_, ?_, I.len⟩
  · rw [filter_lt_succ _ hK p, if_neg hpk, List.append_nil]; exact I.accE
  · intro q hq hqlt
    have : q < p := by
      have : q ≠ p := fun h => hpk (h ▸ hq)
      omega
    exact I.done q hq this
  · intro q hq
    exact I.rest q (fun h => hq ⟨h.1, by
      have : q ≠ p := fun e => hpk (e ▸ h.1)
      omega⟩)

/-! ### The forward arc loop (`pre`): execution -/

abbrev CB (root n k v : Nat) (acc : Int) : List Cell := [ci root, ci n, ci k, ci v, cs 0, cs acc]

theorem tg_get (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (p : Nat) (hp : p < target.length) :
    a.tg.getD p 0 = (target.getD p 0 : Int) := by
  rw [R.tg]; simp [List.getD_eq_getElem?_getD, hp]

theorem tg_getq (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (p : Nat) (hp : p < target.length) :
    a.tg[p]? = some (target.getD p 0 : Int) := by
  rw [vec_getI a.tg p (by rw [R.tg]; simp [hp]), tg_get head target parent ord n a R p hp]

theorem pa_getq (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (w : Nat) (hw : w < n) :
    a.pa[w]? = some (parent.getD w 0) := by
  rw [vec_getI a.pa w (by rw [R.pa, R.palen]; exact hw), R.pa]

theorem arc_lt (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (v : Nat) (hv : v < n) (p : Nat) (hp : p ∈ arcs head v) :
    p < target.length := by
  unfold arcs at hp
  rw [List.mem_range'_1] at hp
  have h1 : head.getD (v + 1) 0 ≤ target.length := by
    rw [← R.hlast]
    -- monotone chain
    have : ∀ d, v + 1 + d ≤ n → head.getD (v + 1) 0 ≤ head.getD (v + 1 + d) 0 := by
      intro d
      induction d with
      | zero => intro _; exact le_refl _
      | succ d ih =>
        intro hd
        exact le_trans (ih (by omega)) (R.hmono (v + 1 + d) (by omega))
    have := this (n - (v + 1)) (by omega)
    rwa [show v + 1 + (n - (v + 1)) = n by omega] at this
  omega

/-- The child test on an arc. -/
theorem ischild_val (mv : MV) (hnv : mv.nv = 9) (ty2 : mv.ty 2 = i32) (P : List Cell) (cl : List Cell) (a : Arr) (vc wc v w : Nat)
    (hv : cl[vc]? = some (ci v)) (hw : cl[wc]? = some (ci w)) (hv31 : v < 2147483648) (hw31 : w < 2147483648)
    (pw : Int) (hpw : a.pa[w]? = some pw) (hpwv : i32.valid pw = true) :
    vdenM mv (VA a) (penvN mv.nv (gS P cl)) (isChild mv.nv vc wc) = some (if pw = (v : Int) then 1 else 0) := by
  have r := rdv mv (VA a) P cl 2 wc w i32 (by omega) ty2.symm hw hw31 pw (by rw [VA_get2]; exact hpw) (by rw [ty2]; exact hpwv)
  have c := cellI mv (VA a) P cl vc v hv hv31
  unfold isChild
  rw [vdenM_binary mv _ _ bT .eq _ _ rfl, r, Option.bind_some, c, Option.bind_some]
  by_cases h : pw = (v : Int)
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

def i1acc (a : Arr) (v p : Nat) (acc : Int) : Int :=
  if a.pa.getD (a.tg.getD p 0).toNat 0 = (v : Int) then mx acc (a.dp.getD (a.tg.getD p 0).toNat 0) else acc

def i1pre (a : Arr) (v p : Nat) (acc : Int) : List Int :=
  if a.pa.getD (a.tg.getD p 0).toNat 0 = (v : Int) then a.pre.set p acc else a.pre

set_option maxHeartbeats 128000000 in
/-- One iteration of the forward arc loop. -/
theorem i1_iter (mv : MV) (hnv : mv.nv = 9) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32) (ty4 : mv.ty 4 = s64)
    (ty5 : mv.ty 5 = s64) (P : List Cell) (fu : Nat) (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat)
    (a : Arr) (R : Ro head target parent ord n a) (Ln : Lens n target.length a) (root k v p : Nat) (acc : Int)
    (hv : v < n) (hp : p ∈ arcs head v) (hrk : root < 2147483648) (hk31 : k < 2147483648)
    (hacc : s64.valid acc = true) (hdpv : ∀ x, s64.valid (a.dp.getD x 0) = true) :
    ∃ r : PRM, pexecM mv fu (I1body mv.nv) (gS P (CB root n k v acc ++ [ci p])) (VA a) = some r ∧ r.ret = none ∧
      r.ps = gS P (CB root n k v (i1acc a v p acc) ++ [ci (p + 1)]) ∧ r.vv = VA { a with pre := i1pre a v p acc } ∧
      r.cost ≤ 1000 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 1 := by
  have hpt : p < target.length := arc_lt head target parent ord n a R v hv p hp
  have hw : target.getD p 0 < n := R.tlt p hpt
  have hn31 := R.nb
  have hp31 : p + 1 < 2147483648 := by have := R.tlen; omega
  have hv31 : v < 2147483648 := by omega
  have hw31 : target.getD p 0 < 2147483648 := by omega
  have hkp : (CB root n k v acc ++ [ci p])[6]? = some (ci p) := by simp
  have hden : vdenM mv (VA a) (penvN mv.nv (gS P (CB root n k v acc ++ [ci p]))) (rdI 1 (vI mv.nv 6)) =
      some (target.getD p 0 : Int) :=
    rdv mv (VA a) P _ 1 6 p i32 (by omega) ty1.symm hkp (by omega) _
      (by rw [VA_get1]; exact tg_getq head target parent ord n a R p hpt) (by rw [ty1]; exact i32v _ hw31)
  have d1 := gSM_decl mv P (CB root n k v acc ++ [ci p]) (VA a) i32 (rdI 1 (vI mv.nv 6)) (target.getD p 0 : Int)
    (target.getD p 0 : Int) hden (conv_signed i32 rfl rfl _ (i32v _ hw31))
  have a1 := (pexecM_prim mv fu (.declare i32 true (rdI 1 (vI mv.nv 6))) _ _).trans d1
  have e8 : CB root n k v acc ++ [ci p] ++ [(⟨i32, (target.getD p 0 : Int)⟩ : Cell)] =
      CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)] := rfl
  rw [e8] at a1
  -- the child test
  have hpw := pa_getq head target parent ord n a R (target.getD p 0) hw
  have hpwv : i32.valid (parent.getD (target.getD p 0) 0) = true := by
    obtain ⟨h0, h1⟩ := R.pav _ hw
    exact Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)
  have hc := ischild_val mv hnv ty2 P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)]) a 3 7 v (target.getD p 0)
    (by simp) (by simp) hv31 hw31 _ hpw hpwv
  have hacc_eq : i1acc a v p acc = if parent.getD (target.getD p 0) 0 = (v : Int) then mx acc (a.dp.getD (target.getD p 0) 0) else acc := by
    unfold i1acc; rw [tg_get head target parent ord n a R p hpt, R.pa]; simp
  have hpre_eq : i1pre a v p acc = if parent.getD (target.getD p 0) 0 = (v : Int) then a.pre.set p acc else a.pre := by
    unfold i1pre; rw [tg_get head target parent ord n a R p hpt, R.pa]; simp
  -- the increment, from a state of the form `CB .. ++ [ci p]`
  have hinc : ∀ (acc' : Int) (vv : Nat → List Int), s64.valid acc' = true →
      ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (incI mv.nv 6)) Sk) (gS P (CB root n k v acc' ++ [ci p])) vv = some r2 ∧
        r2.ret = none ∧ r2.ps = gS P (CB root n k v acc' ++ [ci (p + 1)]) ∧ r2.vv = vv ∧ r2.cost ≤ 100 ∧
        r2.need ≤ P.length + 100 ∧ r2.wk = 0 := by
    intro acc' vv _
    have e2 := inc_val mv vv _ (mv.nv + 6) p (envs mv P (CB root n k v acc' ++ [ci p]) 6 (ci p) (by simp) (i32vn p (by omega))) hp31
    have s2 := gSM_assign mv P (CB root n k v acc' ++ [ci p]) vv 6 (by simp) i32 _ _ _ e2 (ci p) (by simp) rfl
      (i32vn p (by omega)) (conv_signed i32 rfl rfl _ (i32vn (p + 1) (by omega)))
    have eB : (CB root n k v acc' ++ [ci p]).set 6 ⟨i32, ((p + 1 : Nat) : Int)⟩ = CB root n k v acc' ++ [ci (p + 1)] := rfl
    rw [eB] at s2
    have a2 := (pexecM_prim mv fu (incI mv.nv 6) _ _).trans s2
    have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  by_cases hch : parent.getD (target.getD p 0) 0 = (v : Int)
  · rw [if_pos hch] at hc
    have hmxv : s64.valid (mx acc (a.dp.getD (target.getD p 0) 0)) = true := by
      unfold mx; split
      · exact hdpv _
      · exact hacc
    -- the write `pre[p] = acc`
    have hx5 : vdenM mv (VA a) (penvN mv.nv (gS P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)]))) (vS mv.nv 5) = some acc :=
      cellS mv _ P _ 5 acc (by simp) hacc
    have hi6 : vdenM mv (VA a) (penvN mv.nv (gS P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)])))
        (.cast u64 (.variable i32 (mv.nv + 6))) = some (p : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact cidx_den _ _ p (envs mv P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)]) 6 (ci p) (by simp) (i32vn p (by omega))) (show p < 2147483648 by omega)
    have hlt5 : p < ((VA a) 5).length := by rw [VA_get5, Ln.pre]; exact hpt
    have hv5 : (mv.ty 5).valid acc = true := by rw [ty5]; exact hacc
    have hw5 := pstmtM_write_ok mv (gS P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)])) (VA a) 5 (by omega)
      (.cast u64 (.variable i32 (mv.nv + 6))) (vS mv.nv 5) acc p hx5 hi6 hlt5 hv5
    rw [ty5, VA_get5, VA_set5] at hw5
    have aw := (pexecM_prim mv fu (wrS 5 (vI mv.nv 6) (vS mv.nv 5)) _ _).trans hw5
    -- the `apply` block
    have hX : vdenM mv (VA { a with pre := a.pre.set p acc }) (penvN mv.nv (gS P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)])))
        (vS mv.nv 5) = some acc := cellS mv _ P _ 5 acc (by simp) hacc
    have hY : vdenM mv (VA { a with pre := a.pre.set p acc })
        (penvN mv.nv (gS P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)] ++ [cs acc])))
        (rdS 4 (vI mv.nv 7)) = some (a.dp.getD (target.getD p 0) 0) :=
      rdv mv _ P _ 4 7 (target.getD p 0) s64 (by omega) ty4.symm (by simp) hw31 _
        (by rw [VA_get4]; exact vec_getI a.dp _ (by rw [Ln.dp]; exact hw)) (by rw [ty4]; exact hdpv _)
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ : ∃ r2 : PRM,
        pexecM mv fu (.sequence (.primitive (.assign (mv.nv + 5) s64 (vS mv.nv 11))) Sk)
          (gS P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)] ++ [cs acc, cs (a.dp.getD (target.getD p 0) 0),
            cs (mx acc (a.dp.getD (target.getD p 0) 0)), cs (mx acc (a.dp.getD (target.getD p 0) 0))]))
          (VA { a with pre := a.pre.set p acc }) = some r2 ∧ r2.ret = none ∧
        r2.ps = gS P (CB root n k v (mx acc (a.dp.getD (target.getD p 0) 0)) ++ [ci p] ++ [ci (target.getD p 0)] ++
          [cs acc, cs (a.dp.getD (target.getD p 0) 0), cs (mx acc (a.dp.getD (target.getD p 0) 0)),
            cs (mx acc (a.dp.getD (target.getD p 0) 0))]) ∧
        r2.vv = VA { a with pre := a.pre.set p acc } ∧ r2.cost ≤ 100 ∧ r2.need ≤ P.length + 80 ∧ r2.wk = 0 := by
      have s5 := gSM_assign mv P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)] ++ [cs acc, cs (a.dp.getD (target.getD p 0) 0),
            cs (mx acc (a.dp.getD (target.getD p 0) 0)), cs (mx acc (a.dp.getD (target.getD p 0) 0))])
        (VA { a with pre := a.pre.set p acc }) 5 (by simp) s64 (vS mv.nv 11) (mx acc (a.dp.getD (target.getD p 0) 0))
        (mx acc (a.dp.getD (target.getD p 0) 0)) (cellS mv _ P _ 11 _ (by simp) hmxv) (cs acc) (by simp) rfl hacc
        (conv_signed s64 rfl rfl _ hmxv)
      have eA : (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)] ++ [cs acc, cs (a.dp.getD (target.getD p 0) 0),
            cs (mx acc (a.dp.getD (target.getD p 0) 0)), cs (mx acc (a.dp.getD (target.getD p 0) 0))]).set 5
            ⟨s64, mx acc (a.dp.getD (target.getD p 0) 0)⟩ =
          CB root n k v (mx acc (a.dp.getD (target.getD p 0) 0)) ++ [ci p] ++ [ci (target.getD p 0)] ++
          [cs acc, cs (a.dp.getD (target.getD p 0) 0), cs (mx acc (a.dp.getD (target.getD p 0) 0)),
            cs (mx acc (a.dp.getD (target.getD p 0) 0))] := rfl
      rw [eA] at s5
      have a5 := (pexecM_prim mv fu (.assign (mv.nv + 5) s64 (vS mv.nv 11)) _ _).trans s5
      have b5 := seqM_some a5 rfl (pexecM_skip mv fu _ _)
      refine ⟨_, b5, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
    obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P (VA { a with pre := a.pre.set p acc }) fu
      (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)]) 8 (by simp) (vS mv.nv 5) (rdS 4 (vI mv.nv 7)) acc
      (a.dp.getD (target.getD p 0) 0) hacc (hdpv _) hX hY _ r2 hr2
    have sW := seqM_some aw rfl hA
    have sc := pexecM_scope mv fu _ _ _ _ sW
    rw [psA, ps2] at sc
    have tk := gS_takeC P (CB root n k v acc ++ [ci p] ++ [ci (target.getD p 0)])
      (CB root n k v (mx acc (a.dp.getD (target.getD p 0) 0)) ++ [ci p] ++ [ci (target.getD p 0)])
      [cs acc, cs (a.dp.getD (target.getD p 0) 0), cs (mx acc (a.dp.getD (target.getD p 0) 0)),
        cs (mx acc (a.dp.getD (target.getD p 0) 0))] rfl
    simp only [tk] at sc
    have b1 := seqM_some sc (by rw [retA, ret2]) (pexecM_skip mv fu _ _)
    have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b1
    have b4 := seqM_some b3 (by simp) (pexecM_skip mv fu _ _)
    have s1 := seqM_some a1 rfl b4
    have b5 := pexecM_scope mv fu _ _ _ _ s1
    have tk2 := gS_takeC P (CB root n k v acc ++ [ci p])
      (CB root n k v (mx acc (a.dp.getD (target.getD p 0) 0)) ++ [ci p]) [ci (target.getD p 0)] rfl
    simp only [tk2] at b5
    obtain ⟨r3, hr3, ret3, ps3, vv3, c3, n3, w3⟩ := hinc (mx acc (a.dp.getD (target.getD p 0) 0))
      (VA { a with pre := a.pre.set p acc }) hmxv
    have b6 := seqM_some b5 (by simp) (by rw [vvA, vv2]; exact hr3)
    refine ⟨_, b6, ret3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hacc_eq, if_pos hch]; exact ps3
    · rw [hpre_eq, if_pos hch]; exact vv3
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA c2 c3 ⊢; omega
    · have hA' := nA (P.length + 100) (by omega) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' n2 n3 ⊢
      omega
    · simp at wA w2 w3 ⊢; omega
  · rw [if_neg hch] at hc
    have b3 := pexecM_branch_false mv fu _ (.sequence (.scope (I1act mv.nv)) Sk) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    have s1 := seqM_some a1 rfl b4
    have b5 := pexecM_scope mv fu _ _ _ _ s1
    have tk := gS_takeC P (CB root n k v acc ++ [ci p]) (CB root n k v acc ++ [ci p]) [ci (target.getD p 0)] rfl
    simp only [tk] at b5
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ := hinc acc (VA a) hacc
    have b6 := seqM_some b5 (by simp) hr2
    refine ⟨_, b6, ret2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hacc_eq, if_neg hch]; exact ps2
    · rw [hpre_eq, if_neg hch]; exact vv2
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n2 ⊢; omega
    · simp at w2 ⊢; omega

theorem hd_getq (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (i : Nat) (hi : i ≤ n) :
    a.hd[i]? = some (head.getD i 0 : Int) := by
  have hl : i < a.hd.length := by rw [R.hd]; simp [R.hlen]; omega
  rw [vec_getI a.hd i hl, R.hd]; simp [List.getD_eq_getElem?_getD, show i < head.length by rw [R.hlen]; omega]

theorem head_le (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (v : Nat) (hv : v < n) : head.getD (v + 1) 0 ≤ target.length := by
  rw [← R.hlast]
  have : ∀ d, v + 1 + d ≤ n → head.getD (v + 1) 0 ≤ head.getD (v + 1 + d) 0 := by
    intro d
    induction d with
    | zero => intro _; exact le_refl _
    | succ d ih => intro hd; exact le_trans (ih (by omega)) (R.hmono (v + 1 + d) (by omega))
  have := this (n - (v + 1)) (by omega)
  rwa [show v + 1 + (n - (v + 1)) = n by omega] at this

/-- The condition `p < head[v + 1]` of the forward arc loop. -/
theorem cond1_val (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (P : List Cell) (cl : List Cell) (a : Arr)
    (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (R : Ro head target parent ord n a)
    (v p : Nat) (hv : v < n) (h3 : cl[3]? = some (ci v)) (h6 : cl[6]? = some (ci p)) (hp : p < 2147483648) :
    vdenM mv (VA a) (penvN mv.nv (gS P cl)) (I1cond mv.nv) = some (if p < head.getD (v + 1) 0 then 1 else 0) := by
  have hh : i32.valid (head.getD (v + 1) 0 : Int) = true := by
    have := head_le head target parent ord n a R v hv
    have := R.tlen
    exact i32vn _ (by omega)
  have r := rdv1 mv (VA a) P cl 0 3 v i32 (by omega) ty0.symm h3 (by have := R.nb; omega) (head.getD (v + 1) 0 : Int)
    (by rw [VA_get0]; exact hd_getq head target parent ord n a R (v + 1) (by omega)) (by rw [ty0]; exact hh)
  have c := cellI mv (VA a) P cl 6 p h6 hp
  unfold I1cond
  rw [vdenM_binary mv _ _ bT .lt _ _ rfl, c, Option.bind_some, r, Option.bind_some]
  generalize head.getD (v + 1) 0 = H
  by_cases h : p < H
  · have : (p : Int) < (H : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((p : Int) < (H : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

theorem Ro.updPre {head target : List Nat} {parent : List Int} {ord : List Nat} {n : Nat} {a : Arr}
    (R : Ro head target parent ord n a) (x : List Int) : Ro head target parent ord n { a with pre := x } :=
  ⟨R.hd, R.tg, R.pa, R.od, R.hlen, R.hmono, R.hlast, R.tlen, R.tlt, R.nb, R.palen, R.pav, R.odlen, R.odlt⟩

theorem i1_child_iff (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (v p : Nat) (hv : v < n) (hp : p ∈ arcs head v) :
    (a.pa.getD (a.tg.getD p 0).toNat 0 = (v : Int)) ↔ p ∈ kidArcs head target parent v := by
  have hpt : p < target.length := arc_lt head target parent ord n a R v hv p hp
  rw [tg_get head target parent ord n a R p hpt, R.pa]
  simp only [Int.toNat_natCast]
  unfold kidArcs
  rw [List.mem_filter]
  simp [hp, tgt]

theorem i1_acc_eq (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (v p : Nat) (hv : v < n) (hp : p ∈ arcs head v) (acc : Int) :
    (i1acc a v p acc = if p ∈ kidArcs head target parent v then mx acc (a.dp.getD (tgt target p) 0) else acc) ∧
    (i1pre a v p acc = if p ∈ kidArcs head target parent v then a.pre.set p acc else a.pre) := by
  have hpt : p < target.length := arc_lt head target parent ord n a R v hv p hp
  have h := i1_child_iff head target parent ord n a R v p hv hp
  have e : (a.tg.getD p 0).toNat = tgt target p := by
    rw [tg_get head target parent ord n a R p hpt]; simp [tgt]
  unfold i1acc i1pre
  rw [e]
  rw [e] at h
  constructor <;> (by_cases hc : a.pa.getD (tgt target p) 0 = (v : Int)
                   · rw [if_pos hc, if_pos (h.mp hc)]
                   · rw [if_neg hc, if_neg (fun hk => hc (h.mpr hk))])

set_option maxHeartbeats 128000000 in
/-- The forward arc loop `for (p = head[v]; p < head[v + 1]; p++) ...`, from the state at arc `p`. -/
theorem i1_loop (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty4 : mv.ty 4 = s64) (ty5 : mv.ty 5 = s64) (P : List Cell) (head target : List Nat) (parent : List Int) (ord : List Nat)
    (n : Nat) (a0 : Arr) (R : Ro head target parent ord n a0) (Ln : Lens n target.length a0) (root k v : Nat) (hv : v < n)
    (hrk : root < 2147483648) (hk31 : k < 2147483648) (hdpv : ∀ x, s64.valid (a0.dp.getD x 0) = true)
    (hdpnn : ∀ x, 0 ≤ a0.dp.getD x 0) :
    ∀ (d p : Nat) (pre' : List Int) (acc : Int) (fu : Nat), head.getD (v + 1) 0 - p = d → head.getD v 0 ≤ p →
      p ≤ head.getD (v + 1) 0 → AI1 head target parent v p a0.dp a0.pre pre' acc → s64.valid acc = true → d + 1 ≤ fu →
      ∃ (res : PRM) (pre'' : List Int) (acc'' : Int),
        pexecM mv fu (.whileLoop (I1cond mv.nv) (I1body mv.nv)) (gS P (CB root n k v acc ++ [ci p])) (VA { a0 with pre := pre' }) = some res ∧
        res.ret = none ∧ res.ps = gS P (CB root n k v acc'' ++ [ci (head.getD (v + 1) 0)]) ∧
        res.vv = VA { a0 with pre := pre'' } ∧
        AI1 head target parent v (head.getD (v + 1) 0) a0.dp a0.pre pre'' acc'' ∧ s64.valid acc'' = true ∧
        res.cost ≤ 1100 * d + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ d := by
  have hend := head_le head target parent ord n a0 R v hv
  have htl := R.tlen
  intro d
  induction d with
  | zero =>
    intro p pre' acc fu hd hp0 hpe I hacc hfu
    have hpeq : p = head.getD (v + 1) 0 := by omega
    subst hpeq
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond1_val mv hnv ty0 P (CB root n k v acc ++ [ci (head.getD (v + 1) 0)]) { a0 with pre := pre' } head target parent ord n (R.updPre pre')
      v (head.getD (v + 1) 0) hv (by simp) (by simp) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, pre', acc, rfl, rfl, rfl, rfl, I, hacc, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro p pre' acc fu hd hp0 hpe I hacc hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hpin : p ∈ arcs head v := by
      unfold arcs; rw [List.mem_range'_1]; omega
    have hc := cond1_val mv hnv ty0 P (CB root n k v acc ++ [ci p]) { a0 with pre := pre' } head target parent ord n (R.updPre pre')
      v p hv (by simp) (by simp) (by omega)
    rw [if_pos (by omega)] at hc
    have Ln' : Lens n target.length { a0 with pre := pre' } := ⟨Ln.dp, by rw [I.len]; exact Ln.pre, Ln.suf, Ln.up, Ln.fu⟩
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := i1_iter mv hnv ty1 ty2 ty4 ty5 P (fu' + 1) head target parent ord n
      { a0 with pre := pre' } (R.updPre pre') Ln' root k v p acc hv hpin hrk hk31 hacc hdpv
    have hq := i1_acc_eq head target parent ord n { a0 with pre := pre' } (R.updPre pre') v p hv hpin acc
    have hq' : i1acc { a0 with pre := pre' } v p acc = (if p ∈ kidArcs head target parent v then mx acc (a0.dp.getD (tgt target p) 0) else acc) := hq.1
    have hp' : i1pre { a0 with pre := pre' } v p acc = (if p ∈ kidArcs head target parent v then pre'.set p acc else pre') := hq.2
    have hI' : AI1 head target parent v (p + 1) a0.dp a0.pre (i1pre { a0 with pre := pre' } v p acc)
        (i1acc { a0 with pre := pre' } v p acc) := by
      rw [hq', hp']
      by_cases hk : p ∈ kidArcs head target parent v
      · rw [if_pos hk, if_pos hk]
        exact ai1_child head target parent v p a0.dp a0.pre pre' acc I hk hdpnn (by rw [I.len]; exact lt_of_lt_of_le (by omega) (le_refl _) |> fun _ => by rw [Ln.pre]; exact arc_lt head target parent ord n a0 R v hv p hpin)
      · rw [if_neg hk, if_neg hk]
        exact ai1_other head target parent v p a0.dp a0.pre pre' acc I hk
    have hacc' : s64.valid (i1acc { a0 with pre := pre' } v p acc) = true := by
      rw [hq']
      by_cases hk : p ∈ kidArcs head target parent v
      · rw [if_pos hk]; unfold mx; split
        · exact hdpv _
        · exact hacc
      · rw [if_neg hk]; exact hacc
    obtain ⟨r2, pre'', acc'', h2, ret2, ps2, vv2, hI2, hacc2, c2, n2, w2⟩ :=
      ih (p + 1) (i1pre { a0 with pre := pre' } v p acc) (i1acc { a0 with pre := pre' } v p acc) fu' (by omega) (by omega) (by omega)
        hI' hacc' (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
    rw [h1]
    simp only [ret1, ps1, vv1]
    rw [h2]
    simp only
    refine ⟨_, pre'', acc'', rfl, ret2, ps2, vv2, hI2, hacc2, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

/-- The cells of `tree_full_dp` while the backward arc loop runs (before the loop variable). -/
abbrev CB2 (root n k v : Nat) (tot back : Int) : List Cell :=
  [ci root, ci n, ci k, ci v, cs 0, cs tot, cs tot, cs (tot + 1), cs 0, cs back]

/-- An `int` cell holding an integer that may be negative. -/
abbrev cpI (z : Int) : Cell := ⟨i32, z⟩

theorem sub1_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (slot k : Nat)
    (h : env slot i32 = some (k : Int)) (hk : k < 2147483648) :
    vdenM mv vv env (.binary i32 .sub (.variable i32 slot) Proofs.TreeFullDpBody.lit1) = some ((k : Int) - 1) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, h, Option.bind_some, den_literal,
    if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .sub (k : Int) 1 = (k : Int) - 1 := rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (Proofs.VectorSumCall.i32_valid _ (by omega) (by omega))

def i2acc (a : Arr) (v p : Nat) (acc : Int) : Int :=
  if a.pa.getD (a.tg.getD p 0).toNat 0 = (v : Int) then mx acc (a.dp.getD (a.tg.getD p 0).toNat 0) else acc

def i2suf (a : Arr) (v p : Nat) (acc : Int) : List Int :=
  if a.pa.getD (a.tg.getD p 0).toNat 0 = (v : Int) then a.suf.set p acc else a.suf

set_option maxHeartbeats 128000000 in
/-- One iteration of the backward arc loop. -/
theorem i2_iter (mv : MV) (hnv : mv.nv = 9) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32) (ty4 : mv.ty 4 = s64)
    (ty6 : mv.ty 6 = s64) (P : List Cell) (fu : Nat) (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat)
    (a : Arr) (R : Ro head target parent ord n a) (Ln : Lens n target.length a) (root k v p : Nat) (tot acc : Int)
    (hv : v < n) (hp : p ∈ arcs head v) (hrk : root < 2147483648) (hk31 : k < 2147483648)
    (htot : s64.valid tot = true) (htot1 : s64.valid (tot + 1) = true) (hacc : s64.valid acc = true) (hdpv : ∀ x, s64.valid (a.dp.getD x 0) = true) :
    ∃ r : PRM, pexecM mv fu (I2body mv.nv) (gS P (CB2 root n k v tot acc ++ [ci p])) (VA a) = some r ∧ r.ret = none ∧
      r.ps = gS P (CB2 root n k v tot (i2acc a v p acc) ++ [cpI ((p : Int) - 1)]) ∧ r.vv = VA { a with suf := i2suf a v p acc } ∧
      r.cost ≤ 1000 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 1 := by
  have hpt : p < target.length := arc_lt head target parent ord n a R v hv p hp
  have hw : target.getD p 0 < n := R.tlt p hpt
  have hn31 := R.nb
  have hp31 : p + 1 < 2147483648 := by have := R.tlen; omega
  have hv31 : v < 2147483648 := by omega
  have hw31 : target.getD p 0 < 2147483648 := by omega
  have hkp : (CB2 root n k v tot acc ++ [ci p])[10]? = some (ci p) := by simp
  have hden : vdenM mv (VA a) (penvN mv.nv (gS P (CB2 root n k v tot acc ++ [ci p]))) (rdI 1 (vI mv.nv 10)) =
      some (target.getD p 0 : Int) :=
    rdv mv (VA a) P _ 1 10 p i32 (by omega) ty1.symm hkp (by omega) _
      (by rw [VA_get1]; exact tg_getq head target parent ord n a R p hpt) (by rw [ty1]; exact i32v _ hw31)
  have d1 := gSM_decl mv P (CB2 root n k v tot acc ++ [ci p]) (VA a) i32 (rdI 1 (vI mv.nv 10)) (target.getD p 0 : Int)
    (target.getD p 0 : Int) hden (conv_signed i32 rfl rfl _ (i32v _ hw31))
  have a1 := (pexecM_prim mv fu (.declare i32 true (rdI 1 (vI mv.nv 10))) _ _).trans d1
  have e8 : CB2 root n k v tot acc ++ [ci p] ++ [(⟨i32, (target.getD p 0 : Int)⟩ : Cell)] =
      CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)] := rfl
  rw [e8] at a1
  -- the child test
  have hpw := pa_getq head target parent ord n a R (target.getD p 0) hw
  have hpwv : i32.valid (parent.getD (target.getD p 0) 0) = true := by
    obtain ⟨h0, h1⟩ := R.pav _ hw
    exact Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)
  have hc := ischild_val mv hnv ty2 P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)]) a 3 11 v (target.getD p 0)
    (by simp) (by simp) hv31 hw31 _ hpw hpwv
  have hacc_eq : i2acc a v p acc = if parent.getD (target.getD p 0) 0 = (v : Int) then mx acc (a.dp.getD (target.getD p 0) 0) else acc := by
    unfold i2acc; rw [tg_get head target parent ord n a R p hpt, R.pa]; simp
  have hpre_eq : i2suf a v p acc = if parent.getD (target.getD p 0) 0 = (v : Int) then a.suf.set p acc else a.suf := by
    unfold i2suf; rw [tg_get head target parent ord n a R p hpt, R.pa]; simp
  -- the decrement, from a state of the form `CB2 .. ++ [ci p]`
  have hinc : ∀ (acc' : Int) (vv : Nat → List Int), s64.valid acc' = true →
      ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (decI mv.nv 10)) Sk) (gS P (CB2 root n k v tot acc' ++ [ci p])) vv = some r2 ∧
        r2.ret = none ∧ r2.ps = gS P (CB2 root n k v tot acc' ++ [cpI ((p : Int) - 1)]) ∧ r2.vv = vv ∧ r2.cost ≤ 100 ∧
        r2.need ≤ P.length + 100 ∧ r2.wk = 0 := by
    intro acc' vv _
    have e2 := sub1_val mv vv _ (mv.nv + 10) p (envs mv P (CB2 root n k v tot acc' ++ [ci p]) 10 (ci p) (by simp) (i32vn p (by omega))) (by omega)
    have s2 := gSM_assign mv P (CB2 root n k v tot acc' ++ [ci p]) vv 10 (by simp) i32 _ _ _ e2 (ci p) (by simp) rfl
      (i32vn p (by omega)) (conv_signed i32 rfl rfl _ (Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)))
    have eB : (CB2 root n k v tot acc' ++ [ci p]).set 10 ⟨i32, (p : Int) - 1⟩ = CB2 root n k v tot acc' ++ [cpI ((p : Int) - 1)] := rfl
    rw [eB] at s2
    have a2 := (pexecM_prim mv fu (decI mv.nv 10) _ _).trans s2
    have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  by_cases hch : parent.getD (target.getD p 0) 0 = (v : Int)
  · rw [if_pos hch] at hc
    have hmxv : s64.valid (mx acc (a.dp.getD (target.getD p 0) 0)) = true := by
      unfold mx; split
      · exact hdpv _
      · exact hacc
    -- the write `pre[p] = acc`
    have hx5 : vdenM mv (VA a) (penvN mv.nv (gS P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)]))) (vS mv.nv 9) = some acc :=
      cellS mv _ P _ 9 acc (by simp) hacc
    have hi6 : vdenM mv (VA a) (penvN mv.nv (gS P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)])))
        (.cast u64 (.variable i32 (mv.nv + 10))) = some (p : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact cidx_den _ _ p (envs mv P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)]) 10 (ci p) (by simp) (i32vn p (by omega))) (show p < 2147483648 by omega)
    have hlt5 : p < ((VA a) 6).length := by rw [VA_get6, Ln.suf]; exact hpt
    have hv5 : (mv.ty 6).valid acc = true := by rw [ty6]; exact hacc
    have hw5 := pstmtM_write_ok mv (gS P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)])) (VA a) 6 (by omega)
      (.cast u64 (.variable i32 (mv.nv + 10))) (vS mv.nv 9) acc p hx5 hi6 hlt5 hv5
    rw [ty6, VA_get6, VA_set6] at hw5
    have aw := (pexecM_prim mv fu (wrS 6 (vI mv.nv 10) (vS mv.nv 9)) _ _).trans hw5
    -- the `apply` block
    have hX : vdenM mv (VA { a with suf := a.suf.set p acc }) (penvN mv.nv (gS P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)])))
        (vS mv.nv 9) = some acc := cellS mv _ P _ 9 acc (by simp) hacc
    have hY : vdenM mv (VA { a with suf := a.suf.set p acc })
        (penvN mv.nv (gS P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)] ++ [cs acc])))
        (rdS 4 (vI mv.nv 11)) = some (a.dp.getD (target.getD p 0) 0) :=
      rdv mv _ P _ 4 11 (target.getD p 0) s64 (by omega) ty4.symm (by simp) hw31 _
        (by rw [VA_get4]; exact vec_getI a.dp _ (by rw [Ln.dp]; exact hw)) (by rw [ty4]; exact hdpv _)
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ : ∃ r2 : PRM,
        pexecM mv fu (.sequence (.primitive (.assign (mv.nv + 9) s64 (vS mv.nv 15))) Sk)
          (gS P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)] ++ [cs acc, cs (a.dp.getD (target.getD p 0) 0),
            cs (mx acc (a.dp.getD (target.getD p 0) 0)), cs (mx acc (a.dp.getD (target.getD p 0) 0))]))
          (VA { a with suf := a.suf.set p acc }) = some r2 ∧ r2.ret = none ∧
        r2.ps = gS P (CB2 root n k v tot (mx acc (a.dp.getD (target.getD p 0) 0)) ++ [ci p] ++ [ci (target.getD p 0)] ++
          [cs acc, cs (a.dp.getD (target.getD p 0) 0), cs (mx acc (a.dp.getD (target.getD p 0) 0)),
            cs (mx acc (a.dp.getD (target.getD p 0) 0))]) ∧
        r2.vv = VA { a with suf := a.suf.set p acc } ∧ r2.cost ≤ 100 ∧ r2.need ≤ P.length + 80 ∧ r2.wk = 0 := by
      have s5 := gSM_assign mv P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)] ++ [cs acc, cs (a.dp.getD (target.getD p 0) 0),
            cs (mx acc (a.dp.getD (target.getD p 0) 0)), cs (mx acc (a.dp.getD (target.getD p 0) 0))])
        (VA { a with suf := a.suf.set p acc }) 9 (by simp) s64 (vS mv.nv 15) (mx acc (a.dp.getD (target.getD p 0) 0))
        (mx acc (a.dp.getD (target.getD p 0) 0)) (cellS mv _ P _ 15 _ (by simp) hmxv) (cs acc) (by simp) rfl hacc
        (conv_signed s64 rfl rfl _ hmxv)
      have eA : (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)] ++ [cs acc, cs (a.dp.getD (target.getD p 0) 0),
            cs (mx acc (a.dp.getD (target.getD p 0) 0)), cs (mx acc (a.dp.getD (target.getD p 0) 0))]).set 9
            ⟨s64, mx acc (a.dp.getD (target.getD p 0) 0)⟩ =
          CB2 root n k v tot (mx acc (a.dp.getD (target.getD p 0) 0)) ++ [ci p] ++ [ci (target.getD p 0)] ++
          [cs acc, cs (a.dp.getD (target.getD p 0) 0), cs (mx acc (a.dp.getD (target.getD p 0) 0)),
            cs (mx acc (a.dp.getD (target.getD p 0) 0))] := rfl
      rw [eA] at s5
      have a5 := (pexecM_prim mv fu (.assign (mv.nv + 9) s64 (vS mv.nv 15)) _ _).trans s5
      have b5 := seqM_some a5 rfl (pexecM_skip mv fu _ _)
      refine ⟨_, b5, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
    obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P (VA { a with suf := a.suf.set p acc }) fu
      (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)]) 12 (by simp) (vS mv.nv 9) (rdS 4 (vI mv.nv 11)) acc
      (a.dp.getD (target.getD p 0) 0) hacc (hdpv _) hX hY _ r2 hr2
    have sW := seqM_some aw rfl hA
    have sc := pexecM_scope mv fu _ _ _ _ sW
    rw [psA, ps2] at sc
    have tk := gS_takeC P (CB2 root n k v tot acc ++ [ci p] ++ [ci (target.getD p 0)])
      (CB2 root n k v tot (mx acc (a.dp.getD (target.getD p 0) 0)) ++ [ci p] ++ [ci (target.getD p 0)])
      [cs acc, cs (a.dp.getD (target.getD p 0) 0), cs (mx acc (a.dp.getD (target.getD p 0) 0)),
        cs (mx acc (a.dp.getD (target.getD p 0) 0))] rfl
    simp only [tk] at sc
    have b1 := seqM_some sc (by rw [retA, ret2]) (pexecM_skip mv fu _ _)
    have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b1
    have b4 := seqM_some b3 (by simp) (pexecM_skip mv fu _ _)
    have s1 := seqM_some a1 rfl b4
    have b5 := pexecM_scope mv fu _ _ _ _ s1
    have tk2 := gS_takeC P (CB2 root n k v tot acc ++ [ci p])
      (CB2 root n k v tot (mx acc (a.dp.getD (target.getD p 0) 0)) ++ [ci p]) [ci (target.getD p 0)] rfl
    simp only [tk2] at b5
    obtain ⟨r3, hr3, ret3, ps3, vv3, c3, n3, w3⟩ := hinc (mx acc (a.dp.getD (target.getD p 0) 0))
      (VA { a with suf := a.suf.set p acc }) hmxv
    have b6 := seqM_some b5 (by simp) (by rw [vvA, vv2]; exact hr3)
    refine ⟨_, b6, ret3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hacc_eq, if_pos hch]; exact ps3
    · rw [hpre_eq, if_pos hch]; exact vv3
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA c2 c3 ⊢; omega
    · have hA' := nA (P.length + 100) (by omega) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' n2 n3 ⊢
      omega
    · simp at wA w2 w3 ⊢; omega
  · rw [if_neg hch] at hc
    have b3 := pexecM_branch_false mv fu _ (.sequence (.scope (I2act mv.nv)) Sk) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    have s1 := seqM_some a1 rfl b4
    have b5 := pexecM_scope mv fu _ _ _ _ s1
    have tk := gS_takeC P (CB2 root n k v tot acc ++ [ci p]) (CB2 root n k v tot acc ++ [ci p]) [ci (target.getD p 0)] rfl
    simp only [tk] at b5
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ := hinc acc (VA a) hacc
    have b6 := seqM_some b5 (by simp) hr2
    refine ⟨_, b6, ret2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hacc_eq, if_neg hch]; exact ps2
    · rw [hpre_eq, if_neg hch]; exact vv2
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n2 ⊢; omega
    · simp at w2 ⊢; omega


/-! ### The backward arc loop (`suf`): math -/

theorem filter_le_cons (l : List Nat) (hl : l.Pairwise (· < ·)) (p : Nat) (hp : p ∈ l) :
    l.filter (fun q => decide (p ≤ q)) = p :: l.filter (fun q => decide (p + 1 ≤ q)) := by
  have h := pairwise_split l hl p hp
  have hA1 : (l.filter (fun q => decide (q < p))).filter (fun q => decide (p ≤ q)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro q hq
    have := (List.mem_filter.mp hq).2
    simp at this ⊢; omega
  have hB1 : (l.filter (fun q => decide (p < q))).filter (fun q => decide (p ≤ q)) = l.filter (fun q => decide (p < q)) := by
    rw [List.filter_eq_self]
    intro q hq
    have := (List.mem_filter.mp hq).2
    simp at this ⊢; omega
  have hA2 : (l.filter (fun q => decide (q < p))).filter (fun q => decide (p + 1 ≤ q)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro q hq
    have := (List.mem_filter.mp hq).2
    simp at this ⊢; omega
  have hB2 : (l.filter (fun q => decide (p < q))).filter (fun q => decide (p + 1 ≤ q)) = l.filter (fun q => decide (p < q)) := by
    rw [List.filter_eq_self]
    intro q hq
    have := (List.mem_filter.mp hq).2
    simp at this ⊢; omega
  conv_lhs => rw [h]
  conv_rhs => rw [h]
  rw [List.filter_append, List.filter_append, hA1, hA2, List.filter_cons_of_pos (by simp), List.filter_cons_of_neg (by simp)]
  rw [hB1, hB2]
  rfl

structure AI2 (head target : List Nat) (parent : List Int) (v t : Nat) (dp suf0 suf' : List Int) (back : Int) : Prop where
  backE : back = fold M0 ((((kidArcs head target parent v).filter fun q => decide (t ≤ q)).map (tgt target)).map
    fun x => dp.getD x 0)
  done : ∀ q ∈ kidArcs head target parent v, t ≤ q →
    suf'.getD q 0 = fold M0 ((ka head target parent v q).map fun x => dp.getD x 0)
  rest : ∀ q, ¬ (q ∈ kidArcs head target parent v ∧ t ≤ q) → suf'.getD q 0 = suf0.getD q 0
  len : suf'.length = suf0.length

theorem ai2_init (head target : List Nat) (parent : List Int) (v : Nat) (dp suf0 : List Int) :
    AI2 head target parent v (head.getD (v + 1) 0) dp suf0 suf0 0 := by
  refine ⟨?_, fun q hq hlt => ?_, fun q _ => rfl, rfl⟩
  · have : (kidArcs head target parent v).filter (fun q => decide (head.getD (v + 1) 0 ≤ q)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro q hq
      have := (kidArcs_ge head target parent v q hq).2
      rw [decide_eq_false (by omega)]
      simp
    rw [this]; rfl
  · exact absurd hlt (by have := (kidArcs_ge head target parent v q hq).2; omega)

theorem ai2_child (head target : List Nat) (parent : List Int) (v p : Nat) (dp suf0 suf' : List Int) (back : Int)
    (I : AI2 head target parent v (p + 1) dp suf0 suf' back) (hpk : p ∈ kidArcs head target parent v)
    (hdp : ∀ x, 0 ≤ dp.getD x 0) (hpl : p < suf'.length) :
    AI2 head target parent v p dp suf0 (suf'.set p back) (mx back (dp.getD (tgt target p) 0)) := by
  have hK := kidArcs_pairwise head target parent v
  have hf := filter_le_cons _ hK p hpk
  have hkaE : ∀ q, ka head target parent v q = (((kidArcs head target parent v).filter fun r => decide (q + 1 ≤ r)).map (tgt target)) := by
    intro q
    unfold ka
    rfl
  have hA : ∀ y ∈ (((kidArcs head target parent v).filter fun q => decide (p + 1 ≤ q)).map (tgt target)).map
      (fun x => dp.getD x 0), M0.V y := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact hdp x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf, List.map_cons, List.map_cons]
    rw [fold_cons M0 _ _ (hdp _) hA, ← I.backE]
    show mx back _ = M0.op _ back
    rw [M0.comm _ _ (hdp _) (by rw [I.backE]; exact fold_V M0 _ hA)]
    rfl
  · intro q hq hqp
    rw [Proofs.SegTreeMath.getD_setE]
    by_cases hqe : q = p
    · subst hqe
      rw [if_pos ⟨rfl, hpl⟩, I.backE, hkaE]
    · rw [if_neg (fun h => hqe h.1)]
      exact I.done q hq (by omega)
  · intro q hq
    rw [Proofs.SegTreeMath.getD_setE]
    have hqp : q ≠ p := fun h => hq ⟨h ▸ hpk, by omega⟩
    rw [if_neg (fun h => hqp h.1)]
    exact I.rest q (fun h => hq ⟨h.1, by omega⟩)
  · simp [I.len]

theorem ai2_other (head target : List Nat) (parent : List Int) (v p : Nat) (dp suf0 suf' : List Int) (back : Int)
    (I : AI2 head target parent v (p + 1) dp suf0 suf' back) (hpk : p ∉ kidArcs head target parent v) :
    AI2 head target parent v p dp suf0 suf' back := by
  have hne : ∀ q ∈ kidArcs head target parent v, p ≤ q ↔ p + 1 ≤ q := by
    intro q hq
    have : q ≠ p := fun h => hpk (h ▸ hq)
    omega
  refine ⟨?_, ?_, ?_, I.len⟩
  · have : (kidArcs head target parent v).filter (fun q => decide (p ≤ q)) =
        (kidArcs head target parent v).filter (fun q => decide (p + 1 ≤ q)) := by
      apply List.filter_congr
      intro q hq
      simp [hne q hq]
    rw [this]; exact I.backE
  · intro q hq hqp
    exact I.done q hq (by
      have : q ≠ p := fun h => hpk (h ▸ hq)
      omega)
  · intro q hq
    exact I.rest q (fun h => hq ⟨h.1, by omega⟩)

/-- A cell holding a possibly negative `int`. -/
theorem cellZ (mv : MV) (vv : Nat → List Int) (P : List Cell) (cl : List Cell) (c : Nat) (z : Int)
    (hc : cl[c]? = some (cpI z)) (hz : i32.valid z = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (vI mv.nv c) = some z := by
  rw [vdenM_scalar _ _ _ _ rfl, den_variable]
  exact envs mv P cl c (cpI z) hc hz

theorem cpI_succ (p : Nat) : cpI (((p + 1 : Nat) : Int) - 1) = ci p := by
  show (⟨i32, ((p + 1 : Nat) : Int) - 1⟩ : Cell) = ⟨i32, (p : Int)⟩
  congr 1; omega

/-- The condition `p >= head[v]` of the backward arc loop. -/
theorem cond2_val (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (P : List Cell) (cl : List Cell) (a : Arr)
    (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (R : Ro head target parent ord n a)
    (v : Nat) (z : Int) (hv : v < n) (h3 : cl[3]? = some (ci v)) (h10 : cl[10]? = some (cpI z))
    (hz : -2147483648 ≤ z ∧ z < 2147483648) :
    vdenM mv (VA a) (penvN mv.nv (gS P cl)) (I2cond mv.nv) = some (if (head.getD v 0 : Int) ≤ z then 1 else 0) := by
  have hh : i32.valid (head.getD v 0 : Int) = true := by
    have := head_le head target parent ord n a R v hv
    have := R.tlen
    have := R.hmono v hv
    exact i32vn _ (by omega)
  have r := rdv mv (VA a) P cl 0 3 v i32 (by omega) ty0.symm h3 (by have := R.nb; omega) (head.getD v 0 : Int)
    (by rw [VA_get0]; exact hd_getq head target parent ord n a R v (by omega)) (by rw [ty0]; exact hh)
  have c := cellZ mv (VA a) P cl 10 z h10 (Proofs.VectorSumCall.i32_valid _ hz.1 hz.2)
  unfold I2cond
  rw [vdenM_binary mv _ _ bT .ge _ _ rfl, c, Option.bind_some, r, Option.bind_some]
  generalize head.getD v 0 = H
  by_cases h : (H : Int) ≤ z
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
theorem i2_acc_eq (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (v p : Nat) (hv : v < n) (hp : p ∈ arcs head v) (acc : Int) :
    (i2acc a v p acc = if p ∈ kidArcs head target parent v then mx acc (a.dp.getD (tgt target p) 0) else acc) ∧
    (i2suf a v p acc = if p ∈ kidArcs head target parent v then a.suf.set p acc else a.suf) := by
  have hpt : p < target.length := arc_lt head target parent ord n a R v hv p hp
  have h := i1_child_iff head target parent ord n a R v p hv hp
  have e : (a.tg.getD p 0).toNat = tgt target p := by
    rw [tg_get head target parent ord n a R p hpt]; simp [tgt]
  unfold i2acc i2suf
  rw [e]
  rw [e] at h
  constructor <;> (by_cases hc : a.pa.getD (tgt target p) 0 = (v : Int)
                   · rw [if_pos hc, if_pos (h.mp hc)]
                   · rw [if_neg hc, if_neg (fun hk => hc (h.mpr hk))])


theorem Ro.updSuf {head target : List Nat} {parent : List Int} {ord : List Nat} {n : Nat} {a : Arr}
    (R : Ro head target parent ord n a) (x : List Int) : Ro head target parent ord n { a with suf := x } :=
  ⟨R.hd, R.tg, R.pa, R.od, R.hlen, R.hmono, R.hlast, R.tlen, R.tlt, R.nb, R.palen, R.pav, R.odlen, R.odlt⟩

set_option maxHeartbeats 128000000 in
/-- The backward arc loop `for (p = head[v + 1] - 1; p >= head[v]; p--) ...`, from the state with `t = p + 1`. -/
theorem i2_loop (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty4 : mv.ty 4 = s64) (ty6 : mv.ty 6 = s64) (P : List Cell) (head target : List Nat) (parent : List Int) (ord : List Nat)
    (n : Nat) (a0 : Arr) (R : Ro head target parent ord n a0) (Ln : Lens n target.length a0) (root k v : Nat) (tot : Int)
    (hv : v < n) (hrk : root < 2147483648) (hk31 : k < 2147483648) (htot : s64.valid tot = true)
    (htot1 : s64.valid (tot + 1) = true) (hdpv : ∀ x, s64.valid (a0.dp.getD x 0) = true)
    (hdpnn : ∀ x, 0 ≤ a0.dp.getD x 0) :
    ∀ (d t : Nat) (suf' : List Int) (back : Int) (fu : Nat), t - head.getD v 0 = d → head.getD v 0 ≤ t →
      t ≤ head.getD (v + 1) 0 → AI2 head target parent v t a0.dp a0.suf suf' back → s64.valid back = true → d + 1 ≤ fu →
      ∃ (res : PRM) (suf'' : List Int) (back'' : Int),
        pexecM mv fu (.whileLoop (I2cond mv.nv) (I2body mv.nv))
          (gS P (CB2 root n k v tot back ++ [cpI ((t : Int) - 1)])) (VA { a0 with suf := suf' }) = some res ∧
        res.ret = none ∧ res.ps = gS P (CB2 root n k v tot back'' ++ [cpI ((head.getD v 0 : Int) - 1)]) ∧
        res.vv = VA { a0 with suf := suf'' } ∧
        AI2 head target parent v (head.getD v 0) a0.dp a0.suf suf'' back'' ∧ s64.valid back'' = true ∧
        res.cost ≤ 1100 * d + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ d := by
  have hend := head_le head target parent ord n a0 R v hv
  have htl := R.tlen
  have hmono := R.hmono v hv
  intro d
  induction d with
  | zero =>
    intro t suf' back fu hd ht0 hte I hback hfu
    have hteq : t = head.getD v 0 := by omega
    subst hteq
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond2_val mv hnv ty0 P (CB2 root n k v tot back ++ [cpI ((head.getD v 0 : Int) - 1)]) { a0 with suf := suf' } head target
      parent ord n (R.updSuf suf') v ((head.getD v 0 : Int) - 1) hv (by simp) (by simp) ⟨by omega, by omega⟩
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, suf', back, rfl, rfl, rfl, rfl, I, hback, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro t suf' back fu hd ht0 hte I hback hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, t = p + 1 := ⟨t - 1, by omega⟩
    have hpin : p ∈ arcs head v := by
      unfold arcs; rw [List.mem_range'_1]; omega
    rw [cpI_succ]
    have hc := cond2_val mv hnv ty0 P (CB2 root n k v tot back ++ [ci p]) { a0 with suf := suf' } head target parent ord n
      (R.updSuf suf') v (p : Int) hv (by simp) (by simp) ⟨by omega, by omega⟩
    rw [if_pos (by omega)] at hc
    have Ln' : Lens n target.length { a0 with suf := suf' } := ⟨Ln.dp, Ln.pre, by rw [I.len]; exact Ln.suf, Ln.up, Ln.fu⟩
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := i2_iter mv hnv ty1 ty2 ty4 ty6 P (fu' + 1) head target parent ord n
      { a0 with suf := suf' } (R.updSuf suf') Ln' root k v p tot back hv hpin hrk hk31 htot htot1 hback hdpv
    have hq := i2_acc_eq head target parent ord n { a0 with suf := suf' } (R.updSuf suf') v p hv hpin back
    have hq' : i2acc { a0 with suf := suf' } v p back = (if p ∈ kidArcs head target parent v then mx back (a0.dp.getD (tgt target p) 0) else back) := hq.1
    have hp' : i2suf { a0 with suf := suf' } v p back = (if p ∈ kidArcs head target parent v then suf'.set p back else suf') := hq.2
    have hI' : AI2 head target parent v p a0.dp a0.suf (i2suf { a0 with suf := suf' } v p back)
        (i2acc { a0 with suf := suf' } v p back) := by
      rw [hq', hp']
      by_cases hk : p ∈ kidArcs head target parent v
      · rw [if_pos hk, if_pos hk]
        exact ai2_child head target parent v p a0.dp a0.suf suf' back I hk hdpnn
          (by rw [I.len, Ln.suf]; exact arc_lt head target parent ord n a0 R v hv p hpin)
      · rw [if_neg hk, if_neg hk]
        exact ai2_other head target parent v p a0.dp a0.suf suf' back I hk
    have hback' : s64.valid (i2acc { a0 with suf := suf' } v p back) = true := by
      rw [hq']
      by_cases hk : p ∈ kidArcs head target parent v
      · rw [if_pos hk]; unfold mx; split
        · exact hdpv _
        · exact hback
      · rw [if_neg hk]; exact hback
    obtain ⟨r2, suf'', back'', h2, ret2, ps2, vv2, hI2, hback2, c2, n2, w2⟩ :=
      ih p (i2suf { a0 with suf := suf' } v p back) (i2acc { a0 with suf := suf' } v p back) fu' (by omega) (by omega) (by omega)
        hI' hback' (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
    rw [h1]
    simp only [ret1, ps1, vv1]
    rw [h2]
    simp only
    refine ⟨_, suf'', back'', rfl, ret2, ps2, vv2, hI2, hback2, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

theorem zeroS_val (mv : MV) (vv : Nat → List Int) (ps : PS) :
    vdenM mv vv (penvN mv.nv ps) zeroS = some 0 := by
  rw [vdenM_scalar _ _ _ _ rfl, den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
  exact conv_signed s64 rfl rfl _ (show s64.valid 0 = true from rfl)

theorem succ_val (mv : MV) (vv : Nat → List Int) (P : List Cell) (cl : List Cell) (c : Nat) (x : Int)
    (hc : cl[c]? = some (cs x)) (hx : s64.valid x = true) (hx1 : s64.valid (x + 1) = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (succS mv.nv c) = some (x + 1) := by
  have e := vr mv P cl c x hc hx
  rw [vdenM_scalar _ _ _ _ rfl]
  unfold succS
  rw [den_binary]
  rw [show (vS mv.nv c).denote (penvN mv.nv (gS P cl)) = some x from e, Option.bind_some, den_cast, den_literal,
    if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have h1 : s64.convert (1 : Int) = some 1 := conv_signed s64 rfl rfl _ (show s64.valid 1 = true from rfl)
  rw [h1, Option.bind_some]
  have : binaryValue .add x 1 = x + 1 := rfl
  rw [this]
  exact conv_signed s64 rfl rfl _ hx1

/-- The start value `head[v + 1] - 1` of the backward arc loop. -/
theorem start2_val (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (P : List Cell) (cl : List Cell) (a : Arr)
    (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (R : Ro head target parent ord n a)
    (v : Nat) (hv : v < n) (h3 : cl[3]? = some (ci v)) :
    vdenM mv (VA a) (penvN mv.nv (gS P cl))
      (.binary i32 .sub (rdI 0 (.binary i32 .add (vI mv.nv 3) Proofs.TreeFullDpBody.lit1)) Proofs.TreeFullDpBody.lit1) =
        some ((head.getD (v + 1) 0 : Int) - 1) := by
  have hh : i32.valid (head.getD (v + 1) 0 : Int) = true := by
    have := head_le head target parent ord n a R v hv
    have := R.tlen
    exact i32vn _ (by omega)
  have r := rdv1 mv (VA a) P cl 0 3 v i32 (by omega) ty0.symm h3 (by have := R.nb; omega) (head.getD (v + 1) 0 : Int)
    (by rw [VA_get0]; exact hd_getq head target parent ord n a R (v + 1) (by omega)) (by rw [ty0]; exact hh)
  have l : vdenM mv (VA a) (penvN mv.nv (gS P cl)) Proofs.TreeFullDpBody.lit1 = some 1 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 1 = true from rfl)]
  rw [vdenM_binary mv _ _ i32 .sub _ _ rfl, r, Option.bind_some, l, Option.bind_some]
  have : binaryValue .sub (head.getD (v + 1) 0 : Int) 1 = (head.getD (v + 1) 0 : Int) - 1 := rfl
  rw [this]
  have := head_le head target parent ord n a R v hv
  have := R.tlen
  exact conv_signed i32 rfl rfl _ (Proofs.VectorSumCall.i32_valid _ (by omega) (by omega))

theorem s64vn (x : Int) (h0 : 0 ≤ x) (h1 : x < 2147483648) : s64.valid x = true := by
  simp [Ty.valid, s64]; omega

theorem od_getq (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (k : Nat) (hk : k < n) :
    a.od[k]? = some (ord.getD k 0 : Int) := by
  have hl : k < a.od.length := by rw [R.od]; simp [R.odlen]; exact hk
  rw [vec_getI a.od k hl, R.od]; simp [List.getD_eq_getElem?_getD, show k < ord.length by rw [R.odlen]; exact hk]

theorem foldl_le (xs : List Int) (B : Int) (hB : 0 ≤ B) (hx : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ B) :
    ∀ acc : Int, 0 ≤ acc → acc ≤ B → 0 ≤ xs.foldl mx acc ∧ xs.foldl mx acc ≤ B := by
  induction xs with
  | nil => intro acc h0 h1; exact ⟨h0, h1⟩
  | cons y xs ih =>
    intro acc h0 h1
    simp only [List.foldl_cons]
    have hy := hx y (List.mem_cons_self ..)
    apply ih (fun z hz => hx z (List.mem_cons_of_mem _ hz))
    · unfold mx; split <;> omega
    · unfold mx; split <;> omega

theorem fold_le (xs : List Int) (B : Int) (hB : 0 ≤ B) (hx : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ B) :
    0 ≤ fold M0 xs ∧ fold M0 xs ≤ B := foldl_le xs B hB hx 0 (le_refl _) hB

set_option maxHeartbeats 512000000 in
/-- The body of the bottom-up loop for the vertex `v = ord[k']`. -/
theorem bu_iter (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (ty4 : mv.ty 4 = s64) (ty6 : mv.ty 6 = s64) (ty5 : mv.ty 5 = s64) (ty8 : mv.ty 8 = s64)
    (P : List Cell) (fu : Nat) (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (Ln : Lens n target.length a) (root k' v : Nat) (hk : k' < n)
    (hvk : v = ord.getD k' 0) (hrk : root < 2147483648) (hdp : ∀ x, 0 ≤ a.dp.getD x 0 ∧ a.dp.getD x 0 ≤ n)
    (hdpc : ∀ q ∈ kidArcs head target parent v, a.dp.getD (tgt target q) 0 ≤ (n : Int) - 1)
    (hnself : ∀ q ∈ kidArcs head target parent v, tgt target q ≠ v)
    (hfu : head.getD (v + 1) 0 - head.getD v 0 + 1 ≤ fu) :
    ∃ (r : PRM) (pre1 suf1 : List Int) (tot back2 : Int),
      pexecM mv fu (BUiter mv.nv) (gS P [ci root, ci n, ci k']) (VA a) = some r ∧ r.ret = none ∧
      r.ps = gS P (CB2 root n k' v tot back2) ∧
      r.vv = VA { a with pre := pre1, dp := a.dp.set v (tot + 1), fu := a.fu.set v tot, suf := suf1 } ∧
      AI1 head target parent v (head.getD (v + 1) 0) a.dp a.pre pre1 tot ∧
      AI2 head target parent v (head.getD v 0) (a.dp.set v (tot + 1)) a.suf suf1 back2 ∧
      0 ≤ tot ∧ tot ≤ n ∧ 0 ≤ back2 ∧ back2 ≤ n ∧
      r.cost ≤ 2300 * (head.getD (v + 1) 0 - head.getD v 0) + 700 ∧ r.need ≤ P.length + 200 ∧
      r.wk ≤ 2 * (head.getD (v + 1) 0 - head.getD v 0) + 2 := by
  have hn31 := R.nb
  have hvn : v < n := by
    rw [hvk]
    apply R.odlt
    have : ord.getD k' 0 = ord[k']'(by rw [R.odlen]; exact hk) := by
      simp [List.getD_eq_getElem?_getD, show k' < ord.length by rw [R.odlen]; exact hk]
    rw [this]; exact List.getElem_mem _
  have hv31 : v < 2147483648 := by omega
  have hk31 : k' < 2147483648 := by omega
  have hend := head_le head target parent ord n a R v hvn
  have hmono := R.hmono v hvn
  have htl := R.tlen
  have h0 : s64.valid (0 : Int) = true := rfl
  -- v = ord[k']
  have S0v : (([ci root, ci n, ci k']  : List Cell))[2]? = some (ci k') := by simp
  have hdv : vdenM mv (VA a) (penvN mv.nv (gS P [ci root, ci n, ci k'])) (rdI 3 (vI mv.nv 2)) = some (v : Int) :=
    rdv mv (VA a) P _ 3 2 k' i32 (by omega) ty3.symm S0v hk31 (v : Int)
      (by rw [VA_get3, hvk]; exact od_getq head target parent ord n a R k' hk) (by rw [ty3]; exact i32vn _ hv31)
  have d1 := gSM_decl mv P [ci root, ci n, ci k'] (VA a) i32 (rdI 3 (vI mv.nv 2)) (v : Int) (v : Int) hdv
    (conv_signed i32 rfl rfl _ (i32vn _ hv31))
  have a1 := (pexecM_prim mv fu (.declare i32 true (rdI 3 (vI mv.nv 2))) _ _).trans d1
  -- e() and acc
  have d2 := gSM_decl mv P ([ci root, ci n, ci k'] ++ [⟨i32, (v : Int)⟩]) (VA a) s64 zeroS 0 0 (zeroS_val mv _ _)
    (conv_signed s64 rfl rfl _ h0)
  have a2 := (pexecM_prim mv fu (.declare s64 true zeroS) _ _).trans d2
  have d3 := gSM_decl mv P ([ci root, ci n, ci k'] ++ [⟨i32, (v : Int)⟩] ++ [⟨s64, 0⟩]) (VA a) s64 (vS mv.nv 4) 0 0
    (cellS mv _ P _ 4 0 (by simp) h0) (conv_signed s64 rfl rfl _ h0)
  have a3 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 4)) _ _).trans d3
  have e3 : [ci root, ci n, ci k'] ++ [(⟨i32, (v : Int)⟩ : Cell)] ++ [(⟨s64, 0⟩ : Cell)] ++ [(⟨s64, 0⟩ : Cell)] = CB root n k' v 0 := rfl
  rw [e3] at a3
  -- the forward arc loop
  have hh : (CB root n k' v 0)[3]? = some (ci v) := by simp
  have hhd : i32.valid (head.getD v 0 : Int) = true := i32vn _ (by omega)
  have hdp1 : vdenM mv (VA a) (penvN mv.nv (gS P (CB root n k' v 0))) (rdI 0 (vI mv.nv 3)) = some (head.getD v 0 : Int) :=
    rdv mv (VA a) P _ 0 3 v i32 (by omega) ty0.symm hh hv31 _
      (by rw [VA_get0]; exact hd_getq head target parent ord n a R v (by omega)) (by rw [ty0]; exact hhd)
  have d4 := gSM_decl mv P (CB root n k' v 0) (VA a) i32 (rdI 0 (vI mv.nv 3)) (head.getD v 0 : Int) (head.getD v 0 : Int) hdp1
    (conv_signed i32 rfl rfl _ hhd)
  have a4 := (pexecM_prim mv fu (.declare i32 true (rdI 0 (vI mv.nv 3))) _ _).trans d4
  have hdpv : ∀ x, s64.valid (a.dp.getD x 0) = true := fun x => s64vn _ (hdp x).1 (by have := (hdp x).2; omega)
  have hdpnn : ∀ x, 0 ≤ a.dp.getD x 0 := fun x => (hdp x).1
  obtain ⟨rL, pre1, tot, hL, retL, psL, vvL, hI1, hvt, cL, nL, wL⟩ := i1_loop mv hnv ty0 ty1 ty2 ty4 ty5 P head target parent ord n a R Ln
    root k' v hvn hrk hk31 hdpv hdpnn (head.getD (v + 1) 0 - head.getD v 0) (head.getD v 0) a.pre 0 fu rfl (le_refl _) hmono
    (ai1_init head target parent v a.dp a.pre) h0 hfu
  have hL' : pexecM mv fu (.whileLoop (I1cond mv.nv) (I1body mv.nv)) (gS P (CB root n k' v 0 ++ [ci (head.getD v 0)])) (VA a) = some rL := hL
  have sL := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have s4 := seqM_some a4 rfl sL
  have sc4 := pexecM_scope mv fu _ _ _ _ s4
  have tk4 := gS_takeC P (CB root n k' v 0) (CB root n k' v tot) [ci (head.getD (v + 1) 0)] rfl
  rw [psL] at sc4
  simp only [tk4] at sc4
  -- bounds of the total
  have hdpn : ∀ y ∈ (((kidArcs head target parent v).filter fun q => decide (q < head.getD (v + 1) 0)).map (tgt target)).map
      (fun x => a.dp.getD x 0), 0 ≤ y ∧ y ≤ (n : Int) - 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact ⟨(hdp _).1, hdpc q (List.mem_filter.mp hq).1⟩
  have htotb := fold_le _ ((n : Int) - 1) (by omega) hdpn
  rw [← hI1.accE] at htotb
  have htot0 : 0 ≤ tot := htotb.1
  have htotn : tot ≤ (n : Int) - 1 := htotb.2
  have hvtot1 : s64.valid (tot + 1) = true := s64vn _ (by omega) (by omega)
  -- the write `full[v] = tot`
  have hx5 : vdenM mv (VA { a with pre := pre1 }) (penvN mv.nv (gS P (CB root n k' v tot))) (vS mv.nv 5) = some tot :=
    cellS mv _ P _ 5 tot (by simp) hvt
  have hi3 : vdenM mv (VA { a with pre := pre1 }) (penvN mv.nv (gS P (CB root n k' v tot))) (.cast u64 (.variable i32 (mv.nv + 3))) =
      some (v : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ _ v (envs mv P (CB root n k' v tot) 3 (ci v) (by simp) (i32vn v hv31)) (show v < 2147483648 by omega)
  have hlt8 : v < ((VA { a with pre := pre1 }) 8).length := by rw [VA_get8]; show v < a.fu.length; rw [Ln.fu]; exact hvn
  have hv8 : (mv.ty 8).valid tot = true := by rw [ty8]; exact hvt
  have hw8 := pstmtM_write_ok mv (gS P (CB root n k' v tot)) (VA { a with pre := pre1 }) 8 (by omega)
    (.cast u64 (.variable i32 (mv.nv + 3))) (vS mv.nv 5) tot v hx5 hi3 hlt8 hv8
  rw [ty8, VA_get8, VA_set8] at hw8
  have aw8 := (pexecM_prim mv fu (wrS 8 (vI mv.nv 3) (vS mv.nv 5)) _ _).trans hw8
  -- x = acc; x + 1
  have d5 := gSM_decl mv P (CB root n k' v tot) (VA { a with pre := pre1, fu := a.fu.set v tot }) s64 (vS mv.nv 5) tot tot
    (cellS mv _ P _ 5 tot (by simp) hvt) (conv_signed s64 rfl rfl _ hvt)
  have a5 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 5)) _ _).trans d5
  have d6 := gSM_decl mv P (CB root n k' v tot ++ [⟨s64, tot⟩]) (VA { a with pre := pre1, fu := a.fu.set v tot }) s64 (succS mv.nv 6)
    (tot + 1) (tot + 1) (succ_val mv _ P _ 6 tot (by simp) hvt hvtot1) (conv_signed s64 rfl rfl _ hvtot1)
  have a6 := (pexecM_prim mv fu (.declare s64 true (succS mv.nv 6)) _ _).trans d6
  -- the write `dp[v] = tot + 1`
  have hx7 : vdenM mv (VA { a with pre := pre1, fu := a.fu.set v tot }) (penvN mv.nv (gS P (CB root n k' v tot ++ [⟨s64, tot⟩] ++ [⟨s64, tot + 1⟩])))
      (vS mv.nv 7) = some (tot + 1) := cellS mv _ P _ 7 (tot + 1) (by simp) hvtot1
  have hi3' : vdenM mv (VA { a with pre := pre1, fu := a.fu.set v tot })
      (penvN mv.nv (gS P (CB root n k' v tot ++ [⟨s64, tot⟩] ++ [⟨s64, tot + 1⟩]))) (.cast u64 (.variable i32 (mv.nv + 3))) = some (v : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ _ v (envs mv P (CB root n k' v tot ++ [⟨s64, tot⟩] ++ [⟨s64, tot + 1⟩]) 3 (ci v) (by simp) (i32vn v hv31)) (show v < 2147483648 by omega)
  have hlt4 : v < ((VA { a with pre := pre1, fu := a.fu.set v tot }) 4).length := by
    rw [VA_get4]; show v < a.dp.length; rw [Ln.dp]; exact hvn
  have hv4 : (mv.ty 4).valid (tot + 1) = true := by rw [ty4]; exact hvtot1
  have hw4 := pstmtM_write_ok mv (gS P (CB root n k' v tot ++ [⟨s64, tot⟩] ++ [⟨s64, tot + 1⟩]))
    (VA { a with pre := pre1, fu := a.fu.set v tot }) 4 (by omega) (.cast u64 (.variable i32 (mv.nv + 3))) (vS mv.nv 7) (tot + 1) v
    hx7 hi3' hlt4 hv4
  rw [ty4, VA_get4, VA_set4] at hw4
  have aw4 := (pexecM_prim mv fu (wrS 4 (vI mv.nv 3) (vS mv.nv 7)) _ _).trans hw4
  -- e() and back
  have d7 := gSM_decl mv P (CB root n k' v tot ++ [⟨s64, tot⟩] ++ [⟨s64, tot + 1⟩])
    (VA { a with pre := pre1, fu := a.fu.set v tot, dp := a.dp.set v (tot + 1) }) s64 zeroS 0 0 (zeroS_val mv _ _)
    (conv_signed s64 rfl rfl _ h0)
  have a7 := (pexecM_prim mv fu (.declare s64 true zeroS) _ _).trans d7
  have d8 := gSM_decl mv P (CB root n k' v tot ++ [⟨s64, tot⟩] ++ [⟨s64, tot + 1⟩] ++ [⟨s64, 0⟩])
    (VA { a with pre := pre1, fu := a.fu.set v tot, dp := a.dp.set v (tot + 1) }) s64 (vS mv.nv 8) 0 0
    (cellS mv _ P _ 8 0 (by simp) h0) (conv_signed s64 rfl rfl _ h0)
  have a8 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 8)) _ _).trans d8
  have e8 : CB root n k' v tot ++ [(⟨s64, tot⟩ : Cell)] ++ [(⟨s64, tot + 1⟩ : Cell)] ++ [(⟨s64, 0⟩ : Cell)] ++ [(⟨s64, 0⟩ : Cell)] =
      CB2 root n k' v tot 0 := rfl
  rw [e8] at a8
  -- the backward arc loop
  have R3 : Ro head target parent ord n { a with pre := pre1, fu := a.fu.set v tot, dp := a.dp.set v (tot + 1) } :=
    ⟨R.hd, R.tg, R.pa, R.od, R.hlen, R.hmono, R.hlast, R.tlen, R.tlt, R.nb, R.palen, R.pav, R.odlen, R.odlt⟩
  have Ln3 : Lens n target.length { a with pre := pre1, fu := a.fu.set v tot, dp := a.dp.set v (tot + 1) } :=
    ⟨by show (a.dp.set v (tot + 1)).length = n; simp [Ln.dp], by show pre1.length = target.length; rw [hI1.len, Ln.pre],
      Ln.suf, Ln.up, by show (a.fu.set v tot).length = n; simp [Ln.fu]⟩
  have hdp3 : ∀ x, 0 ≤ (a.dp.set v (tot + 1)).getD x 0 ∧ (a.dp.set v (tot + 1)).getD x 0 ≤ (n : Int) := by
    intro x
    rw [Proofs.SegTreeMath.getD_setE]
    by_cases hxv : x = v ∧ v < a.dp.length
    · rw [if_pos hxv]; exact ⟨by omega, by omega⟩
    · rw [if_neg hxv]; exact hdp x
  have hdpv3 : ∀ x, s64.valid ((a.dp.set v (tot + 1)).getD x 0) = true := fun x => s64vn _ (hdp3 x).1 (by have := (hdp3 x).2; omega)
  have hdpnn3 : ∀ x, 0 ≤ (a.dp.set v (tot + 1)).getD x 0 := fun x => (hdp3 x).1
  have hcell10 : vdenM mv (VA { a with pre := pre1, fu := a.fu.set v tot, dp := a.dp.set v (tot + 1) })
      (penvN mv.nv (gS P (CB2 root n k' v tot 0)))
      (.binary i32 .sub (rdI 0 (.binary i32 .add (vI mv.nv 3) Proofs.TreeFullDpBody.lit1)) Proofs.TreeFullDpBody.lit1) =
      some ((head.getD (v + 1) 0 : Int) - 1) :=
    start2_val mv hnv ty0 P (CB2 root n k' v tot 0) _ head target parent ord n R3 v hvn (by simp)
  have hnn1 : i32.valid ((head.getD (v + 1) 0 : Int) - 1) = true :=
    Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)
  have d9 := gSM_decl mv P (CB2 root n k' v tot 0) (VA { a with pre := pre1, fu := a.fu.set v tot, dp := a.dp.set v (tot + 1) }) i32
    (.binary i32 .sub (rdI 0 (.binary i32 .add (vI mv.nv 3) Proofs.TreeFullDpBody.lit1)) Proofs.TreeFullDpBody.lit1)
    ((head.getD (v + 1) 0 : Int) - 1) ((head.getD (v + 1) 0 : Int) - 1) hcell10 (conv_signed i32 rfl rfl _ hnn1)
  have a9 := (pexecM_prim mv fu (.declare i32 true (.binary i32 .sub (rdI 0 (.binary i32 .add (vI mv.nv 3) Proofs.TreeFullDpBody.lit1))
    Proofs.TreeFullDpBody.lit1)) _ _).trans d9
  have htotv : s64.valid tot = true := hvt
  obtain ⟨rM, suf1, back2, hM, retM, psM, vvM, hI2, hvb, cM, nM, wM⟩ := i2_loop mv hnv ty0 ty1 ty2 ty4 ty6 P head target parent ord n
    { a with pre := pre1, fu := a.fu.set v tot, dp := a.dp.set v (tot + 1) } R3 Ln3 root k' v tot hvn hrk hk31 htotv hvtot1 hdpv3 hdpnn3
    (head.getD (v + 1) 0 - head.getD v 0) (head.getD (v + 1) 0) a.suf 0 fu (by omega) hmono (le_refl _)
    (ai2_init head target parent v (a.dp.set v (tot + 1)) a.suf) h0 hfu
  have hM' : pexecM mv fu (.whileLoop (I2cond mv.nv) (I2body mv.nv))
      (gS P (CB2 root n k' v tot 0 ++ [cpI ((head.getD (v + 1) 0 : Int) - 1)]))
      (VA { a with pre := pre1, fu := a.fu.set v tot, dp := a.dp.set v (tot + 1) }) = some rM := hM
  have sM := seqM_some hM' retM (pexecM_skip mv fu rM.ps rM.vv)
  have s9 := seqM_some a9 rfl sM
  have sc9 := pexecM_scope mv fu _ _ _ _ s9
  have tk9 := gS_takeC P (CB2 root n k' v tot 0) (CB2 root n k' v tot back2) [cpI ((head.getD v 0 : Int) - 1)] rfl
  rw [psM] at sc9
  simp only [tk9] at sc9
  -- chain
  have e11 := seqM_some sc9 (by simp) (pexecM_skip mv fu _ _)
  have e10 := seqM_some a8 rfl e11
  have e9 := seqM_some a7 rfl e10
  have e8' := seqM_some aw4 rfl e9
  have e7 := seqM_some a6 rfl e8'
  have e6 := seqM_some a5 rfl e7
  have e5 := seqM_some aw8 rfl e6
  have e4 := seqM_some sc4 (by simp) (by rw [vvL]; exact e5)
  have e3 := seqM_some a3 rfl e4
  have e2 := seqM_some a2 rfl e3
  have e1 := seqM_some a1 rfl e2
  have hb2b : 0 ≤ back2 ∧ back2 ≤ (n : Int) - 1 := by
    have hh := hI2.backE
    have hel : ∀ y ∈ (((kidArcs head target parent v).filter fun q => decide (head.getD v 0 ≤ q)).map (tgt target)).map
        (fun x => (a.dp.set v (tot + 1)).getD x 0), 0 ≤ y ∧ y ≤ (n : Int) - 1 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      have hqk := (List.mem_filter.mp hq).1
      rw [Proofs.SegTreeMath.getD_setE, if_neg (fun h => hnself q hqk h.1)]
      exact ⟨(hdp _).1, hdpc q hqk⟩
    have := fold_le _ ((n : Int) - 1) (by omega) hel
    rw [← hh] at this
    exact this
  refine ⟨_, pre1, suf1, tot, back2, e1, rfl, ?_, ?_, hI1, ?_, htot0, by omega, hb2b.1, by omega, ?_, ?_, ?_⟩
  · rfl
  · rw [vvM]
  · exact hI2
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL cM ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nL nM ⊢; omega
  · simp at wL wM ⊢; omega


/-! ### The bottom-up loop: invariant -/

/-- After the positions `t, t + 1, ..., n - 1` of `ord` have been processed. -/
structure BUI (head target : List Nat) (parent : List Int) (ord : List Nat) (n t : Nat) (a : Arr) : Prop where
  glob : ∀ x, 0 ≤ a.dp.getD x 0 ∧ a.dp.getD x 0 ≤ n
  tot : ∀ j, t ≤ j → j < n → a.fu.getD (ord.getD j 0) 0 =
    fold M0 ((kidT head target parent (ord.getD j 0)).map fun x => a.dp.getD x 0)
  dpE : ∀ j, t ≤ j → j < n → a.dp.getD (ord.getD j 0) 0 = a.fu.getD (ord.getD j 0) 0 + 1
  dpB : ∀ j, t ≤ j → j < n → a.dp.getD (ord.getD j 0) 0 ≤ (n : Int) - j
  pre : ∀ j, t ≤ j → j < n → ∀ q ∈ kidArcs head target parent (ord.getD j 0),
    a.pre.getD q 0 = fold M0 ((kb head target parent (ord.getD j 0) q).map fun x => a.dp.getD x 0)
  suf : ∀ j, t ≤ j → j < n → ∀ q ∈ kidArcs head target parent (ord.getD j 0),
    a.suf.getD q 0 = fold M0 ((ka head target parent (ord.getD j 0) q).map fun x => a.dp.getD x 0)

theorem bui_init (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (h : ∀ x, 0 ≤ a.dp.getD x 0 ∧ a.dp.getD x 0 ≤ n) : BUI head target parent ord n n a :=
  ⟨h, fun j hj hjn => absurd hjn (by omega), fun j hj hjn => absurd hjn (by omega),
    fun j hj hjn => absurd hjn (by omega), fun j hj hjn => absurd hjn (by omega), fun j hj hjn => absurd hjn (by omega)⟩

theorem pos_ord {ord : List Nat} (hnd : ord.Nodup) (j : Nat) (hj : j < ord.length) : pos ord (ord.getD j 0) = j := by
  have : ord.getD j 0 = ord[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [this]
  unfold pos
  exact List.Nodup.idxOf_getElem hnd j hj

theorem ord_inj {ord : List Nat} (hnd : ord.Nodup) (i j : Nat) (hi : i < ord.length) (hj : j < ord.length)
    (h : ord.getD i 0 = ord.getD j 0) : i = j := by
  have h1 := pos_ord hnd i hi
  have h2 := pos_ord hnd j hj
  rw [h] at h1
  omega


theorem head_chain (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) : ∀ i j, i ≤ j → j ≤ n → head.getD i 0 ≤ head.getD j 0 := by
  intro i j hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ j hij ih =>
    exact le_trans (ih (by omega)) (R.hmono j (by omega))

theorem arcs_disj (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (v w : Nat) (hv : v < n) (hw : w < n) (hvw : v ≠ w) (q : Nat)
    (h1 : q ∈ arcs head v) (h2 : q ∈ arcs head w) : False := by
  unfold arcs at h1 h2
  rw [List.mem_range'_1] at h1 h2
  rcases Nat.lt_or_gt_of_ne hvw with h | h
  · have := head_chain head target parent ord n a R (v + 1) w (by omega) (by omega)
    omega
  · have := head_chain head target parent ord n a R (w + 1) v (by omega) (by omega)
    omega

theorem kidArcs_disj (head target : List Nat) (parent : List Int) (ord : List Nat) (n : Nat) (a : Arr)
    (R : Ro head target parent ord n a) (v w : Nat) (hv : v < n) (hw : w < n) (hvw : v ≠ w) (q : Nat)
    (h1 : q ∈ kidArcs head target parent v) : q ∉ kidArcs head target parent w := fun h2 =>
  arcs_disj head target parent ord n a R v w hv hw hvw q (List.mem_filter.mp h1).1 (List.mem_filter.mp h2).1

theorem ord_pos_get {ord : List Nat} (x : Nat) (hx : x ∈ ord) : ord.getD (pos ord x) 0 = x := by
  have hl : pos ord x < ord.length := List.idxOf_lt_length_of_mem hx
  have : ord.getD (pos ord x) 0 = ord[pos ord x] := by simp [List.getD_eq_getElem?_getD, hl]
  rw [this]
  exact List.getElem_idxOf hl


theorem dp_congr (dp : List Int) (v : Nat) (c : Int) (xs : List Nat) (hx : ∀ x ∈ xs, x ≠ v) :
    xs.map (fun x => (dp.set v c).getD x 0) = xs.map (fun x => dp.getD x 0) := by
  apply List.map_congr_left
  intro x hxm
  rw [Proofs.SegTreeMath.getD_setE, if_neg (fun h => hx x hxm h.1)]

theorem kb_sub (head target : List Nat) (parent : List Int) (v q x : Nat) (hx : x ∈ kb head target parent v q) :
    x ∈ kidT head target parent v := by
  unfold kb at hx; unfold kidT
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨r, (List.mem_filter.mp hr).1, rfl⟩

theorem ka_sub (head target : List Nat) (parent : List Int) (v q x : Nat) (hx : x ∈ ka head target parent v q) :
    x ∈ kidT head target parent v := by
  unfold ka at hx; unfold kidT
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨r, (List.mem_filter.mp hr).1, rfl⟩

set_option maxHeartbeats 512000000 in
/-- One step of the bottom-up loop keeps the invariant. -/
theorem bu_step (M : TS head target parent ord n root) (R : Ro head target parent ord n a) (Ln : Lens n target.length a)
    (k' v : Nat) (hk : k' < n) (hvk : v = ord.getD k' 0) (I : BUI head target parent ord n (k' + 1) a)
    (pre1 suf1 : List Int) (tot back2 : Int)
    (hI1 : AI1 head target parent v (head.getD (v + 1) 0) a.dp a.pre pre1 tot)
    (hI2 : AI2 head target parent v (head.getD v 0) (a.dp.set v (tot + 1)) a.suf suf1 back2) :
    0 ≤ tot ∧ tot ≤ (n : Int) - k' - 1 ∧
    BUI head target parent ord n k' { a with pre := pre1, dp := a.dp.set v (tot + 1), fu := a.fu.set v tot, suf := suf1 } := by
  have hvn : v < n := by
    rw [hvk]; apply M.ordlt
    have : ord.getD k' 0 = ord[k']'(by rw [M.ordlen]; exact hk) := by
      simp [List.getD_eq_getElem?_getD, show k' < ord.length by rw [M.ordlen]; exact hk]
    rw [this]; exact List.getElem_mem _
  have hposv : pos ord v = k' := by rw [hvk]; exact pos_ord M.ordnd k' (by rw [M.ordlen]; exact hk)
  -- the children of `v`
  have hkid : ∀ q ∈ kidArcs head target parent v, tgt target q < n ∧ tgt target q ≠ v ∧ k' < pos ord (tgt target q) ∧
      pos ord (tgt target q) < n := by
    intro q hq
    obtain ⟨_, hxn, _, _, _, hpos⟩ := M.kid_facts v hvn q hq
    have := M.pos_lt _ hxn
    exact ⟨hxn, by intro h; rw [h] at hpos; omega, by omega, this⟩
  have hchild : ∀ q ∈ kidArcs head target parent v, a.dp.getD (tgt target q) 0 ≤ (n : Int) - k' - 1 := by
    intro q hq
    obtain ⟨hxn, _, hj1, hj2⟩ := hkid q hq
    have hmem : tgt target q ∈ ord := M.ordmem _ hxn
    have := I.dpB (pos ord (tgt target q)) (by omega) hj2
    rw [ord_pos_get _ hmem] at this
    omega
  have hnonneg : ∀ x, 0 ≤ a.dp.getD x 0 := fun x => (I.glob x).1
  -- the total
  have hfilt : (kidArcs head target parent v).filter (fun q => decide (q < head.getD (v + 1) 0)) = kidArcs head target parent v := by
    rw [List.filter_eq_self]
    intro q hq
    simpa using (kidArcs_ge head target parent v q hq).2
  have htotE : tot = fold M0 ((kidT head target parent v).map fun x => a.dp.getD x 0) := by
    have := hI1.accE
    rw [hfilt] at this
    exact this
  have htotb : 0 ≤ tot ∧ tot ≤ (n : Int) - k' - 1 := by
    rw [htotE]
    apply fold_le _ _ (by have := hk; omega)
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact ⟨hnonneg _, hchild q hq⟩
  refine ⟨htotb.1, htotb.2, ?_⟩
  have hdl : v < a.dp.length := by rw [Ln.dp]; exact hvn
  have hfl : v < a.fu.length := by rw [Ln.fu]; exact hvn
  -- a vertex at a later position is not a child of an earlier one, and vice versa
  have hlater : ∀ j, k' < j → j < n → ∀ x ∈ kidT head target parent (ord.getD j 0), x ≠ v := by
    intro j hj hjn x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have hu : ord.getD j 0 < n := M.ordlt _ (by
      have : ord.getD j 0 = ord[j]'(by rw [M.ordlen]; exact hjn) := by
        simp [List.getD_eq_getElem?_getD, show j < ord.length by rw [M.ordlen]; exact hjn]
      rw [this]; exact List.getElem_mem _)
    obtain ⟨_, hxn, _, _, _, hpos⟩ := M.kid_facts _ hu q hq
    rw [pos_ord M.ordnd j (by rw [M.ordlen]; exact hjn)] at hpos
    intro h; rw [h] at hpos; omega
  have hself : ∀ x ∈ kidT head target parent v, x ≠ v := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact (hkid q hq).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show 0 ≤ (a.dp.set v (tot + 1)).getD x 0 ∧ (a.dp.set v (tot + 1)).getD x 0 ≤ (n : Int)
    rw [Proofs.SegTreeMath.getD_setE]
    by_cases hxv : x = v ∧ v < a.dp.length
    · rw [if_pos hxv]; omega
    · rw [if_neg hxv]; exact I.glob x
  · intro j hj hjn
    by_cases hjk : j = k'
    · subst hjk
      rw [← hvk]
      show (a.fu.set v tot).getD v 0 = fold M0 ((kidT head target parent v).map fun x => (a.dp.set v (tot + 1)).getD x 0)
      rw [Proofs.SegTreeMath.getD_setE, if_pos ⟨rfl, hfl⟩, dp_congr _ _ _ _ hself, ← htotE]
    · have hj' : k' + 1 ≤ j := by omega
      have hne : ord.getD j 0 ≠ v := by
        intro h; rw [hvk] at h
        exact hjk (ord_inj M.ordnd _ _ (by rw [M.ordlen]; exact hjn) (by rw [M.ordlen]; exact hk) h)
      show (a.fu.set v tot).getD (ord.getD j 0) 0 = fold M0 ((kidT head target parent (ord.getD j 0)).map fun x => (a.dp.set v (tot + 1)).getD x 0)
      rw [Proofs.SegTreeMath.getD_setE, if_neg (fun h => hne h.1), dp_congr _ _ _ _ (hlater j (by omega) hjn)]
      exact I.tot j hj' hjn
  · intro j hj hjn
    by_cases hjk : j = k'
    · subst hjk
      rw [← hvk]
      show (a.dp.set v (tot + 1)).getD v 0 = (a.fu.set v tot).getD v 0 + 1
      rw [Proofs.SegTreeMath.getD_setE, Proofs.SegTreeMath.getD_setE, if_pos ⟨rfl, hdl⟩, if_pos ⟨rfl, hfl⟩]
    · have hj' : k' + 1 ≤ j := by omega
      have hne : ord.getD j 0 ≠ v := by
        intro h; rw [hvk] at h
        exact hjk (ord_inj M.ordnd _ _ (by rw [M.ordlen]; exact hjn) (by rw [M.ordlen]; exact hk) h)
      show (a.dp.set v (tot + 1)).getD (ord.getD j 0) 0 = (a.fu.set v tot).getD (ord.getD j 0) 0 + 1
      rw [Proofs.SegTreeMath.getD_setE, Proofs.SegTreeMath.getD_setE, if_neg (fun h => hne h.1), if_neg (fun h => hne h.1)]
      exact I.dpE j hj' hjn
  · intro j hj hjn
    by_cases hjk : j = k'
    · subst hjk
      rw [← hvk]
      show (a.dp.set v (tot + 1)).getD v 0 ≤ (n : Int) - j
      rw [Proofs.SegTreeMath.getD_setE, if_pos ⟨rfl, hdl⟩]
      omega
    · have hj' : k' + 1 ≤ j := by omega
      have hne : ord.getD j 0 ≠ v := by
        intro h; rw [hvk] at h
        exact hjk (ord_inj M.ordnd _ _ (by rw [M.ordlen]; exact hjn) (by rw [M.ordlen]; exact hk) h)
      show (a.dp.set v (tot + 1)).getD (ord.getD j 0) 0 ≤ (n : Int) - j
      rw [Proofs.SegTreeMath.getD_setE, if_neg (fun h => hne h.1)]
      exact I.dpB j hj' hjn
  · intro j hj hjn q hq
    by_cases hjk : j = k'
    · subst hjk
      rw [← hvk] at hq ⊢
      show pre1.getD q 0 = fold M0 ((kb head target parent v q).map fun x => (a.dp.set v (tot + 1)).getD x 0)
      rw [dp_congr _ _ _ _ (fun x hx => hself x (kb_sub head target parent v q x hx))]
      exact hI1.done q hq (by simpa using (kidArcs_ge head target parent v q hq).2)
    · have hj' : k' + 1 ≤ j := by omega
      have hne : ord.getD j 0 ≠ v := by
        intro h; rw [hvk] at h
        exact hjk (ord_inj M.ordnd _ _ (by rw [M.ordlen]; exact hjn) (by rw [M.ordlen]; exact hk) h)
      have hun : ord.getD j 0 < n := M.ordlt _ (by
        have : ord.getD j 0 = ord[j]'(by rw [M.ordlen]; exact hjn) := by
          simp [List.getD_eq_getElem?_getD, show j < ord.length by rw [M.ordlen]; exact hjn]
        rw [this]; exact List.getElem_mem _)
      show pre1.getD q 0 = fold M0 ((kb head target parent (ord.getD j 0) q).map fun x => (a.dp.set v (tot + 1)).getD x 0)
      rw [dp_congr _ _ _ _ (fun x hx => hlater j (by omega) hjn x (kb_sub head target parent _ q x hx))]
      have hnot : ¬ (q ∈ kidArcs head target parent v ∧ q < head.getD (v + 1) 0) :=
        fun h => kidArcs_disj head target parent ord n a R _ _ hun hvn hne q hq h.1
      rw [hI1.rest q hnot]
      exact I.pre j hj' hjn q hq
  · intro j hj hjn q hq
    by_cases hjk : j = k'
    · subst hjk
      rw [← hvk] at hq ⊢
      show suf1.getD q 0 = fold M0 ((ka head target parent v q).map fun x => (a.dp.set v (tot + 1)).getD x 0)
      exact hI2.done q hq (by have := (kidArcs_ge head target parent v q hq).1; omega)
    · have hj' : k' + 1 ≤ j := by omega
      have hne : ord.getD j 0 ≠ v := by
        intro h; rw [hvk] at h
        exact hjk (ord_inj M.ordnd _ _ (by rw [M.ordlen]; exact hjn) (by rw [M.ordlen]; exact hk) h)
      have hun : ord.getD j 0 < n := M.ordlt _ (by
        have : ord.getD j 0 = ord[j]'(by rw [M.ordlen]; exact hjn) := by
          simp [List.getD_eq_getElem?_getD, show j < ord.length by rw [M.ordlen]; exact hjn]
        rw [this]; exact List.getElem_mem _)
      show suf1.getD q 0 = fold M0 ((ka head target parent (ord.getD j 0) q).map fun x => (a.dp.set v (tot + 1)).getD x 0)
      rw [dp_congr _ _ _ _ (fun x hx => hlater j (by omega) hjn x (ka_sub head target parent _ q x hx))]
      have hnot : ¬ (q ∈ kidArcs head target parent v ∧ head.getD v 0 ≤ q) :=
        fun h => kidArcs_disj head target parent ord n a R _ _ hun hvn hne q hq h.1
      rw [hI2.rest q hnot]
      exact I.suf j hj' hjn q hq


/-- What the next iteration of the bottom-up loop needs from the invariant. -/
theorem bu_pre (M : TS head target parent ord n root) (k' v : Nat) (hk : k' < n) (hvk : v = ord.getD k' 0)
    (I : BUI head target parent ord n (k' + 1) a) :
    (∀ q ∈ kidArcs head target parent v, a.dp.getD (tgt target q) 0 ≤ (n : Int) - 1) ∧
    (∀ q ∈ kidArcs head target parent v, tgt target q ≠ v) ∧ v < n := by
  have hvn : v < n := by
    rw [hvk]; apply M.ordlt
    have : ord.getD k' 0 = ord[k']'(by rw [M.ordlen]; exact hk) := by
      simp [List.getD_eq_getElem?_getD, show k' < ord.length by rw [M.ordlen]; exact hk]
    rw [this]; exact List.getElem_mem _
  have hposv : pos ord v = k' := by rw [hvk]; exact pos_ord M.ordnd k' (by rw [M.ordlen]; exact hk)
  have hkid : ∀ q ∈ kidArcs head target parent v, tgt target q < n ∧ tgt target q ≠ v ∧ k' < pos ord (tgt target q) ∧
      pos ord (tgt target q) < n := by
    intro q hq
    obtain ⟨_, hxn, _, _, _, hpos⟩ := M.kid_facts v hvn q hq
    have := M.pos_lt _ hxn
    exact ⟨hxn, by intro h; rw [h] at hpos; omega, by omega, this⟩
  refine ⟨?_, fun q hq => (hkid q hq).2.1, hvn⟩
  intro q hq
  obtain ⟨hxn, _, hj1, hj2⟩ := hkid q hq
  have hmem : tgt target q ∈ ord := M.ordmem _ hxn
  have := I.dpB (pos ord (tgt target q)) (by omega) hj2
  rw [ord_pos_get _ hmem] at this
  omega

theorem nodup_map_of_inj (f : Nat → Nat) (l : List Nat) (h : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (hl : l.Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun x hx y hy => h x (by simp [hx]) y (by simp [hy])) (List.nodup_cons.mp hl).2⟩
    intro hm
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    have := h b (by simp [hb]) a (by simp) hfb
    exact (List.nodup_cons.mp hl).1 (this ▸ hb)

/-- The degree sum over the first `t` positions. -/
def degSum (head : List Nat) (ord : List Nat) (t : Nat) : Nat :=
  ((List.range t).map fun j => head.getD (ord.getD j 0 + 1) 0 - head.getD (ord.getD j 0) 0).sum

theorem degSum_succ (head : List Nat) (ord : List Nat) (t : Nat) :
    degSum head ord (t + 1) = degSum head ord t + (head.getD (ord.getD t 0 + 1) 0 - head.getD (ord.getD t 0) 0) := by
  unfold degSum
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem degSum_le (M : TS head target parent ord n root) (R : Ro head target parent ord n a) (t : Nat) (ht : t ≤ n) :
    degSum head ord t ≤ target.length := by
  have hnd : ((List.range t).map fun j => ord.getD j 0).Nodup := by
    apply nodup_map_of_inj _ _ _ List.nodup_range
    intro x hx y hy h
    exact ord_inj M.ordnd x y (by rw [M.ordlen]; have := List.mem_range.mp hx; omega)
      (by rw [M.ordlen]; have := List.mem_range.mp hy; omega) h
  have hlt : ∀ x ∈ (List.range t).map (fun j => ord.getD j 0), x < n := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hjt := List.mem_range.mp hj
    apply M.ordlt
    have : ord.getD j 0 = ord[j]'(by rw [M.ordlen]; omega) := by
      simp [List.getD_eq_getElem?_getD, show j < ord.length by rw [M.ordlen]; omega]
    rw [this]; exact List.getElem_mem _
  have h1 := Proofs.TreeRootMath.sum_nodup_le (fun x => head.getD (x + 1) 0 - head.getD x 0) n _ hnd hlt
  have h2 := Proofs.TreeRootMath.sum_outdeg head n R.hmono
  unfold degSum
  have : ((List.range t).map fun j => head.getD (ord.getD j 0 + 1) 0 - head.getD (ord.getD j 0) 0).sum =
      (((List.range t).map (fun j => ord.getD j 0)).map (fun x => head.getD (x + 1) 0 - head.getD x 0)).sum := by
    rw [List.map_map]; rfl
  rw [this]
  have := R.hlast
  omega


/-- The arrays after one iteration of the bottom-up loop at the vertex `v`. -/
def buA (a : Arr) (pre1 suf1 : List Int) (v : Nat) (tot : Int) : Arr :=
  { a with pre := pre1, dp := a.dp.set v (tot + 1), fu := a.fu.set v tot, suf := suf1 }

set_option maxHeartbeats 512000000 in
/-- The body of the bottom-up loop (including `k--`). -/
theorem bu_body (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (ty4 : mv.ty 4 = s64) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = s64) (ty8 : mv.ty 8 = s64)
    (P : List Cell) (fuel : Nat) (M : TS head target parent ord n root) (R : Ro head target parent ord n a)
    (Ln : Lens n target.length a) (root' k' : Nat) (hk : k' < n) (hrk : root' < 2147483648)
    (I : BUI head target parent ord n (k' + 1) a) (hfu : n + target.length + 2 ≤ fuel) :
    ∃ (r : PRM) (pre1 suf1 : List Int) (tot : Int),
      pexecM mv fuel (BUbody mv.nv) (gS P [ci root', ci n, ci k']) (VA a) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci root', ci n, cpI ((k' : Int) - 1)] ∧
      r.vv = VA (buA a pre1 suf1 (ord.getD k' 0) tot) ∧
      BUI head target parent ord n k' (buA a pre1 suf1 (ord.getD k' 0) tot) ∧
      pre1.length = a.pre.length ∧ suf1.length = a.suf.length ∧
      r.cost ≤ 2400 * (head.getD (ord.getD k' 0 + 1) 0 - head.getD (ord.getD k' 0) 0) + 900 ∧ r.need ≤ P.length + 250 ∧
      r.wk ≤ 2 * (head.getD (ord.getD k' 0 + 1) 0 - head.getD (ord.getD k' 0) 0) + 2 := by
  obtain ⟨v, hvk⟩ : ∃ v, v = ord.getD k' 0 := ⟨_, rfl⟩
  obtain ⟨hdpc, hnself, hvn⟩ := bu_pre M k' v hk hvk I
  have hdeg := head_le head target parent ord n a R v hvn
  have hmono := R.hmono v hvn
  obtain ⟨r, pre1, suf1, tot, back2, hr, retr, psr, vvr, hI1, hI2, ht0, htn, hb0, hbn, cr, nr, wr⟩ :=
    bu_iter mv hnv ty0 ty1 ty2 ty3 ty4 ty6 ty5 ty8 P fuel head target parent ord n a R Ln root' k' v hk hvk hrk I.glob hdpc hnself
      (by have := R.tlen; omega)
  obtain ⟨_, _, hI'⟩ := bu_step M R Ln k' v hk hvk I pre1 suf1 tot back2 hI1 hI2
  have sc := pexecM_scope mv fuel _ _ _ _ hr
  have hps : r.ps = gS P ([ci root', ci n, ci k'] ++ [ci v, cs 0, cs tot, cs tot, cs (tot + 1), cs 0, cs back2]) := psr
  rw [hps] at sc
  have tk := gS_takeC P [ci root', ci n, ci k'] [ci root', ci n, ci k'] [ci v, cs 0, cs tot, cs tot, cs (tot + 1), cs 0, cs back2] rfl
  simp only [tk] at sc
  -- k--
  have hk31 : k' < 2147483648 := by have := R.nb; omega
  have e2 := sub1_val mv r.vv _ (mv.nv + 2) k' (envs mv P [ci root', ci n, ci k'] 2 (ci k') (by simp) (i32vn k' (by omega))) hk31
  have s2 := gSM_assign mv P [ci root', ci n, ci k'] r.vv 2 (by simp) i32 _ _ _ e2 (ci k') (by simp) rfl (i32vn k' (by omega))
    (conv_signed i32 rfl rfl _ (Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)))
  have eB : [ci root', ci n, ci k'].set 2 ⟨i32, (k' : Int) - 1⟩ = [ci root', ci n, cpI ((k' : Int) - 1)] := rfl
  rw [eB] at s2
  have a2 := (pexecM_prim mv fuel (decI mv.nv 2) _ _).trans s2
  have b2 := seqM_some a2 rfl (pexecM_skip mv fuel _ _)
  have b1 := seqM_some sc retr b2
  refine ⟨_, pre1, suf1, tot, b1, rfl, rfl, ?_, ?_, hI1.len, hI2.len, ?_, ?_, ?_⟩
  · rw [← hvk]; exact vvr
  · rw [← hvk]; exact hI'
  · rw [← hvk]; simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cr ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nr ⊢; omega
  · rw [← hvk]; simp at wr ⊢; omega


theorem condK_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (z : Int) (hz : -2147483648 ≤ z ∧ z < 2147483648)
    (h2 : cl[2]? = some (cpI z)) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .ge (vI mv.nv 2) (.literal i32 0)) = some (if (0 : Int) ≤ z then 1 else 0) := by
  have e := envs mv P cl 2 (cpI z) h2 (Proofs.VectorSumCall.i32_valid _ hz.1 hz.2)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary]
  have e' : (vI mv.nv 2).denote (penvN mv.nv (gS P cl)) = some z := by
    show (NExpr.variable i32 (mv.nv + 2)).denote _ = some z
    rw [den_variable]; exact e
  rw [e', Option.bind_some, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
  by_cases h : (0 : Int) ≤ z
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 512000000 in
/-- The bottom-up loop `for (k = n - 1; k >= 0; k--)`, from the state with `t = k + 1` positions left. -/
theorem bu_loop (mv : MV) (hnv : mv.nv = 9) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (ty3 : mv.ty 3 = i32) (ty4 : mv.ty 4 = s64) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = s64) (ty8 : mv.ty 8 = s64)
    (P : List Cell) (M : TS head target parent ord n root) (a0 : Arr) (R : Ro head target parent ord n a0)
    (Ln0 : Lens n target.length a0) (root' : Nat) (hrk : root' < 2147483648) :
    ∀ (t : Nat) (a : Arr) (fuel : Nat), t ≤ n → Ro head target parent ord n a → Lens n target.length a →
      BUI head target parent ord n t a → t + 1 + n + target.length + 2 ≤ fuel →
      ∃ (res : PRM) (a' : Arr),
        pexecM mv fuel (.whileLoop (.binary bT .ge (vI mv.nv 2) (.literal i32 0)) (BUbody mv.nv))
          (gS P [ci root', ci n, cpI ((t : Int) - 1)]) (VA a) = some res ∧ res.ret = none ∧
        res.ps = gS P [ci root', ci n, cpI ((0 : Int) - 1)] ∧ res.vv = VA a' ∧ BUI head target parent ord n 0 a' ∧
        Ro head target parent ord n a' ∧ Lens n target.length a' ∧
        res.cost ≤ 2400 * degSum head ord t + 1000 * t + 30 ∧ res.need ≤ P.length + 250 ∧
        res.wk ≤ 2 * degSum head ord t + 2 * t ∧ a'.up = a.up := by
  intro t
  induction t with
  | zero =>
    intro a fuel ht R Ln I hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fuel = fu' + 1 := ⟨fuel - 1, by omega⟩
    have hc := condK_val mv P (VA a) [ci root', ci n, cpI (((0 : Nat) : Int) - 1)] (((0 : Nat) : Int) - 1) ⟨by omega, by omega⟩ (by simp)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, a, rfl, rfl, rfl, rfl, I, R, Ln, ?_, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, degSum]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp [degSum]
  | succ t ih =>
    intro a fuel ht R Ln I hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fuel = fu' + 1 := ⟨fuel - 1, by omega⟩
    have hk : t < n := by omega
    rw [show (((t + 1 : Nat) : Int) - 1) = (t : Int) by omega]
    have hc := condK_val mv P (VA a) [ForLoop.ci root', ForLoop.ci n, ForLoop.ci t] (t : Int) ⟨by omega, by have := R.nb; omega⟩ (by simp [cpI, ForLoop.ci])
    rw [if_pos (by omega)] at hc
    obtain ⟨r1, pre1, suf1, tot, h1, ret1, ps1, vv1, hI1, hpl, hsl, c1, n1, w1⟩ :=
      bu_body mv hnv ty0 ty1 ty2 ty3 ty4 ty5 ty6 ty8 P (fu' + 1) M R Ln root' t hk hrk I (by omega)
    have R' : Ro head target parent ord n (buA a pre1 suf1 (ord.getD t 0) tot) :=
      ⟨R.hd, R.tg, R.pa, R.od, R.hlen, R.hmono, R.hlast, R.tlen, R.tlt, R.nb, R.palen, R.pav, R.odlen, R.odlt⟩
    have hvn : ord.getD t 0 < n := (bu_pre M t _ hk rfl I).2.2
    have Ln' : Lens n target.length (buA a pre1 suf1 (ord.getD t 0) tot) :=
      ⟨by show (a.dp.set _ _).length = n; simp [Ln.dp], by show pre1.length = target.length; rw [hpl, Ln.pre],
        by show suf1.length = target.length; rw [hsl, Ln.suf], Ln.up, by show (a.fu.set _ _).length = n; simp [Ln.fu]⟩
    obtain ⟨r2, a', h2, ret2, ps2, vv2, hI2, R2, Ln2, c2, n2, w2, hup2⟩ := ih (buA a pre1 suf1 (ord.getD t 0) tot) fu' (by omega) R' Ln' hI1
      (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
    rw [h1]
    simp only [ret1, ps1, vv1]
    rw [h2]
    simp only
    refine ⟨_, a', rfl, ret2, ps2, vv2, hI2, R2, Ln2, ?_, ?_, ?_, hup2⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; rw [degSum_succ]; simp only [List.getD_eq_getElem?_getD]; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; rw [degSum_succ]; simp only [List.getD_eq_getElem?_getD] at *; omega

end Proofs.TreeFullDpExec
