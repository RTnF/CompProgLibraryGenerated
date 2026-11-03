import Proofs.TreePathExec
import Proofs.InvGcdMath
import Proofs.GcdU64Call
import Proofs.Generated.InvGcd

namespace Proofs.InvGcdExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs pexecM_branch_true pexecM_branch_false)
open Proofs.TopoSortExec (i32v one_den zero_den)
open Proofs.TreeArcCostsExec (VC VC_get0 VC_get1 VC_set1)
open Proofs.InvGcdMath

/-! ### `inv_gcd` (nv = 1: out).  Cells: 0 = a, 1 = b, 2 = s, 3 = t, 4 = m0, 5 = m1, 6 = u, 7 = tmp -/

abbrev vS (nv k : Nat) : NExpr := .variable s64 (nv + k)
abbrev lit0 : NExpr := .cast s64 (.literal i32 0)
abbrev lit1 : NExpr := .cast s64 (.literal i32 1)
abbrev eMod (nv : Nat) : NExpr := .divrem s64 true (vS nv 0) (vS nv 1)
abbrev pA1 (nv : Nat) : NStmt := .assign (nv + 0) s64 (eMod nv)
abbrev cNeg (nv : Nat) : NExpr := .binary bT .lt (vS nv 0) lit0
abbrev pA2 (nv : Nat) : NStmt := .assign (nv + 0) s64 (.binary s64 .add (vS nv 0) (vS nv 1))
abbrev Y1 (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (pA2 nv)) Sk)) Sk
abbrev cW (nv : Nat) : NExpr := .binary bT .ne (vS nv 3) lit0
abbrev dU (nv : Nat) : NStmt := .declare s64 true (.divrem s64 false (vS nv 2) (vS nv 3))
abbrev aS (nv : Nat) : NStmt := .assign (nv + 2) s64 (.binary s64 .sub (vS nv 2) (.binary s64 .mul (vS nv 3) (vS nv 6)))
abbrev aM0 (nv : Nat) : NStmt := .assign (nv + 4) s64 (.binary s64 .sub (vS nv 4) (.binary s64 .mul (vS nv 5) (vS nv 6)))
abbrev dTmp (nv : Nat) : NStmt := .declare s64 true (vS nv 2)
abbrev aVar (nv j k : Nat) : NStmt := .assign (nv + j) s64 (vS nv k)
abbrev Bin (nv : Nat) : Command :=
  .sequence (.primitive (dU nv)) (.sequence (.primitive (aS nv)) (.sequence (.primitive (aM0 nv))
    (.sequence (.primitive (dTmp nv)) (.sequence (.primitive (aVar nv 2 3)) (.sequence (.primitive (aVar nv 3 7))
      (.sequence (.primitive (aVar nv 7 4)) (.sequence (.primitive (aVar nv 4 5)) (.sequence (.primitive (aVar nv 5 7)) Sk))))))))
abbrev Bw (nv : Nat) : Command := .sequence (.scope (Bin nv)) Sk
abbrev cNeg2 (nv : Nat) : NExpr := .binary bT .lt (vS nv 4) lit0
abbrev pA3 (nv : Nat) : NStmt :=
  .assign (nv + 4) s64 (.binary s64 .add (vS nv 4) (.divrem s64 false (vS nv 1) (vS nv 2)))
abbrev Y2 (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (pA3 nv)) Sk)) Sk
abbrev w0 (nv : Nat) : NStmt := .write (.local 0) s64 (.cast u64 (.literal i32 0)) (vS nv 2)
abbrev w1 (nv : Nat) : NStmt := .write (.local 0) s64 (.cast u64 (.literal i32 1)) (vS nv 4)
abbrev bodyIG (nv : Nat) : Command :=
  .sequence (.primitive (pA1 nv)) (.sequence (.branch (cNeg nv) (Y1 nv) Sk)
    (.sequence (.primitive (.declare s64 true (vS nv 1))) (.sequence (.primitive (.declare s64 true (vS nv 0)))
      (.sequence (.primitive (.declare s64 true lit0)) (.sequence (.primitive (.declare s64 true lit1))
        (.sequence (.whileLoop (cW nv) (Bw nv)) (.sequence (.branch (cNeg2 nv) (Y2 nv) Sk)
          (.sequence (.primitive (w0 nv)) (.sequence (.primitive (w1 nv)) Sk)))))))))

theorem body_eqIG : Proofs.InvGcdInstance.inv_gcd.body = bodyIG 1 := rfl

abbrev K (a b : Nat) (s t m0 m1 : Int) : List Cell := [cs a, cs b, cs s, cs t, cs m0, cs m1]

theorem v64 (x : Int) (h : x.natAbs < 9223372036854775808) : s64.valid x = true :=
  Proofs.BellmanFordExec.s64_valid_of x (by omega)

theorem vr (mv : MV) (P cl : List Cell) (k : Nat) (x : Int) (hk : cl[k]? = some (cs x)) (hv : s64.valid x = true) :
    (vS mv.nv k).denote (penvN mv.nv (gS P cl)) = some x := by
  show (NExpr.variable s64 (mv.nv + k)).denote _ = _
  rw [den_variable]
  exact envs mv P cl k (cs x) hk hv

theorem bnd (env : Nat → Ty → Option Int) (op : Binary) (l r : NExpr) (x y z : Int) (hl : l.denote env = some x)
    (hr : r.denote env = some y) (hz : s64.convert (binaryValue op x y) = some z) :
    (NExpr.binary s64 op l r).denote env = some z := by
  rw [den_binary, hl, Option.bind_some, hr, Option.bind_some, hz]

theorem cdr_s64 (rem : Bool) (s t : Nat) (ht : 0 < t) (hs : s < 9223372036854775808) :
    checkedDivRem s64 rem (s : Int) (t : Int) = some (if rem then ((s % t : Nat) : Int) else ((s / t : Nat) : Int)) := by
  have hq : (s : Int).tdiv (t : Int) = ((s / t : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg s)]; exact (Int.natCast_div s t).symm
  have hr : (s : Int).tmod (t : Int) = ((s % t : Nat) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg s)]; exact (Int.natCast_mod s t).symm
  have hqv : s64.valid ((s / t : Nat) : Int) = true := v64 _ (by
    have := Nat.div_le_self s t; rw [Int.natAbs_natCast]; omega)
  have hrv : s64.valid ((s % t : Nat) : Int) = true := v64 _ (by
    have := Nat.mod_le s t; rw [Int.natAbs_natCast]; omega)
  have ht0 : ((t : Int) == 0) = false := by simp; omega
  cases rem
  · unfold checkedDivRem
    simp only [ht0, hq, hqv, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    exact conv_signed s64 rfl rfl _ hqv
  · unfold checkedDivRem
    simp only [ht0, hq, hr, hqv, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    exact conv_signed s64 rfl rfl _ hrv

theorem st_var (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (j k : Nat) (x y : Int)
    (hj : cl[j]? = some (cs x)) (hk : cl[k]? = some (cs y)) (vx : s64.valid x = true) (vy : s64.valid y = true) :
    pstmtM mv (aVar mv.nv j k) (gS P cl) vv = some ⟨gS P (cl.set j (cs y)), vv, none, (vwp (vS mv.nv k)).1 + 1,
      P.length + 2 * cl.length + (vwp (vS mv.nv k)).2 + 2, 0⟩ := by
  have hjl : j < cl.length := (List.getElem?_eq_some_iff.mp hj).1
  exact gSM_assign mv P cl vv j hjl s64 (vS mv.nv k) y y (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P cl k y hk vy)
    (cs x) hj rfl vx (conv_signed s64 rfl rfl _ vy)

set_option maxHeartbeats 16000000 in
/-- One iteration of the loop of `inv_gcd`. -/
theorem b_iter (mv : MV) (hnv : mv.nv = 1) (P : List Cell) (vv : Nat → List Int) (a b s t : Nat) (m0 m1 : Int) (fu : Nat)
    (hb : 0 < b) (hb63 : b < 9223372036854775808) (ha : a < b) (I : Inv b a s t m0 m1) (ht : t ≠ 0) :
    ∃ r : PRM, pexecM mv fu (Bw mv.nv) (gS P (K a b (s : Int) (t : Int) m0 m1)) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (K a b (t : Int) ((s % t : Nat) : Int) m1 (m0 - m1 * ((s / t : Nat) : Int))) ∧ r.vv = vv ∧
      r.cost ≤ 500 ∧ r.need ≤ P.length + 100 ∧ r.wk = 0 := by
  have htpos : 0 < t := Nat.pos_of_ne_zero ht
  obtain ⟨hm0, hm1, hm1u, hm0'⟩ := inv_bounds b a s t m0 m1 hb I ht
  have hts := I.h5
  have hsb := I.h7
  have hdm : (s : Int) = (t : Int) * ((s / t : Nat) : Int) + ((s % t : Nat) : Int) := by
    exact_mod_cast (Nat.div_add_mod s t).symm
  have hmod : s % t < t := Nat.mod_lt _ htpos
  have hdiv : s / t ≤ s := Nat.div_le_self s t
  have hmul : t * (s / t) ≤ s := Nat.mul_div_le s t
  have hrI : ((s % t : Nat) : Int) = (s : Int) - (t : Int) * ((s / t : Nat) : Int) := by omega
  -- validity
  have vs : s64.valid (s : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have vt : s64.valid (t : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have va : s64.valid (a : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have vb : s64.valid (b : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have vm0 : s64.valid m0 = true := v64 _ (by omega)
  have vm1 : s64.valid m1 = true := v64 _ (by omega)
  have vu : s64.valid ((s / t : Nat) : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have vtu : s64.valid ((t : Int) * ((s / t : Nat) : Int)) = true := v64 _ (by
    have : (t : Int) * ((s / t : Nat) : Int) = ((t * (s / t) : Nat) : Int) := by push_cast; rfl
    rw [this, Int.natAbs_natCast]; omega)
  have vmu : s64.valid (m1 * ((s / t : Nat) : Int)) = true := v64 _ (by omega)
  have vr' : s64.valid ((s % t : Nat) : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have vm2 : s64.valid (m0 - m1 * ((s / t : Nat) : Int)) = true := v64 _ (by omega)
  have cdv : checkedDivRem s64 false (s : Int) (t : Int) = some ((s / t : Nat) : Int) := by
    have := cdr_s64 false s t htpos (by omega)
    simpa using this
  have hs63 : s < 9223372036854775808 := by omega
  generalize hu : ((s / t : Nat) : Int) = u at *
  generalize hr : ((s % t : Nat) : Int) = rI at *
  generalize hm2 : m0 - m1 * u = m2 at *
  have hsub : (s : Int) - (t : Int) * u = rI := by omega
  have hmu : m0 - m1 * u = m2 := hm2
  -- the environments of the six states
  have c1 := fun (cl : List Cell) k => vr mv P cl k
  -- 1: int u = s / t
  have e1 : vdenM mv vv (penvN mv.nv (gS P (K a b (s : Int) (t : Int) m0 m1))) (.divrem s64 false (vS mv.nv 2) (vS mv.nv 3)) = some u := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, vr mv P _ 2 s rfl vs, Option.bind_some, vr mv P _ 3 t rfl vt,
      Option.bind_some, cdv]
  have d1 := gSM_decl mv P (K a b (s : Int) (t : Int) m0 m1) vv s64 _ u u e1 (conv_signed s64 rfl rfl _ vu)
  have a1 := (pexecM_prim mv fu (dU mv.nv) _ _).trans d1
  -- 2: s = s - t * u
  have e2 : vdenM mv vv (penvN mv.nv (gS P (K a b (s : Int) (t : Int) m0 m1 ++ [cs u]))) (.binary s64 .sub (vS mv.nv 2)
      (.binary s64 .mul (vS mv.nv 3) (vS mv.nv 6))) = some rI := by
    rw [vdenM_scalar _ _ _ _ rfl]
    refine bnd _ .sub _ _ s ((t : Int) * u) rI (vr mv P _ 2 s rfl vs)
      (bnd _ .mul _ _ t u _ (vr mv P _ 3 t rfl vt) (vr mv P _ 6 u rfl vu) (conv_signed s64 rfl rfl _ vtu)) ?_
    show s64.convert ((s : Int) - (t : Int) * u) = some rI
    rw [hsub]; exact conv_signed s64 rfl rfl _ vr'
  have d2 := gSM_assign mv P (K a b (s : Int) (t : Int) m0 m1 ++ [cs u]) vv 2 (by simp) s64 _ _ _ e2 (cs s) rfl rfl vs
    (conv_signed s64 rfl rfl _ vr')
  have a2 := (pexecM_prim mv fu (aS mv.nv) _ _).trans d2
  -- 3: m0 = m0 - m1 * u
  have e3 : vdenM mv vv (penvN mv.nv (gS P [cs a, cs b, cs rI, cs t, cs m0, cs m1, cs u])) (.binary s64 .sub (vS mv.nv 4)
      (.binary s64 .mul (vS mv.nv 5) (vS mv.nv 6))) = some m2 := by
    rw [vdenM_scalar _ _ _ _ rfl]
    refine bnd _ .sub _ _ m0 (m1 * u) m2 (vr mv P _ 4 m0 rfl vm0)
      (bnd _ .mul _ _ m1 u _ (vr mv P _ 5 m1 rfl vm1) (vr mv P _ 6 u rfl vu) (conv_signed s64 rfl rfl _ vmu)) ?_
    show s64.convert (m0 - m1 * u) = some m2
    rw [hmu]; exact conv_signed s64 rfl rfl _ vm2
  have d3 := gSM_assign mv P [cs a, cs b, cs rI, cs t, cs m0, cs m1, cs u] vv 4 (by simp) s64 _ _ _ e3 (cs m0) rfl rfl vm0
    (conv_signed s64 rfl rfl _ vm2)
  have a3 := (pexecM_prim mv fu (aM0 mv.nv) _ _).trans d3
  -- 4: long long tmp = s
  have e4 : vdenM mv vv (penvN mv.nv (gS P [cs a, cs b, cs rI, cs t, cs m2, cs m1, cs u])) (vS mv.nv 2) = some rI := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 2 rI rfl vr'
  have d4 := gSM_decl mv P [cs a, cs b, cs rI, cs t, cs m2, cs m1, cs u] vv s64 _ rI rI e4 (conv_signed s64 rfl rfl _ vr')
  have a4 := (pexecM_prim mv fu (dTmp mv.nv) _ _).trans d4
  -- 5..9: the swaps
  have a5 := (pexecM_prim mv fu (aVar mv.nv 2 3) _ _).trans
    (st_var mv P vv [cs a, cs b, cs rI, cs t, cs m2, cs m1, cs u, cs rI] 2 3 rI t rfl rfl vr' vt)
  have a6 := (pexecM_prim mv fu (aVar mv.nv 3 7) _ _).trans
    (st_var mv P vv [cs a, cs b, cs t, cs t, cs m2, cs m1, cs u, cs rI] 3 7 t rI rfl rfl vt vr')
  have a7 := (pexecM_prim mv fu (aVar mv.nv 7 4) _ _).trans
    (st_var mv P vv [cs a, cs b, cs t, cs rI, cs m2, cs m1, cs u, cs rI] 7 4 rI m2 rfl rfl vr' vm2)
  have a8 := (pexecM_prim mv fu (aVar mv.nv 4 5) _ _).trans
    (st_var mv P vv [cs a, cs b, cs t, cs rI, cs m2, cs m1, cs u, cs m2] 4 5 m2 m1 rfl rfl vm2 vm1)
  have a9 := (pexecM_prim mv fu (aVar mv.nv 5 7) _ _).trans
    (st_var mv P vv [cs a, cs b, cs t, cs rI, cs m1, cs m1, cs u, cs m2] 5 7 m1 m2 rfl rfl vm1 vm2)
  have b9 := seqM_some a9 rfl (pexecM_skip mv fu _ _)
  have b8 := seqM_some a8 rfl b9
  have b7 := seqM_some a7 rfl b8
  have b6 := seqM_some a6 rfl b7
  have b5 := seqM_some a5 rfl b6
  have b4 := seqM_some a4 rfl b5
  have b3 := seqM_some a3 rfl b4
  have b2 := seqM_some a2 rfl b3
  have b1 := seqM_some a1 rfl b2
  have b0 := pexecM_scope mv fu _ _ _ _ b1
  have tk := gS_takeC P (K a b (s : Int) (t : Int) m0 m1) (K a b (t : Int) rI m1 m2) [cs u, cs m2] rfl
  obtain ⟨r1, hr1, hr1ps, hr1ret, hr1vv, hr1w, hr1c, hr1n⟩ : ∃ r1 : PRM, pexecM mv fu (Bin mv.nv) (gS P (K a b (s : Int) (t : Int) m0 m1)) vv = some r1 ∧
      r1.ps = gS P (K a b (t : Int) rI m1 m2 ++ [cs u, cs m2]) ∧ r1.ret = none ∧ r1.vv = vv ∧ r1.wk = 0 ∧ r1.cost ≤ 450 ∧ r1.need ≤ P.length + 100 := by
    refine ⟨_, b1, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len]
  have b0 := pexecM_scope mv fu _ _ _ _ hr1
  rw [hr1ps] at b0
  simp only [tk] at b0
  have b00 := seqM_some b0 hr1ret (pexecM_skip mv fu _ _)
  refine ⟨_, b00, rfl, rfl, hr1vv, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hr1c ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hr1n ⊢; omega
  · simp [hr1w]

theorem lit0_den (env : Nat → Ty → Option Int) : lit0.denote env = some 0 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
  exact conv_signed s64 rfl rfl _ (show s64.valid 0 = true from rfl)

theorem lit1_den (env : Nat → Ty → Option Int) : lit1.denote env = some 1 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  exact conv_signed s64 rfl rfl _ (show s64.valid 1 = true from rfl)

theorem cond_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (a b : Nat) (s t m0 m1 : Int)
    (vt : s64.valid t = true) :
    vdenM mv vv (penvN mv.nv (gS P (K a b s t m0 m1))) (cW mv.nv) = some (if t = 0 then 0 else 1) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, vr mv P _ 3 t rfl vt, Option.bind_some, lit0_den, Option.bind_some]
  by_cases h : t = 0
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 16000000 in
/-- The loop `while (t != 0) {...}`. -/
theorem while_exec (mv : MV) (hnv : mv.nv = 1) (P : List Cell) (vv : Nat → List Int) (a b : Nat) (hb : 0 < b)
    (hb63 : b < 9223372036854775808) (ha : a < b) :
    ∀ (t s : Nat) (m0 m1 : Int) (fu : Nat), Inv b a s t m0 m1 → Proofs.GcdU64Call.gsteps s t + 1 ≤ fu →
      ∃ (res : PRM) (sF : Nat) (m0F m1F : Int),
        pexecM mv fu (.whileLoop (cW mv.nv) (Bw mv.nv)) (gS P (K a b (s : Int) (t : Int) m0 m1)) vv = some res ∧
        res.ret = none ∧ res.ps = gS P (K a b (sF : Int) 0 m0F m1F) ∧ res.vv = vv ∧ Inv b a sF 0 m0F m1F ∧
        res.cost ≤ 520 * Proofs.GcdU64Call.gsteps s t + 20 ∧ res.need ≤ P.length + 100 ∧ res.wk = 0 := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro s m0 m1 fu I hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hts := I.h5
    have hsb := I.h7
    have vt : s64.valid (t : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
    have hc := cond_val mv P vv a b (s : Int) (t : Int) m0 m1 vt
    by_cases z : t = 0
    · subst z
      rw [if_pos (show ((0 : Nat) : Int) = 0 from rfl)] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, s, m0, m1, rfl, rfl, rfl, rfl, I, ?_, ?_, rfl⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · have hz : (t : Int) ≠ 0 := by omega
      rw [if_neg hz] at hc
      obtain ⟨r1, h1, ret1, p1, vv1, c1, n1, w1⟩ := b_iter mv hnv P vv a b s t m0 m1 (fu' + 1) hb hb63 ha I z
      have I' := inv_step b a s t m0 m1 hb I z
      obtain ⟨r2, sF, m0F, m1F, h2, ret2, p2, vv2, IF, c2, n2, w2⟩ :=
        ih (s % t) (Nat.mod_lt _ (by omega)) t m1 (m0 - m1 * ((s / t : Nat) : Int)) fu' I'
          (by rw [Proofs.GcdU64Call.gsteps_pos s t z] at hfu; omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, p1, vv1, h2]
      refine ⟨_, sF, m0F, m1F, rfl, ret2, p2, vv2, IF, ?_, ?_, ?_⟩
      · rw [Proofs.GcdU64Call.gsteps_pos s t z]
        simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
      · simp at w1 w2 ⊢; omega

/-- `if (c) { st; }` as the converter writes it at the top level of a function body. -/
abbrev If1 (c : NExpr) (st : NStmt) : Command := .branch c (.sequence (.scope (.sequence (.primitive st) Sk)) Sk) Sk

theorem if1_true (mv : MV) (fu : Nat) (c : NExpr) (st : NStmt) (P cl cl' : List Cell) (vv : Nat → List Int) (r : PRM)
    (hc : vdenM mv vv (penvN mv.nv (gS P cl)) c = some 1) (hst : pstmtM mv st (gS P cl) vv = some r)
    (hret : r.ret = none) (hps : r.ps = gS P cl') (hlen : cl.length = cl'.length) :
    ∃ r' : PRM, pexecM mv fu (If1 c st) (gS P cl) vv = some r' ∧ r'.ret = none ∧ r'.ps = gS P cl' ∧ r'.vv = r.vv ∧
      r'.cost ≤ r.cost + (vwp c).1 + 2 ∧ r'.need ≤ max r.need (P.length + 2 * cl.length + (vwp c).2 + 2) ∧ r'.wk = r.wk := by
  have a1 := (pexecM_prim mv fu st _ _).trans hst
  have b1 := seqM_some a1 hret (pexecM_skip mv fu _ _)
  have sc := pexecM_scope mv fu _ _ _ _ b1
  rw [hps] at sc
  have tk := Proofs.PexecKit.scope_take (gS P cl) (gS P cl') (by simp [gS_mem_len, hlen]) (by simp [gS_bs_len, hlen])
  simp only [tk] at sc
  have b2 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  have br := pexecM_branch_true mv fu c _ Sk _ _ 1 hc (by decide) _ b2
  refine ⟨_, br, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp; try omega
  · simp [gS_mem_len, gS_bs_len]
    try omega
  · simp

theorem if1_false (mv : MV) (fu : Nat) (c : NExpr) (st : NStmt) (P cl : List Cell) (vv : Nat → List Int)
    (hc : vdenM mv vv (penvN mv.nv (gS P cl)) c = some 0) :
    ∃ r' : PRM, pexecM mv fu (If1 c st) (gS P cl) vv = some r' ∧ r'.ret = none ∧ r'.ps = gS P cl ∧ r'.vv = vv ∧
      r'.cost ≤ (vwp c).1 + 1 ∧ r'.need ≤ P.length + 2 * cl.length + (vwp c).2 + 2 ∧ r'.wk = 0 := by
  have br := pexecM_branch_false mv fu c (.sequence (.scope (.sequence (.primitive st) Sk)) Sk) Sk _ _ hc _
    (pexecM_skip mv fu _ _)
  refine ⟨_, br, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp [gS_mem_len, gS_bs_len]
    omega
  · simp

/-- `a % b` of C++ for `b > 0` and any valid `a`. -/
theorem cdr_tmod (a : Int) (b : Nat) (hb : 0 < b) (hb63 : b < 9223372036854775808) (va : s64.valid a = true) :
    checkedDivRem s64 true a (b : Int) = some (a.tmod (b : Int)) ∧ -(b : Int) < a.tmod (b : Int) ∧ a.tmod (b : Int) < b ∧
      (b : Int) ∣ a.tmod (b : Int) - a := by
  have hb0 : (0 : Int) < (b : Int) := by exact_mod_cast hb
  have hva : -9223372036854775808 ≤ a ∧ a < 9223372036854775808 := by
    have := va; simp [Ty.valid, s64] at this; omega
  have hlt : a.tmod (b : Int) < b := Int.tmod_lt_of_pos a hb0
  have hlow : -(b : Int) < a.tmod (b : Int) := by
    by_cases ha : 0 ≤ a
    · have := Int.tmod_nonneg (b : Int) ha; omega
    · have h1 : (-a).tmod (b : Int) < b := Int.tmod_lt_of_pos (-a) hb0
      rw [Int.neg_tmod] at h1; omega
  have hq : s64.valid (a.tdiv (b : Int)) = true := by
    apply Proofs.BellmanFordExec.s64_valid_of
    by_cases ha : 0 ≤ a
    · rw [Int.tdiv_eq_ediv_of_nonneg ha]
      have h1 := Int.ediv_le_self (b : Int) ha
      have h2 := Int.ediv_nonneg ha (Int.le_of_lt hb0)
      omega
    · have h0 : 0 ≤ -a := by omega
      have e : a.tdiv (b : Int) = -((-a).tdiv (b : Int)) := by rw [Int.neg_tdiv]; simp
      rw [e, Int.tdiv_eq_ediv_of_nonneg h0]
      have h1 := Int.ediv_le_self (b : Int) h0
      have h2 := Int.ediv_nonneg h0 (Int.le_of_lt hb0)
      omega
  have hmv : s64.valid (a.tmod (b : Int)) = true := Proofs.BellmanFordExec.s64_valid_of _ (by omega)
  refine ⟨?_, hlow, hlt, ?_⟩
  · unfold checkedDivRem
    have hb1 : ((b : Int) == 0) = false := by simp; omega
    simp only [hb1, hq, Bool.false_eq_true, ↓reduceIte, Bool.not_true, ite_true]
    exact conv_signed s64 rfl rfl _ hmv
  · rw [Int.tmod_def]
    exact ⟨-(a.tdiv (b : Int)), by ring⟩

theorem eq_emod (a : Int) (b : Nat) (c : Int) (hb : 0 < b) (h : (b : Int) ∣ c - a) (h0 : 0 ≤ c) (h1 : c < b) :
    c = a % (b : Int) := by
  have h2 : c % (b : Int) = a % (b : Int) := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)
  rw [Int.emod_eq_of_lt h0 h1] at h2
  exact h2

theorem neg_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (a1 : Int) (b : Nat) (va1 : s64.valid a1 = true) :
    vdenM mv vv (penvN mv.nv (gS P [cs a1, cs b])) (cNeg mv.nv) = some (if a1 < 0 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, vr mv P _ 0 a1 rfl va1, Option.bind_some, lit0_den, Option.bind_some]
  by_cases h : a1 < 0
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 16000000 in
/-- `if (a < 0) { a = a + b; }` after `a = a % b`: afterwards the first cell holds `a0 mod b` in `[0, b)`. -/
theorem if_pre (mv : MV) (hnv : mv.nv = 1) (P : List Cell) (vv : Nat → List Int) (a0 : Int) (b : Nat) (fu : Nat)
    (hb : 0 < b) (hb63 : b < 9223372036854775808) (va : s64.valid a0 = true) :
    ∃ (r : PRM) (an : Nat), pexecM mv fu (If1 (cNeg mv.nv) (pA2 mv.nv)) (gS P [cs (a0.tmod (b : Int)), cs b]) vv = some r ∧
      r.ret = none ∧ r.ps = gS P [cs an, cs b] ∧ r.vv = vv ∧ (an : Int) = a0 % (b : Int) ∧ an < b ∧
      r.cost ≤ 30 ∧ r.need ≤ P.length + 40 ∧ r.wk = 0 := by
  obtain ⟨_, hlow, hlt, hdvd⟩ := cdr_tmod a0 b hb hb63 va
  have hb0 : (0 : Int) < (b : Int) := by exact_mod_cast hb
  generalize ha1 : a0.tmod (b : Int) = a1 at *
  have va1 : s64.valid a1 = true := Proofs.BellmanFordExec.s64_valid_of _ (by omega)
  have vbb : s64.valid (b : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  by_cases h : a1 < 0
  · have hc := neg_val mv P vv a1 b va1
    rw [if_pos h] at hc
    have hsum : s64.valid (a1 + (b : Int)) = true := Proofs.BellmanFordExec.s64_valid_of _ (by omega)
    have e : vdenM mv vv (penvN mv.nv (gS P [cs a1, cs b])) (.binary s64 .add (vS mv.nv 0) (vS mv.nv 1)) = some (a1 + (b : Int)) := by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact bnd _ .add _ _ a1 b _ (vr mv P _ 0 a1 rfl va1) (vr mv P _ 1 b rfl vbb) (conv_signed s64 rfl rfl _ hsum)
    have st := gSM_assign mv P [cs a1, cs b] vv 0 (by simp) s64 _ _ _ e (cs a1) rfl rfl va1 (conv_signed s64 rfl rfl _ hsum)
    have hdv : (b : Int) ∣ (a1 + (b : Int)) - a0 := by
      rw [show a1 + (b : Int) - a0 = (a1 - a0) + (b : Int) by ring]
      exact Int.dvd_add hdvd (Int.dvd_refl _)
    have heq := eq_emod a0 b (a1 + (b : Int)) hb hdv (by omega) (by omega)
    obtain ⟨an, han⟩ : ∃ an : Nat, (an : Int) = a1 + (b : Int) := ⟨(a1 + (b : Int)).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨r, hr, hret, hps, hvv, hcost, hneed, hwk⟩ := if1_true mv fu _ _ P _ [cs an, cs b] vv _ hc st rfl
      (by rw [han]; rfl) rfl
    refine ⟨r, an, hr, hret, hps, hvv, by rw [han]; exact heq, by omega, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at hcost ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len] at hneed ⊢; omega
    · simpa using hwk
  · have hc := neg_val mv P vv a1 b va1
    rw [if_neg h] at hc
    have hdv : (b : Int) ∣ a1 - a0 := hdvd
    have heq := eq_emod a0 b a1 hb hdv (by omega) (by omega)
    obtain ⟨an, han⟩ : ∃ an : Nat, (an : Int) = a1 := ⟨a1.toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨r, hr, hret, hps, hvv, hcost, hneed, hwk⟩ := if1_false mv fu (cNeg mv.nv) (pA2 mv.nv) P [cs a1, cs b] vv hc
    refine ⟨r, an, hr, hret, by rw [hps, han], hvv, by rw [han]; exact heq, by omega, ?_, ?_, hwk⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at hcost ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len] at hneed ⊢; omega

theorem neg2_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (a b : Nat) (s t m0 m1 : Int) (vm0 : s64.valid m0 = true) :
    vdenM mv vv (penvN mv.nv (gS P (K a b s t m0 m1))) (cNeg2 mv.nv) = some (if m0 < 0 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, vr mv P _ 4 m0 rfl vm0, Option.bind_some, lit0_den, Option.bind_some]
  by_cases h : m0 < 0
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 16000000 in
/-- `if (m0 < 0) { m0 = m0 + b / s; }` after the loop. -/
theorem if_post (mv : MV) (hnv : mv.nv = 1) (P : List Cell) (vv : Nat → List Int) (an b sF : Nat) (m0F m1F : Int) (fu : Nat)
    (hb : 0 < b) (hb63 : b < 9223372036854775808) (I : Inv b an sF 0 m0F m1F) :
    ∃ (r : PRM), pexecM mv fu (If1 (cNeg2 mv.nv) (pA3 mv.nv)) (gS P (K an b (sF : Int) 0 m0F m1F)) vv = some r ∧
      r.ret = none ∧ r.ps = gS P (K an b (sF : Int) 0 (if m0F < 0 then m0F + ((b / sF : Nat) : Int) else m0F) m1F) ∧
      r.vv = vv ∧ r.cost ≤ 60 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 := by
  obtain ⟨hg, hsb, hs, hlt, hd⟩ := inv_final b an sF m0F m1F hb I
  have hsb' := I.h7
  have hdb : b / sF ≤ b := Nat.div_le_self b sF
  have vs : s64.valid (sF : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have vq : s64.valid ((b / sF : Nat) : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have vm0 : s64.valid m0F = true := v64 _ (by omega)
  have vb : s64.valid (b : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have cdv : checkedDivRem s64 false (b : Int) (sF : Int) = some ((b / sF : Nat) : Int) := by
    have := cdr_s64 false b sF hs hb63
    simpa using this
  by_cases h : m0F < 0
  · have hc := neg2_val mv P vv an b (sF : Int) 0 m0F m1F vm0
    rw [if_pos h] at hc
    have hsum : s64.valid (m0F + ((b / sF : Nat) : Int)) = true := v64 _ (by omega)
    have e : vdenM mv vv (penvN mv.nv (gS P (K an b (sF : Int) 0 m0F m1F))) (.binary s64 .add (vS mv.nv 4)
        (.divrem s64 false (vS mv.nv 1) (vS mv.nv 2))) = some (m0F + ((b / sF : Nat) : Int)) := by
      rw [vdenM_scalar _ _ _ _ rfl]
      refine bnd _ .add _ _ m0F ((b / sF : Nat) : Int) _ (vr mv P _ 4 m0F rfl vm0) ?_ (conv_signed s64 rfl rfl _ hsum)
      rw [den_divrem, vr mv P _ 1 b rfl vb, Option.bind_some, vr mv P _ 2 sF rfl vs, Option.bind_some, cdv]
    have st := gSM_assign mv P (K an b (sF : Int) 0 m0F m1F) vv 4 (by simp) s64 _ _ _ e (cs m0F) rfl rfl vm0
      (conv_signed s64 rfl rfl _ hsum)
    obtain ⟨r, hr, hret, hps, hvv, hcost, hneed, hwk⟩ := if1_true mv fu _ _ P _ (K an b (sF : Int) 0 (m0F + ((b / sF : Nat) : Int)) m1F)
      vv _ hc st rfl rfl rfl
    refine ⟨r, hr, hret, by rw [if_pos h]; exact hps, hvv, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at hcost ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len] at hneed ⊢; omega
    · simpa using hwk
  · have hc := neg2_val mv P vv an b (sF : Int) 0 m0F m1F vm0
    rw [if_neg h] at hc
    obtain ⟨r, hr, hret, hps, hvv, hcost, hneed, hwk⟩ := if1_false mv fu (cNeg2 mv.nv) (pA3 mv.nv) P
      (K an b (sF : Int) 0 m0F m1F) vv hc
    refine ⟨r, hr, hret, by rw [if_neg h]; exact hps, hvv, ?_, ?_, hwk⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at hcost ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len] at hneed ⊢; omega

def VO (O : List Int) : Nat → List Int := fun k => if k = 0 then O else []
theorem VO_get0 (O : List Int) : VO O 0 = O := by simp [VO]
theorem VO_set0 (O x : List Int) : upd (VO O) 0 x = VO x := by
  funext k; unfold upd VO; split <;> simp_all

theorem lit_idx (env : Nat → Ty → Option Int) (k : Nat) (hk : k < 2147483648) :
    (NExpr.cast u64 (.literal i32 (k : Int))).denote env = some (k : Int) := by
  rw [den_cast, den_literal, if_pos (validN k hk), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)

theorem log2_mono_le (x y : Nat) (hx : x ≠ 0) (h : x ≤ y) : Nat.log2 x ≤ Nat.log2 y := by
  rw [Nat.le_log2 (by omega)]
  exact Nat.le_trans (Nat.log2_self_le hx) h

set_option maxHeartbeats 16000000 in
/-- The whole body of `inv_gcd`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (O : List Int) (P : List Cell) (a0 : Int) (b : Nat)
    (hb : 0 < b) (hb63 : b < 9223372036854775808) (va : s64.valid a0 = true) (hO : 2 ≤ O.length) (fu : Nat)
    (hfu : 2 * Nat.log2 b + 3 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyIG mv.nv) (gS P [cs a0, cs b]) (VO O) = some r ∧ r.ret = none ∧
      ∃ (an sF : Nat) (xF : Int), (an : Int) = a0 % (b : Int) ∧ an < b ∧ sF = Nat.gcd b an ∧ 0 ≤ xF ∧
        xF < ((b / sF : Nat) : Int) ∧ (b : Int) ∣ xF * (an : Int) - (sF : Int) ∧
        r.vv = VO ((O.set 0 (sF : Int)).set 1 xF) ∧ (∃ cs : List Cell, r.ps = gS P cs) ∧
        r.cost ≤ 1040 * Nat.log2 b + 800 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 := by
  have vb : s64.valid (b : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  obtain ⟨hdiv, hlow, hlt, hdvd⟩ := cdr_tmod a0 b hb hb63 va
  have va1 : s64.valid (a0.tmod (b : Int)) = true := Proofs.BellmanFordExec.s64_valid_of _ (by omega)
  -- 1: a = a % b
  have e1 : vdenM mv (VO O) (penvN mv.nv (gS P [cs a0, cs b])) (eMod mv.nv) = some (a0.tmod (b : Int)) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, vr mv P _ 0 a0 rfl va, Option.bind_some, vr mv P _ 1 b rfl vb,
      Option.bind_some, hdiv]
  have d1 := gSM_assign mv P [cs a0, cs b] (VO O) 0 (by simp) s64 _ _ _ e1 (cs a0) rfl rfl va (conv_signed s64 rfl rfl _ va1)
  have a1 := (pexecM_prim mv fu (pA1 mv.nv) _ _).trans d1
  -- 2: if (a < 0)
  obtain ⟨r2, an, h2, ret2, ps2, vv2, han, hanb, c2, n2, w2⟩ := if_pre mv hnv P (VO O) a0 b fu hb hb63 va
  -- 3-6: declarations
  have van : s64.valid (an : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have v0 : s64.valid 0 = true := rfl
  have v1 : s64.valid 1 = true := rfl
  have d3 := gSM_decl mv P [cs (an : Int), cs b] (VO O) s64 (vS mv.nv 1) (b : Int) (b : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 1 b rfl vb) (conv_signed s64 rfl rfl _ vb)
  have a3 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 1)) _ _).trans d3
  have d4 := gSM_decl mv P [cs (an : Int), cs b, cs b] (VO O) s64 (vS mv.nv 0) (an : Int) (an : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 0 an rfl van) (conv_signed s64 rfl rfl _ van)
  have a4 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 0)) _ _).trans d4
  have d5 := gSM_decl mv P [cs (an : Int), cs b, cs b, cs an] (VO O) s64 lit0 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact lit0_den _) (conv_signed s64 rfl rfl _ v0)
  have a5 := (pexecM_prim mv fu (.declare s64 true lit0) _ _).trans d5
  have d6 := gSM_decl mv P [cs (an : Int), cs b, cs b, cs an, cs 0] (VO O) s64 lit1 1 1
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact lit1_den _) (conv_signed s64 rfl rfl _ v1)
  have a6 := (pexecM_prim mv fu (.declare s64 true lit1) _ _).trans d6
  -- 7: the loop
  have hI := inv_init b an hb hanb
  obtain ⟨rw_, sF, m0F, m1F, h7, ret7, ps7, vv7, IF, c7, n7, w7⟩ :=
    while_exec mv hnv P (VO O) an b hb hb63 hanb an b 0 1 fu hI (by
      have := Proofs.GcdU64Call.gsteps_le
      by_cases han0 : an = 0
      · subst han0; rw [Proofs.GcdU64Call.gsteps_zero]; omega
      · have h1 := this an b (by omega)
        have h2 := log2_mono_le an b han0 (by omega)
        omega)
  -- 8: if (m0 < 0)
  obtain ⟨r8, h8, ret8, ps8, vv8, c8, n8, w8⟩ := if_post mv hnv P (VO O) an b sF m0F m1F fu hb hb63 IF
  have hout := inv_out b an sF m0F m1F hb IF
  obtain ⟨hx0, hx1, hx2⟩ := hout
  obtain ⟨hg, hsb, hs, hlt', hd⟩ := inv_final b an sF m0F m1F hb IF
  have hsb' := IF.h7
  set xF : Int := (if m0F < 0 then m0F + ((b / sF : Nat) : Int) else m0F) with hxF
  have hdb : b / sF ≤ b := Nat.div_le_self b sF
  have vs : s64.valid (sF : Int) = true := v64 _ (by rw [Int.natAbs_natCast]; omega)
  have vx : s64.valid xF = true := v64 _ (by
    have : ((b / sF : Nat) : Int) ≤ b := by exact_mod_cast hdb
    omega)
  -- 9, 10: out[0] = s; out[1] = m0
  have hO0 : 0 < (VO O 0).length := by rw [VO_get0]; omega
  have hw0 := pstmtM_write_ok mv (gS P (K an b (sF : Int) 0 xF m1F)) (VO O) 0 (by omega) (.cast u64 (.literal i32 0)) (vS mv.nv 2)
    (sF : Int) 0 (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 2 sF rfl vs)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact lit_idx _ 0 (by decide)) hO0 (by rw [ty0]; exact vs)
  rw [ty0, VO_get0, VO_set0] at hw0
  have x0 := (pexecM_prim mv fu (w0 mv.nv) _ _).trans hw0
  have hO1 : 1 < ((O.set 0 (sF : Int))).length := by simp; omega
  have hw1 := pstmtM_write_ok mv (gS P (K an b (sF : Int) 0 xF m1F)) (VO (O.set 0 (sF : Int))) 0 (by omega)
    (.cast u64 (.literal i32 1)) (vS mv.nv 4) xF 1
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 4 xF rfl vx)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact lit_idx _ 1 (by decide)) (by rw [VO_get0]; exact hO1) (by rw [ty0]; exact vx)
  rw [ty0, VO_get0, VO_set0] at hw1
  have x1 := (pexecM_prim mv fu (w1 mv.nv) _ _).trans hw1
  -- assemble
  have y1 := seqM_some x1 rfl (pexecM_skip mv fu _ _)
  have y0 := seqM_some x0 rfl y1
  have z8 := seqM_some h8 ret8 (by rw [vv8, ps8]; exact y0)
  have z7 := seqM_some h7 ret7 (by rw [ps7, vv7]; exact z8)
  have z6 := seqM_some a6 rfl z7
  have z5 := seqM_some a5 rfl z6
  have z4 := seqM_some a4 rfl z5
  have z3 := seqM_some a3 rfl z4
  have z2 := seqM_some h2 ret2 (by rw [ps2, vv2]; exact z3)
  have z1 := seqM_some a1 rfl (by exact z2)
  have hgs : Nat.log2 b = Nat.log2 b := rfl
  refine ⟨_, z1, rfl, an, sF, xF, han, hanb, hg, hx0, hx1, hx2, rfl, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · have hst : Proofs.GcdU64Call.gsteps b an ≤ 2 * Nat.log2 b + 1 := by
      by_cases han0 : an = 0
      · subst han0; rw [Proofs.GcdU64Call.gsteps_zero]; omega
      · have h1 := Proofs.GcdU64Call.gsteps_le an b (by omega)
        have h2 := log2_mono_le an b han0 (by omega)
        omega
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c2 c7 c8 ⊢
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n2 n7 n8 ⊢
    omega
  · simp at w2 w7 w8 ⊢
    omega

end Proofs.InvGcdExec
