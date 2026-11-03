import Proofs.ForLoopB
import Proofs.BellmanFordMath

namespace Proofs.BellmanFordExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)

abbrev M31 : Nat := 2147483648
/-- A cell holding a `long long`. -/
abbrev cs (x : Int) : Cell := ⟨s64, x⟩

/-- The relaxation of edge `e` on the distance list `D`. -/
def relaxL (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D : List Int) : List Int :=
  if D.getD (F.getD e 0) 0 ≠ inf ∧ D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
  then D.set (T.getD e 0) (D.getD (F.getD e 0) 0 + Cc.getD e 0) else D

/-- The contents of the four vectors: `from`, `to`, `cost`, `dist`. -/
def VV (F T : List Nat) (Cc D : List Int) : Nat → List Int := fun k =>
  if k = 0 then F.map (fun x : Nat => (x : Int)) else if k = 1 then T.map (fun x : Nat => (x : Int))
  else if k = 2 then Cc else if k = 3 then D else []

theorem VV_write (F T : List Nat) (Cc D : List Int) (x : List Int) :
    upd (VV F T Cc D) 3 x = VV F T Cc x := by
  funext k
  unfold upd VV
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · by_cases h2 : k = 2
      · subst h2; simp
      · by_cases h3 : k = 3
        · subst h3; simp
        · simp [h0, h1, h2, h3]

theorem VV_get0 (F T : List Nat) (Cc D : List Int) : VV F T Cc D 0 = F.map (fun x : Nat => (x : Int)) := by simp [VV]
theorem VV_get1 (F T : List Nat) (Cc D : List Int) : VV F T Cc D 1 = T.map (fun x : Nat => (x : Int)) := by simp [VV]
theorem VV_get2 (F T : List Nat) (Cc D : List Int) : VV F T Cc D 2 = Cc := by simp [VV]
theorem VV_get3 (F T : List Nat) (Cc D : List Int) : VV F T Cc D 3 = D := by simp [VV]

theorem vec_getM (v : List Nat) (j : Nat) (hj : j < v.length) :
    (v.map (fun x : Nat => (x : Int)))[j]? = some ((v.getD j 0 : Nat) : Int) := by
  simp [List.getElem?_map, hj, List.getD_eq_getElem?_getD]

theorem vec_getI (v : List Int) (j : Nat) (hj : j < v.length) : v[j]? = some (v.getD j 0) := by
  simp [hj, List.getD_eq_getElem?_getD]

theorem vdenM_binary (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (t : Ty) (op : Binary) (l r : NExpr)
    (h : (NExpr.binary t op l r).scalarOnly = false) :
    vdenM mv vv env (.binary t op l r) =
      (vdenM mv vv env l).bind fun a => (vdenM mv vv env r).bind fun b => t.convert (binaryValue op a b) := by
  rw [vdenM, if_neg (by rw [h]; decide)]

theorem rdM_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (k : Nat) (hk : k < mv.nv) (t : Ty)
    (hty : t = mv.ty k) (index : NExpr) (hs : index.scalarOnly = true) (hrc : (NExpr.read t (.local k) index).scalarOnly = false)
    (idx : Nat) (hd : index.denote env = some (idx : Int)) (x : Int) (hx : (vv k)[idx]? = some x)
    (hxv : (mv.ty k).valid x = true) :
    vdenM mv vv env (.read t (.local k) index) = some x := by
  rw [vdenM, if_neg (by rw [hrc]; decide), if_pos ⟨hk, hty, hs⟩, hd, Option.bind_some]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg idx), Int.toNat_natCast, hx, Option.bind_some, if_pos hxv]

/-- The index `(unsigned long long)(variable k)` of an `int` variable holding a small natural number. -/
theorem cidx_den (env : Nat → Ty → Option Int) (k x : Nat) (h : env k i32 = some (x : Int)) (hx : x < M31) :
    (NExpr.cast u64 (.variable i32 k)).denote env = some (x : Int) := by
  rw [den_cast, den_variable, h, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have : x < 2147483648 := hx; omega)


/-! ### The program (variable `nv + c` is the scalar cell `c`: 0 = n, 1 = inf, 2 = m, 3 = rounds, 4 = i, 5 = e, 6 = u, 7 = v, 8 = nd) -/

abbrev rdIdx (nv c : Nat) : NExpr := .cast u64 (.variable i32 (nv + c))
abbrev iU (nv : Nat) : NExpr := .read i32 (.local 0) (rdIdx nv 5)
abbrev iV (nv : Nat) : NExpr := .read i32 (.local 1) (rdIdx nv 5)
abbrev dU (nv : Nat) : NExpr := .read s64 (.local 3) (rdIdx nv 6)
abbrev cE (nv : Nat) : NExpr := .read s64 (.local 2) (rdIdx nv 5)
abbrev dV (nv : Nat) : NExpr := .read s64 (.local 3) (rdIdx nv 7)
abbrev cond1 (nv : Nat) : NExpr := .binary bT .ne (dU nv) (.variable s64 (nv + 1))
abbrev ndE (nv : Nat) : NExpr := .binary s64 .add (dU nv) (cE nv)
abbrev cond2 (nv : Nat) : NExpr := .binary bT .lt (.variable s64 (nv + 8)) (dV nv)
abbrev wrS (nv : Nat) : NStmt := .write (.local 3) s64 (rdIdx nv 7) (.variable s64 (nv + 8))
abbrev Y2 (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (wrS nv)) Sk)) Sk
abbrev BR2 (nv : Nat) : Command := .branch (cond2 nv) (Y2 nv) Sk
abbrev Y1 (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.declare s64 true (ndE nv))) (.sequence (BR2 nv) Sk))) Sk
abbrev BR1 (nv : Nat) : Command := .branch (cond1 nv) (Y1 nv) Sk
abbrev XB (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (iU nv))) (.sequence (.primitive (.declare i32 true (iV nv))) (.sequence (BR1 nv) Sk))
abbrev declM : NStmt := .declare i32 true (.cast i32 (.size (.integer i32) (.local 0)))
abbrev declR (nv : Nat) : NStmt := .declare i32 true (.binary i32 .sub (.variable i32 nv) (.literal i32 1))
abbrev bodyBF (nv : Nat) : Command :=
  .sequence (.primitive declM) (.sequence (.primitive (declR nv))
    (.sequence (forStmtB nv 4 3 (.sequence (forStmtB nv 5 2 (XB nv)) Sk)) Sk))


theorem ne_conv (x y : Int) : bT.convert (binaryValue .ne x y) = some (if x ≠ y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : (x != y) = true := by simp [h]
    simp [binaryValue, this, h, Ty.convert, bT, Ty.valid]

theorem lt_conv (x y : Int) : bT.convert (binaryValue .lt x y) = some (if x < y then 1 else 0) := by
  by_cases h : x < y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]


theorem envs (mv : MV) (P cl : List Cell) (k : Nat) (c : Cell) (hk : cl[k]? = some c) (hv : c.type.valid c.value = true) :
    penvN mv.nv (gS P cl) (mv.nv + k) c.type = some c.value := gSM_env mv.nv P cl k c hk hv

theorem s64_valid_of (x : Int) (h : -9223372036854775808 ≤ x ∧ x < 9223372036854775808) : s64.valid x = true := by
  show Ty.valid ⟨64, true, false⟩ x = true
  simp [Ty.valid]
  omega

theorem i32_valid_nat (x : Nat) (h : x < M31) : i32.valid (x : Int) = true := validN x h

/-- The environment of `[n, inf, m, rounds, i, e, u, v]`. -/
theorem envBF (mv : MV) (P : List Cell) (n m rounds i e u v : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < M31) (hu : u < M31) (hv : v < M31)
    (hinf : s64.valid inf = true) :
    penvN mv.nv (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci u, ci v]) mv.nv i32 = some (n : Int) ∧
    penvN mv.nv (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci u, ci v]) (mv.nv + 1) s64 = some inf ∧
    penvN mv.nv (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci u, ci v]) (mv.nv + 5) i32 = some (e : Int) ∧
    penvN mv.nv (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci u, ci v]) (mv.nv + 6) i32 = some (u : Int) ∧
    penvN mv.nv (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci u, ci v]) (mv.nv + 7) i32 = some (v : Int) :=
  ⟨envs mv P _ 0 (ci n) rfl (i32_valid_nat n hn), envs mv P _ 1 (cs inf) rfl hinf,
   envs mv P _ 5 (ci e) rfl (i32_valid_nat e he), envs mv P _ 6 (ci u) rfl (i32_valid_nat u hu),
   envs mv P _ 7 (ci v) rfl (i32_valid_nat v hv)⟩


theorem pexecM_branch_true (mv : MV) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vv : Nat → List Int) (v : Int)
    (hv : vdenM mv vv (penvN mv.nv ps) c = some v) (hne : v ≠ 0) (r : PRM) (hr : pexecM mv fu y ps vv = some r) :
    pexecM mv fu (.branch c y n) ps vv =
      some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecM]
  simp [hv, hne, hr]

theorem pexecM_branch_false (mv : MV) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vv : Nat → List Int)
    (hv : vdenM mv vv (penvN mv.nv ps) c = some 0) (r : PRM) (hr : pexecM mv fu n ps vv = some r) :
    pexecM mv fu (.branch c y n) ps vv =
      some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecM]
  simp [hv, hr]

/-- The two declarations `int u = from[e]; int v = to[e];` followed by `REST`. -/
theorem decl_uv (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32)
    (F T : List Nat) (Cc D : List Int) (P : List Cell) (n m rounds i e : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (fu : Nat) (REST : Command) (rr : PRM)
    (hrest : pexecM mv fu REST (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0), ci (T.getD e 0)])
      (VV F T Cc D) = some rr) :
    ∃ r : PRM, pexecM mv fu (.sequence (.primitive (.declare i32 true (iU mv.nv))) (.sequence (.primitive (.declare i32 true (iV mv.nv))) REST))
      (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e]) (VV F T Cc D) = some r ∧ r.ret = rr.ret ∧
      r.ps = rr.ps ∧ r.vv = rr.vv ∧ r.cost ≤ 20 + rr.cost ∧ r.need ≤ max (P.length + 40) rr.need ∧ r.wk = rr.wk := by
  have hu : F.getD e 0 < n := by
    have : F.getD e 0 = F[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, he]
    rw [this]; exact hFn _ (List.getElem_mem _)
  have hv : T.getD e 0 < n := by
    have : T.getD e 0 = T[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, he]
    rw [this]; exact hTn _ (List.getElem_mem _)
  have E5 := envs mv P [ci n, cs inf, ci m, ci rounds, ci i, ci e] 5 (ci e) rfl (i32_valid_nat e (by omega))
  have vu := rdM_val mv (VV F T Cc D) (penvN mv.nv (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e])) 0 (by omega) i32
    hty0.symm (rdIdx mv.nv 5) rfl rfl e (cidx_den _ (mv.nv + 5) e E5 (by omega)) ((F.getD e 0 : Nat) : Int)
    (by rw [VV_get0]; exact vec_getM F e (by omega)) (by rw [hty0]; exact i32_valid_nat _ (by omega))
  have d1 := gSM_decl mv P [ci n, cs inf, ci m, ci rounds, ci i, ci e] (VV F T Cc D) i32 _ _ _ vu
    (conv_signed i32 rfl rfl _ (i32_valid_nat _ (by omega)))
  have q1 := (pexecM_prim mv fu (.declare i32 true (iU mv.nv)) _ _).trans d1
  have E5' := envs mv P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0)] 5 (ci e) rfl (i32_valid_nat e (by omega))
  have vv' := rdM_val mv (VV F T Cc D) (penvN mv.nv (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0)])) 1
    (by omega) i32 hty1.symm (rdIdx mv.nv 5) rfl rfl e (cidx_den _ (mv.nv + 5) e E5' (by omega)) ((T.getD e 0 : Nat) : Int)
    (by rw [VV_get1]; exact vec_getM T e (by omega)) (by rw [hty1]; exact i32_valid_nat _ (by omega))
  have d2 := gSM_decl mv P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0)] (VV F T Cc D) i32 _ _ _ vv'
    (conv_signed i32 rfl rfl _ (i32_valid_nat _ (by omega)))
  have q2 := (pexecM_prim mv fu (.declare i32 true (iV mv.nv)) _ _).trans d2
  have q3 := seqM_some q2 rfl hrest
  have q4 := seqM_some q1 rfl q3
  refine ⟨_, q4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega
  · simp

abbrev cC (n m rounds i e u v : Nat) (inf : Int) : List Cell := [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci u, ci v]
abbrev cD (n m rounds i e u v : Nat) (inf nd : Int) : List Cell := [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci u, ci v, cs nd]

/-- `dist[to[e]] = nd;` inside two braces, with `nd < dist[v]` known. -/
theorem y2_exec (mv : MV) (hnv : mv.nv = 4) (hty3 : mv.ty 3 = s64)
    (F T : List Nat) (Cc D : List Int) (P : List Cell) (n m rounds i e u v : Nat) (inf nd : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < M31) (hu : u < M31) (hv : v < n)
    (hinf : s64.valid inf = true) (hnd : s64.valid nd = true) (hDl : D.length = n) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Y2 mv.nv) (gS P (cD n m rounds i e u v inf nd)) (VV F T Cc D) = some r ∧ r.ret = none ∧
      r.ps = gS P (cD n m rounds i e u v inf nd) ∧ r.vv = VV F T Cc (D.set v nd) ∧
      r.cost ≤ 100 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 1 := by
  have E7 := envs mv P (cD n m rounds i e u v inf nd) 7 (ci v) rfl (i32_valid_nat v (by omega))
  have E8 := envs mv P (cD n m rounds i e u v inf nd) 8 (cs nd) rfl hnd
  have hp : vdenM mv (VV F T Cc D) (penvN mv.nv (gS P (cD n m rounds i e u v inf nd))) (rdIdx mv.nv 7) = some (v : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 7) v E7 (by omega)
  have hx : vdenM mv (VV F T Cc D) (penvN mv.nv (gS P (cD n m rounds i e u v inf nd))) (.variable s64 (mv.nv + 8)) = some nd := by
    rw [vdenM_scalar _ _ _ _ rfl]
    rw [den_variable]; exact E8
  have w := pstmtM_write_ok mv (gS P (cD n m rounds i e u v inf nd)) (VV F T Cc D) 3 (by omega) (rdIdx mv.nv 7)
    (.variable s64 (mv.nv + 8)) nd v hx hp (by rw [VV_get3]; omega) (by rw [hty3]; exact hnd)
  rw [hty3, VV_get3, VV_write] at w
  have a1 := (pexecM_prim mv fu (wrS mv.nv) _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (cD n m rounds i e u v inf nd)) (VV F T Cc (D.set v nd)))
  have a3 := pexecM_scope mv fu _ _ _ _ a2
  have tk : (⟨(gS P (cD n m rounds i e u v inf nd)).mem.take (gS P (cD n m rounds i e u v inf nd)).mem.length,
      (gS P (cD n m rounds i e u v inf nd)).bs.take (gS P (cD n m rounds i e u v inf nd)).bs.length⟩ : PS) =
      gS P (cD n m rounds i e u v inf nd) := by simp
  simp only [tk] at a3
  have a4 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (cD n m rounds i e u v inf nd)) (VV F T Cc (D.set v nd)))
  refine ⟨_, a4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


/-- `if (nd < dist[v]) dist[v] = nd;` after `long long nd = dist[u] + cost[e];` inside braces. -/
theorem y1_exec (mv : MV) (hnv : mv.nv = 4) (hty2 : mv.ty 2 = s64) (hty3 : mv.ty 3 = s64)
    (F T : List Nat) (Cc D : List Int) (P : List Cell) (n m rounds i e u v : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m) (hu : u < n) (hv : v < n)
    (hinf : s64.valid inf = true) (hDl : D.length = n) (hCl : Cc.length = m)
    (hDv : ∀ x ∈ D, s64.valid x = true) (hCv : ∀ x ∈ Cc, s64.valid x = true)
    (hsum : s64.valid (D.getD u 0 + Cc.getD e 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Y1 mv.nv) (gS P (cC n m rounds i e u v inf)) (VV F T Cc D) = some r ∧ r.ret = none ∧
      r.ps = gS P (cC n m rounds i e u v inf) ∧
      r.vv = VV F T Cc (if D.getD u 0 + Cc.getD e 0 < D.getD v 0 then D.set v (D.getD u 0 + Cc.getD e 0) else D) ∧
      r.cost ≤ 300 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 1 := by
  have hDu : D.getD u 0 ∈ D := by
    have : D.getD u 0 = D[u]'(by omega) := by simp [List.getD_eq_getElem?_getD, hDl, hu]
    rw [this]; exact List.getElem_mem _
  have hDvv : D.getD v 0 ∈ D := by
    have : D.getD v 0 = D[v]'(by omega) := by simp [List.getD_eq_getElem?_getD, hDl, hv]
    rw [this]; exact List.getElem_mem _
  have hCe : Cc.getD e 0 ∈ Cc := by
    have : Cc.getD e 0 = Cc[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hCl, he]
    rw [this]; exact List.getElem_mem _
  obtain ⟨_, _, E5, E6, E7⟩ := envBF mv P n m rounds i e u v inf hn hm hr hi (by omega) (by omega) (by omega) hinf
  have vdu := rdM_val mv (VV F T Cc D) (penvN mv.nv (gS P (cC n m rounds i e u v inf))) 3 (by omega) s64 hty3.symm
    (rdIdx mv.nv 6) rfl rfl u (cidx_den _ (mv.nv + 6) u E6 (by omega)) (D.getD u 0)
    (by rw [VV_get3]; exact vec_getI D u (by omega)) (by rw [hty3]; exact hDv _ hDu)
  have vce := rdM_val mv (VV F T Cc D) (penvN mv.nv (gS P (cC n m rounds i e u v inf))) 2 (by omega) s64 hty2.symm
    (rdIdx mv.nv 5) rfl rfl e (cidx_den _ (mv.nv + 5) e E5 (by omega)) (Cc.getD e 0)
    (by rw [VV_get2]; exact vec_getI Cc e (by omega)) (by rw [hty2]; exact hCv _ hCe)
  have vnd : vdenM mv (VV F T Cc D) (penvN mv.nv (gS P (cC n m rounds i e u v inf))) (ndE mv.nv) =
      some (D.getD u 0 + Cc.getD e 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdu, vce, Option.bind_some, Option.bind_some]
    exact conv_signed s64 rfl rfl _ hsum
  have d1 := gSM_decl mv P (cC n m rounds i e u v inf) (VV F T Cc D) s64 _ _ _ vnd (conv_signed s64 rfl rfl _ hsum)
  have q1 := (pexecM_prim mv fu (.declare s64 true (ndE mv.nv)) _ _).trans d1
  -- the state after the declaration
  have hpsD : gS P (cC n m rounds i e u v inf ++ [⟨s64, D.getD u 0 + Cc.getD e 0⟩]) =
      gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) := rfl
  rw [hpsD] at q1
  have hnd : s64.valid (D.getD u 0 + Cc.getD e 0) = true := hsum
  have E8 := envs mv P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) 8 (cs (D.getD u 0 + Cc.getD e 0)) rfl hnd
  have E7' := envs mv P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) 7 (ci v) rfl (i32_valid_nat v (by omega))
  have vdv := rdM_val mv (VV F T Cc D) (penvN mv.nv (gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)))) 3
    (by omega) s64 hty3.symm (rdIdx mv.nv 7) rfl rfl v (cidx_den _ (mv.nv + 7) v E7' (by omega)) (D.getD v 0)
    (by rw [VV_get3]; exact vec_getI D v (by omega)) (by rw [hty3]; exact hDv _ hDvv)
  have vc2 : vdenM mv (VV F T Cc D) (penvN mv.nv (gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)))) (cond2 mv.nv) =
      some (if D.getD u 0 + Cc.getD e 0 < D.getD v 0 then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdenM_scalar _ _ _ _ rfl, den_variable, E8, vdv, Option.bind_some, Option.bind_some]
    exact lt_conv _ _
  -- the inner branch
  obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ : ∃ rb : PRM,
      pexecM mv fu (.sequence (BR2 mv.nv) Sk) (gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0))) (VV F T Cc D) = some rb ∧
      rb.ret = none ∧ rb.ps = gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) ∧
      rb.vv = VV F T Cc (if D.getD u 0 + Cc.getD e 0 < D.getD v 0 then D.set v (D.getD u 0 + Cc.getD e 0) else D) ∧
      rb.cost ≤ 150 ∧ rb.need ≤ P.length + 80 ∧ rb.wk ≤ 1 := by
    by_cases hlt : D.getD u 0 + Cc.getD e 0 < D.getD v 0
    · rw [if_pos hlt] at vc2
      obtain ⟨ry, hy, hyret, hyps, hyvv, hyc, hyn, hyw⟩ := y2_exec mv hnv hty3 F T Cc D P n m rounds i e u v inf
        (D.getD u 0 + Cc.getD e 0) hn hm hr hi (by omega) (by omega) hv hinf hnd hDl fu
      have b1 := pexecM_branch_true mv fu (cond2 mv.nv) (Y2 mv.nv) Sk _ _ 1 vc2 (by decide) ry hy
      have b2 := seqM_some b1 hyret (pexecM_skip mv fu ry.ps ry.vv)
      have hl : ry.ps.mem.length + ry.ps.bs.length = P.length + 18 := by rw [hyps]; simp [gS_size]
      refine ⟨_, b2, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact hyps
      · rw [if_pos hlt]; exact hyvv
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hyc ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hyn ⊢; omega
      · simpa using hyw
    · rw [if_neg hlt] at vc2
      have b1 := pexecM_branch_false mv fu (cond2 mv.nv) (Y2 mv.nv) Sk _ _ vc2 _ (pexecM_skip mv fu _ _)
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · rw [if_neg hlt]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
      · simp
  have q2 := seqM_some q1 rfl hrb
  have q3 := pexecM_scope mv fu _ _ _ _ q2
  have tk := gS_takeC P (cC n m rounds i e u v inf) (cC n m rounds i e u v inf) [cs (D.getD u 0 + Cc.getD e 0)] rfl
  rw [hrbps] at q3
  have hpsD' : gS P (cD n m rounds i e u v inf (D.getD u 0 + Cc.getD e 0)) =
      gS P (cC n m rounds i e u v inf ++ [cs (D.getD u 0 + Cc.getD e 0)]) := rfl
  rw [hpsD'] at q3
  simp only [tk] at q3
  have q4 := seqM_some q3 hrbret (pexecM_skip mv fu _ _)
  refine ⟨_, q4, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact hrbvv
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
  · simp at *; omega


theorem getD_mem (D : List Int) (j : Nat) (h : j < D.length) : D.getD j 0 ∈ D := by
  have : D.getD j 0 = D[j] := by simp [List.getD_eq_getElem?_getD, h]
  rw [this]; exact List.getElem_mem _

theorem relaxL_eq (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D : List Int) :
    relaxL inf F T Cc e D =
      if D.getD (F.getD e 0) 0 ≠ inf then
        (if D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
         then D.set (T.getD e 0) (D.getD (F.getD e 0) 0 + Cc.getD e 0) else D)
      else D := by
  unfold relaxL
  by_cases h1 : D.getD (F.getD e 0) 0 ≠ inf
  · rw [if_pos h1]
    by_cases h2 : D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
    · rw [if_pos ⟨h1, h2⟩, if_pos h2]
    · rw [if_neg (fun h => h2 h.2), if_neg h2]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

/-- `if (dist[u] != inf) { ... }` followed by the empty statement. -/
theorem br1_exec (mv : MV) (hnv : mv.nv = 4) (hty2 : mv.ty 2 = s64) (hty3 : mv.ty 3 = s64)
    (F T : List Nat) (Cc D : List Int) (P : List Cell) (n m rounds i e : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m)
    (hu : F.getD e 0 < n) (hv : T.getD e 0 < n)
    (hinf : s64.valid inf = true) (hDl : D.length = n) (hCl : Cc.length = m)
    (hDv : ∀ x ∈ D, s64.valid x = true) (hCv : ∀ x ∈ Cc, s64.valid x = true)
    (hsum : s64.valid (D.getD (F.getD e 0) 0 + Cc.getD e 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (.sequence (BR1 mv.nv) Sk)
      (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf)) (VV F T Cc D) = some r ∧ r.ret = none ∧
      r.ps = gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf) ∧ r.vv = VV F T Cc (relaxL inf F T Cc e D) ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 1 := by
  have hDu : D.getD (F.getD e 0) 0 ∈ D := getD_mem D _ (by omega)
  obtain ⟨_, E1, E5, E6, E7⟩ := envBF mv P n m rounds i e (F.getD e 0) (T.getD e 0) inf hn hm hr hi (by omega) (by omega)
    (by omega) hinf
  have vdu := rdM_val mv (VV F T Cc D) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) 3 (by omega) s64
    hty3.symm (rdIdx mv.nv 6) rfl rfl (F.getD e 0) (cidx_den _ (mv.nv + 6) _ E6 (by omega)) (D.getD (F.getD e 0) 0)
    (by rw [VV_get3]; exact vec_getI D _ (by omega)) (by rw [hty3]; exact hDv _ hDu)
  have vc1 : vdenM mv (VV F T Cc D) (penvN mv.nv (gS P (cC n m rounds i e (F.getD e 0) (T.getD e 0) inf))) (cond1 mv.nv) =
      some (if D.getD (F.getD e 0) 0 ≠ inf then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vdu, vdenM_scalar _ _ _ _ rfl, den_variable, E1, Option.bind_some, Option.bind_some]
    exact ne_conv _ _
  rw [relaxL_eq]
  by_cases hd : D.getD (F.getD e 0) 0 ≠ inf
  · rw [if_pos hd] at vc1
    obtain ⟨ry, hy, hyret, hyps, hyvv, hyc, hyn, hyw⟩ := y1_exec mv hnv hty2 hty3 F T Cc D P n m rounds i e (F.getD e 0)
      (T.getD e 0) inf hn hm hr hi he hu hv hinf hDl hCl hDv hCv hsum fu
    have b1 := pexecM_branch_true mv fu (cond1 mv.nv) (Y1 mv.nv) Sk _ _ 1 vc1 (by decide) ry hy
    have b2 := seqM_some b1 hyret (pexecM_skip mv fu ry.ps ry.vv)
    have hl : ry.ps.mem.length + ry.ps.bs.length = P.length + 16 := by rw [hyps]; simp [gS_size]
    refine ⟨_, b2, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact hyps
    · rw [if_pos hd]; exact hyvv
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hyc ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hyn ⊢; omega
    · simpa using hyw
  · rw [if_neg hd] at vc1
    have b1 := pexecM_branch_false mv fu (cond1 mv.nv) (Y1 mv.nv) Sk _ _ vc1 _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [if_neg hd]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp


/-- The loop body: `int u = from[e]; int v = to[e]; if (dist[u] != inf) {...}`. -/
theorem e_body (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (F T : List Nat) (Cc D : List Int) (P : List Cell) (n m rounds i e : Nat) (inf : Int)
    (hn : n < M31) (hm : m < M31) (hr : rounds < M31) (hi : i < M31) (he : e < m)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D.length = n)
    (hCv : ∀ x ∈ Cc, s64.valid x = true) (hDv : ∀ x ∈ D, s64.valid x = true)
    (hsum : s64.valid (D.getD (F.getD e 0) 0 + Cc.getD e 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (XB mv.nv) (gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e]) (VV F T Cc D) = some r ∧
      r.ret = none ∧
      r.ps = gS P [ci n, cs inf, ci m, ci rounds, ci i, ci e, ci (F.getD e 0), ci (T.getD e 0)] ∧
      r.vv = VV F T Cc (relaxL inf F T Cc e D) ∧ r.cost ≤ 450 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 1 := by
  have hu : F.getD e 0 < n := by
    have : F.getD e 0 = F[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, he]
    rw [this]; exact hFn _ (List.getElem_mem _)
  have hv : T.getD e 0 < n := by
    have : T.getD e 0 = T[e]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, he]
    rw [this]; exact hTn _ (List.getElem_mem _)
  obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ := br1_exec mv hnv hty2 hty3 F T Cc D P n m rounds i e inf hn hm hr hi he
    hu hv hinf hDl hCl hDv hCv hsum fu
  obtain ⟨r, hrr, hret, hps, hvv, hc, hnd, hw⟩ := decl_uv mv hnv hty0 hty1 F T Cc D P n m rounds i e inf hn hm hr hi he hinf
    hFl hTl hFn hTn fu (.sequence (BR1 mv.nv) Sk) rb hrb
  refine ⟨r, hrr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hret]; exact hrbret
  · rw [hps]; exact hrbps
  · rw [hvv]; exact hrbvv
  · omega
  · omega
  · omega


/-- The distance list after relaxing the edges `0 .. t-1` in order. -/
def passPrefix (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (D0 : List Int) : List Int :=
  (List.range t).foldl (fun d e => relaxL inf F T Cc e d) D0

theorem passPrefix_zero (inf : Int) (F T : List Nat) (Cc : List Int) (D0 : List Int) :
    passPrefix inf F T Cc 0 D0 = D0 := rfl

theorem passPrefix_succ (inf : Int) (F T : List Nat) (Cc : List Int) (t : Nat) (D0 : List Int) :
    passPrefix inf F T Cc (t + 1) D0 = relaxL inf F T Cc t (passPrefix inf F T Cc t D0) := by
  unfold passPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem relaxL_length (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D : List Int) :
    (relaxL inf F T Cc e D).length = D.length := by
  unfold relaxL
  split <;> simp

theorem passPrefix_length (inf : Int) (F T : List Nat) (Cc : List Int) (D0 : List Int) :
    ∀ t, (passPrefix inf F T Cc t D0).length = D0.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [passPrefix_succ, relaxL_length, ih]

theorem relaxL_bound (inf Cb L : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D : List Int)
    (hCb : -Cb ≤ Cc.getD e 0) (hu : F.getD e 0 < D.length) (hv : T.getD e 0 < D.length)
    (hD : ∀ x ∈ D, L ≤ x ∧ x ≤ inf) (hCb0 : 0 ≤ Cb) : ∀ x ∈ relaxL inf F T Cc e D, L - Cb ≤ x ∧ x ≤ inf := by
  intro x hx
  have hdu := hD _ (getD_mem D _ hu)
  have hdv := hD _ (getD_mem D _ hv)
  unfold relaxL at hx
  by_cases h : D.getD (F.getD e 0) 0 ≠ inf ∧ D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
  · rw [if_pos h] at hx
    rcases List.mem_or_eq_of_mem_set hx with h1 | h1
    · have := hD _ h1; omega
    · omega
  · rw [if_neg h] at hx
    have := hD _ hx; omega

theorem passPrefix_bound (inf Cb lo : Int) (F T : List Nat) (Cc : List Int) (D0 : List Int) (n m : Nat)
    (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m) (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n)
    (hDl : D0.length = n) (hCb0 : 0 ≤ Cb) (hCb : ∀ x ∈ Cc, -Cb ≤ x ∧ x ≤ Cb) (hD0 : ∀ x ∈ D0, lo ≤ x ∧ x ≤ inf) :
    ∀ t, t ≤ m → ∀ x ∈ passPrefix inf F T Cc t D0, lo - (t : Int) * Cb ≤ x ∧ x ≤ inf := by
  intro t
  induction t with
  | zero => intro _ x hx; simpa [passPrefix_zero] using hD0 x hx
  | succ t ih =>
    intro ht x hx
    rw [passPrefix_succ] at hx
    have hu : F.getD t 0 < n := by
      have : F.getD t 0 = F[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, show t < m by omega]
      rw [this]; exact hFn _ (List.getElem_mem _)
    have hv : T.getD t 0 < n := by
      have : T.getD t 0 = T[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, show t < m by omega]
      rw [this]; exact hTn _ (List.getElem_mem _)
    have hcm : Cc.getD t 0 ∈ Cc := getD_mem Cc t (by omega)
    have := relaxL_bound inf Cb (lo - (t : Int) * Cb) F T Cc t (passPrefix inf F T Cc t D0) (by have := hCb _ hcm; omega)
      (by rw [passPrefix_length, hDl]; exact hu) (by rw [passPrefix_length, hDl]; exact hv) (ih (by omega)) hCb0 x hx
    rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
    omega



/-- All bounds that make every sum in a pass fit in a `long long`. -/
structure Bnd (inf Cb lo : Int) (m : Nat) (Cc D0 : List Int) : Prop where
  cb0 : 0 ≤ Cb
  cbH : Cb ≤ 2305843009213693952
  infH : inf ≤ 4611686018427387904
  loH : -4611686018427387904 ≤ lo - (m : Int) * Cb
  cc : ∀ x ∈ Cc, -Cb ≤ x ∧ x ≤ Cb
  d0 : ∀ x ∈ D0, lo ≤ x ∧ x ≤ inf

theorem step_valid (inf Cb lo : Int) (m t : Nat) (Cc D0 : List Int) (b : Bnd inf Cb lo m Cc D0) (htm : t ≤ m)
    (D : List Int) (hD : ∀ x ∈ D, lo - (t : Int) * Cb ≤ x ∧ x ≤ inf) :
    (∀ x ∈ D, s64.valid x = true) ∧ (∀ x ∈ Cc, s64.valid x = true) ∧
      ∀ x ∈ D, ∀ c ∈ Cc, s64.valid (x + c) = true := by
  have hmul : (t : Int) * Cb ≤ (m : Int) * Cb := Int.mul_le_mul_of_nonneg_right (by omega) b.cb0
  have b0 := b.cb0; have b1 := b.cbH; have b2 := b.infH; have b3 := b.loH
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have := hD x hx
    exact s64_valid_of x (by omega)
  · intro x hx
    have := b.cc x hx
    exact s64_valid_of x (by omega)
  · intro x hx c hc
    have h1 := hD x hx
    have h2 := b.cc c hc
    exact s64_valid_of _ (by omega)


/-- The inner loop `for (int e = 0; e < m; e++) {...}`: one pass over the edges. -/
theorem e_loop (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (F T : List Nat) (Cc D0 : List Int) (P : List Cell) (n m rounds i : Nat) (inf Cb lo : Int)
    (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hr : rounds < M31) (hi : i < M31)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) (b : Bnd inf Cb lo m Cc D0) (fu : Nat)
    (hfu : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 5 2 (XB mv.nv)) (gS P [ci n, cs inf, ci m, ci rounds, ci i]) (VV F T Cc D0) =
      some res ∧ res.ps = gS P [ci n, cs inf, ci m, ci rounds, ci i] ∧
      res.vv = VV F T Cc (passPrefix inf F T Cc m D0) ∧ res.ret = none ∧ res.cost ≤ 470 * m + 30 ∧
      res.need ≤ P.length + 100 ∧ res.wk ≤ m := by
  have hm' : m < 2147483647 := hm2
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 5 2 m (by omega) hm' (XB mv.nv)
    (fun t vv C => vv = VV F T Cc (passPrefix inf F T Cc t D0) ∧ C = [ci n, cs inf, ci m, ci rounds, ci i]) 450 100 1 0
    (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hbd := passPrefix_bound inf Cb lo F T Cc D0 n m hFl hTl hCl hFn hTn hDl b.cb0 b.cc b.d0 t (by omega)
      have hv := step_valid inf Cb lo m t Cc D0 b (by omega) _ hbd
      have hu : F.getD t 0 < n := by
        have : F.getD t 0 = F[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, ht]
        rw [this]; exact hFn _ (List.getElem_mem _)
      have hDlt : (passPrefix inf F T Cc t D0).length = n := by rw [passPrefix_length, hDl]
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := e_body mv hnv hty0 hty1 hty2 hty3 F T Cc (passPrefix inf F T Cc t D0) P n m
        rounds i t inf hn hm hr hi ht hinf hFl hTl hCl hFn hTn hDlt hv.2.1 hv.1
        (hv.2.2 _ (getD_mem _ _ (by omega)) _ (getD_mem Cc t (by omega))) fu
      refine ⟨r, [ci (F.getD t 0), ci (T.getD t 0)], [ci n, cs inf, ci m, ci rounds, ci i], hr, hret, hps, rfl, rfl,
        ⟨?_, rfl⟩, hc, ?_, hwk⟩
      · rw [hvv, passPrefix_succ]
      · omega)
    (VV F T Cc D0) [ci n, cs inf, ci m, ci rounds, ci i] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI
  subst hC
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega


/-- One full pass over all `m` edges. -/
def passL (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (D : List Int) : List Int := passPrefix inf F T Cc m D

/-- `r` full passes. -/
def roundsL (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) : Nat → List Int → List Int
  | 0, D => D
  | r + 1, D => passL inf F T Cc m (roundsL inf F T Cc m r D)

theorem roundsL_length (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (D0 : List Int) :
    ∀ r, (roundsL inf F T Cc m r D0).length = D0.length := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih => simp only [roundsL, passL]; rw [passPrefix_length, ih]

theorem roundsL_bound (inf Cb lo : Int) (F T : List Nat) (Cc : List Int) (D0 : List Int) (n m : Nat)
    (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m) (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n)
    (hDl : D0.length = n) (hCb0 : 0 ≤ Cb) (hCb : ∀ x ∈ Cc, -Cb ≤ x ∧ x ≤ Cb) (hD0 : ∀ x ∈ D0, lo ≤ x ∧ x ≤ inf) :
    ∀ r, ∀ x ∈ roundsL inf F T Cc m r D0, lo - (r : Int) * ((m : Int) * Cb) ≤ x ∧ x ≤ inf := by
  intro r
  induction r with
  | zero => intro x hx; simpa [roundsL] using hD0 x hx
  | succ r ih =>
    intro x hx
    simp only [roundsL, passL] at hx
    have := passPrefix_bound inf Cb (lo - (r : Int) * ((m : Int) * Cb)) F T Cc (roundsL inf F T Cc m r D0) n m hFl hTl hCl hFn
      hTn (by rw [roundsL_length, hDl]) hCb0 hCb ih m (Nat.le_refl _) x hx
    rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
    omega

/-- One round of the outer loop. -/
theorem i_body (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (F T : List Nat) (Cc D : List Int) (P : List Cell) (n m rounds i : Nat) (inf Cb lo : Int)
    (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hr : rounds < M31) (hi : i < M31)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D.length = n) (b : Bnd inf Cb lo m Cc D) (fu : Nat)
    (hfu : m + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (.sequence (forStmtB mv.nv 5 2 (XB mv.nv)) Sk) (gS P [ci n, cs inf, ci m, ci rounds, ci i])
      (VV F T Cc D) = some r ∧ r.ret = none ∧ r.ps = gS P [ci n, cs inf, ci m, ci rounds, ci i] ∧
      r.vv = VV F T Cc (passL inf F T Cc m D) ∧ r.cost ≤ 470 * m + 30 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ m := by
  obtain ⟨res, hres, hps, hvv, hret, hc, hnd, hw⟩ := e_loop mv hnv hty0 hty1 hty2 hty3 F T Cc D P n m rounds i inf Cb lo hn hm hm2 hr
    hi hinf hFl hTl hCl hFn hTn hDl b fu hfu
  have q := seqM_some hres hret (pexecM_skip mv fu res.ps res.vv)
  refine ⟨_, q, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact hps
  · exact hvv
  · simpa using hc
  · simp [gS_size] at hnd hps ⊢; rw [hps]; simp [gS_size]; omega
  · simpa using hw


/-- The outer loop `for (int i = 0; i < rounds; i++) {...}`. -/
theorem i_loop (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (F T : List Nat) (Cc D0 : List Int) (P : List Cell) (n m rounds : Nat) (inf Cb lo : Int)
    (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hr : rounds < 2147483647)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) (b : Bnd inf Cb lo m Cc D0)
    (hloR : -4611686018427387904 ≤ lo - (rounds : Int) * ((m : Int) * Cb)) (fu : Nat) (hfu : m + 1 + rounds + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 4 3 (.sequence (forStmtB mv.nv 5 2 (XB mv.nv)) Sk))
      (gS P [ci n, cs inf, ci m, ci rounds]) (VV F T Cc D0) = some res ∧ res.ps = gS P [ci n, cs inf, ci m, ci rounds] ∧
      res.vv = VV F T Cc (roundsL inf F T Cc m rounds D0) ∧ res.ret = none ∧
      res.cost ≤ (470 * m + 50) * rounds + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ m * rounds := by
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 4 3 rounds (by omega) hr
    (.sequence (forStmtB mv.nv 5 2 (XB mv.nv)) Sk)
    (fun t vv C => vv = VV F T Cc (roundsL inf F T Cc m t D0) ∧ C = [ci n, cs inf, ci m, ci rounds]) (470 * m + 30) 100 m (m + 1)
    (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ hfu'
      subst hvv; subst hC
      have hK : 0 ≤ (m : Int) * Cb := Int.mul_nonneg (Int.natCast_nonneg m) b.cb0
      have hmul : ((t : Int) + 1) * ((m : Int) * Cb) ≤ (rounds : Int) * ((m : Int) * Cb) :=
        Int.mul_le_mul_of_nonneg_right (by omega) hK
      have hmul' : ((t : Int) + 1) * ((m : Int) * Cb) = (t : Int) * ((m : Int) * Cb) + (m : Int) * Cb := by
        rw [Int.add_mul, Int.one_mul]
      have bt : Bnd inf Cb (lo - (t : Int) * ((m : Int) * Cb)) m Cc (roundsL inf F T Cc m t D0) :=
        ⟨b.cb0, b.cbH, b.infH, by omega, b.cc, roundsL_bound inf Cb lo F T Cc D0 n m hFl hTl hCl hFn hTn hDl b.cb0 b.cc b.d0 t⟩
      have hlen : (roundsL inf F T Cc m t D0).length = n := by rw [roundsL_length, hDl]
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := i_body mv hnv hty0 hty1 hty2 hty3 F T Cc (roundsL inf F T Cc m t D0) P n m rounds t
        inf Cb (lo - (t : Int) * ((m : Int) * Cb)) hn hm hm2 (by show rounds < 2147483648; omega) (by show t < 2147483648; omega)
        hinf hFl hTl hCl hFn hTn hlen bt fu (by omega)
      refine ⟨r, [], [ci n, cs inf, ci m, ci rounds], hr, hret, hps, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      rw [hvv]; rfl)
    (VV F T Cc D0) [ci n, cs inf, ci m, ci rounds] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI
  subst hC
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega


theorem size_val0 (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = i32) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (hn : (vv 0).length < 2147483648) :
    vdenM mv vv env (.cast i32 (.size (.integer i32) (.local 0))) = some ((vv 0).length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer i32) (.local 0))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer i32) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer i32) (.local 0)) = some ((vv 0).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨by omega, hty0.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

/-- The whole body of `bellman_ford` (for `n ≥ 1`). -/
theorem body_exec (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (F T : List Nat) (Cc D0 : List Int) (P : List Cell) (n m : Nat) (inf Cb lo : Int)
    (hn : n < M31) (hn1 : 1 ≤ n) (hm2 : m < 2147483647)
    (hinf : s64.valid inf = true) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) (b : Bnd inf Cb lo m Cc D0)
    (hloR : -4611686018427387904 ≤ lo - ((n - 1 : Nat) : Int) * ((m : Int) * Cb)) (fu : Nat)
    (hfu : m + 1 + (n - 1) + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyBF mv.nv) (gS P [ci n, cs inf]) (VV F T Cc D0) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, cs inf, ci m, ci (n - 1)] ∧ r.vv = VV F T Cc (roundsL inf F T Cc m (n - 1) D0) ∧
      r.cost ≤ (470 * m + 50) * (n - 1) + 100 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ m * (n - 1) := by
  have hm31 : m < M31 := by
    show m < 2147483648
    omega
  have hlen0 : (VV F T Cc D0 0).length = m := by rw [VV_get0]; simp [hFl]
  have hsz := size_val0 mv hnv hty0 (VV F T Cc D0) (penvN mv.nv (gS P [ci n, cs inf])) (by rw [hlen0]; exact hm31)
  rw [hlen0] at hsz
  have d1 := gSM_decl mv P [ci n, cs inf] (VV F T Cc D0) i32 _ _ _ hsz (conv_signed i32 rfl rfl _ (validN m hm31))
  have q1 := (pexecM_prim mv fu declM _ _).trans d1
  have hE0 : penvN mv.nv (gS P [ci n, cs inf, ci m]) mv.nv i32 = some (n : Int) :=
    envs mv P [ci n, cs inf, ci m] 0 (ci n) rfl (validN n hn)
  have hsub : vdenM mv (VV F T Cc D0) (penvN mv.nv (gS P [ci n, cs inf, ci m])) (.binary i32 .sub (.variable i32 mv.nv) (.literal i32 1)) =
      some ((n - 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, hE0, Option.bind_some, den_literal,
      if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
    have : binaryValue .sub (n : Int) 1 = ((n - 1 : Nat) : Int) := by
      show (n : Int) - 1 = _
      omega
    rw [this]
    exact conv_signed i32 rfl rfl _ (validN _ (by have : n < 2147483648 := hn; omega))
  have d2 := gSM_decl mv P [ci n, cs inf, ci m] (VV F T Cc D0) i32 _ _ _ hsub
    (conv_signed i32 rfl rfl _ (validN _ (by have : n < 2147483648 := hn; omega)))
  have q2 := (pexecM_prim mv fu (declR mv.nv) _ _).trans d2
  have hn31 : n - 1 < 2147483647 := by have : n < 2147483648 := hn; omega
  obtain ⟨rl, hrl, hrlps, hrlvv, hrlret, hrlc, hrln, hrlw⟩ := i_loop mv hnv hty0 hty1 hty2 hty3 F T Cc D0 P n m (n - 1) inf Cb lo hn
    hm31 hm2 hn31 hinf hFl hTl hCl hFn hTn hDl b hloR fu hfu
  have q3 := seqM_some hrl hrlret (pexecM_skip mv fu rl.ps rl.vv)
  have q4 := seqM_some q2 rfl q3
  have q5 := seqM_some q1 rfl q4
  refine ⟨_, q5, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrlps
  · exact hrlvv
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrlc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrln ⊢
    have : rl.ps.mem.length + rl.ps.bs.length = P.length + 8 := by rw [hrlps]; simp [gS_size]
    omega
  · simpa using hrlw

end Proofs.BellmanFordExec
