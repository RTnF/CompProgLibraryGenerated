import Proofs.ForLoopB
import Proofs.BellmanFordExec
import Proofs.FenwickBuildMath
import Proofs.Generated.FenwickTree

namespace Proofs.FenwickTreeExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB Proofs.FenwickMath Proofs.FenwickBuildMath
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den envs M31 vdenM_binary vec_getM vec_getI pexecM_branch_true pexecM_branch_false
  i32_valid_nat s64_valid_of)

/-! ### `FenwickTree<long long>::FenwickTree(const std::vector<long long> &)` (nv = 2)
Vectors: 0 = `tree` (writable), 1 = `v`. Cells: 0 = n, 1 = k, then in the second loop 2 = i, 3 = j. -/

abbrev ixk (nv : Nat) : NExpr := .cast u64 (.binary i32 .add (.variable i32 (nv + 1)) (.literal i32 1))
abbrev rdk (nv : Nat) : NExpr := .read s64 (.local 1) (.cast u64 (.variable i32 (nv + 1)))
abbrev wr1S (nv : Nat) : NStmt := .write (.local 0) s64 (ixk nv) (rdk nv)
abbrev B1 (nv : Nat) : Command := .sequence (.primitive (wr1S nv)) Sk
abbrev iDecl (nv : Nat) : NStmt := .declare i32 true (.binary i32 .add (.variable i32 (nv + 1)) (.literal i32 1))
abbrev lowV (nv c : Nat) : NExpr := .cast i32 (.binary u32 .band (.cast u32 (.variable i32 (nv + c)))
  (.binary u32 .sub (.literal u32 0) (.cast u32 (.variable i32 (nv + c)))))
abbrev jDecl (nv : Nat) : NStmt := .declare i32 true (.binary i32 .add (.variable i32 (nv + 2)) (lowV nv 2))
abbrev cond2 (nv : Nat) : NExpr := .binary bT .le (.variable i32 (nv + 3)) (.variable i32 nv)
abbrev rdJ (nv : Nat) : NExpr := .read s64 (.local 0) (.cast u64 (.variable i32 (nv + 3)))
abbrev rdI (nv : Nat) : NExpr := .read s64 (.local 0) (.cast u64 (.variable i32 (nv + 2)))
abbrev wr2S (nv : Nat) : NStmt := .write (.local 0) s64 (.cast u64 (.variable i32 (nv + 3))) (.binary s64 .add (rdJ nv) (rdI nv))
abbrev Y2 (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (wr2S nv)) Sk)) Sk
abbrev B2 (nv : Nat) : Command :=
  .sequence (.primitive (iDecl nv)) (.sequence (.primitive (jDecl nv)) (.sequence (.branch (cond2 nv) (Y2 nv) Sk) Sk))
abbrev declN : NStmt := .declare i32 true (.cast i32 (.size (.integer s64) (.local 1)))
abbrev progN (nv : Nat) : Command :=
  .sequence (.primitive declN) (.sequence (forStmtB nv 1 0 (B1 nv)) (.sequence (forStmtB nv 1 0 (B2 nv)) Sk))

theorem body_eqN : Proofs.FenwickTreeInstance.FenwickTree_long_long_new2.body = progN 2 := rfl

/-- The contents of the vectors `tree`, `v`. -/
def VFT (T V : List Int) : Nat → List Int := fun k => if k = 0 then T else if k = 1 then V else []

theorem VFT_get0 (T V : List Int) : VFT T V 0 = T := by simp [VFT]
theorem VFT_get1 (T V : List Int) : VFT T V 1 = V := by simp [VFT]

theorem VFT_write0 (T V : List Int) (p : Nat) (x : Int) :
    upd (VFT T V) 0 ((VFT T V 0).set p x) = VFT (T.set p x) V := by
  funext k
  unfold upd VFT
  by_cases h0 : k = 0
  · subst h0; simp
  · simp [h0]

theorem succ_denF (env : Nat → Ty → Option Int) (k x : Nat) (h : env k i32 = some (x : Int)) (hx : x + 1 < 2147483648) :
    (NExpr.cast u64 (.binary i32 .add (.variable i32 k) (.literal i32 1))).denote env = some ((x + 1 : Nat) : Int) := by
  have one : (NExpr.literal i32 1).denote env = some 1 := by
    rw [den_literal, if_pos (show i32.valid 1 = true from rfl)]
  rw [den_cast, den_binary, den_variable, h, Option.bind_some, one, Option.bind_some]
  have e : binaryValue .add (x : Int) 1 = ((x + 1 : Nat) : Int) := by
    show (x : Int) + 1 = _; push_cast; rfl
  rw [e, conv_signed i32 rfl rfl _ (validN _ hx), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)

/-- The state of `tree` after `t` iterations of the copy loop. -/
def P1 (T0 V : List Int) (t : Nat) (X : List Int) : Prop :=
  X.length = T0.length ∧ ∀ q, q < X.length → X[q]? = (if q = 0 then T0[0]? else if q ≤ t then V[q - 1]? else T0[q]?)

theorem P1_zero (T0 V : List Int) : P1 T0 V 0 T0 := by
  refine ⟨rfl, ?_⟩
  intro q hq
  by_cases h : q = 0
  · subst h; simp
  · simp [h]

theorem P1_step (T0 V X : List Int) (t : Nat) (h : P1 T0 V t X) (ht : t < V.length) (hX : t + 1 < X.length) :
    P1 T0 V (t + 1) (X.set (t + 1) (V.getD t 0)) := by
  refine ⟨by simp [h.1], ?_⟩
  intro q hq
  by_cases hq1 : q = t + 1
  · subst hq1
    rw [List.getElem?_set_self hX]
    simp [List.getD_eq_getElem?_getD, ht]
  · rw [List.getElem?_set_ne (Ne.symm hq1)]
    have hq' : q < X.length := by simpa using hq
    rw [h.2 q hq']
    by_cases h0 : q = 0
    · simp [h0]
    · have : (q ≤ t + 1) ↔ (q ≤ t) := by omega
      simp [h0, this]

set_option maxHeartbeats 4000000 in
/-- `tree[k + 1] = v[k];` -/
theorem b1_exec (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (fu : Nat) (P : List Cell)
    (X V : List Int) (n t : Nat) (hn : n < 2147483647) (ht : t < n) (hV : V.length = n) (hX : X.length = n + 1)
    (hVv : ∀ y ∈ V, s64.valid y = true) :
    ∃ r : PRM, pexecM mv fu (B1 mv.nv) (gS P [ci n, ci t]) (VFT X V) = some r ∧ r.ret = none ∧ r.ps = gS P [ci n, ci t] ∧
      r.vv = VFT (X.set (t + 1) (V.getD t 0)) V ∧ r.cost ≤ 100 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 1 := by
  have E1 := envs mv P [ci n, ci t] 1 (ci t) rfl (validN t (by omega))
  have hp : vdenM mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t])) (ixk mv.nv) = some ((t + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact succ_denF _ (mv.nv + 1) t E1 (by omega)
  have hmem : V.getD t 0 ∈ V := by
    have : V.getD t 0 = V[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hV, ht]
    rw [this]; exact List.getElem_mem _
  have hx := rdM_val mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t])) 1 (by omega) s64 hty1.symm
    (.cast u64 (.variable i32 (mv.nv + 1))) rfl rfl t (cidx_den _ (mv.nv + 1) t E1 (show t < 2147483648 by omega)) (V.getD t 0)
    (by rw [VFT_get1]; exact vec_getI V t (by omega)) (by rw [hty1]; exact hVv _ hmem)
  have wr := pstmtM_write_ok mv (gS P [ci n, ci t]) (VFT X V) 0 (by omega) _ _ (V.getD t 0) (t + 1) hx hp
    (by rw [VFT_get0]; omega) (by rw [hty0]; exact hVv _ hmem)
  rw [hty0, VFT_write0] at wr
  have w1 := (pexecM_prim mv fu (wr1S mv.nv) _ _).trans wr
  have w2 := seqM_some w1 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, w2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


theorem le_conv (x y : Int) : bT.convert (binaryValue .le x y) = some (if x ≤ y then 1 else 0) := by
  by_cases h : x ≤ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem inc_den (env : Nat → Ty → Option Int) (k x : Nat) (h : env k i32 = some (x : Int)) (hx : x + 1 < 2147483648) :
    (NExpr.binary i32 .add (.variable i32 k) (.literal i32 1)).denote env = some ((x + 1 : Nat) : Int) := by
  have one : (NExpr.literal i32 1).denote env = some 1 := by
    rw [den_literal, if_pos (show i32.valid 1 = true from rfl)]
  rw [den_binary, den_variable, h, Option.bind_some, one, Option.bind_some]
  have e : binaryValue .add (x : Int) 1 = ((x + 1 : Nat) : Int) := by
    show (x : Int) + 1 = _; push_cast; rfl
  rw [e]
  exact conv_signed i32 rfl rfl _ (validN _ hx)

theorem lowV_den (env : Nat → Ty → Option Int) (nv c k : Nat) (h0 : 0 < k) (h1 : k < 2147483648)
    (e : env (nv + c) i32 = some (k : Int)) : (lowV nv c).denote env = some (lowb k : Int) := by
  have hk32 : (k : Int) % 4294967296 = (k : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  have c1 : (NExpr.cast u32 (.variable i32 (nv + c))).denote env = some (k : Int) := by
    rw [den_cast, den_variable, e, Option.bind_some, convert_u32, hk32]
  have c0 : (NExpr.literal u32 0).denote env = some 0 := by
    rw [den_literal, if_pos (show u32.valid 0 = true from rfl)]
  have c2 : (NExpr.binary u32 .sub (.literal u32 0) (.cast u32 (.variable i32 (nv + c)))).denote env =
      some (4294967296 - (k : Int)) := by
    rw [den_binary, c0, c1]
    simp only [Option.bind_some, convert_u32]
    have : binaryValue .sub 0 (k : Int) = -(k : Int) := by show 0 - (k : Int) = _; omega
    rw [this]
    congr 1
    omega
  have hl := lowb_pos k h0
  have hl' := lowb_le k h0
  have c3 : (NExpr.binary u32 .band (.cast u32 (.variable i32 (nv + c)))
      (.binary u32 .sub (.literal u32 0) (.cast u32 (.variable i32 (nv + c))))).denote env = some (lowb k : Int) := by
    rw [den_binary, c1, c2]
    simp only [Option.bind_some, convert_u32]
    have hband : binaryValue .band (k : Int) (4294967296 - (k : Int)) = (lowb k : Int) := by
      show (((k : Int).toNat &&& (4294967296 - (k : Int)).toNat : Nat) : Int) = _
      have a1 : (k : Int).toNat = k := by omega
      have a2 : (4294967296 - (k : Int)).toNat = 2^32 - k := by omega
      rw [a1, a2, lowbit_eval k h0 h1]
    rw [hband]
    congr 1
    omega
  rw [den_cast, c3, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ (by omega))

/-- `tree[j] = tree[j] + tree[i];` inside braces. -/
theorem y2_exec (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = s64) (fu : Nat) (P : List Cell) (X V : List Int)
    (n t j : Nat) (hn : n < 1073741824) (ht : t < n) (hj : j < X.length) (hjn : j < 2147483648) (hi : t + 1 < X.length)
    (hel : ∀ y ∈ X, s64.valid y = true) (hsum : s64.valid (X.getD j 0 + X.getD (t + 1) 0) = true) :
    ∃ r : PRM, pexecM mv fu (Y2 mv.nv) (gS P [ci n, ci t, ci (t + 1), ci j]) (VFT X V) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, ci t, ci (t + 1), ci j] ∧ r.vv = VFT (X.set j (X.getD j 0 + X.getD (t + 1) 0)) V ∧
      r.cost ≤ 100 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 1 := by
  have E2 := envs mv P [ci n, ci t, ci (t + 1), ci j] 2 (ci (t + 1)) rfl (validN (t + 1) (by omega))
  have E3 := envs mv P [ci n, ci t, ci (t + 1), ci j] 3 (ci j) rfl (validN j hjn)
  have mj : X.getD j 0 ∈ X := by
    have : X.getD j 0 = X[j] := by simp [List.getD_eq_getElem?_getD, hj]
    rw [this]; exact List.getElem_mem _
  have mi : X.getD (t + 1) 0 ∈ X := by
    have : X.getD (t + 1) 0 = X[t + 1] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [this]; exact List.getElem_mem _
  have vj := rdM_val mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t, ci (t + 1), ci j])) 0 (by omega) s64 hty0.symm
    (.cast u64 (.variable i32 (mv.nv + 3))) rfl rfl j (cidx_den _ (mv.nv + 3) j E3 (show j < 2147483648 by omega))
    (X.getD j 0) (by rw [VFT_get0]; exact vec_getI X j hj) (by rw [hty0]; exact hel _ mj)
  have vi := rdM_val mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t, ci (t + 1), ci j])) 0 (by omega) s64 hty0.symm
    (.cast u64 (.variable i32 (mv.nv + 2))) rfl rfl (t + 1) (cidx_den _ (mv.nv + 2) (t + 1) E2 (show t + 1 < 2147483648 by omega))
    (X.getD (t + 1) 0) (by rw [VFT_get0]; exact vec_getI X (t + 1) hi) (by rw [hty0]; exact hel _ mi)
  have hx : vdenM mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t, ci (t + 1), ci j])) (.binary s64 .add (rdJ mv.nv) (rdI mv.nv)) =
      some (X.getD j 0 + X.getD (t + 1) 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ (by simp [NExpr.scalarOnly]), vj, vi, Option.bind_some, Option.bind_some]
    have : binaryValue .add (X.getD j 0) (X.getD (t + 1) 0) = X.getD j 0 + X.getD (t + 1) 0 := rfl
    rw [this]
    exact Ty.convert_of_valid _ _ hsum
  have hp : vdenM mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t, ci (t + 1), ci j])) (.cast u64 (.variable i32 (mv.nv + 3))) =
      some (j : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 3) j E3 (show j < 2147483648 by omega)
  have w := pstmtM_write_ok mv (gS P [ci n, ci t, ci (t + 1), ci j]) (VFT X V) 0 (by omega) _ _ _ j hx hp
    (by rw [VFT_get0]; exact hj) (by rw [hty0]; exact hsum)
  rw [hty0, VFT_write0] at w
  have a1 := (pexecM_prim mv fu (wr2S mv.nv) _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P [ci n, ci t, ci (t + 1), ci j]) (VFT (X.set j (X.getD j 0 + X.getD (t + 1) 0)) V))
  have a3 := pexecM_scope mv fu _ _ _ _ a2
  have tk : (⟨(gS P [ci n, ci t, ci (t + 1), ci j]).mem.take (gS P [ci n, ci t, ci (t + 1), ci j]).mem.length,
      (gS P [ci n, ci t, ci (t + 1), ci j]).bs.take (gS P [ci n, ci t, ci (t + 1), ci j]).bs.length⟩ : PS) =
      gS P [ci n, ci t, ci (t + 1), ci j] := by simp
  simp only [tk] at a3
  have a4 := seqM_some a3 rfl (pexecM_skip mv fu (gS P [ci n, ci t, ci (t + 1), ci j]) (VFT (X.set j (X.getD j 0 + X.getD (t + 1) 0)) V))
  refine ⟨_, a4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


set_option maxHeartbeats 8000000 in
/-- The second loop body: `int i = k + 1; int j = i + lowbit(i); if (j <= n) tree[j] = tree[j] + tree[i];`. -/
theorem b2_exec (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = s64) (fu : Nat) (P : List Cell) (X V : List Int)
    (n t : Nat) (hn : n + 1 ≤ 1073741824) (ht : t < n) (hX : X.length = n + 1)
    (hel : ∀ y ∈ X, s64.valid y = true)
    (hsum : (t + 1) + lowb (t + 1) < X.length →
      s64.valid (X.getD ((t + 1) + lowb (t + 1)) 0 + X.getD (t + 1) 0) = true) :
    ∃ r : PRM, pexecM mv fu (B2 mv.nv) (gS P [ci n, ci t]) (VFT X V) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, ci t, ci (t + 1), ci ((t + 1) + lowb (t + 1))] ∧ r.vv = VFT (bstep X (t + 1)) V ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 1 := by
  have hl := lowb_pos (t + 1) (by omega)
  have hl' := lowb_le (t + 1) (by omega)
  have E1 := envs mv P [ci n, ci t] 1 (ci t) rfl (validN t (by omega))
  have vi : vdenM mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t])) (.binary i32 .add (.variable i32 (mv.nv + 1)) (.literal i32 1)) =
      some ((t + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact inc_den _ (mv.nv + 1) t E1 (by omega)
  have d1 := gSM_decl mv P [ci n, ci t] (VFT X V) i32 _ _ _ vi (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q1 := (pexecM_prim mv fu (iDecl mv.nv) _ _).trans d1
  have E2 := envs mv P [ci n, ci t, ci (t + 1)] 2 (ci (t + 1)) rfl (validN (t + 1) (by omega))
  have vj : vdenM mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t, ci (t + 1)])) (.binary i32 .add (.variable i32 (mv.nv + 2)) (lowV mv.nv 2)) =
      some (((t + 1) + lowb (t + 1) : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ (by simp [NExpr.scalarOnly]), den_binary, den_variable, E2, Option.bind_some,
      lowV_den _ mv.nv 2 (t + 1) (by omega) (by omega) E2, Option.bind_some]
    have : binaryValue .add ((t + 1 : Nat) : Int) (lowb (t + 1) : Int) = (((t + 1) + lowb (t + 1) : Nat) : Int) := by
      show _ + _ = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (validN _ (by omega))
  have d2 := gSM_decl mv P [ci n, ci t, ci (t + 1)] (VFT X V) i32 _ _ _ vj (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q2 := (pexecM_prim mv fu (jDecl mv.nv) _ _).trans d2
  have E0 : penvN mv.nv (gS P [ci n, ci t, ci (t + 1), ci ((t + 1) + lowb (t + 1))]) mv.nv i32 = some (n : Int) :=
    envs mv P [ci n, ci t, ci (t + 1), ci ((t + 1) + lowb (t + 1))] 0 (ci n) rfl (validN n (by omega))
  have E3 := envs mv P [ci n, ci t, ci (t + 1), ci ((t + 1) + lowb (t + 1))] 3 (ci ((t + 1) + lowb (t + 1))) rfl
    (validN _ (by omega))
  have vc : vdenM mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t, ci (t + 1), ci ((t + 1) + lowb (t + 1))])) (cond2 mv.nv) =
      some (if (((t + 1) + lowb (t + 1) : Nat) : Int) ≤ (n : Int) then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E3, Option.bind_some, den_variable, E0, Option.bind_some]
    exact le_conv _ _
  by_cases hJ : (t + 1) + lowb (t + 1) < X.length
  · have hle : (((t + 1) + lowb (t + 1) : Nat) : Int) ≤ (n : Int) := by omega
    rw [if_pos hle] at vc
    obtain ⟨ry, hy, hyret, hyps, hyvv, hyc, hyn, hyw⟩ := y2_exec mv hnv hty0 fu P X V n t ((t + 1) + lowb (t + 1))
      (by omega) ht hJ (by omega) (by omega) hel (hsum hJ)
    have b1 := pexecM_branch_true mv fu (cond2 mv.nv) (Y2 mv.nv) Sk _ _ 1 vc (by decide) ry hy
    have b2 := seqM_some b1 hyret (pexecM_skip mv fu ry.ps ry.vv)
    have fin := seqM_some q1 rfl (seqM_some q2 rfl b2)
    refine ⟨_, fin, rfl, hyps, ?_, ?_, ?_, ?_⟩
    · rw [hyvv]; unfold bstep; rw [if_pos hJ]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hyc ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hyn ⊢
      have : ry.ps.mem.length + ry.ps.bs.length = P.length + 8 := by rw [hyps]; simp [gS_size]
      omega
    · simpa using hyw
  · have hle : ¬ ((((t + 1) + lowb (t + 1) : Nat) : Int) ≤ (n : Int)) := by omega
    rw [if_neg hle] at vc
    have b1 := pexecM_branch_false mv fu (cond2 mv.nv) (Y2 mv.nv) Sk _ _ vc _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have fin := seqM_some q1 rfl (seqM_some q2 rfl b2)
    refine ⟨_, fin, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · unfold bstep; rw [if_neg hJ]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp


/-- The state of `tree` after `t` iterations of the second loop. -/
def bst (X : List Int) : Nat → List Int
  | 0 => X
  | t + 1 => bstep (bst X t) (t + 1)

theorem bstep_length (X : List Int) (k : Nat) : (bstep X k).length = X.length := by
  unfold bstep; split <;> simp

theorem bst_length (X : List Int) (t : Nat) : (bst X t).length = X.length := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [bst]; rw [bstep_length, ih]

theorem bst_binv (V X : List Int) (h : BInv V 1 X) : ∀ t, t ≤ V.length → BInv V (t + 1) (bst X t) := by
  intro t
  induction t with
  | zero => intro _; exact h
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have hl : (bst X t).length = V.length + 1 := by rw [h1.1]
    exact binv_step V (bst X t) (t + 1) h1 (by omega) (by omega)

-- Every update value stays in range (the precondition of the constructor).
def BOkT (A : List Int) (n : Nat) : Prop :=
  ∀ k, 1 ≤ k → k + lowb k < n → s64.valid (A.getD (k + lowb k - 1) 0 + pre A k - pre A (k + lowb k - lowb (k + lowb k))) = true

theorem upd_valT (A tree : List Int) (k : Nat) (h : BInv A k tree) (hk : 1 ≤ k) (hkn : k < tree.length)
    (hJ : k + lowb k < tree.length) :
    tree.getD (k + lowb k) 0 + tree.getD k 0 =
      A.getD (k + lowb k - 1) 0 + pre A k - pre A (k + lowb k - lowb (k + lowb k)) := by
  have hL := lowb_pos k hk
  have hkv := h.2 k hk hkn
  have hkA : k - 1 < A.length := by have := h.1; omega
  have hseg : tree[k]? = some (seg A k) := by
    rw [hkv, if_neg (by omega), Wc_self k hk]
    congr 1
    have := pre_succ A (k-1) hkA
    have e : k - 1 + 1 = k := by omega
    rw [e] at this
    unfold seg
    omega
  have hget : tree.getD k 0 = seg A k := by simp [List.getD_eq_getElem?_getD, hseg]
  have hv := h.2 (k + lowb k) (by omega) hJ
  have hgj : tree.getD (k + lowb k) 0 = A.getD (k + lowb k - 1) 0 + pre A (Wc (k + lowb k) k) -
      pre A (k + lowb k - lowb (k + lowb k)) := by
    simp [List.getD_eq_getElem?_getD, hv, if_neg (show ¬ (k + lowb k < k) by omega)]
  rw [hgj, hget, (Wc_at_j k hk).1]
  unfold seg
  omega

theorem bst_valid (V X : List Int) (hok : BOkT V (V.length + 1)) (h : BInv V 1 X) (hel : ∀ y ∈ X, s64.valid y = true) :
    ∀ t, t ≤ V.length → ∀ y ∈ bst X t, s64.valid y = true := by
  intro t
  induction t with
  | zero => intro _ y hy; exact hel y hy
  | succ t ih =>
    intro ht y hy
    have hI := bst_binv V X h t (by omega)
    have hlen : (bst X t).length = V.length + 1 := hI.1
    simp only [bst] at hy
    unfold bstep at hy
    split at hy
    · rename_i hJ
      rcases List.mem_or_eq_of_mem_set hy with hm | heq
      · exact ih (by omega) y hm
      · rw [heq, upd_valT V (bst X t) (t + 1) hI (by omega) (by omega) hJ]
        exact hok (t + 1) (by omega) (by omega)
    · exact ih (by omega) y hy

set_option maxHeartbeats 8000000 in
theorem l1_loop (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (fu : Nat) (P : List Cell)
    (T0 V : List Int) (n : Nat) (hn : n < 2147483647) (hV : V.length = n) (hT : T0.length = n + 1)
    (hVv : ∀ y ∈ V, s64.valid y = true) (hfu : n + 1 ≤ fu) :
    ∃ (res : PRM) (X1 : List Int), pexecM mv fu (forStmtB mv.nv 1 0 (B1 mv.nv)) (gS P [ci n]) (VFT T0 V) = some res ∧
      res.ps = gS P [ci n] ∧ res.vv = VFT X1 V ∧ P1 T0 V n X1 ∧ res.ret = none ∧ res.cost ≤ 120 * n + 30 ∧
      res.need ≤ P.length + 60 ∧ res.wk ≤ n := by
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 1 0 n (by omega) hn (B1 mv.nv)
    (fun t vv C => (∃ X, vv = VFT X V ∧ P1 T0 V t X) ∧ C = [ci n]) 100 60 1 0 (by omega)
    (by
      intro t vv C fu ht hCl hC0 ⟨⟨X, hvv, hP⟩, hC⟩ _
      subst hvv; subst hC
      have hX : X.length = n + 1 := by rw [hP.1]; exact hT
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := b1_exec mv hnv hty0 hty1 fu P X V n t hn ht hV hX hVv
      exact ⟨r, [], [ci n], hr, hret, hps, rfl, rfl, ⟨⟨X.set (t + 1) (V.getD t 0), hvv, P1_step T0 V X t hP (by omega) (by omega)⟩, rfl⟩,
        hc, hnd, hwk⟩)
    (VFT T0 V) [ci n] rfl rfl ⟨⟨T0, rfl, P1_zero T0 V⟩, rfl⟩ fu (by omega)
  obtain ⟨⟨X1, hvv, hP⟩, hC⟩ := hIn
  subst hC
  exact ⟨res, X1, hr', hps, hvv, hP, hret, by omega, by omega, by omega⟩

set_option maxHeartbeats 8000000 in
theorem l2_loop (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = s64) (fu : Nat) (P : List Cell)
    (X1 V : List Int) (n : Nat) (hn : n + 1 ≤ 1073741824) (hV : V.length = n) (hX1 : X1.length = n + 1)
    (hI : BInv V 1 X1) (hel : ∀ y ∈ X1, s64.valid y = true) (hok : BOkT V (n + 1)) (hfu : n + 1 ≤ fu) :
    ∃ (res : PRM), pexecM mv fu (forStmtB mv.nv 1 0 (B2 mv.nv)) (gS P [ci n]) (VFT X1 V) = some res ∧
      res.ps = gS P [ci n] ∧ res.vv = VFT (bst X1 n) V ∧ res.ret = none ∧ res.cost ≤ 420 * n + 30 ∧
      res.need ≤ P.length + 100 ∧ res.wk ≤ n := by
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 1 0 n (by omega) (by omega) (B2 mv.nv)
    (fun t vv C => vv = VFT (bst X1 t) V ∧ C = [ci n]) 400 100 1 0 (by omega)
    (by
      intro t vv C fu ht hCl hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hBI := bst_binv V X1 hI t (by omega)
      have hlen : (bst X1 t).length = n + 1 := by rw [hBI.1, hV]
      have hv := bst_valid V X1 (by rwa [hV]) hI hel t (by omega)
      have hsum : (t + 1) + lowb (t + 1) < (bst X1 t).length →
          s64.valid ((bst X1 t).getD ((t + 1) + lowb (t + 1)) 0 + (bst X1 t).getD (t + 1) 0) = true := by
        intro hJ
        rw [upd_valT V (bst X1 t) (t + 1) hBI (by omega) (by omega) hJ]
        exact hok (t + 1) (by omega) (by omega)
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := b2_exec mv hnv hty0 fu P (bst X1 t) V n t hn ht hlen hv hsum
      exact ⟨r, [ci (t + 1), ci ((t + 1) + lowb (t + 1))], [ci n], hr, hret, hps, rfl, rfl, ⟨hvv, rfl⟩, hc, hnd, hwk⟩)
    (VFT X1 V) [ci n] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hIn
  subst hC
  exact ⟨res, hr', hps, hvv, hret, by omega, by omega, by omega⟩

theorem size_val1 (mv : MV) (hnv : mv.nv = 2) (hty1 : mv.ty 1 = s64) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (hn : (vv 1).length < 2147483648) :
    vdenM mv vv env (.cast i32 (.size (.integer s64) (.local 1))) = some ((vv 1).length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer s64) (.local 1))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer s64) (.local 1)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer s64) (.local 1)) = some ((vv 1).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨by omega, hty1.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

set_option maxHeartbeats 8000000 in
/-- The whole constructor body. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (fu : Nat) (P : List Cell)
    (T0 V : List Int) (n : Nat) (hn : n + 1 ≤ 1073741824) (hV : V.length = n) (hT : T0.length = n + 1)
    (hVv : ∀ y ∈ V, s64.valid y = true) (hTv : ∀ y ∈ T0, s64.valid y = true) (hok : BOkT V (n + 1)) (hfu : n + 1 ≤ fu) :
    ∃ (r : PRM) (X2 : List Int), pexecM mv fu (progN mv.nv) (gS P []) (VFT T0 V) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n] ∧ r.vv = VFT X2 V ∧ FInv X2 V ∧ r.cost ≤ 560 * n + 100 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 * n := by
  have hsz := size_val1 mv hnv hty1 (VFT T0 V) (penvN mv.nv (gS P [])) (by rw [VFT_get1, hV]; omega)
  rw [VFT_get1, hV] at hsz
  have d0 := gSM_decl mv P [] (VFT T0 V) i32 _ _ _ hsz (conv_signed i32 rfl rfl _ (validN n (by omega)))
  have q0 := (pexecM_prim mv fu declN _ _).trans d0
  obtain ⟨r1, X1, h1, p1, v1, hP1, ret1, c1, n1, w1⟩ := l1_loop mv hnv hty0 hty1 fu P T0 V n (by omega) hV hT hVv hfu
  have hX1 : X1.length = n + 1 := by rw [hP1.1]; exact hT
  have hinit : BInv V 1 X1 := by
    refine binv_init V X1 (by rw [hX1, hV]) ?_
    intro t ht1 ht2
    have := hP1.2 t ht2
    rw [this, if_neg (by omega), if_pos (by omega)]
    exact vec_getI V (t - 1) (by omega)
  have hel1 : ∀ y ∈ X1, s64.valid y = true := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
    have hq' := hP1.2 q hq
    rw [List.getElem?_eq_getElem hq] at hq'
    by_cases h0 : q = 0
    · subst h0
      rw [if_pos rfl] at hq'
      exact hTv _ (List.mem_of_getElem? hq'.symm)
    · rw [if_neg h0, if_pos (by omega)] at hq'
      exact hVv _ (List.mem_of_getElem? hq'.symm)
  obtain ⟨r2, h2, p2, v2, ret2, c2, n2, w2⟩ := l2_loop mv hnv hty0 fu P X1 V n hn hV hX1 hinit hel1 hok hfu
  have f1 := seqM_some h1 ret1 (by rw [p1, v1]; exact seqM_some h2 ret2 (pexecM_skip mv fu r2.ps r2.vv))
  have f2 := seqM_some q0 rfl f1
  have hfin : BInv V (bst X1 n).length (bst X1 n) := by
    have := bst_binv V X1 hinit n (by omega)
    rw [bst_length, hX1]
    simpa [hV] using this
  refine ⟨_, bst X1 n, f2, rfl, ?_, ?_, binv_final V _ hfin, ?_, ?_, ?_⟩
  · exact p2
  · exact v2
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at n1 n2 ⊢
    have : r2.ps.mem.length + r2.ps.bs.length = P.length + 2 := by rw [p2]; simp [gS_size]
    omega
  · simp at w1 w2 ⊢; omega

end Proofs.FenwickTreeExec
