import Proofs.MultiVecCallN
import Proofs.ForLoopBN
import Proofs.FloydNestedExec
import Proofs.TreeLcaMath
import Proofs.TopoSortExec
import Proofs.Generated.TreeLca

namespace Proofs.TreeLcaExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVecN Proofs.MultiKitN Proofs.ForLoopMN Proofs.ForLoopCN
open Proofs.VecStmtX
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.PrefixSumsCall (bT)
open Proofs.BellmanFordExec (cidx_den M31)
open Proofs.TopoSortExec (i32v one_den zero_den)
open Proofs.FloydNestedExec (pexecM_branch_true pexecM_branch_false)
open Proofs.TreeAncestorMath (tab itr itr_add)
open Proofs.TreeLcaMath (descA descA_zero descA_succ TabAll descA_lt)

/-! ### `tree_lca_same_depth` (nv = 1: the nested table is slot 0).
Cells: 0 = u, 1 = v, 2 = depth, 3 = top, 4 = p, 5 = k, 6 = nu, 7 = nv -/

abbrev cA (nv : Nat) : NExpr :=
  .binary bT .le (.binary i32 .mul (.variable i32 (nv + 4)) (.literal i32 2)) (.variable i32 (nv + 2))
abbrev updP (nv : Nat) : NStmt := .assign (nv + 4) i32 (.binary i32 .mul (.variable i32 (nv + 4)) (.literal i32 2))
abbrev updT (nv : Nat) : NStmt := .assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.literal i32 1))
abbrev BA (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (updP nv)) (.sequence (.primitive (updT nv)) Sk))) Sk
abbrev cEq (nv : Nat) : NExpr := .binary bT .eq (.variable i32 (nv + 0)) (.variable i32 (nv + 1))
abbrev retU (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (.ret (.variable i32 (nv + 0)))) Sk)) Sk
abbrev cK (nv : Nat) : NExpr := .binary bT .ge (.variable i32 (nv + 5)) (.literal i32 0)
abbrev rowAt (nv k c : Nat) : NExpr :=
  .read i32 (.row (.local 0) (.integer i32) (.cast u64 (.variable i32 (nv + k)))) (.cast u64 (.variable i32 (nv + c)))
abbrev cNe (nv : Nat) : NExpr := .binary bT .ne (.variable i32 (nv + 6)) (.variable i32 (nv + 7))
abbrev mvUV (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.assign (nv + 0) i32 (.variable i32 (nv + 6))))
    (.sequence (.primitive (.assign (nv + 1) i32 (.variable i32 (nv + 7)))) Sk))) Sk
abbrev decK (nv : Nat) : NStmt := .assign (nv + 5) i32 (.binary i32 .sub (.variable i32 (nv + 5)) (.literal i32 1))
abbrev BC (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.declare i32 true (rowAt nv 5 0)))
    (.sequence (.primitive (.declare i32 true (rowAt nv 5 1)))
      (.sequence (.branch (cNe nv) (mvUV nv) Sk) (.sequence (.primitive (decK nv)) Sk))))) Sk
abbrev retAnc (nv : Nat) : NExpr :=
  .read i32 (.row (.local 0) (.integer i32) (.cast u64 (.literal i32 0))) (.cast u64 (.variable i32 (nv + 0)))
abbrev retRes (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (retAnc nv))) (.sequence (.primitive (.ret (.variable i32 (nv + 6)))) Sk)
abbrev bodyLC (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.literal i32 0))) (.sequence (.primitive (.declare i32 true (.literal i32 1)))
    (.sequence (.whileLoop (cA nv) (BA nv)) (.sequence (.branch (cEq nv) (retU nv) Sk)
      (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 3)))) (.sequence (.whileLoop (cK nv) (BC nv))
        (retRes nv))))))

theorem body_eqLC : Proofs.TreeLcaInstance.tree_lca_same_depth.body = bodyLC 1 := rfl

theorem ge_conv (x y : Int) : bT.convert (binaryValue .ge x y) = some (if x ≥ y then 1 else 0) := by
  by_cases h : x ≥ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem le_conv (x y : Int) : bT.convert (binaryValue .le x y) = some (if x ≤ y then 1 else 0) := by
  by_cases h : x ≤ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem eq_conv (x y : Int) : bT.convert (binaryValue .eq x y) = some (if x = y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem ne_conv (x y : Int) : bT.convert (binaryValue .ne x y) = some (if x ≠ y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : (x != y) = true := by simp [h]
    simp [binaryValue, this, h, Ty.convert, bT, Ty.valid]

/-- Reading `table[cells[kc]][cells[cc]]`. -/
theorem rowRd_val (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = i32)
    (vv : Nat → List Int) (P cells : List Cell) (kc cc rk col : Nat) (r : List Int) (x : Int)
    (hkc : cells[kc]? = some (ci rk)) (hcc : cells[cc]? = some (ci col)) (hk : rk < M31) (hcol : col < M31)
    (hwr : rk < mv.wrows 0) (hr : vv (rowKey 0 rk) = r) (hx : r[col]? = some x) (hxv : i32.valid x = true) :
    vdenN mv vv (penvN mv.nv (gS P cells)) (rowAt mv.nv kc cc) = some x := by
  have e0 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + cc) col
    (gSM_env mv.nv P cells cc (ci col) hcc (i32v col hcol)) hcol
  have e2 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + kc) rk
    (gSM_env mv.nv P cells kc (ci rk) hkc (i32v rk hk)) hk
  simp only [rowAt, vdenN]
  rw [if_pos ⟨by omega, hfl, hty.symm, hty.symm, rfl, rfl⟩]
  rw [e2, Option.bind_some, e0, Option.bind_some, if_pos ⟨Int.natCast_nonneg rk, by rw [Int.toNat_natCast]; exact hwr⟩,
    Int.toNat_natCast, hr]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg col), Int.toNat_natCast, hx, Option.bind_some, hty, if_pos hxv]

abbrev cells5 (u v dep top p : Nat) : List Cell := [ci u, ci v, ci dep, ci top, ci p]

theorem condA_val (mv : MV) (hnv : mv.nv = 1) (vv : Nat → List Int) (P : List Cell) (u v dep top p : Nat)
    (hdep : dep < M31) (hp : p * 2 < M31) (hpM : p < M31) :
    vdenM mv vv (penvN mv.nv (gS P (cells5 u v dep top p))) (cA mv.nv) = some (if p * 2 ≤ dep then 1 else 0) := by
  have e2 := gSM_env mv.nv P (cells5 u v dep top p) 2 (ci dep) rfl (i32v dep hdep)
  have e4 := gSM_env mv.nv P (cells5 u v dep top p) 4 (ci p) rfl (i32v p hpM)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_binary, den_variable, e4, Option.bind_some, den_literal,
    if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
  have hm : binaryValue .mul (p : Int) 2 = ((p * 2 : Nat) : Int) := by
    show (p : Int) * 2 = _; push_cast; rfl
  rw [hm, conv_signed i32 rfl rfl _ (i32v _ hp), Option.bind_some, den_variable, e2, Option.bind_some, le_conv]
  by_cases h : p * 2 ≤ dep
  · have : ((p * 2 : Nat) : Int) ≤ (dep : Int) := by omega
    simp [h]
    omega
  · have : ¬ (((p * 2 : Nat) : Int) ≤ (dep : Int)) := by omega
    simp [h]
    omega

set_option maxHeartbeats 8000000 in
theorem iterA_exec (mv : MV) (hnv : mv.nv = 1) (vv : Nat → List Int) (P : List Cell) (u v dep top p : Nat)
    (hdep : dep < M31) (hp2 : p * 2 < M31) (hp4 : p * 2 * 2 < M31) (hpM : p < M31) (htop : top + 1 < M31) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (BA mv.nv) (gS P (cells5 u v dep top p)) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (cells5 u v dep (top + 1) (p * 2)) ∧ r.vv = vv ∧ r.cost ≤ 60 ∧ r.need ≤ P.length + 40 ∧ r.wk = 0 := by
  have e4 := gSM_env mv.nv P (cells5 u v dep top p) 4 (ci p) rfl (i32v p hpM)
  have hx : vdenN mv vv (penvN mv.nv (gS P (cells5 u v dep top p)))
      (.binary i32 .mul (.variable i32 (mv.nv + 4)) (.literal i32 2)) = some ((p * 2 : Nat) : Int) := by
    rw [vdenN_scalar _ _ _ _ rfl, den_binary, den_variable, e4, Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
    have : binaryValue .mul (p : Int) 2 = ((p * 2 : Nat) : Int) := by
      show (p : Int) * 2 = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ hp2)
  have as1 := gSM_assign mv P (cells5 u v dep top p) vv 4 (by simp) i32 _ _ _ hx (ci p) rfl rfl (i32v p hpM)
    (conv_signed i32 rfl rfl _ (i32v _ hp2))
  have u1 := (pexecM_prim mv fu (updP mv.nv) _ _).trans as1
  have hset1 : (cells5 u v dep top p).set 4 ⟨i32, ((p * 2 : Nat) : Int)⟩ = cells5 u v dep top (p * 2) := rfl
  rw [hset1] at u1
  have e3 := gSM_env mv.nv P (cells5 u v dep top (p * 2)) 3 (ci top) rfl (i32v top (by omega))
  have hx2 : vdenN mv vv (penvN mv.nv (gS P (cells5 u v dep top (p * 2))))
      (.binary i32 .add (.variable i32 (mv.nv + 3)) (.literal i32 1)) = some ((top + 1 : Nat) : Int) := by
    rw [vdenN_scalar _ _ _ _ rfl, den_binary, den_variable, e3, Option.bind_some, den_literal,
      if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
    have : binaryValue .add (top : Int) 1 = ((top + 1 : Nat) : Int) := by
      show (top : Int) + 1 = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ htop)
  have as2 := gSM_assign mv P (cells5 u v dep top (p * 2)) vv 3 (by simp) i32 _ _ _ hx2 (ci top) rfl rfl (i32v top (by omega))
    (conv_signed i32 rfl rfl _ (i32v _ htop))
  have u2 := (pexecM_prim mv fu (updT mv.nv) _ _).trans as2
  have hset2 : (cells5 u v dep top (p * 2)).set 3 ⟨i32, ((top + 1 : Nat) : Int)⟩ = cells5 u v dep (top + 1) (p * 2) := rfl
  rw [hset2] at u2
  have w3 := seqM_some u2 rfl (pexecM_skip mv fu _ vv)
  have w2 := seqM_some u1 rfl w3
  have sc := pexecM_scope mv fu _ _ _ _ w2
  have tk := gS_takeC P (cells5 u v dep top p) (cells5 u v dep (top + 1) (p * 2)) [] rfl
  simp only [List.append_nil] at tk
  simp only [tk] at sc
  have w4 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, w4, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]

theorem vwp_cA (nv : Nat) : vwp (cA nv) = (5, 5) := by simp [vwp, NExpr.nodes]

set_option maxHeartbeats 16000000 in
/-- The loop `while (p * 2 <= depth) { p = p * 2; top = top + 1; }`. -/
theorem topLoop_exec (mv : MV) (hnv : mv.nv = 1) (vv : Nat → List Int) (P : List Cell) (u v dep : Nat)
    (hdep : dep < 1073741824) :
    ∀ g top p fu, dep - p = g → 0 < p → p = 2 ^ top → p < 1073741824 → (p = 1 ∨ p ≤ dep) → g + 2 ≤ fu →
      ∃ (res : PRM) (top' p' : Nat), pexecM mv fu (.whileLoop (cA mv.nv) (BA mv.nv)) (gS P (cells5 u v dep top p)) vv = some res ∧
        res.ret = none ∧ res.ps = gS P (cells5 u v dep top' p') ∧ res.vv = vv ∧ p' = 2 ^ top' ∧ top ≤ top' ∧
        dep < p' * 2 ∧ p' < 1073741824 ∧ (p' = 1 ∨ p' ≤ dep) ∧ res.cost ≤ 100 * (top' - top) + 20 ∧ res.need ≤ P.length + 60 ∧ res.wk = 0 := by
  have hdepM : dep < M31 := by show dep < 2147483648; omega
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
    intro top p fu hg hp0 hp hpb hpd hfu
    have hpM : p < M31 := by show p < 2147483648; omega
    have hp2 : p * 2 < M31 := by show p * 2 < 2147483648; omega
    have hc : vdenM mv vv (penvN mv.nv (gS P (cells5 u v dep top p))) (cA mv.nv) = some (if p * 2 ≤ dep then 1 else 0) :=
      condA_val mv hnv vv P u v dep top p hdepM hp2 hpM
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    by_cases hcont : p * 2 ≤ dep
    · rw [if_pos hcont] at hc
      have htop : top < 30 := by
        refine Classical.byContradiction (fun hge => ?_)
        have : 2 ^ 30 ≤ 2 ^ top := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 ^ 30 = 1073741824 := by norm_num
        omega
      have hp4 : p * 2 * 2 < M31 := by show p * 2 * 2 < 2147483648; omega
      have htopM : top + 1 < M31 := by show top + 1 < 2147483648; omega
      obtain ⟨r, hr, hret, hps, hvv, hc1, hn1, hw1⟩ := iterA_exec mv hnv vv P u v dep top p hdepM hp2 hp4 hpM htopM (fu' + 1)
      obtain ⟨r2, top', p', h2, hret2, hps2, hvv2, hp', hle, hdp, hpb', hpd', hc2, hn2, hw2⟩ := ih (dep - p * 2) (by omega)
        (top + 1) (p * 2) fu' rfl (by omega) (by rw [hp, Nat.pow_succ]) (by omega) (Or.inr hcont) (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, hr, hret, hps, hvv, h2, vwp_cA]
      refine ⟨_, top', p', rfl, hret2, hps2, hvv2, hp', by omega, hdp, hpb', hpd', ?_, ?_, ?_⟩
      · simp [vwp_cA] at *
        omega
      · simp [gS_mem_len, gS_bs_len] at *
        omega
      · simp at *; omega
    · rw [if_neg hcont] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_cA]
      refine ⟨_, top, p, rfl, rfl, rfl, rfl, hp, Nat.le_refl _, by omega, hpb, hpd, ?_, ?_, rfl⟩
      · simp
      · simp [gS_mem_len, gS_bs_len]

theorem i32_valid_of (x : Int) (h : -2147483648 ≤ x ∧ x < 2147483648) : i32.valid x = true := by
  show Ty.valid ⟨32, true, false⟩ x = true
  simp [Ty.valid]
  omega

abbrev cmk (k : Nat) : Cell := ⟨i32, (k : Int) - 1⟩
abbrev cells6 (u v dep top p : Nat) (kc : Cell) : List Cell := [ci u, ci v, ci dep, ci top, ci p, kc]

set_option maxHeartbeats 16000000 in
/-- One iteration of the descent at level `k`. -/
theorem iterC_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = i32) (T : List (List Nat))
    (N k u v dep top p : Nat) (vv : Nat → List Int) (P : List Cell) (hN : N < M31) (hu : u < N) (hv : v < N) (hk : k < M31)
    (hrows : ∀ t, t < mv.wrows 0 → vv (rowKey 0 t) = (T.getD t []).map (fun x : Nat => (x : Int)))
    (hwr : k < mv.wrows 0) (hul : u < (T.getD k []).length) (hvl : v < (T.getD k []).length)
    (hnuN : tab T k u < N) (hnvN : tab T k v < N) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (BC mv.nv) (gS P (cells6 u v dep top p (ci k))) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (cells6 (if tab T k u ≠ tab T k v then tab T k u else u) (if tab T k u ≠ tab T k v then tab T k v else v)
        dep top p (cmk k)) ∧ r.vv = vv ∧ r.cost ≤ 160 ∧ r.need ≤ P.length + 80 ∧ r.wk = 0 := by
  have hvM : u < M31 := Nat.lt_trans hu hN
  have hvM' : v < M31 := Nat.lt_trans hv hN
  have hnuM : tab T k u < M31 := Nat.lt_trans hnuN hN
  have hnvM : tab T k v < M31 := Nat.lt_trans hnvN hN
  have hx1 : ((T.getD k []).map (fun x : Nat => (x : Int)))[u]? = some ((tab T k u : Nat) : Int) := by
    unfold tab
    generalize T.getD k [] = r at hul ⊢
    rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hul]
    rfl
  have hx2 : ((T.getD k []).map (fun x : Nat => (x : Int)))[v]? = some ((tab T k v : Nat) : Int) := by
    unfold tab
    generalize T.getD k [] = r at hvl ⊢
    rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvl]
    rfl
  have r1 := rowRd_val mv hnv hfl hty vv P (cells6 u v dep top p (ci k)) 5 0 k u _ _ rfl rfl hk hvM hwr (hrows k hwr) hx1
    (i32v _ hnuM)
  have d1 := gSM_decl mv P (cells6 u v dep top p (ci k)) vv i32 _ _ _ r1 (conv_signed i32 rfl rfl _ (i32v _ hnuM))
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have r2 := rowRd_val mv hnv hfl hty vv P (cells6 u v dep top p (ci k) ++ [ci (tab T k u)]) 5 1 k v _ _ rfl rfl hk hvM' hwr
    (hrows k hwr) hx2 (i32v _ hnvM)
  have d2 := gSM_decl mv P (cells6 u v dep top p (ci k) ++ [ci (tab T k u)]) vv i32 _ _ _ r2
    (conv_signed i32 rfl rfl _ (i32v _ hnvM))
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  have e6 := gSM_env mv.nv P (cells6 u v dep top p (ci k) ++ [ci (tab T k u)] ++ [ci (tab T k v)]) 6 (ci (tab T k u)) rfl (i32v _ hnuM)
  have e7 := gSM_env mv.nv P (cells6 u v dep top p (ci k) ++ [ci (tab T k u)] ++ [ci (tab T k v)]) 7 (ci (tab T k v)) rfl (i32v _ hnvM)
  have hcond : vdenM mv vv (penvN mv.nv (gS P (cells6 u v dep top p (ci k) ++ [ci (tab T k u)] ++ [ci (tab T k v)])))
      (cNe mv.nv) = some (if tab T k u ≠ tab T k v then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e6, Option.bind_some, den_variable, e7, Option.bind_some, ne_conv]
    by_cases h : tab T k u = tab T k v
    · have : ((tab T k u : Nat) : Int) = ((tab T k v : Nat) : Int) := by rw [h]
      simp [h, this]
    · have : ¬ (((tab T k u : Nat) : Int) = ((tab T k v : Nat) : Int)) := by omega
      simp [h, this]
  -- the branch
  have hcells : ∀ (a b : Nat), cells6 a b dep top p (ci k) ++ [ci (tab T k u)] ++ [ci (tab T k v)] =
      [ci a, ci b, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] := fun a b => rfl
  obtain ⟨u', v', r3, hr3, hret3, hps3, hvv3, hc3, hn3, hw3, hu', hv'⟩ :
      ∃ (u' v' : Nat) (r3 : PRM), pexecM mv fu (.branch (cNe mv.nv) (mvUV mv.nv) Sk)
        (gS P (cells6 u v dep top p (ci k) ++ [ci (tab T k u)] ++ [ci (tab T k v)])) vv = some r3 ∧ r3.ret = none ∧
        r3.ps = gS P [ci u', ci v', ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] ∧ r3.vv = vv ∧
        r3.cost ≤ 80 ∧ r3.need ≤ P.length + 70 ∧ r3.wk = 0 ∧
        u' = (if tab T k u ≠ tab T k v then tab T k u else u) ∧ v' = (if tab T k u ≠ tab T k v then tab T k v else v) := by
    by_cases hne : tab T k u ≠ tab T k v
    · rw [if_pos hne] at hcond
      have ea := gSM_env mv.nv P [ci u, ci v, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] 6 (ci (tab T k u)) rfl
        (i32v _ hnuM)
      have hxa : vdenN mv vv (penvN mv.nv (gS P [ci u, ci v, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)]))
          (.variable i32 (mv.nv + 6)) = some ((tab T k u : Nat) : Int) := by
        rw [vdenN_scalar _ _ _ _ rfl, den_variable]; exact ea
      have as1 := gSM_assign mv P [ci u, ci v, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] vv 0 (by simp) i32 _ _ _
        hxa (ci u) rfl rfl (i32v u hvM) (conv_signed i32 rfl rfl _ (i32v _ hnuM))
      have a1 := (pexecM_prim mv fu _ _ _).trans as1
      have eb := gSM_env mv.nv P [ci (tab T k u), ci v, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] 7
        (ci (tab T k v)) rfl (i32v _ hnvM)
      have hxb : vdenN mv vv (penvN mv.nv (gS P [ci (tab T k u), ci v, ci dep, ci top, ci p, ci k, ci (tab T k u),
          ci (tab T k v)])) (.variable i32 (mv.nv + 7)) = some ((tab T k v : Nat) : Int) := by
        rw [vdenN_scalar _ _ _ _ rfl, den_variable]; exact eb
      have as2 := gSM_assign mv P [ci (tab T k u), ci v, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] vv 1
        (by simp) i32 _ _ _ hxb (ci v) rfl rfl (i32v v hvM') (conv_signed i32 rfl rfl _ (i32v _ hnvM))
      have a2 := (pexecM_prim mv fu _ _ _).trans as2
      have hset1 : [ci u, ci v, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)].set 0
          ⟨i32, ((tab T k u : Nat) : Int)⟩ = [ci (tab T k u), ci v, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] := rfl
      have hset2 : [ci (tab T k u), ci v, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)].set 1
          ⟨i32, ((tab T k v : Nat) : Int)⟩ = [ci (tab T k u), ci (tab T k v), ci dep, ci top, ci p, ci k, ci (tab T k u),
            ci (tab T k v)] := rfl
      rw [hset1] at a1
      rw [hset2] at a2
      have a3 := seqM_some a2 rfl (pexecM_skip mv fu _ vv)
      have a4 := seqM_some a1 rfl a3
      have sc := pexecM_scope mv fu _ _ _ _ a4
      have tk := gS_takeC P [ci u, ci v, ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)]
        [ci (tab T k u), ci (tab T k v), ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] [] rfl
      simp only [List.append_nil] at tk
      simp only [tk] at sc
      have sk := seqM_some sc rfl (pexecM_skip mv fu _ _)
      rw [hcells] at hcond
      have b1 := pexecM_branch_true mv fu (cNe mv.nv) (mvUV mv.nv) Sk _ _ 1 hcond (by decide) _ sk
      refine ⟨tab T k u, tab T k v, _, b1, rfl, rfl, rfl, ?_, ?_, rfl, by rw [if_pos hne], by rw [if_pos hne]⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · rw [if_neg hne] at hcond
      rw [hcells] at hcond
      have b1 := pexecM_branch_false mv fu (cNe mv.nv) (mvUV mv.nv) Sk _ _ hcond _ (pexecM_skip mv fu _ _)
      refine ⟨u, v, _, b1, rfl, rfl, rfl, ?_, ?_, rfl, by rw [if_neg hne], by rw [if_neg hne]⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  have hkM : k < M31 := hk
  have ek := gSM_env mv.nv P [ci u', ci v', ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] 5 (ci k) rfl (i32v k hkM)
  have hxk : vdenN mv vv (penvN mv.nv (gS P [ci u', ci v', ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)]))
      (.binary i32 .sub (.variable i32 (mv.nv + 5)) (.literal i32 1)) = some ((k : Int) - 1) := by
    rw [vdenN_scalar _ _ _ _ rfl, den_binary, den_variable, ek, Option.bind_some, den_literal,
      if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
    have : binaryValue .sub (k : Int) 1 = (k : Int) - 1 := rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32_valid_of _ (by have : k < 2147483648 := hk; omega))
  have as3 := gSM_assign mv P [ci u', ci v', ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)] vv 5 (by simp) i32 _ _ _
    hxk (ci k) rfl rfl (i32v k hkM) (conv_signed i32 rfl rfl _ (i32_valid_of _ (by have : k < 2147483648 := hk; omega)))
  have u3 := (pexecM_prim mv fu (decK mv.nv) _ _).trans as3
  have hset3 : [ci u', ci v', ci dep, ci top, ci p, ci k, ci (tab T k u), ci (tab T k v)].set 5 ⟨i32, (k : Int) - 1⟩ =
      cells6 u' v' dep top p (cmk k) ++ [ci (tab T k u), ci (tab T k v)] := rfl
  rw [hset3] at u3
  have f1 := seqM_some u3 rfl (pexecM_skip mv fu _ vv)
  have f2 := seqM_some hr3 hret3 (by rw [hps3, hvv3]; exact f1)
  have f3 := seqM_some q2 rfl f2
  have f4 := seqM_some q1 rfl f3
  have sc := pexecM_scope mv fu _ _ _ _ f4
  have tk := gS_takeC P (cells6 u v dep top p (ci k)) (cells6 u' v' dep top p (cmk k)) [ci (tab T k u), ci (tab T k v)] rfl
  simp only [tk] at sc
  have f5 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, f5, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hu', hv']
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc3 ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hn3 ⊢; omega
  · simp; omega

theorem condK_val (mv : MV) (hnv : mv.nv = 1) (vv : Nat → List Int) (P : List Cell) (u v dep top p c : Nat)
    (hc : c < M31) :
    vdenM mv vv (penvN mv.nv (gS P (cells6 u v dep top p (cmk c)))) (cK mv.nv) = some (if 1 ≤ c then 1 else 0) := by
  have e5 := gSM_env mv.nv P (cells6 u v dep top p (cmk c)) 5 (cmk c) rfl (i32_valid_of ((c : Int) - 1) (by have : c < 2147483648 := hc; omega))
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e5, Option.bind_some, den_literal,
    if_pos (show i32.valid 0 = true from rfl), Option.bind_some, ge_conv]
  by_cases h : 1 ≤ c
  · have : ((c : Int) - 1 ≥ 0) := by omega
    simp [h]
  · have : ¬ ((c : Int) - 1 ≥ 0) := by omega
    simp [h]

theorem vwp_cK (nv : Nat) : vwp (cK nv) = (3, 3) := by simp [vwp, NExpr.nodes]

theorem descA_step (T : List (List Nat)) (c u v : Nat) :
    descA T (c + 1) u v = descA T c (if tab T c u ≠ tab T c v then tab T c u else u)
      (if tab T c u ≠ tab T c v then tab T c v else v) := by
  rw [descA_succ]
  by_cases h : tab T c u ≠ tab T c v
  · simp [h]
  · simp [h]

set_option maxHeartbeats 16000000 in
/-- The descent loop `while (k >= 0) {...}` from level `c - 1`. -/
theorem descLoop_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = i32) (T : List (List Nat))
    (f : Nat → Nat) (N dep top p : Nat) (vv : Nat → List Int) (P : List Cell) (hN : N < M31)
    (hrows : ∀ t, t < mv.wrows 0 → vv (rowKey 0 t) = (T.getD t []).map (fun x : Nat => (x : Int))) :
    ∀ c u v fu, c < M31 → TabAll T f N (c - 1) → u < N → v < N → c ≤ mv.wrows 0 → c + 1 ≤ fu →
      ∃ res : PRM, pexecM mv fu (.whileLoop (cK mv.nv) (BC mv.nv)) (gS P (cells6 u v dep top p (cmk c))) vv = some res ∧
        res.ret = none ∧ res.ps = gS P (cells6 (descA T c u v).1 (descA T c u v).2 dep top p (cmk 0)) ∧ res.vv = vv ∧
        res.cost ≤ 200 * c + 20 ∧ res.need ≤ P.length + 80 ∧ res.wk = 0 := by
  intro c
  induction c with
  | zero =>
    intro u v fu _ _ _ _ _ hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := condK_val mv hnv vv P u v dep top p 0 (by show 0 < 2147483648; omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_cK]
    refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩
    · rw [descA_zero]
    · simp
    · simp [gS_mem_len, gS_bs_len]
  | succ c ih =>
    intro u v fu hcM hT hu hv hw hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := condK_val mv hnv vv P u v dep top p (c + 1) hcM
    rw [if_pos (by omega)] at hc
    have hk : cmk (c + 1) = ci c := by
      show (⟨i32, ((c + 1 : Nat) : Int) - 1⟩ : Cell) = ⟨i32, (c : Int)⟩
      congr 1
      push_cast
      omega
    have hTc : ∀ x, x < N → tab T c x = itr f (2 ^ c) x ∧ tab T c x < N ∧ x < (T.getD c []).length :=
      fun x hx => hT c (by omega) x hx
    have hcM' : c < M31 := Nat.lt_trans (Nat.lt_succ_self c) hcM
    obtain ⟨r, hr, hret, hps, hvv, hc1, hn1, hw1⟩ := iterC_exec mv hnv hfl hty T N c u v dep top p vv P hN hu hv hcM' hrows
      (by omega) (hTc u hu).2.2 (hTc v hv).2.2 (hTc u hu).2.1 (hTc v hv).2.1 (fu' + 1)
    have hu' : (if tab T c u ≠ tab T c v then tab T c u else u) < N := by
      by_cases h : tab T c u ≠ tab T c v
      · rw [if_pos h]; exact (hTc u hu).2.1
      · rw [if_neg h]; exact hu
    have hv' : (if tab T c u ≠ tab T c v then tab T c v else v) < N := by
      by_cases h : tab T c u ≠ tab T c v
      · rw [if_pos h]; exact (hTc v hv).2.1
      · rw [if_neg h]; exact hv
    obtain ⟨r2, h2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := ih _ _ fu' hcM' (fun k hk' x hx => hT k (by omega) x hx) hu' hv'
      (by omega) (by omega)
    rw [hk] at hc ⊢
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, hr, hret, hps, hvv, h2, vwp_cK]
    refine ⟨_, rfl, hret2, ?_, hvv2, ?_, ?_, ?_⟩
    · rw [hps2, descA_step]
    · simp [vwp_cK] at *
      omega
    · simp [gS_mem_len, gS_bs_len] at *
      omega
    · simp at *; omega

theorem cEq_val (mv : MV) (hnv : mv.nv = 1) (vv : Nat → List Int) (P : List Cell) (u v dep top p : Nat)
    (hu : u < M31) (hv : v < M31) :
    vdenM mv vv (penvN mv.nv (gS P (cells5 u v dep top p))) (cEq mv.nv) = some (if u = v then 1 else 0) := by
  have e0 := gSM_env mv.nv P (cells5 u v dep top p) 0 (ci u) rfl (i32v u hu)
  have e1 := gSM_env mv.nv P (cells5 u v dep top p) 1 (ci v) rfl (i32v v hv)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e0, Option.bind_some, den_variable, e1, Option.bind_some, eq_conv]
  by_cases h : u = v
  · simp [h]
  · have : ¬ ((u : Int) = (v : Int)) := by omega
    simp [h, this]

/-- Reading `table[0][u]`. -/
theorem retAnc_val (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = i32)
    (vv : Nat → List Int) (P cells : List Cell) (u : Nat) (r : List Int) (x : Int)
    (hc : cells[0]? = some (ci u)) (hu : u < M31) (hwr : 0 < mv.wrows 0) (hr : vv (rowKey 0 0) = r) (hx : r[u]? = some x)
    (hxv : i32.valid x = true) :
    vdenN mv vv (penvN mv.nv (gS P cells)) (retAnc mv.nv) = some x := by
  have e0 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + 0) u (gSM_env mv.nv P cells 0 (ci u) hc (i32v u hu)) hu
  simp only [retAnc, vdenN]
  rw [if_pos ⟨by omega, hfl, hty.symm, hty.symm, rfl, rfl⟩]
  rw [den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some, convert_u64, Option.bind_some, e0,
    Option.bind_some, if_pos ⟨by decide, by simpa using hwr⟩]
  have : ((0 : Int) % 18446744073709551616).toNat = 0 := by decide
  rw [this, hr]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg u), Int.toNat_natCast, hx, Option.bind_some, hty, if_pos hxv]

set_option maxHeartbeats 16000000 in
/-- The whole body of `tree_lca_same_depth`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = i32) (T : List (List Nat))
    (f : Nat → Nat) (N K u v dep : Nat) (vv : Nat → List Int) (P : List Cell) (hN : N < M31) (hu : u < N) (hv : v < N)
    (hdep : dep < 1073741824) (hK : dep < 2 ^ (K + 1)) (H : TabAll T f N K) (hK30 : K < 30)
    (hrows : ∀ t, t < mv.wrows 0 → vv (rowKey 0 t) = (T.getD t []).map (fun x : Nat => (x : Int)))
    (hwr : K + 1 ≤ mv.wrows 0) (fu : Nat) (hfu : dep + 40 ≤ fu) :
    ∃ (r : PRM) (w top' : Nat), pexecM mv fu (bodyLC mv.nv) (gS P [ci u, ci v, ci dep]) vv = some r ∧
      r.ret = some (w : Int) ∧ dep < 2 ^ (top' + 1) ∧ top' ≤ K ∧ (u = v → w = u) ∧
      (u ≠ v → w = tab T 0 (descA T (top' + 1) u v).1) ∧ w < N ∧
      r.vv = vv ∧ (∃ cs : List Cell, r.ps = gS P cs) ∧
      r.cost ≤ 300 * (top' + 1) + 400 ∧ r.need ≤ P.length + 80 ∧ r.wk = 0 := by
  have huM : u < M31 := Nat.lt_trans hu hN
  have hvM : v < M31 := Nat.lt_trans hv hN
  have hdepM : dep < M31 := by show dep < 2147483648; omega
  have d1 := gSM_decl mv P [ci u, ci v, ci dep] vv i32 (.literal i32 0) 0 0
    (by rw [vdenN_scalar _ _ _ _ rfl]; exact zero_den _) (conv_signed i32 rfl rfl _ (i32v 0 (by decide)))
  have q1 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d1
  have d2 := gSM_decl mv P [ci u, ci v, ci dep, ci 0] vv i32 (.literal i32 1) 1 1
    (by rw [vdenN_scalar _ _ _ _ rfl]; exact one_den _) (conv_signed i32 rfl rfl _ (i32v 1 (by decide)))
  have q2 := (pexecM_prim mv fu (.declare i32 true (.literal i32 1)) _ _).trans d2
  obtain ⟨rA, top', p', hrA, hretA, hpsA, hvvA, hp', hle, hdp, hpb, hpd, hcA, hnA, hwA⟩ :=
    topLoop_exec mv hnv vv P u v dep hdep (dep - 1) 0 1 fu rfl (by decide) (by simp) (by decide) (Or.inl rfl) (by omega)
  have htopK : top' ≤ K := by
    rcases hpd with h1 | h1
    · have : top' = 0 := by
        have : 2 ^ top' = 1 := by rw [← hp']; exact h1
        have h2 := Nat.pow_eq_one.mp this
        omega
      omega
    · have h2 : 2 ^ top' < 2 ^ (K + 1) := by rw [← hp']; omega
      have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h2
      omega
  have hdt : dep < 2 ^ (top' + 1) := by rw [Nat.pow_succ, ← hp']; omega
  have hwA' : pexecM mv fu (.whileLoop (cA mv.nv) (BA mv.nv)) (gS P (cells5 u v dep 0 1)) vv = some rA := hrA
  have hc := cEq_val mv hnv vv P u v dep top' p' huM hvM
  by_cases huv : u = v
  · -- equal vertices
    rw [if_pos huv] at hc
    have e0 := gSM_env mv.nv P (cells5 u v dep top' p') 0 (ci u) rfl (i32v u huM)
    have rr := pstmtM_ret_ok mv (gS P (cells5 u v dep top' p')) vv (.variable i32 mv.nv) (u : Int)
      (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e0)
    have s1 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
    have s2 := pexecM_scope mv fu _ _ _ _ s1
    have tk := gS_takeC P (cells5 u v dep top' p') (cells5 u v dep top' p') [] rfl
    simp only [List.append_nil] at tk
    simp only [tk] at s2
    have s3 := seqM_ret (b := Sk) s2 rfl
    have b1 := pexecM_branch_true mv fu (cEq mv.nv) (retU mv.nv) Sk _ _ 1 hc (by decide) _ s3
    have s4 := seqM_ret (b := (.sequence (.primitive (.declare i32 true (.variable i32 (mv.nv + 3)))) (.sequence
      (.whileLoop (cK mv.nv) (BC mv.nv)) (retRes mv.nv)))) b1 rfl
    have c3 := seqM_some hwA' hretA (by rw [hpsA, hvvA]; exact s4)
    have c2 := seqM_some q2 rfl c3
    have c1 := seqM_some q1 rfl c2
    refine ⟨_, u, top', c1, rfl, hdt, htopK, fun _ => rfl, fun h => absurd huv h, hu, ?_, ⟨_, rfl⟩, ?_, ?_, ?_⟩
    · simp [hvvA]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hcA ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hnA ⊢; omega
    · simp at hwA ⊢; omega
  · -- the descent
    rw [if_neg huv] at hc
    have b1 := pexecM_branch_false mv fu (cEq mv.nv) (retU mv.nv) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    have et := gSM_env mv.nv P (cells5 u v dep top' p') 3 (ci top') rfl (i32v top' (by
      have : top' ≤ K := htopK
      show top' < 2147483648; omega))
    have d3 := gSM_decl mv P (cells5 u v dep top' p') vv i32 (.variable i32 (mv.nv + 3)) top' top'
      (by rw [vdenN_scalar _ _ _ _ rfl, den_variable]; exact et) (conv_signed i32 rfl rfl _ (i32v top' (by
        have : top' ≤ K := htopK
        show top' < 2147483648; omega)))
    have q3 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 3))) _ _).trans d3
    have hk : cmk (top' + 1) = ci top' := by
      show (⟨i32, ((top' + 1 : Nat) : Int) - 1⟩ : Cell) = ⟨i32, (top' : Int)⟩
      congr 1
      push_cast
      omega
    have hHK : TabAll T f N top' := fun k hk' x hx => H k (by omega) x hx
    have hcM : top' + 1 < M31 := by show top' + 1 < 2147483648; omega
    obtain ⟨rC, hrC, hretC, hpsC, hvvC, hcC, hnC, hwC⟩ := descLoop_exec mv hnv hfl hty T f N dep top' p' vv P hN hrows (top' + 1) u v
      (fu - 0) hcM (by simpa using hHK) hu hv (by omega) (by omega)
    rw [hk] at hrC
    have hlt := descA_lt T f N (top' + 1) u v (by simpa using hHK) hu hv
    have hlt0 := (H 0 (by omega) _ hlt.1).2
    have hx0 : ((T.getD 0 []).map (fun x : Nat => (x : Int)))[(descA T (top' + 1) u v).1]? =
        some ((tab T 0 (descA T (top' + 1) u v).1 : Nat) : Int) := by
      unfold tab
      have hl := hlt0.2
      generalize T.getD 0 [] = r at hl ⊢
      rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
      rfl
    have hwr0 : 0 < mv.wrows 0 := by omega
    have hrr := retAnc_val mv hnv hfl hty vv P (cells6 (descA T (top' + 1) u v).1 (descA T (top' + 1) u v).2 dep top' p' (cmk 0))
      (descA T (top' + 1) u v).1 _ _ rfl (Nat.lt_trans hlt.1 hN) hwr0 (hrows 0 hwr0) hx0
      (i32v _ (Nat.lt_trans hlt0.1 hN))
    have d4 := gSM_decl mv P (cells6 (descA T (top' + 1) u v).1 (descA T (top' + 1) u v).2 dep top' p' (cmk 0)) vv i32 _ _ _ hrr
      (conv_signed i32 rfl rfl _ (i32v _ (Nat.lt_trans hlt0.1 hN)))
    have q4 := (pexecM_prim mv fu (.declare i32 true (retAnc mv.nv)) _ _).trans d4
    have e6 := gSM_env mv.nv P (cells6 (descA T (top' + 1) u v).1 (descA T (top' + 1) u v).2 dep top' p' (cmk 0) ++
      [ci (tab T 0 (descA T (top' + 1) u v).1)]) 6 (ci (tab T 0 (descA T (top' + 1) u v).1)) rfl
      (i32v _ (Nat.lt_trans hlt0.1 hN))
    have rr := pstmtM_ret_ok mv (gS P (cells6 (descA T (top' + 1) u v).1 (descA T (top' + 1) u v).2 dep top' p' (cmk 0) ++
      [ci (tab T 0 (descA T (top' + 1) u v).1)])) vv (.variable i32 (mv.nv + 6)) ((tab T 0 (descA T (top' + 1) u v).1 : Nat) : Int)
      (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e6)
    have s1 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
    have s2 := seqM_some q4 rfl s1
    have s3 := seqM_some hrC hretC (by rw [hpsC, hvvC]; exact s2)
    have s4 := seqM_some q3 rfl (by simpa using s3)
    have s5 := seqM_some b1 rfl s4
    have c3 := seqM_some hwA' hretA (by rw [hpsA, hvvA]; exact s5)
    have c2 := seqM_some q2 rfl c3
    have c1 := seqM_some q1 rfl c2
    refine ⟨_, tab T 0 (descA T (top' + 1) u v).1, top', c1, rfl, hdt, htopK, fun h => absurd h huv, fun _ => rfl, hlt0.1, ?_, ⟨_, rfl⟩, ?_, ?_, ?_⟩
    · simp [hvvA, hvvC]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hcA hcC ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hnA hnC ⊢; omega
    · simp at hwA hwC ⊢; omega

end Proofs.TreeLcaExec
