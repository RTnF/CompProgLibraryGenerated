import Proofs.MultiVecCallN
import Proofs.ForLoopBN
import Proofs.FloydNestedExec
import Proofs.TreeAncestorMath
import Proofs.TopoSortExec
import Proofs.Generated.TreeAncestor

namespace Proofs.TreeAncestorExec
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
open Proofs.TreeAncestorMath (tab ancQ ancQ_zero ancQ_succ TabOK bits bits_zero bits_succ)

/-! ### `tree_ancestor` (nv = 1: the nested table is slot 0).  Cells: 0 = v, 1 = i, 2 = k, 3 = j -/

abbrev cW (nv : Nat) : NExpr := .binary bT .le (.variable i32 (nv + 3)) (.variable i32 (nv + 1))
abbrev bitE (nv : Nat) : NExpr :=
  .binary bT .eq (.divrem i32 true (.divrem i32 false (.variable i32 (nv + 1)) (.variable i32 (nv + 3))) (.literal i32 2))
    (.literal i32 1)
abbrev rdE (nv : Nat) : NExpr :=
  .read i32 (.row (.local 0) (.integer i32) (.cast u64 (.variable i32 (nv + 2)))) (.cast u64 (.variable i32 (nv + 0)))
abbrev asV (nv : Nat) : NStmt := .assign (nv + 0) i32 (rdE nv)
abbrev Yb (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (asV nv)) Sk)) Sk
abbrev updJ (nv : Nat) : NStmt := .assign (nv + 3) i32 (.binary i32 .mul (.variable i32 (nv + 3)) (.literal i32 2))
abbrev updK (nv : Nat) : NStmt := .assign (nv + 2) i32 (.binary i32 .add (.variable i32 (nv + 2)) (.literal i32 1))
abbrev Bw (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (bitE nv) (Yb nv) Sk)
    (.sequence (.primitive (updJ nv)) (.sequence (.primitive (updK nv)) Sk)))) Sk
abbrev bodyAN (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.literal i32 0))) (.sequence (.primitive (.declare i32 true (.literal i32 1)))
    (.sequence (.whileLoop (cW nv) (Bw nv)) (.sequence (.primitive (.ret (.variable i32 nv))) Sk)))

theorem body_eqAN : Proofs.TreeAncestorInstance.tree_ancestor.body = bodyAN 1 := rfl

theorem le_conv (x y : Int) : bT.convert (binaryValue .le x y) = some (if x ≤ y then 1 else 0) := by
  by_cases h : x ≤ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem eq_conv (x y : Int) : bT.convert (binaryValue .eq x y) = some (if x = y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem divrem_nat (a b : Nat) (hb : 0 < b) (ha : a < M31) :
    checkedDivRem i32 false (a : Int) (b : Int) = some ((a / b : Nat) : Int) ∧
    checkedDivRem i32 true (a : Int) (b : Int) = some ((a % b : Nat) : Int) := by
  have hq : (a : Int).tdiv (b : Int) = ((a / b : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg a)]; exact (Int.natCast_div a b).symm
  have hr : (a : Int).tmod (b : Int) = ((a % b : Nat) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg a)]; exact (Int.natCast_mod a b).symm
  have hvq : i32.valid (((a / b : Nat) : Int)) = true := validN _ (by have := Nat.div_le_self a b; have : a < 2147483648 := ha; omega)
  have hvr : i32.valid (((a % b : Nat) : Int)) = true := validN _ (by have := Nat.mod_le a b; have : a < 2147483648 := ha; omega)
  have hb0 : ((b : Int) == 0) = false := by simp; omega
  constructor
  · unfold checkedDivRem
    rw [hb0, hq]
    simp only [Bool.false_eq_true, ↓reduceIte, hvq, Bool.not_true]
    exact conv_signed i32 rfl rfl _ hvq
  · unfold checkedDivRem
    rw [hb0, hq, hr]
    simp only [Bool.false_eq_true, ↓reduceIte, hvq, Bool.not_true]
    exact conv_signed i32 rfl rfl _ hvr

abbrev cells4 (v i k j : Nat) : List Cell := [ci v, ci i, ci k, ci j]

theorem condW_val (mv : MV) (hnv : mv.nv = 1) (vv : Nat → List Int) (P : List Cell) (v i k j : Nat)
    (hi : i < M31) (hj : j < M31) :
    vdenN mv vv (penvN mv.nv (gS P (cells4 v i k j))) (cW mv.nv) = some (if j ≤ i then 1 else 0) := by
  have e1 := gSM_env mv.nv P (cells4 v i k j) 1 (ci i) rfl (i32v i hi)
  have e3 := gSM_env mv.nv P (cells4 v i k j) 3 (ci j) rfl (i32v j hj)
  rw [vdenN_scalar _ _ _ _ rfl, den_binary, den_variable, e3, Option.bind_some, den_variable, e1, Option.bind_some]
  have : binaryValue .le (j : Int) (i : Int) = if (j : Int) ≤ (i : Int) then 1 else 0 := by
    show (if (j : Int) ≤ (i : Int) then 1 else 0) = _; rfl
  rw [le_conv]
  by_cases h : j ≤ i
  · have : (j : Int) ≤ (i : Int) := by omega
    simp [h, this]
  · have : ¬ ((j : Int) ≤ (i : Int)) := by omega
    simp [h, this]

theorem bitE_val (mv : MV) (hnv : mv.nv = 1) (vv : Nat → List Int) (P : List Cell) (v i k j : Nat)
    (hi : i < M31) (hj : j < M31) (hj0 : 0 < j) :
    vdenN mv vv (penvN mv.nv (gS P (cells4 v i k j))) (bitE mv.nv) = some (if (i / j) % 2 = 1 then 1 else 0) := by
  have e1 := gSM_env mv.nv P (cells4 v i k j) 1 (ci i) rfl (i32v i hi)
  have e3 := gSM_env mv.nv P (cells4 v i k j) 3 (ci j) rfl (i32v j hj)
  obtain ⟨d1, _⟩ := divrem_nat i j hj0 hi
  obtain ⟨_, d2⟩ := divrem_nat (i / j) 2 (by omega) (by have := Nat.div_le_self i j; omega)
  have d2' : checkedDivRem i32 true ((i / j : Nat) : Int) 2 = some ((i / j % 2 : Nat) : Int) := d2
  rw [vdenN_scalar _ _ _ _ rfl, den_binary, den_divrem, den_divrem, den_variable, e1, Option.bind_some, den_variable, e3,
    Option.bind_some, d1, Option.bind_some, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, d2',
    Option.bind_some, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some, eq_conv]
  generalize i / j = q
  by_cases h : q % 2 = 1
  · have : ((q % 2 : Nat) : Int) = 1 := by omega
    simp [h, this]
  · have : ¬ (((q % 2 : Nat) : Int) = 1) := by omega
    simp [h, this]
    omega

theorem readA_val (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = i32)
    (vv : Nat → List Int) (P : List Cell) (v i k j : Nat) (r : List Int) (x : Int)
    (hk : k < M31) (hv : v < M31) (hwr : k < mv.wrows 0) (hr : vv (rowKey 0 k) = r) (hx : r[v]? = some x)
    (hxv : i32.valid x = true) :
    vdenN mv vv (penvN mv.nv (gS P (cells4 v i k j))) (rdE mv.nv) = some x := by
  have e0 := cidx_den (penvN mv.nv (gS P (cells4 v i k j))) (mv.nv + 0) v
    (gSM_env mv.nv P (cells4 v i k j) 0 (ci v) rfl (i32v v hv)) hv
  have e2 := cidx_den (penvN mv.nv (gS P (cells4 v i k j))) (mv.nv + 2) k
    (gSM_env mv.nv P (cells4 v i k j) 2 (ci k) rfl (i32v k hk)) hk
  simp only [rdE, vdenN]
  rw [if_pos ⟨by omega, hfl, hty.symm, hty.symm, rfl, rfl⟩]
  rw [e2, Option.bind_some, e0, Option.bind_some, if_pos ⟨Int.natCast_nonneg k, by rw [Int.toNat_natCast]; exact hwr⟩,
    Int.toNat_natCast, hr]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg v), Int.toNat_natCast, hx, Option.bind_some, hty, if_pos hxv]

set_option maxHeartbeats 8000000 in
/-- One iteration of the loop. -/
theorem iter_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = i32) (T : List (List Nat))
    (N i : Nat) (vv : Nat → List Int) (P : List Cell) (v k j : Nat) (hN : N < M31) (hi : i < 1073741824) (hj0 : 0 < j)
    (hji : j ≤ i) (hv : v < N) (hk : k < M31) (hk1 : k + 1 < M31)
    (hrows : ∀ t, t < mv.wrows 0 → vv (rowKey 0 t) = (T.getD t []).map (fun x : Nat => (x : Int)))
    (hbit : (i / j) % 2 = 1 → k < mv.wrows 0 ∧ v < (T.getD k []).length ∧ tab T k v < N) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Bw mv.nv) (gS P (cells4 v i k j)) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (cells4 (if (i / j) % 2 = 1 then tab T k v else v) i (k + 1) (j * 2)) ∧ r.vv = vv ∧
      r.cost ≤ 200 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 := by
  have hiM : i < M31 := by have : i < 1073741824 := hi; show i < 2147483648; omega
  have hjM : j < M31 := by show j < 2147483648; omega
  have hvM : v < M31 := Nat.lt_trans hv hN
  have vb := bitE_val mv hnv vv P v i k j hiM hjM hj0
  -- the branch
  obtain ⟨v', r1, hr1, hret1, hps1, hvv1, hc1, hn1, hw1, hv'def, hv'N⟩ :
      ∃ (v' : Nat) (r1 : PRM), pexecM mv fu (.branch (bitE mv.nv) (Yb mv.nv) Sk) (gS P (cells4 v i k j)) vv = some r1 ∧
        r1.ret = none ∧ r1.ps = gS P (cells4 v' i k j) ∧ r1.vv = vv ∧ r1.cost ≤ 80 ∧ r1.need ≤ P.length + 50 ∧ r1.wk = 0 ∧
        v' = (if (i / j) % 2 = 1 then tab T k v else v) ∧ v' < N := by
    by_cases hb : (i / j) % 2 = 1
    · obtain ⟨hwr, hlen, hlt⟩ := hbit hb
      rw [if_pos hb] at vb
      have hx : ((T.getD k []).map (fun x : Nat => (x : Int)))[v]? = some ((tab T k v : Nat) : Int) := by
        unfold tab
        generalize T.getD k [] = r at hlen ⊢
        rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
        rfl
      have hrd := readA_val mv hnv hfl hty vv P v i k j _ _ hk hvM hwr (hrows k hwr) hx
        (i32v _ (by have : tab T k v < N := hlt; have : N < M31 := hN; omega))
      have as := gSM_assign mv P (cells4 v i k j) vv 0 (by simp) i32 (rdE mv.nv) _ _ hrd (ci v) rfl rfl (i32v v hvM)
        (conv_signed i32 rfl rfl _ (i32v _ (by have : tab T k v < N := hlt; have : N < M31 := hN; omega)))
      have a1 := (pexecM_prim mv fu (asV mv.nv) _ _).trans as
      have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
      have a3 := pexecM_scope mv fu _ _ _ _ a2
      have tk := gS_takeC P (cells4 v i k j) (cells4 (tab T k v) i k j) [] rfl
      simp only [List.append_nil] at tk
      have hset : (cells4 v i k j).set 0 ⟨i32, ((tab T k v : Nat) : Int)⟩ = cells4 (tab T k v) i k j := rfl
      rw [hset] at a3
      simp only [tk] at a3
      have a4 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
      have b1 := pexecM_branch_true mv fu (bitE mv.nv) (Yb mv.nv) Sk _ _ 1 vb (by decide) _ a4
      refine ⟨tab T k v, _, b1, rfl, rfl, rfl, ?_, ?_, rfl, by rw [if_pos hb], hlt⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · rw [if_neg hb] at vb
      have b1 := pexecM_branch_false mv fu (bitE mv.nv) (Yb mv.nv) Sk _ _ vb _ (pexecM_skip mv fu _ _)
      refine ⟨v, _, b1, rfl, rfl, rfl, ?_, ?_, rfl, by rw [if_neg hb], hv⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  -- j = j * 2
  have hv'M : v' < M31 := Nat.lt_trans hv'N hN
  have hj2 : j * 2 < M31 := by show j * 2 < 2147483648; omega
  have E3 := gSM_env mv.nv P (cells4 v' i k j) 3 (ci j) rfl (i32v j hjM)
  have hx2 : vdenN mv vv (penvN mv.nv (gS P (cells4 v' i k j)))
      (.binary i32 .mul (.variable i32 (mv.nv + 3)) (.literal i32 2)) = some ((j * 2 : Nat) : Int) := by
    rw [vdenN_scalar _ _ _ _ rfl, den_binary, den_variable, E3, Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
    have : binaryValue .mul (j : Int) 2 = ((j * 2 : Nat) : Int) := by
      show (j : Int) * 2 = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ hj2)
  have as1 := gSM_assign mv P (cells4 v' i k j) vv 3 (by simp) i32 _ _ _ hx2 (ci j) rfl rfl (i32v j hjM)
    (conv_signed i32 rfl rfl _ (i32v _ hj2))
  have u1 := (pexecM_prim mv fu (updJ mv.nv) _ _).trans as1
  have hset1 : (cells4 v' i k j).set 3 ⟨i32, ((j * 2 : Nat) : Int)⟩ = cells4 v' i k (j * 2) := rfl
  rw [hset1] at u1
  -- k = k + 1
  have E2 := gSM_env mv.nv P (cells4 v' i k (j * 2)) 2 (ci k) rfl (i32v k hk)
  have hx3 : vdenN mv vv (penvN mv.nv (gS P (cells4 v' i k (j * 2))))
      (.binary i32 .add (.variable i32 (mv.nv + 2)) (.literal i32 1)) = some ((k + 1 : Nat) : Int) := by
    rw [vdenN_scalar _ _ _ _ rfl, den_binary, den_variable, E2, Option.bind_some, den_literal,
      if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
    have : binaryValue .add (k : Int) 1 = ((k + 1 : Nat) : Int) := by
      show (k : Int) + 1 = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ hk1)
  have as2 := gSM_assign mv P (cells4 v' i k (j * 2)) vv 2 (by simp) i32 _ _ _ hx3 (ci k) rfl rfl (i32v k hk)
    (conv_signed i32 rfl rfl _ (i32v _ hk1))
  have u2 := (pexecM_prim mv fu (updK mv.nv) _ _).trans as2
  have hset2 : (cells4 v' i k (j * 2)).set 2 ⟨i32, ((k + 1 : Nat) : Int)⟩ = cells4 v' i (k + 1) (j * 2) := rfl
  rw [hset2] at u2
  have w3 := seqM_some u2 rfl (pexecM_skip mv fu _ vv)
  have w2 := seqM_some u1 rfl w3
  have w1 := seqM_some hr1 hret1 (by rw [hps1, hvv1]; exact w2)
  have sc := pexecM_scope mv fu _ _ _ _ w1
  have tk := gS_takeC P (cells4 v i k j) (cells4 v' i (k + 1) (j * 2)) [] rfl
  simp only [List.append_nil] at tk
  simp only [tk] at sc
  have w4 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, w4, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hv'def]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc1 ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hn1 ⊢; omega
  · simp; omega

theorem vwp_cW (nv : Nat) : vwp (cW nv) = (3, 3) := by simp [vwp, NExpr.nodes]

set_option maxHeartbeats 16000000 in
/-- The loop `while (j <= i) {...}`: it runs `bits (i / j)` times. -/
theorem while_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = i32) (T : List (List Nat))
    (f : Nat → Nat) (N i : Nat) (vv : Nat → List Int) (P : List Cell) (hN : N < M31) (hi : i < 1073741824)
    (H : TabOK T f N i)
    (hrows : ∀ t, t < mv.wrows 0 → vv (rowKey 0 t) = (T.getD t []).map (fun x : Nat => (x : Int)))
    (hwr : ∀ k, 2 ^ k ≤ i → k < mv.wrows 0) :
    ∀ q k j v fu, j = 2 ^ k → q = i / j → v < N → j < M31 → q + 1 ≤ fu →
      ∃ (res : PRM) (k' j' : Nat), pexecM mv fu (.whileLoop (cW mv.nv) (Bw mv.nv)) (gS P (cells4 v i k j)) vv = some res ∧
        res.ret = none ∧ res.ps = gS P (cells4 (ancQ T q k v) i k' j') ∧ res.vv = vv ∧
        res.cost ≤ 210 * bits q + 20 ∧ res.need ≤ P.length + 60 ∧ res.wk = 0 := by
  have hiM : i < M31 := by have : i < 1073741824 := hi; show i < 2147483648; omega
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro k j v fu hj hq hv hjM hfu
    have hj0 : 0 < j := by rw [hj]; exact Nat.two_pow_pos k
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc : vdenM mv vv (penvN mv.nv (gS P (cells4 v i k j))) (cW mv.nv) = some (if j ≤ i then 1 else 0) :=
      condW_val mv hnv vv P v i k j hiM hjM
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · -- the loop exits
      subst h0
      have hlt : i < j := by
        by_contra hge
        have : 1 ≤ i / j := (Nat.le_div_iff_mul_le hj0).mpr (by omega)
        omega
      rw [if_neg (by omega)] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_cW]
      refine ⟨_, k, j, rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩
      · rw [ancQ_zero]
      · rw [bits_zero]; simp
      · simp [gS_mem_len, gS_bs_len]
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hji : j ≤ i := by
        by_contra hgt
        have : i / j = 0 := Nat.div_eq_of_lt (by omega)
        omega
      rw [if_pos hji] at hc
      have hk30 : k < 30 := by
        by_contra hge
        have : 2 ^ 30 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 ^ 30 = 1073741824 := by norm_num
        omega
      have hk2 : 2 ^ k ≤ i := by rw [← hj]; exact hji
      have hbit : (i / j) % 2 = 1 → k < mv.wrows 0 ∧ v < (T.getD k []).length ∧ tab T k v < N := by
        intro _
        obtain ⟨_, h2, h3⟩ := H k hk2 v hv
        exact ⟨hwr k hk2, h3, h2⟩
      have hkM : k + 1 < M31 := by show k + 1 < 2147483648; omega
      obtain ⟨r, hr, hret, hps, hvv, hc1, hn1, hw1⟩ := iter_exec mv hnv hfl hty T N i vv P v k j hN hi hj0 hji hv (by omega) hkM
        hrows hbit fu'.succ
      have hj2 : j * 2 < M31 := by show j * 2 < 2147483648; omega
      have hv' : (if (i / j) % 2 = 1 then tab T k v else v) < N := by
        by_cases hb : (i / j) % 2 = 1
        · rw [if_pos hb]; exact (H k hk2 v hv).2.1
        · rw [if_neg hb]; exact hv
      have hq2 : (q' + 1) / 2 = i / (j * 2) := by rw [hq, Nat.div_div_eq_div_mul]
      have hj' : j * 2 = 2 ^ (k + 1) := by rw [hj, Nat.pow_succ]
      obtain ⟨r2, k', j', h2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := ih ((q' + 1) / 2) (by omega) (k + 1) (j * 2)
        (if (i / j) % 2 = 1 then tab T k v else v) fu' hj' hq2 hv' hj2 (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, hr, hret, hps, hvv, h2, vwp_cW]
      refine ⟨_, k', j', rfl, hret2, ?_, hvv2, ?_, ?_, ?_⟩
      · rw [hps2, ancQ_succ, ← hq]
      · rw [bits_succ]
        simp [vwp_cW] at *
        omega
      · simp [gS_mem_len, gS_bs_len] at *
        omega
      · simp at *; omega

set_option maxHeartbeats 16000000 in
/-- The whole body of `tree_ancestor`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = i32) (T : List (List Nat))
    (f : Nat → Nat) (N i v : Nat) (vv : Nat → List Int) (P : List Cell) (hN : N < M31) (hi : i < 1073741824)
    (H : TabOK T f N i) (hv : v < N)
    (hrows : ∀ t, t < mv.wrows 0 → vv (rowKey 0 t) = (T.getD t []).map (fun x : Nat => (x : Int)))
    (hwr : ∀ k, 2 ^ k ≤ i → k < mv.wrows 0) (fu : Nat) (hfu : i + 2 ≤ fu) :
    ∃ (r : PRM) (k' j' : Nat), pexecM mv fu (bodyAN mv.nv) (gS P [ci v, ci i]) vv = some r ∧
      r.ret = some ((ancQ T i 0 v : Nat) : Int) ∧ r.ps = gS P (cells4 (ancQ T i 0 v) i k' j') ∧ r.vv = vv ∧
      r.cost ≤ 210 * bits i + 100 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 := by
  have hiM : i < M31 := by have : i < 1073741824 := hi; show i < 2147483648; omega
  have hvM : v < M31 := Nat.lt_trans hv hN
  have d1 := gSM_decl mv P [ci v, ci i] vv i32 (.literal i32 0) 0 0 (by rw [vdenN_scalar _ _ _ _ rfl]; exact zero_den _)
    (conv_signed i32 rfl rfl _ (i32v 0 (by decide)))
  have q1 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d1
  have d2 := gSM_decl mv P [ci v, ci i, ci 0] vv i32 (.literal i32 1) 1 1 (by rw [vdenN_scalar _ _ _ _ rfl]; exact one_den _)
    (conv_signed i32 rfl rfl _ (i32v 1 (by decide)))
  have q2 := (pexecM_prim mv fu (.declare i32 true (.literal i32 1)) _ _).trans d2
  obtain ⟨rw_, k', j', hrw, hret, hps, hvv, hc, hn, hwk⟩ := while_exec mv hnv hfl hty T f N i vv P hN hi H hrows hwr i 0 1 v
    fu (by rfl) (by simp) hv (by decide) (by omega)
  have hfin : ancQ T i 0 v < N := (Proofs.TreeAncestorMath.anc_spec T f N i v H hv).2
  have hfM : ancQ T i 0 v < M31 := Nat.lt_trans hfin hN
  have hv0 : penvN mv.nv (gS P (cells4 (ancQ T i 0 v) i k' j')) (mv.nv + 0) i32 = some ((ancQ T i 0 v : Nat) : Int) :=
    gSM_env mv.nv P (cells4 (ancQ T i 0 v) i k' j') 0 (ci (ancQ T i 0 v)) rfl (i32v _ hfM)
  have rr := pstmtM_ret_ok mv (gS P (cells4 (ancQ T i 0 v) i k' j')) vv (.variable i32 mv.nv) ((ancQ T i 0 v : Nat) : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact hv0)
  have e6 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have c3 := seqM_some hrw hret (by rw [hps, hvv]; exact e6)
  have c2 := seqM_some q2 rfl c3
  have c1 := seqM_some q1 rfl c2
  refine ⟨_, k', j', c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hn ⊢; omega
  · simp; omega

end Proofs.TreeAncestorExec
