import Proofs.TreeArcCostsExec
import Proofs.InvGcdExec
import Proofs.SegTreeMath
import Proofs.Generated.SquareMatrix

namespace Proofs.SquareMatrixEw
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
open Proofs.TreeArcCostsExec (VC VC_get0 VC_get1 VC_set1)

theorem VC_set0 (A B x : List Int) : upd (VC A B) 0 x = VC x B := by
  funext k; unfold upd VC; split <;> simp_all

/-! ### `a[i] = a[i] bop b[i]` for `i < n * n` on `unsigned long long` vectors (`mat_add_assign`, `mat_sub_assign`) (nv = 2).
Cells: 0 = n, 1 = m = n * n, 2 = i -/

abbrev ewCond (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 2)) (.variable i32 (nv + 1))
abbrev ewWrite (nv : Nat) (bop : Binary) : NStmt :=
  .write (.local 0) u64 (.cast u64 (.variable i32 (nv + 2)))
    (.binary u64 bop (.read u64 (.local 0) (.cast u64 (.variable i32 (nv + 2)))) (.read u64 (.local 1) (.cast u64 (.variable i32 (nv + 2)))))
abbrev ewInc (nv : Nat) : NStmt := .assign (nv + 2) i32 (.binary i32 .add (.variable i32 (nv + 2)) (.literal i32 1))
abbrev ewBody (nv : Nat) (bop : Binary) : Command :=
  .sequence (.scope (.sequence (.primitive (ewWrite nv bop)) Sk)) (.sequence (.primitive (ewInc nv)) Sk)
abbrev bodyEW (nv : Nat) (bop : Binary) : Command :=
  .sequence (.primitive (.declare i32 true (.binary i32 .mul (.variable i32 nv) (.variable i32 nv))))
    (.sequence (.scope (.sequence (.primitive (.declare i32 true (.literal i32 0)))
      (.sequence (.whileLoop (ewCond nv) (ewBody nv bop)) Sk))) Sk)

theorem body_eqAdd : Proofs.SquareMatrixInstance.mat_add_assign_std_vector_unsigned_long_long.body = bodyEW 2 .add := rfl
theorem body_eqSub : Proofs.SquareMatrixInstance.mat_sub_assign_std_vector_unsigned_long_long.body = bodyEW 2 .sub := rfl

abbrev M64 : Int := 18446744073709551616
abbrev EC (n m i : Nat) : List Cell := [ci n, ci m, ci i]

/-- All entries are `unsigned long long` values. -/
def AllU (L : List Int) : Prop := ∀ x ∈ L, u64.valid x = true

theorem allU_get (L : List Int) (h : AllU L) (j : Nat) (hj : j < L.length) : u64.valid (L.getD j 0) = true := by
  have : L.getD j 0 = L[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [this]; exact h _ (List.getElem_mem _)

theorem u64_mod_valid (v : Int) : u64.valid (v % M64) = true := by
  have h1 : 0 ≤ v % M64 := Int.emod_nonneg _ (by decide)
  have h2 : v % M64 < M64 := Int.emod_lt_of_pos _ (by decide)
  simp only [u64, Ty.valid]
  simp
  exact ⟨h1, h2⟩

/-- After `t` iterations the first `t` entries hold `a[j] bop b[j]` and the others are unchanged. -/
def EwInv (bop : Binary) (A B : List Int) (t : Nat) (Vt : List Int) : Prop :=
  Vt.length = A.length ∧ ∀ j, j < A.length →
    Vt.getD j 0 = if j < t then binaryValue bop (A.getD j 0) (B.getD j 0) % M64 else A.getD j 0

theorem ewInv_init (bop : Binary) (A B : List Int) : EwInv bop A B 0 A := by
  refine ⟨rfl, ?_⟩
  intro j hj
  simp

theorem ewInv_step (bop : Binary) (A B : List Int) (t : Nat) (Vt : List Int) (h : EwInv bop A B t Vt) (ht : t < A.length) :
    EwInv bop A B (t + 1) (Vt.set t (binaryValue bop (A.getD t 0) (B.getD t 0) % M64)) := by
  obtain ⟨hl, hj⟩ := h
  refine ⟨by simp [hl], ?_⟩
  intro j hjj
  rw [Proofs.SegTreeMath.getD_setE, hj j hjj]
  by_cases hjt : j = t
  · subst hjt
    rw [if_pos ⟨rfl, by omega⟩, if_pos (by omega)]
  · rw [if_neg (fun hh => hjt hh.1)]
    by_cases hr : j < t
    · rw [if_pos hr, if_pos (by omega)]
    · rw [if_neg hr, if_neg (by omega)]

set_option maxHeartbeats 16000000 in
/-- One iteration: `a[i] = a[i] bop b[i]; i++`. -/
theorem ew_iter (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = u64) (ty1 : mv.ty 1 = u64) (P : List Cell) (fu : Nat)
    (bop : Binary) (n m i : Nat) (A B Vt : List Int) (hn : n < 2147483648) (hm : m < 2147483648) (hi : i < m)
    (hmA : m ≤ A.length) (hmB : m ≤ B.length) (hA : AllU A) (hB : AllU B) (hInv : EwInv bop A B i Vt) :
    ∃ r : PRM, pexecM mv fu (ewBody mv.nv bop) (gS P (EC n m i)) (VC Vt B) = some r ∧ r.ret = none ∧
      r.ps = gS P (EC n m (i + 1)) ∧ r.vv = VC (Vt.set i (binaryValue bop (A.getD i 0) (B.getD i 0) % M64)) B ∧
      r.cost ≤ 500 ∧ r.need ≤ P.length + 60 ∧ r.wk = 1 := by
  have hi31 : i < 2147483648 := by omega
  have hxi : Vt.getD i 0 = A.getD i 0 := by
    have := hInv.2 i (by omega)
    rw [this, if_neg (by omega)]
  have vA : u64.valid (A.getD i 0) = true := allU_get A hA i (by omega)
  have vB : u64.valid (B.getD i 0) = true := allU_get B hB i (by omega)
  have E2 : penvN mv.nv (gS P (EC n m i)) (mv.nv + 2) i32 = some (i : Int) :=
    envs mv P (EC n m i) 2 (ci i) rfl (i32v i hi31)
  have hd := cidx_den _ _ i E2 hi31
  have r0 := rdM_val mv (VC Vt B) _ 0 (by omega) u64 ty0.symm (.cast u64 (.variable i32 (mv.nv + 2))) rfl rfl i hd
    (Vt.getD i 0) (by rw [VC_get0]; exact vec_getI Vt i (by have := hInv.1; omega))
    (by rw [ty0]; rw [hxi]; exact vA)
  have r1 := rdM_val mv (VC Vt B) _ 1 (by omega) u64 ty1.symm (.cast u64 (.variable i32 (mv.nv + 2))) rfl rfl i hd
    (B.getD i 0) (by rw [VC_get1]; exact vec_getI B i (by omega)) (by rw [ty1]; exact vB)
  have hval : vdenM mv (VC Vt B) (penvN mv.nv (gS P (EC n m i)))
      (.binary u64 bop (.read u64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 2))))
        (.read u64 (.local 1) (.cast u64 (.variable i32 (mv.nv + 2))))) =
      some (binaryValue bop (A.getD i 0) (B.getD i 0) % M64) := by
    rw [vdenM_binary mv _ _ u64 bop _ _ rfl, r0, Option.bind_some, r1, Option.bind_some, hxi, convert_u64]
  have hw := pstmtM_write_ok mv (gS P (EC n m i)) (VC Vt B) 0 (by omega) (.cast u64 (.variable i32 (mv.nv + 2)))
    (.binary u64 bop (.read u64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 2))))
      (.read u64 (.local 1) (.cast u64 (.variable i32 (mv.nv + 2)))))
    (binaryValue bop (A.getD i 0) (B.getD i 0) % M64) i hval
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact hd) (by rw [VC_get0]; have := hInv.1; omega)
    (by rw [ty0]; exact u64_mod_valid _)
  rw [ty0, VC_get0, VC_set0] at hw
  have a1 := (pexecM_prim mv fu (ewWrite mv.nv bop) _ _).trans hw
  have b1 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
  have b0 := pexecM_scope mv fu _ _ _ _ b1
  have tk := Proofs.PexecKit.scope_take (gS P (EC n m i)) (gS P (EC n m i)) (by simp) (by simp)
  simp only [tk] at b0
  have E2' : penvN mv.nv (gS P (EC n m i)) (mv.nv + 2) i32 = some (i : Int) := E2
  have e2 := inc_val mv (VC (Vt.set i (binaryValue bop (A.getD i 0) (B.getD i 0) % M64)) B) _ (mv.nv + 2) i E2' (by omega)
  have s2 := gSM_assign mv P (EC n m i) (VC (Vt.set i (binaryValue bop (A.getD i 0) (B.getD i 0) % M64)) B) 2 (by simp) i32 _ _ _ e2
    (ci i) rfl rfl (i32v i hi31) (conv_signed i32 rfl rfl _ (i32v (i + 1) (by show i + 1 < 2147483648; omega)))
  have eB : (EC n m i).set 2 ⟨i32, ((i + 1 : Nat) : Int)⟩ = EC n m (i + 1) := rfl
  rw [eB] at s2
  have a2 := (pexecM_prim mv fu (ewInc mv.nv) _ _).trans s2
  have b3 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  have b4 := seqM_some b0 rfl b3
  refine ⟨_, b4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

theorem cond_ew_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (n m i : Nat) (hm : m < 2147483648) (hi : i < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (EC n m i))) (ewCond mv.nv) = some (if i < m then 1 else 0) := by
  have ei : penvN mv.nv (gS P (EC n m i)) (mv.nv + 2) i32 = some (i : Int) := envs mv P (EC n m i) 2 (ci i) rfl (i32v i hi)
  have em : penvN mv.nv (gS P (EC n m i)) (mv.nv + 1) i32 = some (m : Int) := envs mv P (EC n m i) 1 (ci m) rfl (i32v m hm)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, ei, Option.bind_some, den_variable, em, Option.bind_some]
  by_cases h : i < m
  · have : (i : Int) < (m : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((i : Int) < (m : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 16000000 in
/-- The loop `for (i = 0; i < m; i++) a[i] = a[i] bop b[i];` from the state after `i` iterations. -/
theorem ew_loop (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = u64) (ty1 : mv.ty 1 = u64) (P : List Cell) (bop : Binary)
    (n m : Nat) (A B : List Int) (hn : n < 2147483648) (hm : m < 2147483648) (hmA : m ≤ A.length) (hmB : m ≤ B.length)
    (hA : AllU A) (hB : AllU B) :
    ∀ (d i : Nat) (Vt : List Int) (fu : Nat), i + d = m → EwInv bop A B i Vt → d + 1 ≤ fu →
      ∃ (res : PRM) (Vf : List Int), pexecM mv fu (.whileLoop (ewCond mv.nv) (ewBody mv.nv bop)) (gS P (EC n m i)) (VC Vt B) = some res ∧
        res.ret = none ∧ res.ps = gS P (EC n m m) ∧ res.vv = VC Vf B ∧ EwInv bop A B m Vf ∧
        res.cost ≤ 600 * d + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ d := by
  intro d
  induction d with
  | zero =>
    intro i Vt fu hid hI hfu
    have him : i = m := by omega
    subst him
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_ew_val mv P (VC Vt B) n i i hm hm
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, Vt, rfl, rfl, rfl, rfl, hI, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro i Vt fu hid hI hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hin : i < m := by omega
    have hc := cond_ew_val mv P (VC Vt B) n m i hm (by omega)
    rw [if_pos hin] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := ew_iter mv hnv ty0 ty1 P (fu' + 1) bop n m i A B Vt hn hm hin hmA hmB hA hB hI
    obtain ⟨r2, Vf, h2, ret2, ps2, vv2, hIf, c2, n2, w2⟩ :=
      ih (i + 1) _ fu' (by omega) (ewInv_step bop A B i Vt hI (by omega)) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1, vv1, h2]
    refine ⟨_, Vf, rfl, ret2, ps2, vv2, hIf, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

set_option maxHeartbeats 16000000 in
/-- The whole body of `mat_add_assign` / `mat_sub_assign`. -/
theorem body_execEw (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = u64) (ty1 : mv.ty 1 = u64) (P : List Cell) (bop : Binary)
    (n : Nat) (A B : List Int) (hnn : n * n < 2147483648) (hn : n < 2147483648) (hmA : n * n ≤ A.length) (hmB : n * n ≤ B.length)
    (hA : AllU A) (hB : AllU B) (fu : Nat) (hfu : n * n + 3 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyEW mv.nv bop) (gS P [ci n]) (VC A B) = some r ∧ r.ret = none ∧
      (∃ cl : List Cell, r.ps = gS P cl) ∧ ∃ Vf : List Int, r.vv = VC Vf B ∧ EwInv bop A B (n * n) Vf ∧
        r.cost ≤ 600 * (n * n) + 100 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ n * n := by
  have eN : penvN mv.nv (gS P [ci n]) mv.nv i32 = some (n : Int) := envs mv P [ci n] 0 (ci n) rfl (i32v n hn)
  have e1 : vdenM mv (VC A B) (penvN mv.nv (gS P [ci n])) (.binary i32 .mul (.variable i32 mv.nv) (.variable i32 mv.nv)) =
      some ((n * n : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eN, Option.bind_some, Option.bind_some]
    have : binaryValue .mul (n : Int) (n : Int) = ((n * n : Nat) : Int) := by
      show (n : Int) * (n : Int) = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ hnn)
  have d1 := gSM_decl mv P [ci n] (VC A B) i32 _ ((n * n : Nat) : Int) ((n * n : Nat) : Int) e1
    (conv_signed i32 rfl rfl _ (i32v _ hnn))
  have a1 := (pexecM_prim mv fu (.declare i32 true (.binary i32 .mul (.variable i32 mv.nv) (.variable i32 mv.nv))) _ _).trans d1
  have d2 := gSM_decl mv P [ci n, ci (n * n)] (VC A B) i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a2 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d2
  obtain ⟨rL, Vf, hL, retL, psL, vvL, hIf, cL, nL, wL⟩ :=
    ew_loop mv hnv ty0 ty1 P bop n (n * n) A B hn hnn hmA hmB hA hB (n * n) 0 A fu (by omega) (ewInv_init bop A B) (by omega)
  have hL' : pexecM mv fu (.whileLoop (ewCond mv.nv) (ewBody mv.nv bop)) (gS P ([ci n, ci (n * n)] ++ [ci 0])) (VC A B) = some rL := hL
  have s1 := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have s2 := seqM_some a2 rfl s1
  have s3 := pexecM_scope mv fu _ _ _ _ s2
  rw [psL] at s3
  have tk : (⟨(gS P (EC n (n * n) (n * n))).mem.take (gS P [ci n, ci (n * n)]).mem.length,
      (gS P (EC n (n * n) (n * n))).bs.take (gS P [ci n, ci (n * n)]).bs.length⟩ : PS) = gS P [ci n, ci (n * n)] :=
    gS_takeC P [ci n, ci (n * n)] [ci n, ci (n * n)] [ci (n * n)] rfl
  simp only [tk] at s3
  have s4 := seqM_some s3 rfl (pexecM_skip mv fu _ _)
  have s5 := seqM_some a1 rfl s4
  refine ⟨_, s5, rfl, ⟨[ci n, ci (n * n)], rfl⟩, Vf, ?_, hIf, ?_, ?_, ?_⟩
  · simp [vvL]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, psL] at nL ⊢; omega
  · simp at wL ⊢; omega

end Proofs.SquareMatrixEw
