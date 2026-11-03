import Proofs.SquareMatrixEw

namespace Proofs.SquareMatrixZero
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
open Proofs.InvGcdExec (vS vr bnd v64 VO VO_get0 VO_set0)
open Proofs.RunLengthExec (inc_val)
open Proofs.SquareMatrixEw (ewCond ewInc EC cond_ew_val u64_mod_valid AllU)

/-! ### `mat_zero`: `a[i] = 0` for `i < n * n` (nv = 1).  Cells: 0 = n, 1 = m = n * n, 2 = i -/

abbrev zWrite (nv : Nat) : NStmt := .write (.local 0) u64 (.cast u64 (.variable i32 (nv + 2))) (.cast u64 (.literal i32 0))
abbrev zBody (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (zWrite nv)) Sk)) (.sequence (.primitive (ewInc nv)) Sk)
abbrev bodyZero (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.binary i32 .mul (.variable i32 nv) (.variable i32 nv))))
    (.sequence (.scope (.sequence (.primitive (.declare i32 true (.literal i32 0)))
      (.sequence (.whileLoop (ewCond nv) (zBody nv)) Sk))) Sk)

theorem body_eqZero : Proofs.SquareMatrixInstance.mat_zero_std_vector_unsigned_long_long.body = bodyZero 1 := rfl

/-- After `t` iterations the first `t` entries are zero and the others are unchanged. -/
def ZInv (A : List Int) (t : Nat) (Vt : List Int) : Prop :=
  Vt.length = A.length ∧ ∀ j, j < A.length → Vt.getD j 0 = if j < t then 0 else A.getD j 0

theorem zInv_init (A : List Int) : ZInv A 0 A := ⟨rfl, fun j _ => by simp⟩

theorem zInv_step (A : List Int) (t : Nat) (Vt : List Int) (h : ZInv A t Vt) (ht : t < A.length) :
    ZInv A (t + 1) (Vt.set t 0) := by
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
theorem z_iter (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = u64) (P : List Cell) (fu : Nat) (n m i : Nat) (A Vt : List Int)
    (hn : n < 2147483648) (hm : m < 2147483648) (hi : i < m) (hmA : m ≤ A.length) (hI : ZInv A i Vt) :
    ∃ r : PRM, pexecM mv fu (zBody mv.nv) (gS P (EC n m i)) (VO Vt) = some r ∧ r.ret = none ∧
      r.ps = gS P (EC n m (i + 1)) ∧ r.vv = VO (Vt.set i 0) ∧ r.cost ≤ 400 ∧ r.need ≤ P.length + 60 ∧ r.wk = 1 := by
  have hi31 : i < 2147483648 := by omega
  have E2 : penvN mv.nv (gS P (EC n m i)) (mv.nv + 2) i32 = some (i : Int) :=
    envs mv P (EC n m i) 2 (ci i) rfl (i32v i hi31)
  have hd := cidx_den _ _ i E2 hi31
  have h0 : (NExpr.cast u64 (.literal i32 0)).denote (penvN mv.nv (gS P (EC n m i))) = some 0 := by
    rw [den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some, convert_u64]
    rfl
  have hw := pstmtM_write_ok mv (gS P (EC n m i)) (VO Vt) 0 (by omega) (.cast u64 (.variable i32 (mv.nv + 2)))
    (.cast u64 (.literal i32 0)) 0 i (by rw [vdenM_scalar _ _ _ _ rfl]; exact h0)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact hd) (by rw [VO_get0]; have := hI.1; omega)
    (by rw [ty0]; exact (show u64.valid 0 = true from rfl))
  rw [ty0, VO_get0, VO_set0] at hw
  have a1 := (pexecM_prim mv fu (zWrite mv.nv) _ _).trans hw
  have b1 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
  have b0 := pexecM_scope mv fu _ _ _ _ b1
  have tk := Proofs.PexecKit.scope_take (gS P (EC n m i)) (gS P (EC n m i)) (by simp) (by simp)
  simp only [tk] at b0
  have e2 := inc_val mv (VO (Vt.set i 0)) _ (mv.nv + 2) i E2 (by omega)
  have s2 := gSM_assign mv P (EC n m i) (VO (Vt.set i 0)) 2 (by simp) i32 _ _ _ e2
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

set_option maxHeartbeats 16000000 in
theorem z_loop (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = u64) (P : List Cell) (n m : Nat) (A : List Int)
    (hn : n < 2147483648) (hm : m < 2147483648) (hmA : m ≤ A.length) :
    ∀ (d i : Nat) (Vt : List Int) (fu : Nat), i + d = m → ZInv A i Vt → d + 1 ≤ fu →
      ∃ (res : PRM) (Vf : List Int), pexecM mv fu (.whileLoop (ewCond mv.nv) (zBody mv.nv)) (gS P (EC n m i)) (VO Vt) = some res ∧
        res.ret = none ∧ res.ps = gS P (EC n m m) ∧ res.vv = VO Vf ∧ ZInv A m Vf ∧
        res.cost ≤ 500 * d + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ d := by
  intro d
  induction d with
  | zero =>
    intro i Vt fu hid hI hfu
    have him : i = m := by omega
    subst him
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_ew_val mv P (VO Vt) n i i hm hm
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
    have hc := cond_ew_val mv P (VO Vt) n m i hm (by omega)
    rw [if_pos hin] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := z_iter mv hnv ty0 P (fu' + 1) n m i A Vt hn hm hin hmA hI
    obtain ⟨r2, Vf, h2, ret2, ps2, vv2, hIf, c2, n2, w2⟩ :=
      ih (i + 1) _ fu' (by omega) (zInv_step A i Vt hI (by omega)) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1, vv1, h2]
    refine ⟨_, Vf, rfl, ret2, ps2, vv2, hIf, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

set_option maxHeartbeats 16000000 in
theorem body_execZero (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = u64) (P : List Cell) (n : Nat) (A : List Int)
    (hnn : n * n < 2147483648) (hn : n < 2147483648) (hmA : n * n ≤ A.length) (fu : Nat) (hfu : n * n + 3 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyZero mv.nv) (gS P [ci n]) (VO A) = some r ∧ r.ret = none ∧
      (∃ cl : List Cell, r.ps = gS P cl) ∧ ∃ Vf : List Int, r.vv = VO Vf ∧ ZInv A (n * n) Vf ∧
        r.cost ≤ 500 * (n * n) + 100 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ n * n := by
  have eN : penvN mv.nv (gS P [ci n]) mv.nv i32 = some (n : Int) := envs mv P [ci n] 0 (ci n) rfl (i32v n hn)
  have e1 : vdenM mv (VO A) (penvN mv.nv (gS P [ci n])) (.binary i32 .mul (.variable i32 mv.nv) (.variable i32 mv.nv)) =
      some ((n * n : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eN, Option.bind_some, Option.bind_some]
    have : binaryValue .mul (n : Int) (n : Int) = ((n * n : Nat) : Int) := by
      show (n : Int) * (n : Int) = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ hnn)
  have d1 := gSM_decl mv P [ci n] (VO A) i32 _ ((n * n : Nat) : Int) ((n * n : Nat) : Int) e1
    (conv_signed i32 rfl rfl _ (i32v _ hnn))
  have a1 := (pexecM_prim mv fu (.declare i32 true (.binary i32 .mul (.variable i32 mv.nv) (.variable i32 mv.nv))) _ _).trans d1
  have d2 := gSM_decl mv P [ci n, ci (n * n)] (VO A) i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a2 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d2
  obtain ⟨rL, Vf, hL, retL, psL, vvL, hIf, cL, nL, wL⟩ :=
    z_loop mv hnv ty0 P n (n * n) A hn hnn hmA (n * n) 0 A fu (by omega) (zInv_init A) (by omega)
  have hL' : pexecM mv fu (.whileLoop (ewCond mv.nv) (zBody mv.nv)) (gS P ([ci n, ci (n * n)] ++ [ci 0])) (VO A) = some rL := hL
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

end Proofs.SquareMatrixZero
