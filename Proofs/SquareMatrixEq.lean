import Proofs.SquareMatrixEw

namespace Proofs.SquareMatrixEq
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
open Proofs.TreeArcCostsExec (VC VC_get0 VC_get1)
open Proofs.SquareMatrixEw (AllU allU_get)

/-! ### `mat_equal`: `same = true; for i < n * n: if (a[i] != b[i]) same = false; return same` (nv = 2).
Cells: 0 = n, 1 = m = n * n, 2 = same (bool), 3 = i -/

abbrev cb (s : Nat) : Cell := ⟨bT, (s : Int)⟩
abbrev EQ (n m s i : Nat) : List Cell := [ci n, ci m, cb s, ci i]

abbrev eqCond (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 3)) (.variable i32 (nv + 1))
abbrev eqNe (nv : Nat) : NExpr :=
  .binary bT .ne (.read u64 (.local 0) (.cast u64 (.variable i32 (nv + 3)))) (.read u64 (.local 1) (.cast u64 (.variable i32 (nv + 3))))
abbrev eqClear (nv : Nat) : NStmt := .assign (nv + 2) bT (.literal bT 0)
abbrev eqInc (nv : Nat) : NStmt := .assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.literal i32 1))
abbrev eqBody (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (eqNe nv) (.sequence (.scope (.sequence (.primitive (eqClear nv)) Sk)) Sk) Sk) Sk))
    (.sequence (.primitive (eqInc nv)) Sk)
abbrev bodyEQ (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.binary i32 .mul (.variable i32 nv) (.variable i32 nv))))
    (.sequence (.primitive (.declare bT true (.literal bT 1)))
      (.sequence (.scope (.sequence (.primitive (.declare i32 true (.literal i32 0)))
        (.sequence (.whileLoop (eqCond nv) (eqBody nv)) Sk)))
        (.sequence (.primitive (.ret (.variable bT (nv + 2)))) Sk)))

theorem body_eqEq : Proofs.SquareMatrixInstance.mat_equal_std_vector_unsigned_long_long.body = bodyEQ 2 := rfl

open Classical in
/-- The flag after `t` iterations. -/
noncomputable def EqInv (A B : List Int) (t s : Nat) : Prop :=
  s = if ∀ j, j < t → A.getD j 0 = B.getD j 0 then 1 else 0

theorem eqInv_init (A B : List Int) : EqInv A B 0 1 := by
  unfold EqInv
  rw [if_pos (fun j hj => absurd hj (Nat.not_lt_zero _))]

open Classical in
theorem eqInv_step (A B : List Int) (t s : Nat) (h : EqInv A B t s) :
    EqInv A B (t + 1) (if A.getD t 0 ≠ B.getD t 0 then 0 else s) := by
  unfold EqInv at *
  by_cases hne : A.getD t 0 ≠ B.getD t 0
  · rw [if_pos hne, if_neg]
    intro hall
    exact hne (hall t (Nat.lt_succ_self t))
  · rw [if_neg hne, h]
    have heq : A.getD t 0 = B.getD t 0 := by simpa using hne
    by_cases hall : ∀ j, j < t → A.getD j 0 = B.getD j 0
    · rw [if_pos hall, if_pos]
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h1 | h1
      · exact hall j h1
      · subst h1; exact heq
    · rw [if_neg hall, if_neg]
      intro hall'
      exact hall (fun j hj => hall' j (Nat.lt_succ_of_lt hj))

theorem cond_eq_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (n m s i : Nat) (hm : m < 2147483648) (hi : i < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (EQ n m s i))) (eqCond mv.nv) = some (if i < m then 1 else 0) := by
  have ei : penvN mv.nv (gS P (EQ n m s i)) (mv.nv + 3) i32 = some (i : Int) := envs mv P (EQ n m s i) 3 (ci i) rfl (i32v i hi)
  have em : penvN mv.nv (gS P (EQ n m s i)) (mv.nv + 1) i32 = some (m : Int) := envs mv P (EQ n m s i) 1 (ci m) rfl (i32v m hm)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, ei, Option.bind_some, den_variable, em, Option.bind_some]
  by_cases h : i < m
  · have : (i : Int) < (m : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((i : Int) < (m : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

theorem ne_eq_val (mv : MV) (ty0 : mv.ty 0 = u64) (ty1 : mv.ty 1 = u64) (P : List Cell) (n m s i : Nat) (A B : List Int)
    (hi31 : i < 2147483648) (hi : i < m) (hmA : m ≤ A.length) (hmB : m ≤ B.length) (hA : AllU A) (hB : AllU B)
    (hnv : mv.nv = 2) :
    vdenM mv (VC A B) (penvN mv.nv (gS P (EQ n m s i))) (eqNe mv.nv) = some (if A.getD i 0 ≠ B.getD i 0 then 1 else 0) := by
  have vA : u64.valid (A.getD i 0) = true := allU_get A hA i (by omega)
  have vB : u64.valid (B.getD i 0) = true := allU_get B hB i (by omega)
  have E3 : penvN mv.nv (gS P (EQ n m s i)) (mv.nv + 3) i32 = some (i : Int) :=
    envs mv P (EQ n m s i) 3 (ci i) rfl (i32v i hi31)
  have hd := cidx_den _ _ i E3 hi31
  have r0 := rdM_val mv (VC A B) _ 0 (by omega) u64 ty0.symm (.cast u64 (.variable i32 (mv.nv + 3))) rfl rfl i hd
    (A.getD i 0) (by rw [VC_get0]; exact vec_getI A i (by omega)) (by rw [ty0]; exact vA)
  have r1 := rdM_val mv (VC A B) _ 1 (by omega) u64 ty1.symm (.cast u64 (.variable i32 (mv.nv + 3))) rfl rfl i hd
    (B.getD i 0) (by rw [VC_get1]; exact vec_getI B i (by omega)) (by rw [ty1]; exact vB)
  rw [vdenM_binary mv _ _ bT .ne _ _ rfl, r0, Option.bind_some, r1, Option.bind_some]
  by_cases h : A.getD i 0 ≠ B.getD i 0
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · have h' : A.getD i 0 = B.getD i 0 := by simpa using h
    simp [binaryValue, h, h', Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 16000000 in
/-- One iteration. -/
theorem eq_iter (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = u64) (ty1 : mv.ty 1 = u64) (P : List Cell) (fu : Nat)
    (n m i s : Nat) (A B : List Int) (hn : n < 2147483648) (hm : m < 2147483648) (hi : i < m)
    (hmA : m ≤ A.length) (hmB : m ≤ B.length) (hA : AllU A) (hB : AllU B) (hs : s ≤ 1) :
    ∃ r : PRM, pexecM mv fu (eqBody mv.nv) (gS P (EQ n m s i)) (VC A B) = some r ∧ r.ret = none ∧
      r.ps = gS P (EQ n m (if A.getD i 0 ≠ B.getD i 0 then 0 else s) (i + 1)) ∧ r.vv = VC A B ∧
      r.cost ≤ 500 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 := by
  have hi31 : i < 2147483648 := by omega
  have hc := ne_eq_val mv ty0 ty1 P n m s i A B hi31 hi hmA hmB hA hB (by omega)
  have hbs : bT.valid (s : Int) = true := by
    have : s = 0 ∨ s = 1 := by omega
    rcases this with rfl | rfl <;> decide
  by_cases hne : A.getD i 0 ≠ B.getD i 0
  · rw [if_pos hne] at hc
    have s1 := gSM_assign mv P (EQ n m s i) (VC A B) 2 (by simp) bT (.literal bT 0) 0 0
      (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show bT.valid 0 = true from rfl)]) (cb s) rfl rfl hbs
      (show bT.convert 0 = some 0 from rfl)
    have eA : (EQ n m s i).set 2 ⟨bT, (0 : Int)⟩ = EQ n m 0 i := rfl
    rw [eA] at s1
    have a1 := (pexecM_prim mv fu (eqClear mv.nv) _ _).trans s1
    have b1 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
    have b0 := pexecM_scope mv fu _ _ _ _ b1
    have tk := Proofs.PexecKit.scope_take (gS P (EQ n m s i)) (gS P (EQ n m 0 i)) (by simp [gS_mem_len]) (by simp [gS_bs_len])
    simp only [tk] at b0
    have b2 := seqM_some b0 rfl (pexecM_skip mv fu _ _)
    have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b2
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    have b5 := pexecM_scope mv fu _ _ _ _ b4
    have tk2 := Proofs.PexecKit.scope_take (gS P (EQ n m s i)) (gS P (EQ n m 0 i)) (by simp [gS_mem_len]) (by simp [gS_bs_len])
    simp only [tk2] at b5
    have E3' : penvN mv.nv (gS P (EQ n m 0 i)) (mv.nv + 3) i32 = some (i : Int) :=
      envs mv P (EQ n m 0 i) 3 (ci i) rfl (i32v i hi31)
    have e2 := inc_val mv (VC A B) _ (mv.nv + 3) i E3' (by omega)
    have s2 := gSM_assign mv P (EQ n m 0 i) (VC A B) 3 (by simp) i32 _ _ _ e2
      (ci i) rfl rfl (i32v i hi31) (conv_signed i32 rfl rfl _ (i32v (i + 1) (by show i + 1 < 2147483648; omega)))
    have eB : (EQ n m 0 i).set 3 ⟨i32, ((i + 1 : Nat) : Int)⟩ = EQ n m 0 (i + 1) := rfl
    rw [eB] at s2
    have a2 := (pexecM_prim mv fu (eqInc mv.nv) _ _).trans s2
    have b6 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
    have b7 := seqM_some b5 rfl b6
    refine ⟨_, b7, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · rw [if_pos hne]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  · rw [if_neg hne] at hc
    have b3 := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (eqClear mv.nv)) Sk)) Sk) Sk _ _ hc _
      (pexecM_skip mv fu _ _)
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    have b5 := pexecM_scope mv fu _ _ _ _ b4
    have tk2 := Proofs.PexecKit.scope_take (gS P (EQ n m s i)) (gS P (EQ n m s i)) (by simp [gS_mem_len]) (by simp [gS_bs_len])
    simp only [tk2] at b5
    have E3' : penvN mv.nv (gS P (EQ n m s i)) (mv.nv + 3) i32 = some (i : Int) :=
      envs mv P (EQ n m s i) 3 (ci i) rfl (i32v i hi31)
    have e2 := inc_val mv (VC A B) _ (mv.nv + 3) i E3' (by omega)
    have s2 := gSM_assign mv P (EQ n m s i) (VC A B) 3 (by simp) i32 _ _ _ e2
      (ci i) rfl rfl (i32v i hi31) (conv_signed i32 rfl rfl _ (i32v (i + 1) (by show i + 1 < 2147483648; omega)))
    have eB : (EQ n m s i).set 3 ⟨i32, ((i + 1 : Nat) : Int)⟩ = EQ n m s (i + 1) := rfl
    rw [eB] at s2
    have a2 := (pexecM_prim mv fu (eqInc mv.nv) _ _).trans s2
    have b6 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
    have b7 := seqM_some b5 rfl b6
    refine ⟨_, b7, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · rw [if_neg hne]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp

set_option maxHeartbeats 16000000 in
/-- The loop from the state after `i` iterations. -/
theorem eq_loop (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = u64) (ty1 : mv.ty 1 = u64) (P : List Cell)
    (n m : Nat) (A B : List Int) (hn : n < 2147483648) (hm : m < 2147483648) (hmA : m ≤ A.length) (hmB : m ≤ B.length)
    (hA : AllU A) (hB : AllU B) :
    ∀ (d i s : Nat) (fu : Nat), i + d = m → EqInv A B i s → d + 1 ≤ fu →
      ∃ (res : PRM) (sF : Nat), pexecM mv fu (.whileLoop (eqCond mv.nv) (eqBody mv.nv)) (gS P (EQ n m s i)) (VC A B) = some res ∧
        res.ret = none ∧ res.ps = gS P (EQ n m sF m) ∧ res.vv = VC A B ∧ EqInv A B m sF ∧
        res.cost ≤ 600 * d + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk = 0 := by
  intro d
  induction d with
  | zero =>
    intro i s fu hid hI hfu
    have him : i = m := by omega
    subst him
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_eq_val mv P (VC A B) n i s i hm hm
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, s, rfl, rfl, rfl, rfl, hI, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  | succ d ih =>
    intro i s fu hid hI hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hin : i < m := by omega
    have hs : s ≤ 1 := by
      unfold EqInv at hI
      rw [hI]; split <;> omega
    have hc := cond_eq_val mv P (VC A B) n m s i hm (by omega)
    rw [if_pos hin] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := eq_iter mv hnv ty0 ty1 P (fu' + 1) n m i s A B hn hm hin hmA hmB hA hB hs
    obtain ⟨r2, sF, h2, ret2, ps2, vv2, hIf, c2, n2, w2⟩ :=
      ih (i + 1) _ fu' (by omega) (eqInv_step A B i s hI) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1, vv1, h2]
    refine ⟨_, sF, rfl, ret2, ps2, vv2, hIf, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

open Classical in
set_option maxHeartbeats 16000000 in
/-- The whole body of `mat_equal`. -/
theorem body_execEq (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = u64) (ty1 : mv.ty 1 = u64) (P : List Cell)
    (n : Nat) (A B : List Int) (hnn : n * n < 2147483648) (hn : n < 2147483648) (hmA : n * n ≤ A.length) (hmB : n * n ≤ B.length)
    (hA : AllU A) (hB : AllU B) (fu : Nat) (hfu : n * n + 3 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyEQ mv.nv) (gS P [ci n]) (VC A B) = some r ∧
      r.ret = some (if ∀ j, j < n * n → A.getD j 0 = B.getD j 0 then 1 else 0) ∧
      (∃ cl : List Cell, r.ps = gS P cl) ∧ r.vv = VC A B ∧
      r.cost ≤ 600 * (n * n) + 200 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 := by
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
  have d2 := gSM_decl mv P [ci n, ci (n * n)] (VC A B) bT (.literal bT 1) 1 1
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show bT.valid 1 = true from rfl)])
    (show bT.convert 1 = some 1 from rfl)
  have a2 := (pexecM_prim mv fu (.declare bT true (.literal bT 1)) _ _).trans d2
  have d3 := gSM_decl mv P [ci n, ci (n * n), cb 1] (VC A B) i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a3 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d3
  obtain ⟨rL, sF, hL, retL, psL, vvL, hIf, cL, nL, wL⟩ :=
    eq_loop mv hnv ty0 ty1 P n (n * n) A B hn hnn hmA hmB hA hB (n * n) 0 1 fu (by omega) (eqInv_init A B) (by omega)
  have hL' : pexecM mv fu (.whileLoop (eqCond mv.nv) (eqBody mv.nv)) (gS P ([ci n, ci (n * n), cb 1] ++ [ci 0])) (VC A B) = some rL := hL
  have s1 := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have s2 := seqM_some a3 rfl s1
  have s3 := pexecM_scope mv fu _ _ _ _ s2
  rw [psL] at s3
  have tk : (⟨(gS P (EQ n (n * n) sF (n * n))).mem.take (gS P [ci n, ci (n * n), cb 1]).mem.length,
      (gS P (EQ n (n * n) sF (n * n))).bs.take (gS P [ci n, ci (n * n), cb 1]).bs.length⟩ : PS) =
        gS P [ci n, ci (n * n), cb sF] :=
    gS_takeC P [ci n, ci (n * n), cb 1] [ci n, ci (n * n), cb sF] [ci (n * n)] rfl
  simp only [tk] at s3
  -- the return
  have hsF : sF ≤ 1 := by
    unfold EqInv at hIf
    rw [hIf]; split <;> omega
  have eS : penvN mv.nv (gS P [ci n, ci (n * n), cb sF]) (mv.nv + 2) bT = some (sF : Int) :=
    envs mv P [ci n, ci (n * n), cb sF] 2 (cb sF) rfl (by
      have : sF = 0 ∨ sF = 1 := by omega
      rcases this with rfl | rfl <;> decide)
  have rr := pstmtM_ret_ok mv (gS P [ci n, ci (n * n), cb sF]) (VC A B) (.variable bT (mv.nv + 2)) (sF : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eS)
  have s4 := seqM_ret (b := Sk) ((pexecM_prim mv fu (.ret (.variable bT (mv.nv + 2))) _ _).trans rr) rfl
  have s5 := seqM_some s3 rfl (by rw [vvL]; exact s4)
  have s6 := seqM_some a2 rfl s5
  have s7 := seqM_some a1 rfl s6
  refine ⟨_, s7, ?_, ⟨_, rfl⟩, rfl, ?_, ?_, ?_⟩
  · show some (sF : Int) = _
    unfold EqInv at hIf
    rw [hIf]; split <;> simp
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, psL] at nL ⊢; omega
  · simp at wL ⊢; omega

end Proofs.SquareMatrixEq
