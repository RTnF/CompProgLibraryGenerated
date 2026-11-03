import Proofs.SquareMatrixZero

namespace Proofs.SquareMatrixId
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
open Proofs.SquareMatrixEw (AllU)

/-! ### `mat_identity` (nv = 1).  Cells: 0 = n, 1 = i, 2 = j -/

abbrev idxIJ (nv : Nat) : NExpr :=
  .cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 (nv + 1)) (.variable i32 (nv + 0))) (.variable i32 (nv + 2)))
abbrev idW0 (nv : Nat) : NStmt := .write (.local 0) u64 (idxIJ nv) (.cast u64 (.literal i32 0))
abbrev idW1 (nv : Nat) : NStmt := .write (.local 0) u64 (idxIJ nv) (.cast u64 (.literal i32 1))
abbrev idCondJ (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 2)) (.variable i32 (nv + 0))
abbrev idCondI (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 1)) (.variable i32 (nv + 0))
abbrev idEq (nv : Nat) : NExpr := .binary bT .eq (.variable i32 (nv + 1)) (.variable i32 (nv + 2))
abbrev idIncJ (nv : Nat) : NStmt := .assign (nv + 2) i32 (.binary i32 .add (.variable i32 (nv + 2)) (.literal i32 1))
abbrev idIncI (nv : Nat) : NStmt := .assign (nv + 1) i32 (.binary i32 .add (.variable i32 (nv + 1)) (.literal i32 1))
abbrev idBodyJ (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (idW0 nv))
    (.sequence (.branch (idEq nv) (.sequence (.scope (.sequence (.primitive (idW1 nv)) Sk)) Sk) Sk) Sk)))
    (.sequence (.primitive (idIncJ nv)) Sk)
abbrev idInnerJ (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.literal i32 0))) (.sequence (.whileLoop (idCondJ nv) (idBodyJ nv)) Sk)
abbrev idBodyI (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.scope (idInnerJ nv)) Sk)) (.sequence (.primitive (idIncI nv)) Sk)
abbrev bodyId (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.declare i32 true (.literal i32 0))) (.sequence (.whileLoop (idCondI nv) (idBodyI nv)) Sk))) Sk

theorem body_eqId : Proofs.SquareMatrixInstance.mat_identity_std_vector_unsigned_long_long.body = bodyId 1 := rfl

abbrev CIJ (n i j : Nat) : List Cell := [ci n, ci i, ci j]

/-- The entry `idx` of the identity matrix of size `n`. -/
def idv (n idx : Nat) : Int := if idx / n = idx % n then 1 else 0

/-- After the first `K` entries have been written, they hold the identity matrix and the others are unchanged. -/
def IdInv (n : Nat) (A : List Int) (K : Nat) (Vt : List Int) : Prop :=
  Vt.length = A.length ∧ ∀ idx, idx < A.length → Vt.getD idx 0 = if idx < K then idv n idx else A.getD idx 0

theorem idInv_init (n : Nat) (A : List Int) : IdInv n A 0 A := ⟨rfl, fun idx _ => by simp⟩

theorem idInv_step (n : Nat) (A : List Int) (K : Nat) (Vt : List Int) (h : IdInv n A K Vt) (hK : K < A.length) :
    IdInv n A (K + 1) (Vt.set K (idv n K)) := by
  obtain ⟨hl, hj⟩ := h
  refine ⟨by simp [hl], ?_⟩
  intro j hjj
  rw [Proofs.SegTreeMath.getD_setE, hj j hjj]
  by_cases hjt : j = K
  · subst hjt
    rw [if_pos ⟨rfl, by omega⟩, if_pos (by omega)]
  · rw [if_neg (fun hh => hjt hh.1)]
    by_cases hr : j < K
    · rw [if_pos hr, if_pos (by omega)]
    · rw [if_neg hr, if_neg (by omega)]

theorem div_mod_ij (n i j : Nat) (hj : j < n) : (i * n + j) / n = i ∧ (i * n + j) % n = j := by
  have hn : 0 < n := by omega
  have h1 : (i * n + j) / n = i := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.succ_mul]; omega
  refine ⟨h1, ?_⟩
  have := Nat.div_add_mod (i * n + j) n
  rw [h1, Nat.mul_comm n i] at this
  omega

theorem idv_ij (n i j : Nat) (hj : j < n) : idv n (i * n + j) = if i = j then 1 else 0 := by
  unfold idv
  obtain ⟨h1, h2⟩ := div_mod_ij n i j hj
  rw [h1, h2]

theorem lt_cells (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (a b x y : Nat)
    (ha : cl[a]? = some (ci x)) (hb : cl[b]? = some (ci y)) (hx : x < 2147483648) (hy : y < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .lt (.variable i32 (mv.nv + a)) (.variable i32 (mv.nv + b))) =
      some (if x < y then 1 else 0) := by
  have ex : penvN mv.nv (gS P cl) (mv.nv + a) i32 = some (x : Int) := envs mv P cl a (ci x) ha (i32v x hx)
  have ey : penvN mv.nv (gS P cl) (mv.nv + b) i32 = some (y : Int) := envs mv P cl b (ci y) hb (i32v y hy)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, ex, Option.bind_some, den_variable, ey, Option.bind_some]
  by_cases h : x < y
  · have : (x : Int) < (y : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((x : Int) < (y : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

theorem eq_cells (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (a b x y : Nat)
    (ha : cl[a]? = some (ci x)) (hb : cl[b]? = some (ci y)) (hx : x < 2147483648) (hy : y < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .eq (.variable i32 (mv.nv + a)) (.variable i32 (mv.nv + b))) =
      some (if x = y then 1 else 0) := by
  have ex : penvN mv.nv (gS P cl) (mv.nv + a) i32 = some (x : Int) := envs mv P cl a (ci x) ha (i32v x hx)
  have ey : penvN mv.nv (gS P cl) (mv.nv + b) i32 = some (y : Int) := envs mv P cl b (ci y) hb (i32v y hy)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, ex, Option.bind_some, den_variable, ey, Option.bind_some]
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : ¬ ((x : Int) = (y : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

theorem idxIJ_den (mv : MV) (P : List Cell) (n i j : Nat) (hnn : n * n < 2147483648) (hi : i < n) (hj : j < n) :
    (idxIJ mv.nv).denote (penvN mv.nv (gS P (CIJ n i j))) = some ((i * n + j : Nat) : Int) := by
  have hsm : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
  have hsm2 : (i + 1) * n = i * n + n := Nat.succ_mul i n
  have hin : i * n + j < n * n := by omega
  have hn31 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hin' : i * n ≤ n * n := by omega
  have hA : i * n < 2147483648 := Nat.lt_of_le_of_lt hin' hnn
  have hB : i * n + j < 2147483648 := Nat.lt_trans hin hnn
  have en : penvN mv.nv (gS P (CIJ n i j)) (mv.nv + 0) i32 = some (n : Int) := envs mv P (CIJ n i j) 0 (ci n) rfl (i32v n hn31)
  have ei : penvN mv.nv (gS P (CIJ n i j)) (mv.nv + 1) i32 = some (i : Int) := envs mv P (CIJ n i j) 1 (ci i) rfl (i32v i (by show i < 2147483648; omega))
  have ej : penvN mv.nv (gS P (CIJ n i j)) (mv.nv + 2) i32 = some (j : Int) := envs mv P (CIJ n i j) 2 (ci j) rfl (i32v j (by show j < 2147483648; omega))
  show (NExpr.cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 (mv.nv + 1)) (.variable i32 (mv.nv + 0)))
    (.variable i32 (mv.nv + 2)))).denote _ = _
  have e1 : binaryValue .mul (i : Int) (n : Int) = ((i * n : Nat) : Int) := by
    show (i : Int) * (n : Int) = _; push_cast; rfl
  have e2 : binaryValue .add ((i * n : Nat) : Int) (j : Int) = ((i * n + j : Nat) : Int) := by
    show ((i * n : Nat) : Int) + (j : Int) = _; push_cast; rfl
  have c1 : i32.convert (binaryValue .mul (i : Int) (n : Int)) = some ((i * n : Nat) : Int) := by
    rw [e1]; exact conv_signed i32 rfl rfl _ (i32v _ hA)
  have c2 : i32.convert (binaryValue .add ((i * n : Nat) : Int) (j : Int)) = some ((i * n + j : Nat) : Int) := by
    rw [e2]; exact conv_signed i32 rfl rfl _ (i32v _ hB)
  have c3 : u64.convert ((i * n + j : Nat) : Int) = some ((i * n + j : Nat) : Int) := by
    have hlt : ((i * n + j : Nat) : Int) < 18446744073709551616 := by omega
    rw [convert_u64, Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt]
  rw [den_cast, den_binary, den_binary, den_variable, den_variable, den_variable, ei, en, ej]
  show ((((some (i : Int)).bind fun a => (some (n : Int)).bind fun b => i32.convert (binaryValue Binary.mul a b)).bind fun a =>
          (some (j : Int)).bind fun b => i32.convert (binaryValue Binary.add a b)).bind fun v => u64.convert v) = _
  rw [Option.bind_some]
  rw [Option.bind_some]
  rw [c1, Option.bind_some, Option.bind_some, c2, Option.bind_some, c3]

set_option maxHeartbeats 16000000 in
/-- One iteration of the inner loop: `a[i * n + j] = 0; if (i == j) a[i * n + j] = 1; j++`. -/
theorem id_inner_iter (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = u64) (P : List Cell) (fu : Nat) (n i j : Nat) (A Vt : List Int)
    (hnn : n * n < 2147483648) (hi : i < n) (hj : j < n) (hlenA : n * n ≤ A.length) (hI : IdInv n A (i * n + j) Vt) :
    ∃ r : PRM, pexecM mv fu (idBodyJ mv.nv) (gS P (CIJ n i j)) (VO Vt) = some r ∧ r.ret = none ∧
      r.ps = gS P (CIJ n i (j + 1)) ∧ r.vv = VO (Vt.set (i * n + j) (idv n (i * n + j))) ∧
      r.cost ≤ 800 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 2 := by
  have hsm : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
  have hsm2 : (i + 1) * n = i * n + n := Nat.succ_mul i n
  have hK : i * n + j < n * n := by omega
  have hn31 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hKlt : i * n + j < Vt.length := by have := hI.1; omega
  have hd := idxIJ_den mv P n i j hnn hi hj
  have h0 : (NExpr.cast u64 (.literal i32 0)).denote (penvN mv.nv (gS P (CIJ n i j))) = some 0 := by
    rw [den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some, convert_u64]
    rfl
  have h1 : (NExpr.cast u64 (.literal i32 1)).denote (penvN mv.nv (gS P (CIJ n i j))) = some 1 := by
    rw [den_cast, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some, convert_u64]
    rfl
  have hw0 := pstmtM_write_ok mv (gS P (CIJ n i j)) (VO Vt) 0 (by omega) (idxIJ mv.nv) (.cast u64 (.literal i32 0)) 0 (i * n + j)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact h0) (by rw [vdenM_scalar _ _ _ _ rfl]; exact hd)
    (by rw [VO_get0]; exact hKlt) (by rw [ty0]; exact (show u64.valid 0 = true from rfl))
  rw [ty0, VO_get0, VO_set0] at hw0
  have a0 := (pexecM_prim mv fu (idW0 mv.nv) _ _).trans hw0
  have hdn : idv n (i * n + j) = if i = j then 1 else 0 := idv_ij n i j hj
  -- the branch
  obtain ⟨rb, hb, retb, psb, vvb, cb, nb, wb⟩ : ∃ rb : PRM,
      pexecM mv fu (.branch (idEq mv.nv) (.sequence (.scope (.sequence (.primitive (idW1 mv.nv)) Sk)) Sk) Sk)
        (gS P (CIJ n i j)) (VO (Vt.set (i * n + j) 0)) = some rb ∧ rb.ret = none ∧ rb.ps = gS P (CIJ n i j) ∧
      rb.vv = VO (Vt.set (i * n + j) (idv n (i * n + j))) ∧ rb.cost ≤ 400 ∧ rb.need ≤ P.length + 60 ∧ rb.wk ≤ 1 := by
    have hc := eq_cells mv P (VO (Vt.set (i * n + j) 0)) (CIJ n i j) 1 2 i j rfl rfl (by omega) (by omega)
    by_cases hij : i = j
    · rw [if_pos hij] at hc
      have hw1 := pstmtM_write_ok mv (gS P (CIJ n i j)) (VO (Vt.set (i * n + j) 0)) 0 (by omega) (idxIJ mv.nv)
        (.cast u64 (.literal i32 1)) 1 (i * n + j) (by rw [vdenM_scalar _ _ _ _ rfl]; exact h1)
        (by rw [vdenM_scalar _ _ _ _ rfl]; exact hd) (by rw [VO_get0]; simp; exact hKlt) (by rw [ty0]; exact (show u64.valid 1 = true from rfl))
      rw [ty0, VO_get0, VO_set0] at hw1
      have a1 := (pexecM_prim mv fu (idW1 mv.nv) _ _).trans hw1
      have b1 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
      have b0 := pexecM_scope mv fu _ _ _ _ b1
      have tk := Proofs.PexecKit.scope_take (gS P (CIJ n i j)) (gS P (CIJ n i j)) (by simp) (by simp)
      simp only [tk] at b0
      have b2 := seqM_some b0 rfl (pexecM_skip mv fu _ _)
      have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b2
      refine ⟨_, b3, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · rw [hdn, if_pos hij]
        simp [List.set_set]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
    · rw [if_neg hij] at hc
      have b3 := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (idW1 mv.nv)) Sk)) Sk) Sk _ _ hc _
        (pexecM_skip mv fu _ _)
      refine ⟨_, b3, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp [hdn, hij]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
  have c1 := seqM_some hb retb (pexecM_skip mv fu rb.ps rb.vv)
  have c2 := seqM_some a0 rfl c1
  have c3 := pexecM_scope mv fu _ _ _ _ c2
  rw [psb, vvb] at c3
  have tk2 := Proofs.PexecKit.scope_take (gS P (CIJ n i j)) (gS P (CIJ n i j)) (by simp) (by simp)
  simp only [tk2] at c3
  have hj31 : j < 2147483648 := by omega
  have E2 : penvN mv.nv (gS P (CIJ n i j)) (mv.nv + 2) i32 = some (j : Int) :=
    envs mv P (CIJ n i j) 2 (ci j) rfl (i32v j hj31)
  have e2 := inc_val mv (VO (Vt.set (i * n + j) (idv n (i * n + j)))) _ (mv.nv + 2) j E2 (by omega)
  have s2 := gSM_assign mv P (CIJ n i j) (VO (Vt.set (i * n + j) (idv n (i * n + j)))) 2 (by simp) i32 _ _ _ e2
    (ci j) rfl rfl (i32v j hj31) (conv_signed i32 rfl rfl _ (i32v (j + 1) (by show j + 1 < 2147483648; omega)))
  have eB : (CIJ n i j).set 2 ⟨i32, ((j + 1 : Nat) : Int)⟩ = CIJ n i (j + 1) := rfl
  rw [eB] at s2
  have a2 := (pexecM_prim mv fu (idIncJ mv.nv) _ _).trans s2
  have b3 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  have b4 := seqM_some c3 rfl b3
  refine ⟨_, b4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    omega
  · simp
    omega

theorem cond_id_j (mv : MV) (P : List Cell) (vv : Nat → List Int) (n i j : Nat) (hn : n < 2147483648) (hj : j < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (CIJ n i j))) (idCondJ mv.nv) = some (if j < n then 1 else 0) :=
  lt_cells mv P vv (CIJ n i j) 2 0 j n rfl rfl hj hn

set_option maxHeartbeats 16000000 in
/-- The inner loop `for (j = 0; j < n; j++) ...` from the state after `j` iterations. -/
theorem id_inner_loop (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = u64) (P : List Cell) (n i : Nat) (A : List Int)
    (hnn : n * n < 2147483648) (hi : i < n) (hlenA : n * n ≤ A.length) :
    ∀ (d j : Nat) (Vt : List Int) (fu : Nat), j + d = n → IdInv n A (i * n + j) Vt → d + 1 ≤ fu →
      ∃ (res : PRM) (Vf : List Int), pexecM mv fu (.whileLoop (idCondJ mv.nv) (idBodyJ mv.nv)) (gS P (CIJ n i j)) (VO Vt) = some res ∧
        res.ret = none ∧ res.ps = gS P (CIJ n i n) ∧ res.vv = VO Vf ∧ IdInv n A (i * n + n) Vf ∧
        res.cost ≤ 900 * d + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ 2 * d := by
  have hn31 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  intro d
  induction d with
  | zero =>
    intro j Vt fu hid hI hfu
    have hjn : j = n := by omega
    subst hjn
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_id_j mv P (VO Vt) j i j hn31 hn31
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, Vt, rfl, rfl, rfl, rfl, hI, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro j Vt fu hid hI hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hin : j < n := by omega
    have hsm : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
    have hsm2 : (i + 1) * n = i * n + n := Nat.succ_mul i n
    have hKA : i * n + j < A.length := by omega
    have hc := cond_id_j mv P (VO Vt) n i j hn31 (by omega)
    rw [if_pos hin] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := id_inner_iter mv hnv ty0 P (fu' + 1) n i j A Vt hnn hi hin hlenA hI
    obtain ⟨r2, Vf, h2, ret2, ps2, vv2, hIf, c2, n2, w2⟩ :=
      ih (j + 1) _ fu' (by omega) (idInv_step n A (i * n + j) Vt hI hKA) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1, vv1, h2]
    refine ⟨_, Vf, rfl, ret2, ps2, vv2, hIf, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

set_option maxHeartbeats 16000000 in
/-- One iteration of the outer loop: the inner loop over `j`, then `i++`. -/
theorem id_outer_iter (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = u64) (P : List Cell) (fu : Nat) (n i : Nat) (A Vt : List Int)
    (hnn : n * n < 2147483648) (hi : i < n) (hlenA : n * n ≤ A.length) (hI : IdInv n A (i * n) Vt) (hfu : n + 4 ≤ fu) :
    ∃ (r : PRM) (Vf : List Int), pexecM mv fu (idBodyI mv.nv) (gS P [ci n, ci i]) (VO Vt) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, ci (i + 1)] ∧ r.vv = VO Vf ∧ IdInv n A ((i + 1) * n) Vf ∧
      r.cost ≤ 900 * n + 100 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 2 * n + 2 := by
  have hn31 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hi31 : i < 2147483648 := by omega
  have hsm2 : (i + 1) * n = i * n + n := Nat.succ_mul i n
  have d2 := gSM_decl mv P [ci n, ci i] (VO Vt) i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a2 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d2
  obtain ⟨rL, Vf, hL, retL, psL, vvL, hIf, cL, nL, wL⟩ :=
    id_inner_loop mv hnv ty0 P n i A hnn hi hlenA n 0 Vt fu (by omega) (by simpa using hI) (by omega)
  have hL' : pexecM mv fu (.whileLoop (idCondJ mv.nv) (idBodyJ mv.nv)) (gS P ([ci n, ci i] ++ [ci 0])) (VO Vt) = some rL := hL
  have s1 := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have s2 := seqM_some a2 rfl s1
  have s3 := pexecM_scope mv fu _ _ _ _ s2
  rw [psL, vvL] at s3
  have tk : (⟨(gS P (CIJ n i n)).mem.take (gS P [ci n, ci i]).mem.length,
      (gS P (CIJ n i n)).bs.take (gS P [ci n, ci i]).bs.length⟩ : PS) = gS P [ci n, ci i] :=
    gS_takeC P [ci n, ci i] [ci n, ci i] [ci n] rfl
  simp only [tk] at s3
  have s4 := seqM_some s3 rfl (pexecM_skip mv fu _ _)
  have s5 := pexecM_scope mv fu _ _ _ _ s4
  have tk2 := Proofs.PexecKit.scope_take (gS P [ci n, ci i]) (gS P [ci n, ci i]) (by simp) (by simp)
  simp only [tk2] at s5
  have E2 : penvN mv.nv (gS P [ci n, ci i]) (mv.nv + 1) i32 = some (i : Int) :=
    envs mv P [ci n, ci i] 1 (ci i) rfl (i32v i hi31)
  have e2 := inc_val mv (VO Vf) _ (mv.nv + 1) i E2 (by omega)
  have s6 := gSM_assign mv P [ci n, ci i] (VO Vf) 1 (by simp) i32 _ _ _ e2
    (ci i) rfl rfl (i32v i hi31) (conv_signed i32 rfl rfl _ (i32v (i + 1) (by show i + 1 < 2147483648; omega)))
  have eB : [ci n, ci i].set 1 ⟨i32, ((i + 1 : Nat) : Int)⟩ = [ci n, ci (i + 1)] := rfl
  rw [eB] at s6
  have a3 := (pexecM_prim mv fu (idIncI mv.nv) _ _).trans s6
  have b3 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
  have b4 := seqM_some s5 rfl b3
  refine ⟨_, Vf, b4, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hsm2]; exact hIf
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, psL] at nL ⊢; omega
  · simp at wL ⊢; omega

theorem cond_id_i (mv : MV) (P : List Cell) (vv : Nat → List Int) (n i : Nat) (hn : n < 2147483648) (hi : i < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P [ci n, ci i])) (idCondI mv.nv) = some (if i < n then 1 else 0) :=
  lt_cells mv P vv [ci n, ci i] 1 0 i n rfl rfl hi hn

set_option maxHeartbeats 16000000 in
/-- The outer loop `for (i = 0; i < n; i++) ...` from the state after `i` iterations. -/
theorem id_outer_loop (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = u64) (P : List Cell) (n : Nat) (A : List Int)
    (hnn : n * n < 2147483648) (hlenA : n * n ≤ A.length) :
    ∀ (d i : Nat) (Vt : List Int) (fu : Nat), i + d = n → IdInv n A (i * n) Vt → n + d + 5 ≤ fu →
      ∃ (res : PRM) (Vf : List Int), pexecM mv fu (.whileLoop (idCondI mv.nv) (idBodyI mv.nv)) (gS P [ci n, ci i]) (VO Vt) = some res ∧
        res.ret = none ∧ res.ps = gS P [ci n, ci n] ∧ res.vv = VO Vf ∧ IdInv n A (n * n) Vf ∧
        res.cost ≤ (900 * n + 200) * d + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ (2 * n + 2) * d := by
  have hn31 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  intro d
  induction d with
  | zero =>
    intro i Vt fu hid hI hfu
    have hjn : i = n := by omega
    subst hjn
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_id_i mv P (VO Vt) i i hn31 hn31
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, Vt, rfl, rfl, rfl, rfl, hI, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro i Vt fu hid hI hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hin : i < n := by omega
    have hc := cond_id_i mv P (VO Vt) n i hn31 (by omega)
    rw [if_pos hin] at hc
    obtain ⟨r1, Vm, h1, ret1, ps1, vv1, hIm, c1, n1, w1⟩ :=
      id_outer_iter mv hnv ty0 P (fu' + 1) n i A Vt hnn hin hlenA hI (by omega)
    obtain ⟨r2, Vf, h2, ret2, ps2, vv2, hIf, c2, n2, w2⟩ :=
      ih (i + 1) Vm fu' (by omega) hIm (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1, vv1, h2]
    have hm : (900 * n + 200) * (d + 1) = (900 * n + 200) * d + (900 * n + 200) := Nat.mul_succ _ _
    have hm2 : (2 * n + 2) * (d + 1) = (2 * n + 2) * d + (2 * n + 2) := Nat.mul_succ _ _
    refine ⟨_, Vf, rfl, ret2, ps2, vv2, hIf, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

set_option maxHeartbeats 16000000 in
/-- The whole body of `mat_identity`. -/
theorem body_execId (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = u64) (P : List Cell) (n : Nat) (A : List Int)
    (hnn : n * n < 2147483648) (hlenA : n * n ≤ A.length) (fu : Nat) (hfu : 2 * n + 7 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyId mv.nv) (gS P [ci n]) (VO A) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n] ∧ ∃ Vf : List Int, r.vv = VO Vf ∧ IdInv n A (n * n) Vf ∧
        r.cost ≤ (900 * n + 200) * n + 100 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ (2 * n + 2) * n + 1 := by
  have d2 := gSM_decl mv P [ci n] (VO A) i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a2 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d2
  obtain ⟨rL, Vf, hL, retL, psL, vvL, hIf, cL, nL, wL⟩ :=
    id_outer_loop mv hnv ty0 P n A hnn hlenA n 0 A fu (by omega) (by simpa using idInv_init n A) (by omega)
  have hL' : pexecM mv fu (.whileLoop (idCondI mv.nv) (idBodyI mv.nv)) (gS P ([ci n] ++ [ci 0])) (VO A) = some rL := hL
  have s1 := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have s2 := seqM_some a2 rfl s1
  have s3 := pexecM_scope mv fu _ _ _ _ s2
  rw [psL, vvL] at s3
  have tk : (⟨(gS P [ci n, ci n]).mem.take (gS P [ci n]).mem.length,
      (gS P [ci n, ci n]).bs.take (gS P [ci n]).bs.length⟩ : PS) = gS P [ci n] :=
    gS_takeC P [ci n] [ci n] [ci n] rfl
  simp only [tk] at s3
  have s4 := seqM_some s3 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, s4, rfl, rfl, Vf, rfl, hIf, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cL ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len, psL] at nL ⊢; omega
  · simp at wL ⊢; omega

end Proofs.SquareMatrixId
