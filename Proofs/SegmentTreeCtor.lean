import Proofs.SegmentTreeExec

namespace Proofs.SegmentTreeCtor
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
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den VO VO_get0 VO_set0)
open Proofs.RunLengthExec (inc_val)
open Proofs.TreeArcCostsExec (VC VC_get0 VC_get1 VC_set1)
open Proofs.SegmentTreeExec
open Proofs.SegTreeMath

abbrev EMIN : Int := -9223372036854775808

/-! ### The constructor (nv = 2: node, v).
Cells: 0 = n, 1 = n (argument of size_of), 2 = size, 3 = p, 4 = size_of result, 5 = n_node, 6 = n (argument of height_of),
7 = h, 8 = size, 9 = p, 10 = height_of result, 11 = h_node, 12 = i -/

abbrev sizeV (nv : Nat) : NExpr := .cast i32 (.size (.integer s64) (.local 1))
abbrev dI (e : NExpr) : Command := .primitive (.declare i32 true e)
abbrev litI (k : Int) : NExpr := .literal i32 k
abbrev vI (nv k : Nat) : NExpr := .variable i32 (nv + k)

abbrev loopA (nv : Nat) : Command :=
  .whileLoop (.binary bT .lt (vI nv 2) (vI nv 1))
    (.sequence (.scope (.sequence (.primitive (.assign (nv + 3) i32 (.binary i32 .mul (vI nv 3) (litI 2))))
      (.sequence (.primitive (.assign (nv + 2) i32 (vI nv 3))) Sk))) Sk)
abbrev loopB (nv : Nat) : Command :=
  .whileLoop (.binary bT .lt (vI nv 8) (vI nv 6))
    (.sequence (.scope (.sequence (.primitive (.assign (nv + 7) i32 (.binary i32 .add (vI nv 7) (litI 1))))
      (.sequence (.primitive (.assign (nv + 9) i32 (.binary i32 .mul (vI nv 9) (litI 2))))
        (.sequence (.primitive (.assign (nv + 8) i32 (vI nv 9))) Sk)))) Sk)
abbrev copyBody (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.write (.local 0) s64 (.cast u64 (.binary i32 .add (vI nv 5) (vI nv 12)))
    (.read s64 (.local 1) (.cast u64 (vI nv 12))))) Sk))
    (.sequence (.primitive (.assign (nv + 12) i32 (.binary i32 .add (vI nv 12) (litI 1)))) Sk)
abbrev buildBody (nv : Nat) : Command :=
  .sequence (.scope (UpdBlk nv 13 0 5 11 12 Sk))
    (.sequence (.primitive (.assign (nv + 12) i32 (.binary i32 .sub (vI nv 12) (litI 1)))) Sk)
/-- `a; b; c; ...` as nested sequences ending with a skip. -/
def seqs : List Command → Command
  | [] => Sk
  | c :: cs => .sequence c (seqs cs)

abbrev scopeCopy (nv : Nat) : Command :=
  .scope (seqs [dI (litI 0), .whileLoop (.binary bT .lt (vI nv 12) (vI nv 0)) (copyBody nv)])
abbrev scopeBuild (nv : Nat) : Command :=
  .scope (seqs [dI (.binary i32 .sub (vI nv 5) (litI 1)), .whileLoop (.binary bT .ge (vI nv 12) (litI 1)) (buildBody nv)])
abbrev bodyCtor (nv : Nat) : Command :=
  seqs [dI (sizeV nv), dI (sizeV nv), dI (litI 0), dI (litI 1), loopA nv, dI (vI nv 2), dI (vI nv 4),
    dI (sizeV nv), dI (litI 0), dI (litI 0), dI (litI 1), loopB nv, dI (vI nv 7), dI (vI nv 10),
    scopeCopy nv, scopeBuild nv]

theorem body_eqCtor : Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_new0.body = bodyCtor 2 := rfl

/-- The value of `size` after `e` iterations of the loop of `size_of` / `height_of`. -/
def szv (e : Nat) : Nat := if e = 0 then 0 else 2 ^ e

theorem szv_zero : szv 0 = 0 := rfl
theorem szv_succ (e : Nat) : szv (e + 1) = 2 ^ (e + 1) := by simp [szv]

theorem szv_mono (e1 e2 : Nat) (h : e1 < e2) : szv e1 < szv e2 := by
  unfold szv
  rw [if_neg (show e2 ≠ 0 by omega)]
  by_cases h0 : e1 = 0
  · rw [if_pos h0]; exact Nat.two_pow_pos e2
  · rw [if_neg h0]; exact Nat.pow_lt_pow_right (by decide) h

theorem k_unique (n k1 k2 : Nat) (h1 : n ≤ szv k1) (h1' : ∀ j, j < k1 → szv j < n)
    (h2 : n ≤ szv k2) (h2' : ∀ j, j < k2 → szv j < n) : k1 = k2 := by
  apply Classical.byContradiction
  intro hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := h2' k1 h; omega
  · have := h1' k2 h; omega

theorem lt_val_i32 (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (a b x y : Nat)
    (ha : cl[a]? = some (ci x)) (hb : cl[b]? = some (ci y)) (hx : x < 2147483648) (hy : y < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .lt (vI mv.nv a) (vI mv.nv b)) = some (if x < y then 1 else 0) := by
  have ex : penvN mv.nv (gS P cl) (mv.nv + a) i32 = some (x : Int) := envs mv P cl a (ci x) ha (i32v x hx)
  have ey : penvN mv.nv (gS P cl) (mv.nv + b) i32 = some (y : Int) := envs mv P cl b (ci y) hb (i32v y hy)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, ex, Option.bind_some, den_variable, ey, Option.bind_some]
  by_cases h : x < y
  · have : (x : Int) < (y : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((x : Int) < (y : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

theorem mul2_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (slot x : Nat)
    (h : env slot i32 = some (x : Int)) (hx : 2 * x < 2147483648) :
    vdenM mv vv env (.binary i32 .mul (.variable i32 slot) (.literal i32 2)) = some ((2 * x : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, h, Option.bind_some, den_literal,
    if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
  have : binaryValue .mul (x : Int) 2 = ((2 * x : Nat) : Int) := by
    show (x : Int) * 2 = _; push_cast; ring
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32v _ (by show 2 * x < 2147483648; omega))

abbrev LA (n size p : Nat) : List Cell := [ci n, ci n, ci size, ci p]

set_option maxHeartbeats 16000000 in
/-- One iteration of the loop of `size_of`: `p = p * 2; size = p;`. -/
theorem iterA (mv : MV) (hnv : mv.nv = 2) (P : List Cell) (vv : Nat → List Int) (fu : Nat) (n size p : Nat)
    (hn : n < 2147483648) (hs : size < 2147483648) (hp : 2 * p < 2147483648) :
    ∃ r : PRM, pexecM mv fu (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + 3) i32 (.binary i32 .mul (vI mv.nv 3) (litI 2))))
      (.sequence (.primitive (.assign (mv.nv + 2) i32 (vI mv.nv 3))) Sk))) Sk) (gS P (LA n size p)) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (LA n (2 * p) (2 * p)) ∧ r.vv = vv ∧ r.cost ≤ 200 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 := by
  have hp' : p < 2147483648 := by omega
  have E3 : penvN mv.nv (gS P (LA n size p)) (mv.nv + 3) i32 = some (p : Int) :=
    envs mv P (LA n size p) 3 (ci p) rfl (i32v p hp')
  have e1 := mul2_val mv vv _ (mv.nv + 3) p E3 hp
  have s1 := gSM_assign mv P (LA n size p) vv 3 (by simp) i32 _ _ _ e1 (ci p) rfl rfl (i32v p hp')
    (conv_signed i32 rfl rfl _ (i32v _ (by show 2 * p < 2147483648; omega)))
  have eA : (LA n size p).set 3 ⟨i32, ((2 * p : Nat) : Int)⟩ = LA n size (2 * p) := rfl
  rw [eA] at s1
  have a1 := (pexecM_prim mv fu (.assign (mv.nv + 3) i32 (.binary i32 .mul (vI mv.nv 3) (litI 2))) _ _).trans s1
  have E3' : penvN mv.nv (gS P (LA n size (2 * p))) (mv.nv + 3) i32 = some ((2 * p : Nat) : Int) :=
    envs mv P (LA n size (2 * p)) 3 (ci (2 * p)) rfl (i32v _ (by show 2 * p < 2147483648; omega))
  have s2 := gSM_assign mv P (LA n size (2 * p)) vv 2 (by simp) i32 (vI mv.nv 3) ((2 * p : Nat) : Int) ((2 * p : Nat) : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3') (ci size) rfl rfl (i32v size hs)
    (conv_signed i32 rfl rfl _ (i32v _ (by show 2 * p < 2147483648; omega)))
  have eB : (LA n size (2 * p)).set 2 ⟨i32, ((2 * p : Nat) : Int)⟩ = LA n (2 * p) (2 * p) := rfl
  rw [eB] at s2
  have a2 := (pexecM_prim mv fu (.assign (mv.nv + 2) i32 (vI mv.nv 3)) _ _).trans s2
  have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  have b1 := seqM_some a1 rfl b2
  have b0 := pexecM_scope mv fu _ _ _ _ b1
  have tk := Proofs.PexecKit.scope_take (gS P (LA n size p)) (gS P (LA n (2 * p) (2 * p))) (by simp [gS_mem_len]) (by simp [gS_bs_len])
  simp only [tk] at b0
  have b3 := seqM_some b0 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, b3, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

set_option maxHeartbeats 16000000 in
/-- The loop of `size_of`: `while (size < n) { p = p * 2; size = p; }` from the state after `e` iterations. -/
theorem loopA_exec (mv : MV) (hnv : mv.nv = 2) (P : List Cell) (vv : Nat → List Int) (n : Nat) (hn1 : 1 ≤ n)
    (hn : n ≤ 1073741824) :
    ∀ (d e fu : Nat), e + d = 30 → (∀ j, j < e → szv j < n) → d + 1 ≤ fu →
      ∃ (res : PRM) (k : Nat), pexecM mv fu (loopA mv.nv) (gS P (LA n (szv e) (2 ^ e))) vv = some res ∧ res.ret = none ∧
        res.ps = gS P (LA n (szv k) (2 ^ k)) ∧ res.vv = vv ∧ e ≤ k ∧ k ≤ 30 ∧ n ≤ szv k ∧ (∀ j, j < k → szv j < n) ∧
        res.cost ≤ 400 * (k - e) + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk = 0 := by
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  have szle : ∀ e, e ≤ 30 → szv e ≤ 1073741824 := by
    intro e he; unfold szv; split
    · omega
    · rw [← h30]; exact Nat.pow_le_pow_right (by decide) he
  have hn' : n < 2147483648 := by omega
  intro d
  induction d with
  | zero =>
    intro e fu he hj hfu
    have he30 : e = 30 := by omega
    subst he30
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hnn : n ≤ szv 30 := by unfold szv; rw [if_neg (by omega), h30]; omega
    have hc := lt_val_i32 mv P vv (LA n (szv 30) (2 ^ 30)) 2 1 (szv 30) n rfl rfl (by have := szle 30 (le_refl _); omega) hn'
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, 30, rfl, rfl, rfl, rfl, le_refl _, le_refl _, hnn, hj, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  | succ d ih =>
    intro e fu he hj hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hs : szv e < 2147483648 := by have := szle e (by omega); omega
    have hc := lt_val_i32 mv P vv (LA n (szv e) (2 ^ e)) 2 1 (szv e) n rfl rfl hs hn'
    by_cases hlt : szv e < n
    · rw [if_pos hlt] at hc
      have he30 : e < 30 := by
        apply Classical.byContradiction
        intro hh
        have : e = 30 := by omega
        subst this
        have : szv 30 = 1073741824 := by unfold szv; rw [if_neg (by omega), h30]
        omega
      have hp : 2 * 2 ^ e < 2147483648 := by
        have : 2 ^ (e + 1) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) he30
        rw [Nat.pow_succ] at this; omega
      have hpe : 2 ^ e < 2147483648 := by omega
      obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := iterA mv hnv P vv (fu' + 1) n (szv e) (2 ^ e) hn' hs hp
      have e2 : 2 * 2 ^ e = 2 ^ (e + 1) := by rw [Nat.pow_succ]; omega
      have e3 : 2 ^ (e + 1) = szv (e + 1) := (szv_succ e).symm
      rw [e2] at ps1
      rw [e3] at ps1
      have hps1 : r1.ps = gS P (LA n (szv (e + 1)) (2 ^ (e + 1))) := by rw [ps1, ← e3]
      obtain ⟨r2, k, h2, ret2, ps2, vv2, hek, hk30, hnk, hmin, c2, n2, w2⟩ :=
        ih (e + 1) fu' (by omega) (by
          intro j hjj
          rcases Nat.lt_or_ge j e with h | h
          · exact hj j h
          · have : j = e := by omega
            subst this; exact hlt) (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, hps1, vv1, h2]
      refine ⟨_, k, rfl, ret2, ps2, vv2, by omega, hk30, hnk, hmin, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
      · simp at w1 w2 ⊢; omega
    · rw [if_neg hlt] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, e, rfl, rfl, rfl, rfl, le_refl _, by omega, by omega, hj, ?_, ?_, rfl⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]

abbrev LB (n N P h size p : Nat) : List Cell := [ci n, ci n, ci N, ci P, ci N, ci N, ci n, ci h, ci size, ci p]

set_option maxHeartbeats 16000000 in
/-- One iteration of the loop of `height_of`: `h++; p = p * 2; size = p;`. -/
theorem iterB (mv : MV) (hnv : mv.nv = 2) (P : List Cell) (vv : Nat → List Int) (fu : Nat) (n N Pk h size p : Nat)
    (hn : n < 2147483648) (hN : N < 2147483648) (hPk : Pk < 2147483648) (hh : h + 1 < 2147483648) (hs : size < 2147483648)
    (hp : 2 * p < 2147483648) :
    ∃ r : PRM, pexecM mv fu (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + 7) i32 (.binary i32 .add (vI mv.nv 7) (litI 1))))
      (.sequence (.primitive (.assign (mv.nv + 9) i32 (.binary i32 .mul (vI mv.nv 9) (litI 2))))
        (.sequence (.primitive (.assign (mv.nv + 8) i32 (vI mv.nv 9))) Sk)))) Sk) (gS P (LB n N Pk h size p)) vv = some r ∧
      r.ret = none ∧ r.ps = gS P (LB n N Pk (h + 1) (2 * p) (2 * p)) ∧ r.vv = vv ∧ r.cost ≤ 300 ∧ r.need ≤ P.length + 80 ∧ r.wk = 0 := by
  have hp' : p < 2147483648 := by omega
  have hh' : h < 2147483648 := by omega
  have E7 : penvN mv.nv (gS P (LB n N Pk h size p)) (mv.nv + 7) i32 = some (h : Int) :=
    envs mv P (LB n N Pk h size p) 7 (ci h) rfl (i32v h hh')
  have e1 := inc_val mv vv _ (mv.nv + 7) h E7 hh
  have s1 := gSM_assign mv P (LB n N Pk h size p) vv 7 (by simp) i32 _ _ _ e1 (ci h) rfl rfl (i32v h hh')
    (conv_signed i32 rfl rfl _ (i32v _ (by show h + 1 < 2147483648; omega)))
  have eA : (LB n N Pk h size p).set 7 ⟨i32, ((h + 1 : Nat) : Int)⟩ = LB n N Pk (h + 1) size p := rfl
  rw [eA] at s1
  have a1 := (pexecM_prim mv fu (.assign (mv.nv + 7) i32 (.binary i32 .add (vI mv.nv 7) (litI 1))) _ _).trans s1
  have E9 : penvN mv.nv (gS P (LB n N Pk (h + 1) size p)) (mv.nv + 9) i32 = some (p : Int) :=
    envs mv P (LB n N Pk (h + 1) size p) 9 (ci p) rfl (i32v p hp')
  have e2 := mul2_val mv vv _ (mv.nv + 9) p E9 hp
  have s2 := gSM_assign mv P (LB n N Pk (h + 1) size p) vv 9 (by simp) i32 _ _ _ e2 (ci p) rfl rfl (i32v p hp')
    (conv_signed i32 rfl rfl _ (i32v _ (by show 2 * p < 2147483648; omega)))
  have eB : (LB n N Pk (h + 1) size p).set 9 ⟨i32, ((2 * p : Nat) : Int)⟩ = LB n N Pk (h + 1) size (2 * p) := rfl
  rw [eB] at s2
  have a2 := (pexecM_prim mv fu (.assign (mv.nv + 9) i32 (.binary i32 .mul (vI mv.nv 9) (litI 2))) _ _).trans s2
  have E9' : penvN mv.nv (gS P (LB n N Pk (h + 1) size (2 * p))) (mv.nv + 9) i32 = some ((2 * p : Nat) : Int) :=
    envs mv P (LB n N Pk (h + 1) size (2 * p)) 9 (ci (2 * p)) rfl (i32v _ (by show 2 * p < 2147483648; omega))
  have s3 := gSM_assign mv P (LB n N Pk (h + 1) size (2 * p)) vv 8 (by simp) i32 (vI mv.nv 9) ((2 * p : Nat) : Int) ((2 * p : Nat) : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E9') (ci size) rfl rfl (i32v size hs)
    (conv_signed i32 rfl rfl _ (i32v _ (by show 2 * p < 2147483648; omega)))
  have eC : (LB n N Pk (h + 1) size (2 * p)).set 8 ⟨i32, ((2 * p : Nat) : Int)⟩ = LB n N Pk (h + 1) (2 * p) (2 * p) := rfl
  rw [eC] at s3
  have a3 := (pexecM_prim mv fu (.assign (mv.nv + 8) i32 (vI mv.nv 9)) _ _).trans s3
  have b3 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
  have b2 := seqM_some a2 rfl b3
  have b1 := seqM_some a1 rfl b2
  have b0 := pexecM_scope mv fu _ _ _ _ b1
  have tk := Proofs.PexecKit.scope_take (gS P (LB n N Pk h size p)) (gS P (LB n N Pk (h + 1) (2 * p) (2 * p)))
    (by simp [gS_mem_len]) (by simp [gS_bs_len])
  simp only [tk] at b0
  have b4 := seqM_some b0 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, b4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

set_option maxHeartbeats 16000000 in
/-- The loop of `height_of` from the state after `e` iterations. -/
theorem loopB_exec (mv : MV) (hnv : mv.nv = 2) (P : List Cell) (vv : Nat → List Int) (n Pk : Nat) (hn1 : 1 ≤ n)
    (hn : n ≤ 1073741824) (hPk : Pk < 2147483648) (N : Nat) (hN : N < 2147483648) :
    ∀ (d e fu : Nat), e + d = 30 → (∀ j, j < e → szv j < n) → d + 1 ≤ fu →
      ∃ (res : PRM) (k : Nat), pexecM mv fu (loopB mv.nv) (gS P (LB n N Pk e (szv e) (2 ^ e))) vv = some res ∧ res.ret = none ∧
        res.ps = gS P (LB n N Pk k (szv k) (2 ^ k)) ∧ res.vv = vv ∧ e ≤ k ∧ k ≤ 30 ∧ n ≤ szv k ∧ (∀ j, j < k → szv j < n) ∧
        res.cost ≤ 500 * (k - e) + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk = 0 := by
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  have szle : ∀ e, e ≤ 30 → szv e ≤ 1073741824 := by
    intro e he; unfold szv; split
    · omega
    · rw [← h30]; exact Nat.pow_le_pow_right (by decide) he
  have hn' : n < 2147483648 := by omega
  intro d
  induction d with
  | zero =>
    intro e fu he hj hfu
    have he30 : e = 30 := by omega
    subst he30
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hnn : n ≤ szv 30 := by unfold szv; rw [if_neg (by omega), h30]; omega
    have hc := lt_val_i32 mv P vv (LB n N Pk 30 (szv 30) (2 ^ 30)) 8 6 (szv 30) n rfl rfl (by have := szle 30 (le_refl _); omega) hn'
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, 30, rfl, rfl, rfl, rfl, le_refl _, le_refl _, hnn, hj, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  | succ d ih =>
    intro e fu he hj hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hs : szv e < 2147483648 := by have := szle e (by omega); omega
    have hc := lt_val_i32 mv P vv (LB n N Pk e (szv e) (2 ^ e)) 8 6 (szv e) n rfl rfl hs hn'
    by_cases hlt : szv e < n
    · rw [if_pos hlt] at hc
      have he30 : e < 30 := by
        apply Classical.byContradiction
        intro hh
        have : e = 30 := by omega
        subst this
        have : szv 30 = 1073741824 := by unfold szv; rw [if_neg (by omega), h30]
        omega
      have hp : 2 * 2 ^ e < 2147483648 := by
        have : 2 ^ (e + 1) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) he30
        rw [Nat.pow_succ] at this; omega
      obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := iterB mv hnv P vv (fu' + 1) n N Pk e (szv e) (2 ^ e) hn' hN hPk
        (by omega) hs hp
      have e2 : 2 * 2 ^ e = 2 ^ (e + 1) := by rw [Nat.pow_succ]; omega
      have e3 : 2 ^ (e + 1) = szv (e + 1) := (szv_succ e).symm
      have hps1 : r1.ps = gS P (LB n N Pk (e + 1) (szv (e + 1)) (2 ^ (e + 1))) := by rw [ps1, e2, ← e3]
      obtain ⟨r2, k, h2, ret2, ps2, vv2, hek, hk30, hnk, hmin, c2, n2, w2⟩ :=
        ih (e + 1) fu' (by omega) (by
          intro j hjj
          rcases Nat.lt_or_ge j e with h | h
          · exact hj j h
          · have : j = e := by omega
            subst this; exact hlt) (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, hps1, vv1, h2]
      refine ⟨_, k, rfl, ret2, ps2, vv2, by omega, hk30, hnk, hmin, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
      · simp at w1 w2 ⊢; omega
    · rw [if_neg hlt] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, e, rfl, rfl, rfl, rfl, le_refl _, by omega, by omega, hj, ?_, ?_, rfl⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]

theorem VC_set0 (A B x : List Int) : upd (VC A B) 0 x = VC x B := by
  funext k; unfold upd VC; split <;> simp_all

abbrev CP (n N Pk k i : Nat) : List Cell := [ci n, ci n, ci N, ci Pk, ci N, ci N, ci n, ci k, ci N, ci Pk, ci k, ci k, ci i]

/-- After `t` iterations of the copy loop the leaves `[N, N + t)` hold `v[0 .. t)` and everything else is the identity. -/
def CopyInv (N : Nat) (v Vt : List Int) (t : Nat) : Prop :=
  Vt.length = 2 * N ∧ ∀ j, j < 2 * N → Vt.getD j 0 = if N ≤ j ∧ j < N + t then v.getD (j - N) 0 else EMIN

theorem copyInv_init (N : Nat) (v : List Int) : CopyInv N v (List.replicate (2 * N) EMIN) 0 := by
  refine ⟨by simp, ?_⟩
  intro j hj
  simp [List.getD_eq_getElem?_getD, hj]

theorem copyInv_step (N : Nat) (v Vt : List Int) (t : Nat) (h : CopyInv N v Vt t) (ht : t < N) :
    CopyInv N v (Vt.set (N + t) (v.getD t 0)) (t + 1) := by
  obtain ⟨hl, hj⟩ := h
  refine ⟨by simp [hl], ?_⟩
  intro j hjj
  rw [getD_setE, hj j hjj]
  by_cases hjt : j = N + t
  · subst hjt
    rw [if_pos ⟨rfl, by simp [hl]; omega⟩, if_pos ⟨by omega, by omega⟩]
    congr 1; omega
  · rw [if_neg (fun hh => hjt hh.1)]
    by_cases hr : N ≤ j ∧ j < N + t
    · rw [if_pos hr, if_pos ⟨hr.1, by omega⟩]
    · rw [if_neg hr, if_neg (fun hh => hr ⟨hh.1, by omega⟩)]

theorem add_idx_den (env : Nat → Ty → Option Int) (a b x y : Nat) (ha : env a i32 = some (x : Int)) (hb : env b i32 = some (y : Int))
    (h : x + y < 2147483648) :
    (NExpr.cast u64 (.binary i32 .add (.variable i32 a) (.variable i32 b))).denote env = some ((x + y : Nat) : Int) := by
  rw [den_cast, den_binary, den_variable, ha, Option.bind_some, den_variable, hb, Option.bind_some]
  have : binaryValue .add (x : Int) (y : Int) = ((x + y : Nat) : Int) := by
    show (x : Int) + (y : Int) = _; push_cast; rfl
  rw [this, conv_signed i32 rfl rfl _ (i32v _ (by show x + y < 2147483648; omega)), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)

set_option maxHeartbeats 16000000 in
/-- One iteration of the copy loop: `node[n_node + i] = v[i]; i++`. -/
theorem copy_iter (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell) (fu : Nat)
    (n N Pk k i : Nat) (Vt v : List Int) (hn : n < 2147483648) (hN : N < 2147483648) (hPk : Pk < 2147483648)
    (hk : k < 2147483648) (hi : i < n) (hnN : n ≤ N) (hNN : 2 * N < 2147483648) (hlen : Vt.length = 2 * N) (hvn : n ≤ v.length)
    (hvv : s64.valid (v.getD i 0) = true) :
    ∃ r : PRM, pexecM mv fu (copyBody mv.nv) (gS P (CP n N Pk k i)) (VC Vt v) = some r ∧ r.ret = none ∧
      r.ps = gS P (CP n N Pk k (i + 1)) ∧ r.vv = VC (Vt.set (N + i) (v.getD i 0)) v ∧
      r.cost ≤ 600 ∧ r.need ≤ P.length + 100 ∧ r.wk = 1 := by
  have hi31 : i < 2147483648 := by omega
  have E5 : penvN mv.nv (gS P (CP n N Pk k i)) (mv.nv + 5) i32 = some (N : Int) :=
    envs mv P (CP n N Pk k i) 5 (ci N) rfl (i32v N hN)
  have E12 : penvN mv.nv (gS P (CP n N Pk k i)) (mv.nv + 12) i32 = some (i : Int) :=
    envs mv P (CP n N Pk k i) 12 (ci i) rfl (i32v i hi31)
  have hrd := rdM_val mv (VC Vt v) _ 1 (by omega) s64 ty1.symm (.cast u64 (vI mv.nv 12)) rfl rfl i
    (cidx_den _ _ i E12 hi31) (v.getD i 0) (by rw [VC_get1]; exact vec_getI v i (by omega)) (by rw [ty1]; exact hvv)
  have hw := pstmtM_write_ok mv (gS P (CP n N Pk k i)) (VC Vt v) 0 (by omega)
    (.cast u64 (.binary i32 .add (vI mv.nv 5) (vI mv.nv 12))) (.read s64 (.local 1) (.cast u64 (vI mv.nv 12))) (v.getD i 0) (N + i)
    hrd (by rw [vdenM_scalar _ _ _ _ rfl]; exact add_idx_den _ _ _ N i E5 E12 (by omega))
    (by rw [VC_get0]; omega) (by rw [ty0]; exact hvv)
  rw [ty0, VC_get0, VC_set0] at hw
  have a1 := (pexecM_prim mv fu (.write (.local 0) s64 (.cast u64 (.binary i32 .add (vI mv.nv 5) (vI mv.nv 12)))
    (.read s64 (.local 1) (.cast u64 (vI mv.nv 12)))) _ _).trans hw
  have b1 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
  have b0 := pexecM_scope mv fu _ _ _ _ b1
  have tk := Proofs.PexecKit.scope_take (gS P (CP n N Pk k i)) (gS P (CP n N Pk k i)) (by simp) (by simp)
  simp only [tk] at b0
  have E12' : penvN mv.nv (gS P (CP n N Pk k i)) (mv.nv + 12) i32 = some (i : Int) := E12
  have e2 := inc_val mv (VC (Vt.set (N + i) (v.getD i 0)) v) _ (mv.nv + 12) i E12' (by omega)
  have s2 := gSM_assign mv P (CP n N Pk k i) (VC (Vt.set (N + i) (v.getD i 0)) v) 12 (by simp) i32 _ _ _ e2 (ci i) rfl rfl
    (i32v i hi31) (conv_signed i32 rfl rfl _ (i32v (i + 1) (by show i + 1 < 2147483648; omega)))
  have eB : (CP n N Pk k i).set 12 ⟨i32, ((i + 1 : Nat) : Int)⟩ = CP n N Pk k (i + 1) := rfl
  rw [eB] at s2
  have a2 := (pexecM_prim mv fu (.assign (mv.nv + 12) i32 (.binary i32 .add (vI mv.nv 12) (litI 1))) _ _).trans s2
  have b3 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  have b4 := seqM_some b0 rfl b3
  refine ⟨_, b4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

set_option maxHeartbeats 16000000 in
/-- The copy loop `for (i = 0; i < n; i++) node[n_node + i] = v[i];` from the state after `i` iterations. -/
theorem copy_loop (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (n N Pk k : Nat) (v : List Int) (hn : n < 2147483648) (hN : N < 2147483648) (hPk : Pk < 2147483648)
    (hk : k < 2147483648) (hnN : n ≤ N) (hNN : 2 * N < 2147483648) (hvn : n ≤ v.length) (hv : AllV maxMon v) :
    ∀ (d i : Nat) (Vt : List Int) (fu : Nat), i + d = n → CopyInv N v Vt i → d + 1 ≤ fu →
      ∃ (res : PRM) (Vf : List Int), pexecM mv fu (.whileLoop (.binary bT .lt (vI mv.nv 12) (vI mv.nv 0)) (copyBody mv.nv))
          (gS P (CP n N Pk k i)) (VC Vt v) = some res ∧ res.ret = none ∧ res.ps = gS P (CP n N Pk k n) ∧
        res.vv = VC Vf v ∧ CopyInv N v Vf n ∧ res.cost ≤ 700 * d + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ d := by
  intro d
  induction d with
  | zero =>
    intro i Vt fu hid hI hfu
    have hin : i = n := by omega
    subst hin
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := lt_val_i32 mv P (VC Vt v) (CP i N Pk k i) 12 0 i i rfl rfl hn hn
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
    have hin : i < n := by omega
    have hc := lt_val_i32 mv P (VC Vt v) (CP n N Pk k i) 12 0 i n rfl rfl (by omega) hn
    rw [if_pos hin] at hc
    have hvi : s64.valid (v.getD i 0) = true := getD_V maxMon v hv i (by omega)
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := copy_iter mv hnv ty0 ty1 P (fu' + 1) n N Pk k i Vt v hn hN hPk hk hin hnN hNN
      hI.1 hvn hvi
    obtain ⟨r2, Vf, h2, ret2, ps2, vv2, hIf, c2, n2, w2⟩ :=
      ih (i + 1) (Vt.set (N + i) (v.getD i 0)) fu' (by omega) (copyInv_step N v Vt i hI (by omega)) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1, vv1, h2]
    refine ⟨_, Vf, rfl, ret2, ps2, vv2, hIf, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

theorem dec_val_c (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (slot k : Nat)
    (h : env slot i32 = some (k : Int)) (hk : 1 ≤ k) (hk2 : k < 2147483648) :
    vdenM mv vv env (.binary i32 .sub (.variable i32 slot) (.literal i32 1)) = some ((k - 1 : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, h, Option.bind_some, den_literal,
    if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .sub (k : Int) 1 = ((k - 1 : Nat) : Int) := by
    show (k : Int) - 1 = _; omega
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32v _ (by show k - 1 < 2147483648; omega))

abbrev CB (n N Pk k i : Nat) : List Cell := CP n N Pk k i

set_option maxHeartbeats 16000000 in
/-- One iteration of the build loop: `update(i); i--`. -/
theorem build_iter (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (P : List Cell) (fu : Nat)
    (n N Pk k i : Nat) (Vt v : List Int) (hn : n < 2147483648) (hN : N < 2147483648) (hPk : Pk < 2147483648)
    (hk : k < 2147483648) (hi1 : 1 ≤ i) (hiN : i < N) (hNN : 2 * N < 2147483648) (hlen : Vt.length = 2 * N)
    (hV : AllV maxMon Vt) :
    ∃ r : PRM, pexecM mv fu (buildBody mv.nv) (gS P (CP n N Pk k i)) (VC Vt v) = some r ∧ r.ret = none ∧
      r.ps = gS P (CP n N Pk k (i - 1)) ∧
      r.vv = VC (Vt.set i (mx (Vt.getD (2 * i) 0) (Vt.getD (2 * i + 1) 0))) v ∧
      r.cost ≤ 800 ∧ r.need ≤ P.length + 105 ∧ r.wk = 1 := by
  have hi31 : i < 2147483648 := by omega
  have vx : s64.valid ((VC Vt v 0).getD (2 * i) 0) = true := by
    rw [VC_get0]; exact getD_V maxMon Vt hV _ (by omega)
  have vy : s64.valid ((VC Vt v 0).getD (2 * i + 1) 0) = true := by
    rw [VC_get0]; exact getD_V maxMon Vt hV _ (by omega)
  obtain ⟨rU, hU, retU, psU, vvU, cU, nU, wU⟩ := upd_exec mv (by omega) ty0 P (VC Vt v) fu (CP n N Pk k i) 13 rfl 0 5 11 12
    n N k i rfl rfl rfl rfl hn hN hk (by omega) (by rw [VC_get0]; omega) vx vy Sk _ (pexecM_skip mv fu _ _)
  have s1 := hU
  obtain ⟨r1, hr1, hr1ps, hr1ret, hr1vv, hr1w, hr1c, hr1n⟩ : ∃ r1 : PRM,
      pexecM mv fu (UpdBlk mv.nv 13 0 5 11 12 Sk) (gS P (CP n N Pk k i)) (VC Vt v) = some r1 ∧
      r1.ps = gS P (CP n N Pk k i ++ [ci n, ci N, ci k, ci i, cs (Vt.getD (2 * i) 0), cs (Vt.getD (2 * i + 1) 0),
        cs (mx (Vt.getD (2 * i) 0) (Vt.getD (2 * i + 1) 0)), cs (mx (Vt.getD (2 * i) 0) (Vt.getD (2 * i + 1) 0))]) ∧
      r1.ret = none ∧ r1.vv = VC (Vt.set i (mx (Vt.getD (2 * i) 0) (Vt.getD (2 * i + 1) 0))) v ∧
      r1.wk = 1 ∧ r1.cost ≤ 340 ∧ r1.need ≤ P.length + 105 := by
    refine ⟨rU, hU, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [VC_get0] at psU
      simpa using psU
    · simpa using retU
    · rw [vvU]
      show upd (VC Vt v) 0 ((VC Vt v 0).set _ _) = _
      rw [VC_get0, VC_set0]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at wU ⊢; try omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cU ⊢; omega
    · have := nU (P.length + 105) (by simp [gS_mem_len, gS_bs_len]) (by omega)
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at this ⊢
      omega
  have b0 := pexecM_scope mv fu _ _ _ _ hr1
  rw [hr1ps] at b0
  have tk := gS_takeC P (CP n N Pk k i) (CP n N Pk k i)
    [ci n, ci N, ci k, ci i, cs (Vt.getD (2 * i) 0), cs (Vt.getD (2 * i + 1) 0),
      cs (mx (Vt.getD (2 * i) 0) (Vt.getD (2 * i + 1) 0)), cs (mx (Vt.getD (2 * i) 0) (Vt.getD (2 * i + 1) 0))] rfl
  simp only [tk] at b0
  -- i--
  have E12 : penvN mv.nv (gS P (CP n N Pk k i)) (mv.nv + 12) i32 = some (i : Int) :=
    envs mv P (CP n N Pk k i) 12 (ci i) rfl (i32v i hi31)
  have e2 := dec_val_c mv (VC (Vt.set i (mx (Vt.getD (2 * i) 0) (Vt.getD (2 * i + 1) 0))) v) _ (mv.nv + 12) i E12 hi1 hi31
  have s2 := gSM_assign mv P (CP n N Pk k i) (VC (Vt.set i (mx (Vt.getD (2 * i) 0) (Vt.getD (2 * i + 1) 0))) v) 12 (by simp)
    i32 _ _ _ e2 (ci i) rfl rfl (i32v i hi31) (conv_signed i32 rfl rfl _ (i32v (i - 1) (by show i - 1 < 2147483648; omega)))
  have eB : (CP n N Pk k i).set 12 ⟨i32, ((i - 1 : Nat) : Int)⟩ = CP n N Pk k (i - 1) := rfl
  rw [eB] at s2
  have a2 := (pexecM_prim mv fu (.assign (mv.nv + 12) i32 (.binary i32 .sub (vI mv.nv 12) (litI 1))) _ _).trans s2
  have b3 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  have b4 := seqM_some b0 hr1ret (by rw [hr1vv]; exact b3)
  refine ⟨_, b4, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [hr1vv]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hr1c ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hr1n ⊢; omega
  · simp at hr1w ⊢; omega

theorem ge_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (n N Pk k i : Nat) (hi : i < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (CP n N Pk k i))) (.binary bT .ge (vI mv.nv 12) (litI 1)) = some (if 1 ≤ i then 1 else 0) := by
  have ei : penvN mv.nv (gS P (CP n N Pk k i)) (mv.nv + 12) i32 = some (i : Int) :=
    envs mv P (CP n N Pk k i) 12 (ci i) rfl (i32v i hi)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, ei, Option.bind_some, den_literal,
    if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  by_cases h : 1 ≤ i
  · have : (i : Int) ≥ 1 := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((i : Int) ≥ 1) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 16000000 in
/-- The build loop `for (i = n_node - 1; i >= 1; i--) update(i);` from the state with counter `i`. -/
theorem build_loop (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (P : List Cell) (n N Pk k : Nat) (v : List Int)
    (hn : n < 2147483648) (hN : N < 2147483648) (hPk : Pk < 2147483648) (hk : k < 2147483648) (hNN : 2 * N < 2147483648) :
    ∀ (i : Nat) (Vt : List Int) (fu : Nat), i < N → BInv maxMon Vt N i → AllV maxMon Vt → Vt.length = 2 * N → i + 1 ≤ fu →
      ∃ (res : PRM) (Vf : List Int), pexecM mv fu (.whileLoop (.binary bT .ge (vI mv.nv 12) (litI 1)) (buildBody mv.nv))
          (gS P (CP n N Pk k i)) (VC Vt v) = some res ∧ res.ret = none ∧ res.ps = gS P (CP n N Pk k 0) ∧
        res.vv = VC Vf v ∧ BInv maxMon Vf N 0 ∧ AllV maxMon Vf ∧ Vf.length = 2 * N ∧ (∀ j, N ≤ j → Vf.getD j 0 = Vt.getD j 0) ∧
        res.cost ≤ 900 * i + 30 ∧ res.need ≤ P.length + 105 ∧ res.wk ≤ i := by
  intro i
  induction i with
  | zero =>
    intro Vt fu hiN hB hV hlen hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := ge_val mv P (VC Vt v) n N Pk k 0 (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, Vt, rfl, rfl, rfl, rfl, hB, hV, hlen, fun j _ => rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ i ih =>
    intro Vt fu hiN hB hV hlen hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := ge_val mv P (VC Vt v) n N Pk k (i + 1) (by omega)
    rw [if_pos (by omega)] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := build_iter mv hnv ty0 P (fu' + 1) n N Pk k (i + 1) Vt v hn hN hPk hk (by omega)
      hiN hNN hlen hV
    have hB' := binv_step maxMon Vt N (i + 1) hB (by omega) hiN hlen
    have hVx : maxMon.V (mx (Vt.getD (2 * (i + 1)) 0) (Vt.getD (2 * (i + 1) + 1) 0)) :=
      maxMon.closed _ _ (getD_V maxMon Vt hV _ (by omega)) (getD_V maxMon Vt hV _ (by omega))
    have hV' := allV_set maxMon Vt hV (i + 1) _ hVx
    have hlen' : (Vt.set (i + 1) (mx (Vt.getD (2 * (i + 1)) 0) (Vt.getD (2 * (i + 1) + 1) 0))).length = 2 * N := by
      simp [hlen]
    have hi1 : i + 1 - 1 = i := by omega
    rw [hi1] at ps1
    obtain ⟨r2, Vf, h2, ret2, ps2, vv2, hBf, hVf, hlenf, hleaf, c2, n2, w2⟩ :=
      ih _ fu' (by omega) (by rw [hi1] at hB'; exact hB') hV' hlen' (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1, vv1, h2]
    refine ⟨_, Vf, rfl, ret2, ps2, vv2, hBf, hVf, hlenf, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [hleaf j hj, getD_setE]
      have : ¬ (j = i + 1 ∧ i + 1 < Vt.length) := fun hh2 => by omega
      rw [if_neg this]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

theorem sizeV_val (mv : MV) (hnv : mv.nv = 2) (ty1 : mv.ty 1 = s64) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (hn : (vv 1).length < 2147483648) :
    vdenM mv vv env (sizeV mv.nv) = some ((vv 1).length : Int) := by
  have hr2 : (sizeV mv.nv).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer s64) (.local 1)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer s64) (.local 1)) = some ((vv 1).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨by omega, ty1.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

theorem lit_i32_val (mv : MV) (vv : Nat → List Int) (cl : List Cell) (P : List Cell) (k : Int) (hk : i32.valid k = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (litI k) = some k := by
  rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos hk]

/-- A declaration `int c = e;` of the constructor: appends the cell `ci x`. -/
theorem decl_ci (mv : MV) (P : List Cell) (vv : Nat → List Int) (fu : Nat) (cl : List Cell) (e : NExpr) (x : Nat)
    (hx : x < 2147483648) (he : vdenM mv vv (penvN mv.nv (gS P cl)) e = some (x : Int)) :
    pexecM mv fu (dI e) (gS P cl) vv = some ⟨gS P (cl ++ [ci x]), vv, none, (vwp e).1 + 1,
      P.length + 2 * cl.length + (vwp e).2 + 4, 0⟩ :=
  (pexecM_prim mv fu (.declare i32 true e) _ _).trans
    (gSM_decl mv P cl vv i32 e (x : Int) (x : Int) he (conv_signed i32 rfl rfl _ (i32v x hx)))


theorem szv_le_pow (k : Nat) : szv k ≤ 2 ^ k := by
  unfold szv; split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

theorem emin_valid_c : s64.valid EMIN = true := by decide

theorem copyInv_allV (N : Nat) (v Vt : List Int) (t : Nat) (h : CopyInv N v Vt t) (hv : AllV maxMon v) (ht : t ≤ v.length) :
    AllV maxMon Vt := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hl := h.1
  have e : Vt.getD j 0 = Vt[j] := by simp [List.getD_eq_getElem?_getD, hj]
  have := h.2 j (by omega)
  rw [← e, this]
  split
  · rename_i hc
    exact getD_V maxMon v hv _ (by omega)
  · exact emin_valid_c

abbrev C12 (n N Pk k : Nat) : List Cell := [ci n, ci n, ci N, ci Pk, ci N, ci N, ci n, ci k, ci N, ci Pk, ci k, ci k]

set_option maxHeartbeats 32000000 in
/-- The whole body of the constructor `SegmentTree(const vector<T>& v)` (for `n >= 1`). -/
theorem body_execCtor (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (Vin : List Int) (n : Nat) (hnv1 : Vin.length = n) (hn1 : 1 ≤ n) (hn29 : n ≤ 536870912) (hVin : AllV maxMon Vin)
    (k : Nat) (hk1 : n ≤ szv k) (hk2 : ∀ j, j < k → szv j < n) (fu : Nat) (hfu : 40 + n + 2 ^ k ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyCtor mv.nv) (gS P []) (VC (List.replicate (2 * szv k) EMIN) Vin) = some r ∧ r.ret = none ∧
      (∃ cl : List Cell, r.ps = gS P cl) ∧
      ∃ Vf : List Int, r.vv = VC Vf Vin ∧ TInv maxMon Vf (szv k) ∧ AllV maxMon Vf ∧ Vf.length = 2 * szv k ∧
        (∀ i, i < n → Vf.getD (szv k + i) 0 = Vin.getD i 0) ∧ (∀ i, n ≤ i → i < szv k → Vf.getD (szv k + i) 0 = EMIN) ∧
        r.cost ≤ 3000 * (2 ^ k + 1) + 3000 ∧ r.need ≤ P.length + 105 ∧ r.wk ≤ 2 ^ k + n := by
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  have hn31 : n < 2147483648 := by omega
  have hvl : (VC (List.replicate (2 * szv k) EMIN) Vin 1).length = n := by rw [VC_get1]; exact hnv1
  have hvl' : (VC (List.replicate (2 * szv k) EMIN) Vin 1).length < 2147483648 := by rw [hvl]; omega
  have h29 : 2 ^ 29 = 536870912 := by norm_num
  have hk29 : k ≤ 29 := by
    apply Classical.byContradiction
    intro hh
    have := hk2 29 (by omega)
    have h2 : szv 29 = 536870912 := by unfold szv; rw [if_neg (by omega), h29]
    omega
  have hk30 : k ≤ 30 := by omega
  have hN30 : szv k ≤ 536870912 := by
    unfold szv; split
    · omega
    · rw [← h29]; exact Nat.pow_le_pow_right (by decide) hk29
  have hNpos : 0 < szv k := by omega
  have hN31 : szv k < 2147483648 := by omega
  have hPk : 2 ^ k < 2147483648 := by
    have : 2 ^ k ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hk29
    omega
  have hk31 : k < 2147483648 := by omega
  have hNN : 2 * szv k < 2147483648 := by omega
  have hp2k : 0 < 2 ^ k := Nat.two_pow_pos k
  have hszle := szv_le_pow k
  -- n, n, 0, 1
  have d1 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu [] (sizeV mv.nv) n hn31
    (by rw [sizeV_val mv hnv ty1 _ _ hvl']; rw [hvl])
  have d2 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu [ci n] (sizeV mv.nv) n hn31
    (by rw [sizeV_val mv hnv ty1 _ _ hvl']; rw [hvl])
  have d3 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu [ci n, ci n] (litI 0) 0 (by omega)
    (by rw [lit_i32_val mv _ _ _ 0 (show i32.valid 0 = true from rfl)]; rfl)
  have d4 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu [ci n, ci n, ci 0] (litI 1) 1 (by omega)
    (by rw [lit_i32_val mv _ _ _ 1 (show i32.valid 1 = true from rfl)]; rfl)
  simp only [List.nil_append, List.cons_append] at d1 d2 d3 d4
  have eLA : [ci n, ci n, ci 0, ci 1] = LA n (szv 0) (2 ^ 0) := rfl
  rw [eLA] at d4
  have a1 := d1
  -- the loop of size_of
  obtain ⟨rA, kA, hA, retA, psA, vvA, hekA, hkA30, hnkA, hminA, cA, nA, wA⟩ :=
    loopA_exec mv hnv P (VC (List.replicate (2 * szv k) EMIN) Vin) n hn1 (by omega) 30 0 fu (by omega) (by intro j hj; omega) (by omega)
  have hkA : kA = k := k_unique n kA k hnkA hminA hk1 hk2
  have hkA' : k = kA := hkA.symm
  subst hkA'
  -- the results of size_of (cells 4, 5)
  have d5 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu (LA n (szv k) (2 ^ k)) (vI mv.nv 2) (szv k) hN31
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact envs mv P (LA n (szv k) (2 ^ k)) 2 (ci (szv k)) rfl (i32v _ hN31))
  have d6 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu (LA n (szv k) (2 ^ k) ++ [ci (szv k)]) (vI mv.nv 4) (szv k) hN31
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact envs mv P (LA n (szv k) (2 ^ k) ++ [ci (szv k)]) 4 (ci (szv k)) rfl (i32v _ hN31))
  have d7 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu (LA n (szv k) (2 ^ k) ++ [ci (szv k), ci (szv k)]) (sizeV mv.nv) n hn31
    (by rw [sizeV_val mv hnv ty1 _ _ hvl']; rw [hvl])
  -- normalise the appended cells
  have eC5 : LA n (szv k) (2 ^ k) ++ [ci (szv k)] = [ci n, ci n, ci (szv k), ci (2 ^ k), ci (szv k)] := rfl
  have eC6 : LA n (szv k) (2 ^ k) ++ [ci (szv k), ci (szv k)] = [ci n, ci n, ci (szv k), ci (2 ^ k), ci (szv k), ci (szv k)] := rfl
  have eC7 : LA n (szv k) (2 ^ k) ++ [ci (szv k), ci (szv k)] ++ [ci n] =
      [ci n, ci n, ci (szv k), ci (2 ^ k), ci (szv k), ci (szv k), ci n] := rfl
  have d8 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu
    [ci n, ci n, ci (szv k), ci (2 ^ k), ci (szv k), ci (szv k), ci n] (litI 0) 0 (by omega)
    (by rw [lit_i32_val mv _ _ _ 0 (show i32.valid 0 = true from rfl)]; rfl)
  have d9 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu
    [ci n, ci n, ci (szv k), ci (2 ^ k), ci (szv k), ci (szv k), ci n, ci 0] (litI 0) 0 (by omega)
    (by rw [lit_i32_val mv _ _ _ 0 (show i32.valid 0 = true from rfl)]; rfl)
  have d10 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu
    [ci n, ci n, ci (szv k), ci (2 ^ k), ci (szv k), ci (szv k), ci n, ci 0, ci 0] (litI 1) 1 (by omega)
    (by rw [lit_i32_val mv _ _ _ 1 (show i32.valid 1 = true from rfl)]; rfl)
  simp only [List.cons_append, List.nil_append] at d8 d9 d10
  have eLB : [ci n, ci n, ci (szv k), ci (2 ^ k), ci (szv k), ci (szv k), ci n, ci 0, ci 0, ci 1] = LB n (szv k) (2 ^ k) 0 (szv 0) (2 ^ 0) := rfl
  rw [eLB] at d10
  obtain ⟨rB, kB, hB, retB, psB, vvB, hekB, hkB30, hnkB, hminB, cB, nB, wB⟩ :=
    loopB_exec mv hnv P (VC (List.replicate (2 * szv k) EMIN) Vin) n (2 ^ k) hn1 (by omega) hPk (szv k) hN31 30 0 fu (by omega)
      (by intro j hj; omega) (by omega)
  have hkB : kB = k := k_unique n kB k hnkB hminB hk1 hk2
  have hkB' : k = kB := hkB.symm
  subst hkB'
  have d11 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu (LB n (szv k) (2 ^ k) k (szv k) (2 ^ k)) (vI mv.nv 7) k hk31
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact envs mv P (LB n (szv k) (2 ^ k) k (szv k) (2 ^ k)) 7 (ci k) rfl (i32v _ hk31))
  have d12 := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu (LB n (szv k) (2 ^ k) k (szv k) (2 ^ k) ++ [ci k]) (vI mv.nv 10) k hk31
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact envs mv P (LB n (szv k) (2 ^ k) k (szv k) (2 ^ k) ++ [ci k]) 10 (ci k) rfl (i32v _ hk31))
  simp only [List.cons_append, List.nil_append, List.append_assoc] at d5 d6 d7 d11 d12
  -- the copy loop
  have dC := decl_ci mv P (VC (List.replicate (2 * szv k) EMIN) Vin) fu (C12 n (szv k) (2 ^ k) k) (litI 0) 0 (by omega)
    (by rw [lit_i32_val mv _ _ _ 0 (show i32.valid 0 = true from rfl)]; rfl)
  have hCI := copyInv_init (szv k) Vin
  obtain ⟨rC, V1, hC, retC, psC, vvC, hI1, cC, nC, wC⟩ :=
    copy_loop mv hnv ty0 ty1 P n (szv k) (2 ^ k) k Vin hn31 hN31 hPk hk31 (by omega) hNN (by omega) hVin n 0
      (List.replicate (2 * szv k) EMIN) fu (by omega) hCI (by omega)
  have hV1 : AllV maxMon V1 := copyInv_allV (szv k) Vin V1 n hI1 hVin (by omega)
  -- the build loop
  have E5 : penvN mv.nv (gS P (C12 n (szv k) (2 ^ k) k)) (mv.nv + 5) i32 = some ((szv k : Nat) : Int) :=
    envs mv P (C12 n (szv k) (2 ^ k) k) 5 (ci (szv k)) rfl (i32v _ hN31)
  have dB := decl_ci mv P (VC V1 Vin) fu (C12 n (szv k) (2 ^ k) k) (.binary i32 .sub (vI mv.nv 5) (litI 1)) (szv k - 1) (by omega)
    (dec_val_c mv (VC V1 Vin) _ (mv.nv + 5) (szv k) E5 (by omega) hN31)
  obtain ⟨rD, Vf, hD, retD, psD, vvD, hBf, hVf, hlenf, hleaf, cD, nD, wD⟩ :=
    build_loop mv hnv ty0 P n (szv k) (2 ^ k) k Vin hn31 hN31 hPk hk31 hNN (szv k - 1) V1 fu (by omega)
      (binv_init maxMon V1 (szv k)) hV1 (by rw [hI1.1]) (by omega)
  -- the scope of the copy loop
  have sloopC := seqM_some hC retC (pexecM_skip mv fu rC.ps rC.vv)
  have sdC := seqM_some dC rfl sloopC
  obtain ⟨rS1, hS1, hS1ps, hS1ret, hS1vv, hS1w, hS1c, hS1n⟩ : ∃ r : PRM,
      pexecM mv fu (seqs [dI (litI 0), .whileLoop (.binary bT .lt (vI mv.nv 12) (vI mv.nv 0)) (copyBody mv.nv)])
        (gS P (C12 n (szv k) (2 ^ k) k)) (VC (List.replicate (2 * szv k) EMIN) Vin) = some r ∧
      r.ps = gS P (CP n (szv k) (2 ^ k) k n) ∧ r.ret = none ∧ r.vv = VC V1 Vin ∧ r.wk ≤ n ∧ r.cost ≤ 700 * n + 100 ∧
      r.need ≤ P.length + 105 := by
    refine ⟨_, sdC, by simpa using psC, by simpa using retC, by simpa using vvC, ?_, ?_, ?_⟩
    · simp at wC ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cC ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, C12, CP, psC] at nC ⊢
      omega
  have b0C := pexecM_scope mv fu _ _ _ _ hS1
  rw [hS1ps] at b0C
  have tkC : (⟨(gS P (CP n (szv k) (2 ^ k) k n)).mem.take (gS P (C12 n (szv k) (2 ^ k) k)).mem.length,
      (gS P (CP n (szv k) (2 ^ k) k n)).bs.take (gS P (C12 n (szv k) (2 ^ k) k)).bs.length⟩ : PS) = gS P (C12 n (szv k) (2 ^ k) k) :=
    gS_takeC P (C12 n (szv k) (2 ^ k) k) (C12 n (szv k) (2 ^ k) k) [ci n] rfl
  simp only [tkC] at b0C
  -- the scope of the build loop
  have sloopD := seqM_some hD retD (pexecM_skip mv fu rD.ps rD.vv)
  have sdD := seqM_some dB rfl sloopD
  obtain ⟨rS2, hS2, hS2ps, hS2ret, hS2vv, hS2w, hS2c, hS2n⟩ : ∃ r : PRM,
      pexecM mv fu (seqs [dI (.binary i32 .sub (vI mv.nv 5) (litI 1)), .whileLoop (.binary bT .ge (vI mv.nv 12) (litI 1)) (buildBody mv.nv)])
        (gS P (C12 n (szv k) (2 ^ k) k)) (VC V1 Vin) = some r ∧
      r.ps = gS P (CP n (szv k) (2 ^ k) k 0) ∧ r.ret = none ∧ r.vv = VC Vf Vin ∧ r.wk ≤ szv k ∧ r.cost ≤ 900 * szv k + 100 ∧
      r.need ≤ P.length + 105 := by
    refine ⟨_, sdD, by simpa using psD, by simpa using retD, by simpa using vvD, ?_, ?_, ?_⟩
    · simp at wD ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cD ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, C12, CP, psD] at nD ⊢; omega
  have b0D := pexecM_scope mv fu _ _ _ _ hS2
  rw [hS2ps] at b0D
  have tkD : (⟨(gS P (CP n (szv k) (2 ^ k) k 0)).mem.take (gS P (C12 n (szv k) (2 ^ k) k)).mem.length,
      (gS P (CP n (szv k) (2 ^ k) k 0)).bs.take (gS P (C12 n (szv k) (2 ^ k) k)).bs.length⟩ : PS) = gS P (C12 n (szv k) (2 ^ k) k) :=
    gS_takeC P (C12 n (szv k) (2 ^ k) k) (C12 n (szv k) (2 ^ k) k) [ci 0] rfl
  simp only [tkD] at b0D
  have eD := seqM_some b0D hS2ret (pexecM_skip mv fu _ _)
  have eC := seqM_some b0C hS1ret (by rw [hS1vv]; exact eD)
  have t12 := seqM_some d12 rfl eC
  have t11 := seqM_some d11 rfl t12
  have tB := seqM_some hB retB (by rw [psB, vvB]; exact t11)
  have t10 := seqM_some d10 rfl tB
  have t9 := seqM_some d9 rfl t10
  have t8 := seqM_some d8 rfl t9
  have t7 := seqM_some d7 rfl t8
  have t6 := seqM_some d6 rfl t7
  have t5 := seqM_some d5 rfl t6
  have tA := seqM_some hA retA (by rw [psA, vvA]; exact t5)
  have t4 := seqM_some d4 rfl tA
  have t3 := seqM_some d3 rfl t4
  have t2 := seqM_some d2 rfl t3
  have t1 := seqM_some d1 rfl t2
  have hlt2k : k < 2 ^ k := Nat.lt_two_pow_self
  have hTI : TInv maxMon Vf (szv k) := ⟨hNpos, hlenf, binv_end maxMon Vf (szv k) hBf⟩
  refine ⟨_, t1, rfl, ⟨C12 n (szv k) (2 ^ k) k, rfl⟩, Vf, ?_, hTI, hVf, hlenf, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hS2vv]
  · intro i hi
    rw [hleaf (szv k + i) (by omega)]
    have := hI1.2 (szv k + i) (by omega)
    rw [this, if_pos ⟨by omega, by omega⟩]
    congr 1; omega
  · intro i hi1 hi2
    rw [hleaf (szv k + i) (by omega)]
    have := hI1.2 (szv k + i) (by omega)
    rw [this, if_neg (fun hh => by omega)]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA cB hS1c hS2c ⊢
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, C12, CP, psA, psB] at nA nB hS1n hS2n ⊢
    omega
  · simp at wA wB hS1w hS2w ⊢
    omega

end Proofs.SegmentTreeCtor
