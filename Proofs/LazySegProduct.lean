import Proofs.LazySegSet
import Proofs.SegTreeMath

namespace Proofs.LazySegProduct
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
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den VO VO_get0 VO_set0)
open Proofs.RunLengthExec (inc_val)
open Proofs.LazySegBlocks
open Proofs.LazySegUpd
open Proofs.SegTreeMath
open Proofs.LazySegMath (Rep LzFid Cl SInvL)
open Proofs.LazySegChmin (chminMon mi)
open Proofs.SegmentTreeExec (UpdBlk upd_exec mx AppBlk appblk_exec maxMon)


/-! ### `LazySegmentTree::product` (nv = 2).
Cells: 0 = n, 1 = n_node, 2 = h_node, 3 = l, 4 = r, 5 = pw, 6 = e (the inlined `M::e()`), 7 = l_op, 8 = e, 9 = r_op -/

abbrev EMIN : Int := -9223372036854775808

abbrev condP (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 3)) (.variable i32 (nv + 4))
abbrev oddE (nv k : Nat) : NExpr :=
  .binary bT .eq (.divrem i32 true (.variable i32 (nv + k)) (.literal i32 2)) (.literal i32 1)
abbrev aLeft (nv : Nat) : NStmt := .assign (nv + 7) s64 (vS nv 13)
abbrev incL (nv : Nat) : NStmt := .assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.literal i32 1))
abbrev decR (nv : Nat) : NStmt := .assign (nv + 4) i32 (.binary i32 .sub (.variable i32 (nv + 4)) (.literal i32 1))
abbrev aRight (nv : Nat) : NStmt := .assign (nv + 9) s64 (vS nv 13)
abbrev halveL (nv : Nat) : NStmt := .assign (nv + 3) i32 (.divrem i32 false (.variable i32 (nv + 3)) (.literal i32 2))
abbrev halveR (nv : Nat) : NStmt := .assign (nv + 4) i32 (.divrem i32 false (.variable i32 (nv + 4)) (.literal i32 2))
abbrev Br1 (nv : Nat) : Command :=
  .sequence (.scope (AppBlk nv 10 (vS nv 7) (.read s64 (.local 0) (.cast u64 (.variable i32 (nv + 3))))
    (.sequence (.primitive (aLeft nv)) (.sequence (.primitive (incL nv)) Sk)))) Sk
abbrev Br2 (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (decR nv))
    (AppBlk nv 10 (.read s64 (.local 0) (.cast u64 (.variable i32 (nv + 4)))) (vS nv 9)
      (.sequence (.primitive (aRight nv)) Sk)))) Sk
abbrev LoopBodyP (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (oddE nv 3) (Br1 nv) Sk) (.sequence (.branch (oddE nv 4) (Br2 nv) Sk)
    (.sequence (.primitive (halveL nv)) (.sequence (.primitive (halveR nv)) Sk))))) Sk

abbrev LPL (n N h l r pw : Nat) (left right : Int) : List Cell :=
  [ci n, ci N, ci h, ci l, ci r, ci pw, cs EMIN, cs left, cs EMIN, cs right]

theorem odd_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (k x : Nat) (hk : cl[k]? = some (ci x))
    (hx : x < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (oddE mv.nv k) = some (if x % 2 = 1 then 1 else 0) := by
  have ex : penvN mv.nv (gS P cl) (mv.nv + k) i32 = some (x : Int) := envs mv P cl k (ci x) hk (i32v x hx)
  have hr : checkedDivRem i32 true (x : Int) 2 = some ((x % 2 : Nat) : Int) := by
    have hq : (x : Int).tdiv 2 = ((x / 2 : Nat) : Int) := by
      rw [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg x)]; omega
    have hr' : (x : Int).tmod 2 = ((x % 2 : Nat) : Int) := by
      rw [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg x)]; omega
    have hv : i32.valid ((x / 2 : Nat) : Int) = true := i32v _ (by show x / 2 < 2147483648; omega)
    have hv2 : i32.valid ((x % 2 : Nat) : Int) = true := i32v _ (by show x % 2 < 2147483648; omega)
    unfold checkedDivRem
    have h0 : ((2 : Int) == 0) = false := by decide
    simp only [h0, hq, hr', hv, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    exact conv_signed i32 rfl rfl _ hv2
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_divrem, den_variable, ex, Option.bind_some, den_literal,
    if_pos (show i32.valid 2 = true from rfl), Option.bind_some, hr, Option.bind_some, den_literal,
    if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  by_cases h : x % 2 = 1
  · have : ((x % 2 : Nat) : Int) = 1 := by omega
    simp [binaryValue, this, h, Ty.convert, bT, Ty.valid]
  · have : ((x % 2 : Nat) : Int) ≠ 1 := by omega
    simp [binaryValue, this, h, Ty.convert, bT, Ty.valid]
    omega

set_option maxHeartbeats 16000000 in
/-- `if (l % 2 == 1) { l_op = apply(l_op, node[l]); l++; }` -/
theorem br1_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (P : List Cell) (fu : Nat) (V : List Int) (vv : Nat → List Int)
    (n N h l r pw : Nat) (left right : Int) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (hl : l + 1 < 2147483648) (hr : r < 2147483648) (vL : s64.valid left = true) (vR : s64.valid right = true)
    (hodd : l % 2 = 1 → l < (vv 0).length ∧ (vv 0).getD l 0 = V.getD l 0 ∧ s64.valid (V.getD l 0) = true) :
    ∃ r1 : PRM, pexecM mv fu (.branch (oddE mv.nv 3) (Br1 mv.nv) Sk) (gS P (LPL n N h l r pw left right)) vv = some r1 ∧
      r1.ret = none ∧ r1.ps = gS P (LPL n N h (pl1 l) r pw (pleft maxMon V l left) right) ∧ r1.vv = vv ∧
      r1.cost ≤ 400 ∧ r1.need ≤ P.length + 100 ∧ r1.wk = 0 := by
  have hl' : l < 2147483648 := by omega
  have hc := odd_val mv P vv (LPL n N h l r pw left right) 3 l rfl hl'
  by_cases hod : l % 2 = 1
  · rw [if_pos hod] at hc
    obtain ⟨hlt, hag, vy⟩ := hodd hod
    set y := V.getD l 0 with hy
    -- the apply block
    have hX : vdenM mv vv (penvN mv.nv (gS P (LPL n N h l r pw left right))) (vS mv.nv 7) = some left := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 7 left rfl vL
    have E3 : penvN mv.nv (gS P (LPL n N h l r pw left right ++ [cs left])) (mv.nv + 3) i32 = some (l : Int) :=
      envs mv P (LPL n N h l r pw left right ++ [cs left]) 3 (ci l) rfl (i32v l hl')
    have hY : vdenM mv vv (penvN mv.nv (gS P (LPL n N h l r pw left right ++ [cs left])))
        (.read s64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 3)))) = some y :=
      rdM_val mv vv _ 0 (by omega) s64 ty0.symm (.cast u64 (.variable i32 (mv.nv + 3))) rfl rfl l
        (cidx_den _ _ l E3 hl') y (by have h := vec_getI (vv 0) l hlt; rw [hag] at h; exact h) (by rw [ty0]; exact vy)
    have vm : s64.valid (mx left y) = true := by unfold mx; split <;> assumption
    -- the rest of the branch body: left = ret; l++
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ : ∃ r2 : PRM,
        pexecM mv fu (.sequence (.primitive (aLeft mv.nv)) (.sequence (.primitive (incL mv.nv)) Sk))
          (gS P (LPL n N h l r pw left right ++ [cs left, cs y, cs (mx left y), cs (mx left y)])) vv = some r2 ∧
        r2.ret = none ∧ r2.ps = gS P (LPL n N h (l + 1) r pw (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]) ∧
        r2.vv = vv ∧ r2.cost ≤ 100 ∧ r2.need ≤ P.length + 60 ∧ r2.wk = 0 := by
      have s1 := gSM_assign mv P (LPL n N h l r pw left right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]) vv 7 (by simp)
        s64 (vS mv.nv 13) (mx left y) (mx left y)
        (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 13 (mx left y) rfl vm) (cs left) rfl rfl vL
        (conv_signed s64 rfl rfl _ vm)
      have a1 := (pexecM_prim mv fu (aLeft mv.nv) _ _).trans s1
      have eA : (LPL n N h l r pw left right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]).set 7 ⟨s64, mx left y⟩ =
          LPL n N h l r pw (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)] := rfl
      rw [eA] at a1
      have E3' : penvN mv.nv (gS P (LPL n N h l r pw (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]))
          (mv.nv + 3) i32 = some (l : Int) :=
        envs mv P (LPL n N h l r pw (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]) 3 (ci l) rfl (i32v l hl')
      have e2 := inc_val mv vv _ (mv.nv + 3) l E3' hl
      have s2 := gSM_assign mv P (LPL n N h l r pw (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]) vv 3
        (by simp) i32 _ _ _ e2 (ci l) rfl rfl (i32v l hl') (conv_signed i32 rfl rfl _ (i32v (l + 1) (by show l + 1 < 2147483648; omega)))
      have eB : (LPL n N h l r pw (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]).set 3 ⟨i32, ((l + 1 : Nat) : Int)⟩ =
          LPL n N h (l + 1) r pw (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)] := rfl
      rw [eB] at s2
      have a2 := (pexecM_prim mv fu (incL mv.nv) _ _).trans s2
      have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
      have b1 := seqM_some a1 rfl b2
      refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
    obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P vv fu (LPL n N h l r pw left right) 10 rfl (vS mv.nv 7)
      (.read s64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 3)))) left y vL vy hX hY
      (.sequence (.primitive (aLeft mv.nv)) (.sequence (.primitive (incL mv.nv)) Sk)) r2 hr2
    have b0 := pexecM_scope mv fu _ _ _ _ hA
    have tk := gS_takeC P (LPL n N h l r pw left right) (LPL n N h (l + 1) r pw (mx left y) right)
      [cs left, cs y, cs (mx left y), cs (mx left y)] rfl
    rw [psA, ps2] at b0
    simp only [tk] at b0
    have b1 := seqM_some b0 (by rw [retA, ret2]) (pexecM_skip mv fu _ _)
    have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b1
    refine ⟨_, b3, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · have e1 : pl1 l = l + 1 := by simp [pl1, hod]
      have e2 : pleft maxMon V l left = mx left y := by simp [pleft, hod, hy]; rfl
      rw [e1, e2]
    · simp [vvA, vv2]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA c2 ⊢; omega
    · have hA' := nA (P.length + 90) (by omega) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' n2 ⊢
      omega
    · simp [wA, w2]
  · rw [if_neg hod] at hc
    have b3 := pexecM_branch_false mv fu _ (Br1 mv.nv) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    refine ⟨_, b3, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · have e1 : pl1 l = l := by simp [pl1, hod]
      have e2 : pleft maxMon V l left = left := by simp [pleft, hod]
      rw [e1, e2]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp

theorem dec_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (slot k : Nat)
    (h : env slot i32 = some (k : Int)) (hk : 1 ≤ k) (hk2 : k < 2147483648) :
    vdenM mv vv env (.binary i32 .sub (.variable i32 slot) (.literal i32 1)) = some ((k - 1 : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, h, Option.bind_some, den_literal,
    if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .sub (k : Int) 1 = ((k - 1 : Nat) : Int) := by
    show (k : Int) - 1 = _; omega
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32v _ (by show k - 1 < 2147483648; omega))

set_option maxHeartbeats 16000000 in
/-- `if (r % 2 == 1) { r--; r_op = apply(node[r], r_op); }` -/
theorem br2_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (P : List Cell) (fu : Nat) (V : List Int) (vv : Nat → List Int)
    (n N h l r pw : Nat) (left right : Int) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (hl : l < 2147483648) (hr : r < 2147483648) (vL : s64.valid left = true) (vR : s64.valid right = true)
    (hodd : r % 2 = 1 → r - 1 < (vv 0).length ∧ (vv 0).getD (r - 1) 0 = V.getD (r - 1) 0 ∧ s64.valid (V.getD (r - 1) 0) = true) :
    ∃ r1 : PRM, pexecM mv fu (.branch (oddE mv.nv 4) (Br2 mv.nv) Sk) (gS P (LPL n N h l r pw left right)) vv = some r1 ∧
      r1.ret = none ∧ r1.ps = gS P (LPL n N h l (pr1 r) pw left (pright maxMon V r right)) ∧ r1.vv = vv ∧
      r1.cost ≤ 400 ∧ r1.need ≤ P.length + 100 ∧ r1.wk = 0 := by
  have hc := odd_val mv P vv (LPL n N h l r pw left right) 4 r rfl hr
  by_cases hod : r % 2 = 1
  · rw [if_pos hod] at hc
    obtain ⟨hlt, hag, vy⟩ := hodd hod
    have hr1 : 1 ≤ r := by omega
    set y := V.getD (r - 1) 0 with hy
    -- r--
    have E4 : penvN mv.nv (gS P (LPL n N h l r pw left right)) (mv.nv + 4) i32 = some (r : Int) :=
      envs mv P (LPL n N h l r pw left right) 4 (ci r) rfl (i32v r hr)
    have e1 := dec_val mv vv _ (mv.nv + 4) r E4 hr1 hr
    have s1 := gSM_assign mv P (LPL n N h l r pw left right) vv 4 (by simp) i32 _ _ _ e1 (ci r) rfl rfl (i32v r hr)
      (conv_signed i32 rfl rfl _ (i32v (r - 1) (by show r - 1 < 2147483648; omega)))
    have eA : (LPL n N h l r pw left right).set 4 ⟨i32, ((r - 1 : Nat) : Int)⟩ = LPL n N h l (r - 1) pw left right := rfl
    rw [eA] at s1
    have a1 := (pexecM_prim mv fu (decR mv.nv) _ _).trans s1
    -- the apply block
    have hr' : r - 1 < 2147483648 := by omega
    have E4' : penvN mv.nv (gS P (LPL n N h l (r - 1) pw left right)) (mv.nv + 4) i32 = some ((r - 1 : Nat) : Int) :=
      envs mv P (LPL n N h l (r - 1) pw left right) 4 (ci (r - 1)) rfl (i32v (r - 1) hr')
    have hX : vdenM mv vv (penvN mv.nv (gS P (LPL n N h l (r - 1) pw left right)))
        (.read s64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 4)))) = some y :=
      rdM_val mv vv _ 0 (by omega) s64 ty0.symm (.cast u64 (.variable i32 (mv.nv + 4))) rfl rfl (r - 1)
        (cidx_den _ _ (r - 1) E4' hr') y (by have h := vec_getI (vv 0) (r - 1) hlt; rw [hag] at h; exact h) (by rw [ty0]; exact vy)
    have hY : vdenM mv vv (penvN mv.nv (gS P (LPL n N h l (r - 1) pw left right ++ [cs y]))) (vS mv.nv 9) = some right := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 9 right rfl vR
    have vm : s64.valid (mx y right) = true := by unfold mx; split <;> assumption
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ : ∃ r2 : PRM,
        pexecM mv fu (.sequence (.primitive (aRight mv.nv)) Sk)
          (gS P (LPL n N h l (r - 1) pw left right ++ [cs y, cs right, cs (mx y right), cs (mx y right)])) vv = some r2 ∧
        r2.ret = none ∧ r2.ps = gS P (LPL n N h l (r - 1) pw left (mx y right) ++ [cs y, cs right, cs (mx y right), cs (mx y right)]) ∧
        r2.vv = vv ∧ r2.cost ≤ 100 ∧ r2.need ≤ P.length + 60 ∧ r2.wk = 0 := by
      have s2 := gSM_assign mv P (LPL n N h l (r - 1) pw left right ++ [cs y, cs right, cs (mx y right), cs (mx y right)]) vv 9
        (by simp) s64 (vS mv.nv 13) (mx y right) (mx y right)
        (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 13 (mx y right) rfl vm) (cs right) rfl rfl vR
        (conv_signed s64 rfl rfl _ vm)
      have eB : (LPL n N h l (r - 1) pw left right ++ [cs y, cs right, cs (mx y right), cs (mx y right)]).set 9 ⟨s64, mx y right⟩ =
          LPL n N h l (r - 1) pw left (mx y right) ++ [cs y, cs right, cs (mx y right), cs (mx y right)] := rfl
      rw [eB] at s2
      have a2 := (pexecM_prim mv fu (aRight mv.nv) _ _).trans s2
      have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
      refine ⟨_, b2, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
    obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P vv fu (LPL n N h l (r - 1) pw left right) 10 rfl
      (.read s64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 4)))) (vS mv.nv 9) y right vy vR hX hY
      (.sequence (.primitive (aRight mv.nv)) Sk) r2 hr2
    have s3 := seqM_some a1 rfl hA
    have b0 := pexecM_scope mv fu _ _ _ _ s3
    have tk := gS_takeC P (LPL n N h l r pw left right) (LPL n N h l (r - 1) pw left (mx y right))
      [cs y, cs right, cs (mx y right), cs (mx y right)] rfl
    rw [psA, ps2] at b0
    simp only [tk] at b0
    have b1 := seqM_some b0 (by rw [retA, ret2]) (pexecM_skip mv fu _ _)
    have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b1
    refine ⟨_, b3, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · have e1 : pr1 r = r - 1 := by simp [pr1, hod]
      have e2 : pright maxMon V r right = mx y right := by simp [pright, hod, hy]; rfl
      rw [e1, e2]
    · simp [vvA, vv2]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA c2 ⊢; omega
    · have hA' := nA (P.length + 90) (by omega) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' n2 ⊢
      omega
    · simp [wA, w2]
  · rw [if_neg hod] at hc
    have b3 := pexecM_branch_false mv fu _ (Br2 mv.nv) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    refine ⟨_, b3, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · have e1 : pr1 r = r := by simp [pr1, hod]
      have e2 : pright maxMon V r right = right := by simp [pright, hod]
      rw [e1, e2]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp

theorem pleft_V (V : List Int) (hV : AllV maxMon V) (l : Nat) (left : Int) (vL : s64.valid left = true)
    (hodd : l % 2 = 1 → l < V.length) : s64.valid (pleft maxMon V l left) = true := by
  unfold pleft
  split
  · exact maxMon.closed _ _ vL (getD_V maxMon V hV l (hodd (by assumption)))
  · exact vL

theorem pright_V (V : List Int) (hV : AllV maxMon V) (r : Nat) (right : Int) (vR : s64.valid right = true)
    (hodd : r % 2 = 1 → r - 1 < V.length) : s64.valid (pright maxMon V r right) = true := by
  unfold pright
  split
  · exact maxMon.closed _ _ (getD_V maxMon V hV (r - 1) (hodd (by assumption))) vR
  · exact vR

set_option maxHeartbeats 16000000 in
/-- One iteration of the loop of `product`. -/
theorem prod_iter (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (P : List Cell) (fu : Nat) (V : List Int) (vv : Nat → List Int)
    (n N h l r pw : Nat) (left right : Int) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (hlr : l < r) (hr : r < 2147483648) (hrV : r ≤ V.length) (hV : AllV maxMon V) (hlenW : V.length ≤ (vv 0).length)
    (hrdL : l % 2 = 1 → (vv 0).getD l 0 = V.getD l 0) (hrdR : r % 2 = 1 → (vv 0).getD (r - 1) 0 = V.getD (r - 1) 0)
    (vL : s64.valid left = true) (vR : s64.valid right = true) :
    ∃ r1 : PRM, pexecM mv fu (LoopBodyP mv.nv) (gS P (LPL n N h l r pw left right)) vv = some r1 ∧ r1.ret = none ∧
      r1.ps = gS P (LPL n N h (pl1 l / 2) (pr1 r / 2) pw (pleft maxMon V l left) (pright maxMon V r right)) ∧
      r1.vv = vv ∧ r1.cost ≤ 1500 ∧ r1.need ≤ P.length + 100 ∧ r1.wk = 0 := by
  have hl : l + 1 < 2147483648 := by omega
  have hoddL : l % 2 = 1 → l < (vv 0).length ∧ (vv 0).getD l 0 = V.getD l 0 ∧ s64.valid (V.getD l 0) = true :=
    fun h' => ⟨by omega, hrdL h', getD_V maxMon V hV l (by omega)⟩
  obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := br1_exec mv hnv ty0 P fu V vv n N h l r pw left right hn hN hh hl hr vL vR hoddL
  have hpl : pl1 l ≤ r := by unfold pl1; split <;> omega
  have vL' : s64.valid (pleft maxMon V l left) = true := pleft_V V hV l left vL (fun _ => by omega)
  have hoddR : r % 2 = 1 → r - 1 < (vv 0).length ∧ (vv 0).getD (r - 1) 0 = V.getD (r - 1) 0 ∧ s64.valid (V.getD (r - 1) 0) = true :=
    fun h' => ⟨by omega, hrdR h', getD_V maxMon V hV (r - 1) (by omega)⟩
  obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := br2_exec mv hnv ty0 P fu V vv n N h (pl1 l) r pw (pleft maxMon V l left) right hn hN hh
    (by omega) hr vL' vR hoddR
  -- l = l / 2
  have hpl' : pl1 l < 2147483648 := by omega
  have hpr : pr1 r ≤ r := by unfold pr1; split <;> omega
  have vR' : s64.valid (pright maxMon V r right) = true := pright_V V hV r right vR (fun _ => by omega)
  have E3 := envs mv P (LPL n N h (pl1 l) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right)) 3 (ci (pl1 l)) rfl (i32v _ hpl')
  have E3' : penvN mv.nv (gS P (LPL n N h (pl1 l) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right))) (mv.nv + 3) i32 =
      some ((pl1 l : Nat) : Int) := E3
  have e3 : vdenM mv vv (penvN mv.nv (gS P (LPL n N h (pl1 l) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right))))
      (.divrem i32 false (.variable i32 (mv.nv + 3)) (.literal i32 2)) = some ((pl1 l / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, E3', Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
    simpa using cdr_i32_div _ 2 hpl' (by omega) (by omega)
  have s3 := gSM_assign mv P (LPL n N h (pl1 l) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right)) vv 3 (by simp) i32 _ _ _ e3
    (ci (pl1 l)) rfl rfl (i32v _ hpl') (conv_signed i32 rfl rfl _ (i32v _ (by show pl1 l / 2 < 2147483648; omega)))
  have eC : (LPL n N h (pl1 l) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right)).set 3 ⟨i32, ((pl1 l / 2 : Nat) : Int)⟩ =
      LPL n N h (pl1 l / 2) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right) := rfl
  rw [eC] at s3
  have a3 := (pexecM_prim mv fu (halveL mv.nv) _ _).trans s3
  -- r = r / 2
  have hpr' : pr1 r < 2147483648 := by omega
  have E4 := envs mv P (LPL n N h (pl1 l / 2) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right)) 4 (ci (pr1 r)) rfl (i32v _ hpr')
  have E4' : penvN mv.nv (gS P (LPL n N h (pl1 l / 2) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right))) (mv.nv + 4) i32 =
      some ((pr1 r : Nat) : Int) := E4
  have e4 : vdenM mv vv (penvN mv.nv (gS P (LPL n N h (pl1 l / 2) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right))))
      (.divrem i32 false (.variable i32 (mv.nv + 4)) (.literal i32 2)) = some ((pr1 r / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, E4', Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
    simpa using cdr_i32_div _ 2 hpr' (by omega) (by omega)
  have s4 := gSM_assign mv P (LPL n N h (pl1 l / 2) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right)) vv 4 (by simp) i32 _ _ _ e4
    (ci (pr1 r)) rfl rfl (i32v _ hpr') (conv_signed i32 rfl rfl _ (i32v _ (by show pr1 r / 2 < 2147483648; omega)))
  have eD : (LPL n N h (pl1 l / 2) (pr1 r) pw (pleft maxMon V l left) (pright maxMon V r right)).set 4 ⟨i32, ((pr1 r / 2 : Nat) : Int)⟩ =
      LPL n N h (pl1 l / 2) (pr1 r / 2) pw (pleft maxMon V l left) (pright maxMon V r right) := rfl
  rw [eD] at s4
  have a4 := (pexecM_prim mv fu (halveR mv.nv) _ _).trans s4
  have b4 := seqM_some a4 rfl (pexecM_skip mv fu _ _)
  have b3 := seqM_some a3 rfl b4
  have b2 := seqM_some h2 ret2 (by rw [ps2, vv2]; exact b3)
  have b1 := seqM_some h1 ret1 (by rw [ps1, vv1]; exact b2)
  obtain ⟨rb, hb, hbps, hbret, hbvv, hbw, hbc, hbn⟩ : ∃ rb : PRM,
      pexecM mv fu (.sequence (.branch (oddE mv.nv 3) (Br1 mv.nv) Sk) (.sequence (.branch (oddE mv.nv 4) (Br2 mv.nv) Sk)
        (.sequence (.primitive (halveL mv.nv)) (.sequence (.primitive (halveR mv.nv)) Sk)))) (gS P (LPL n N h l r pw left right)) vv = some rb ∧
      rb.ps = gS P (LPL n N h (pl1 l / 2) (pr1 r / 2) pw (pleft maxMon V l left) (pright maxMon V r right)) ∧ rb.ret = none ∧
      rb.vv = vv ∧ rb.wk = 0 ∧ rb.cost ≤ 1400 ∧ rb.need ≤ P.length + 100 := by
    refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [w1, w2]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
  have b0 := pexecM_scope mv fu _ _ _ _ hb
  rw [hbps] at b0
  have tk := Proofs.PexecKit.scope_take (gS P (LPL n N h l r pw left right))
    (gS P (LPL n N h (pl1 l / 2) (pr1 r / 2) pw (pleft maxMon V l left) (pright maxMon V r right)))
    (by simp [gS_mem_len]) (by simp [gS_bs_len])
  simp only [tk] at b0
  have b5 := seqM_some b0 hbret (pexecM_skip mv fu _ _)
  refine ⟨_, b5, rfl, rfl, hbvv, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hbc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hbn ⊢; omega
  · simp [hbw]

theorem cond_p_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (n N h l r pw : Nat) (left right : Int)
    (hl : l < 2147483648) (hr : r < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (LPL n N h l r pw left right))) (condP mv.nv) = some (if l < r then 1 else 0) := by
  have el : penvN mv.nv (gS P (LPL n N h l r pw left right)) (mv.nv + 3) i32 = some (l : Int) :=
    envs mv P (LPL n N h l r pw left right) 3 (ci l) rfl (i32v l hl)
  have er : penvN mv.nv (gS P (LPL n N h l r pw left right)) (mv.nv + 4) i32 = some (r : Int) :=
    envs mv P (LPL n N h l r pw left right) 4 (ci r) rfl (i32v r hr)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, el, Option.bind_some, den_variable, er, Option.bind_some]
  by_cases hlt : l < r
  · have : (l : Int) < (r : Int) := by omega
    simp [binaryValue, hlt, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((l : Int) < (r : Int)) := by omega
    simp [binaryValue, hlt, this, Ty.convert, bT, Ty.valid]

/-- The number of iterations of the product loop for the width `w = r - l`. -/
def lsteps (w : Nat) : Nat := if w = 0 then 0 else Nat.log2 w + 1

theorem width_half (l r : Nat) (h : l < r) : pr1 r / 2 - pl1 l / 2 ≤ (r - l) / 2 := by
  unfold pl1 pr1; split <;> split <;> omega

theorem lsteps_step (w w' : Nat) (hw : 0 < w) (h : w' ≤ w / 2) : lsteps w' + 1 ≤ lsteps w := by
  unfold lsteps
  rw [if_neg (show w ≠ 0 by omega)]
  by_cases h0 : w' = 0
  · subst h0; simp
  · rw [if_neg h0]
    have : Nat.log2 w' + 1 ≤ Nat.log2 w := by
      rw [Nat.le_log2 (by omega), Nat.pow_succ]
      have := Nat.log2_self_le h0
      omega
    omega

set_option maxHeartbeats 16000000 in
/-- The loop `while (l < r) {...}`. -/
theorem prod_loop (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (P : List Cell) (V : List Int) (vv : Nat → List Int)
    (n N h pw : Nat) (T : Int)
    (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648) (hV : AllV maxMon V) (hT : TInv maxMon V N)
    (hN2 : 2 * N < 2147483648) (hlenW : V.length ≤ (vv 0).length) (LR : Nat → Nat → Prop)
    (hLRstep : ∀ l r, LR l r → l < r → LR (pl1 l / 2) (pr1 r / 2))
    (hLRrd : ∀ l r, LR l r → l < r → (l % 2 = 1 → (vv 0).getD l 0 = V.getD l 0) ∧
      (r % 2 = 1 → (vv 0).getD (r - 1) 0 = V.getD (r - 1) 0)) :
    ∀ (w l r : Nat) (left right : Int) (fu : Nat), r - l = w → LR l r → PInv maxMon V N T l r left right → lsteps w + 1 ≤ fu →
      ∃ (res : PRM) (lF rF : Nat) (leftF rightF : Int), pexecM mv fu (.whileLoop (condP mv.nv) (LoopBodyP mv.nv))
          (gS P (LPL n N h l r pw left right)) vv = some res ∧ res.ret = none ∧
        res.ps = gS P (LPL n N h lF rF pw leftF rightF) ∧ res.vv = vv ∧ PInv maxMon V N T lF rF leftF rightF ∧ ¬ lF < rF ∧
        res.cost ≤ 1600 * lsteps w + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk = 0 := by
  intro w
  induction w using Nat.strongRecOn with
  | _ w ih =>
    intro l r left right fu hw hLR hI hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hlen := hT.2.1
    obtain ⟨h1, h1', h2, h3, h4, h5⟩ := hI
    have hr31 : r < 2147483648 := by omega
    have hl31 : l < 2147483648 := by omega
    have hc := cond_p_val mv P vv n N h l r pw left right hl31 hr31
    by_cases hlr : l < r
    · rw [if_pos hlr] at hc
      obtain ⟨r1, hr1, ret1, ps1, vv1, c1, n1, w1⟩ := prod_iter mv hnv ty0 P (fu' + 1) V vv n N h l r pw left right hn hN hh hlr hr31
        (by omega) hV hlenW (hLRrd l r hLR hlr).1 (hLRrd l r hLR hlr).2 h3 h4
      have hI0 : PInv maxMon V N T l r left right := ⟨h1, h1', h2, h3, h4, h5⟩
      have hI' := prod_step maxMon V N T hV hT l r left right hI0 hlr
      have hwid := width_half l r hlr
      obtain ⟨r2, lF, rF, leftF, rightF, hr2, ret2, ps2, vv2, hIF, hex, c2, n2, w2⟩ :=
        ih (pr1 r / 2 - pl1 l / 2) (by omega) (pl1 l / 2) (pr1 r / 2) _ _ fu' rfl (hLRstep l r hLR hlr) hI' (by
          have := lsteps_step w (pr1 r / 2 - pl1 l / 2) (by omega) (by omega); omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, hr1, ret1, ps1, vv1, hr2]
      have hls := lsteps_step w (pr1 r / 2 - pl1 l / 2) (by omega) (by omega)
      refine ⟨_, lF, rF, leftF, rightF, rfl, ret2, ps2, vv2, hIF, hex, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
      · simp at w1 w2 ⊢; omega
    · rw [if_neg hlr] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      have hw0 : w = 0 := by omega
      refine ⟨_, l, r, left, right, rfl, rfl, rfl, rfl, ⟨h1, h1', h2, h3, h4, h5⟩, hlr, ?_, ?_, rfl⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, lsteps, hw0]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]


end Proofs.LazySegProduct
