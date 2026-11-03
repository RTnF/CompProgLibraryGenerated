import Proofs.SegmentTreeExec
import Proofs.SegmentTreeSet

namespace Proofs.SegmentTreeProduct
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
open Proofs.SegmentTreeExec
open Proofs.SegTreeMath

/-! ### `SegmentTree::product` (nv = 1: node).
Cells: 0 = n, 1 = n_node, 2 = h_node, 3 = l, 4 = r, 5 = e (the inlined `M::e()`), 6 = l_op, 7 = e, 8 = r_op -/

abbrev EMIN : Int := -9223372036854775808

abbrev condP (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 3)) (.variable i32 (nv + 4))
abbrev oddE (nv k : Nat) : NExpr :=
  .binary bT .eq (.divrem i32 true (.variable i32 (nv + k)) (.literal i32 2)) (.literal i32 1)
abbrev aLeft (nv : Nat) : NStmt := .assign (nv + 6) s64 (vS nv 12)
abbrev incL (nv : Nat) : NStmt := .assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.literal i32 1))
abbrev decR (nv : Nat) : NStmt := .assign (nv + 4) i32 (.binary i32 .sub (.variable i32 (nv + 4)) (.literal i32 1))
abbrev aRight (nv : Nat) : NStmt := .assign (nv + 8) s64 (vS nv 12)
abbrev halveL (nv : Nat) : NStmt := .assign (nv + 3) i32 (.divrem i32 false (.variable i32 (nv + 3)) (.literal i32 2))
abbrev halveR (nv : Nat) : NStmt := .assign (nv + 4) i32 (.divrem i32 false (.variable i32 (nv + 4)) (.literal i32 2))
abbrev Br1 (nv : Nat) : Command :=
  .sequence (.scope (AppBlk nv 9 (vS nv 6) (.read s64 (.local 0) (.cast u64 (.variable i32 (nv + 3))))
    (.sequence (.primitive (aLeft nv)) (.sequence (.primitive (incL nv)) Sk)))) Sk
abbrev Br2 (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (decR nv))
    (AppBlk nv 9 (.read s64 (.local 0) (.cast u64 (.variable i32 (nv + 4)))) (vS nv 8)
      (.sequence (.primitive (aRight nv)) Sk)))) Sk
abbrev LoopBodyP (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (oddE nv 3) (Br1 nv) Sk) (.sequence (.branch (oddE nv 4) (Br2 nv) Sk)
    (.sequence (.primitive (halveL nv)) (.sequence (.primitive (halveR nv)) Sk))))) Sk
abbrev bodyProd (nv : Nat) : Command :=
  .sequence (.primitive (.declare s64 true (.literal s64 EMIN)))
    (.sequence (.primitive (.declare s64 true (vS nv 5)))
      (.sequence (.primitive (.declare s64 true (.literal s64 EMIN)))
        (.sequence (.primitive (.declare s64 true (vS nv 7)))
          (.sequence (.primitive (.assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.variable i32 (nv + 1)))))
            (.sequence (.primitive (.assign (nv + 4) i32 (.binary i32 .add (.variable i32 (nv + 4)) (.variable i32 (nv + 1)))))
              (.sequence (.whileLoop (condP nv) (LoopBodyP nv))
                (AppBlk nv 9 (vS nv 6) (vS nv 8) (.sequence (.primitive (.ret (vS nv 12))) Sk))))))))

theorem body_eqProd : Proofs.SegmentTreeInstance.SegmentTree_cp__SegMax_long_long__long_long_product.body = bodyProd 1 := rfl

abbrev LP (n N h l r : Nat) (left right : Int) : List Cell :=
  [ci n, ci N, ci h, ci l, ci r, cs EMIN, cs left, cs EMIN, cs right]

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
theorem br1_exec (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (fu : Nat) (V : List Int)
    (n N h l r : Nat) (left right : Int) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (hl : l + 1 < 2147483648) (hr : r < 2147483648) (vL : s64.valid left = true) (vR : s64.valid right = true)
    (hodd : l % 2 = 1 → l < V.length ∧ s64.valid (V.getD l 0) = true) :
    ∃ r1 : PRM, pexecM mv fu (.branch (oddE mv.nv 3) (Br1 mv.nv) Sk) (gS P (LP n N h l r left right)) (VO V) = some r1 ∧
      r1.ret = none ∧ r1.ps = gS P (LP n N h (pl1 l) r (pleft maxMon V l left) right) ∧ r1.vv = VO V ∧
      r1.cost ≤ 400 ∧ r1.need ≤ P.length + 100 ∧ r1.wk = 0 := by
  have hl' : l < 2147483648 := by omega
  have hc := odd_val mv P (VO V) (LP n N h l r left right) 3 l rfl hl'
  by_cases hod : l % 2 = 1
  · rw [if_pos hod] at hc
    obtain ⟨hlt, vy⟩ := hodd hod
    set y := V.getD l 0 with hy
    -- the apply block
    have hX : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h l r left right))) (vS mv.nv 6) = some left := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 6 left rfl vL
    have E3 : penvN mv.nv (gS P (LP n N h l r left right ++ [cs left])) (mv.nv + 3) i32 = some (l : Int) :=
      envs mv P (LP n N h l r left right ++ [cs left]) 3 (ci l) rfl (i32v l hl')
    have hY : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h l r left right ++ [cs left])))
        (.read s64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 3)))) = some y :=
      rdM_val mv (VO V) _ 0 (by omega) s64 ty0.symm (.cast u64 (.variable i32 (mv.nv + 3))) rfl rfl l
        (cidx_den _ _ l E3 hl') y (by rw [VO_get0]; exact vec_getI V l hlt) (by rw [ty0]; exact vy)
    have vm : s64.valid (mx left y) = true := by unfold mx; split <;> assumption
    -- the rest of the branch body: left = ret; l++
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ : ∃ r2 : PRM,
        pexecM mv fu (.sequence (.primitive (aLeft mv.nv)) (.sequence (.primitive (incL mv.nv)) Sk))
          (gS P (LP n N h l r left right ++ [cs left, cs y, cs (mx left y), cs (mx left y)])) (VO V) = some r2 ∧
        r2.ret = none ∧ r2.ps = gS P (LP n N h (l + 1) r (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]) ∧
        r2.vv = VO V ∧ r2.cost ≤ 100 ∧ r2.need ≤ P.length + 60 ∧ r2.wk = 0 := by
      have s1 := gSM_assign mv P (LP n N h l r left right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]) (VO V) 6 (by simp)
        s64 (vS mv.nv 12) (mx left y) (mx left y)
        (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 12 (mx left y) rfl vm) (cs left) rfl rfl vL
        (conv_signed s64 rfl rfl _ vm)
      have a1 := (pexecM_prim mv fu (aLeft mv.nv) _ _).trans s1
      have eA : (LP n N h l r left right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]).set 6 ⟨s64, mx left y⟩ =
          LP n N h l r (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)] := rfl
      rw [eA] at a1
      have E3' : penvN mv.nv (gS P (LP n N h l r (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]))
          (mv.nv + 3) i32 = some (l : Int) :=
        envs mv P (LP n N h l r (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]) 3 (ci l) rfl (i32v l hl')
      have e2 := inc_val mv (VO V) _ (mv.nv + 3) l E3' hl
      have s2 := gSM_assign mv P (LP n N h l r (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]) (VO V) 3
        (by simp) i32 _ _ _ e2 (ci l) rfl rfl (i32v l hl') (conv_signed i32 rfl rfl _ (i32v (l + 1) (by show l + 1 < 2147483648; omega)))
      have eB : (LP n N h l r (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)]).set 3 ⟨i32, ((l + 1 : Nat) : Int)⟩ =
          LP n N h (l + 1) r (mx left y) right ++ [cs left, cs y, cs (mx left y), cs (mx left y)] := rfl
      rw [eB] at s2
      have a2 := (pexecM_prim mv fu (incL mv.nv) _ _).trans s2
      have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
      have b1 := seqM_some a1 rfl b2
      refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
    obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P (VO V) fu (LP n N h l r left right) 9 rfl (vS mv.nv 6)
      (.read s64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 3)))) left y vL vy hX hY
      (.sequence (.primitive (aLeft mv.nv)) (.sequence (.primitive (incL mv.nv)) Sk)) r2 hr2
    have b0 := pexecM_scope mv fu _ _ _ _ hA
    have tk := gS_takeC P (LP n N h l r left right) (LP n N h (l + 1) r (mx left y) right)
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
theorem br2_exec (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (fu : Nat) (V : List Int)
    (n N h l r : Nat) (left right : Int) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (hl : l < 2147483648) (hr : r < 2147483648) (vL : s64.valid left = true) (vR : s64.valid right = true)
    (hodd : r % 2 = 1 → r - 1 < V.length ∧ s64.valid (V.getD (r - 1) 0) = true) :
    ∃ r1 : PRM, pexecM mv fu (.branch (oddE mv.nv 4) (Br2 mv.nv) Sk) (gS P (LP n N h l r left right)) (VO V) = some r1 ∧
      r1.ret = none ∧ r1.ps = gS P (LP n N h l (pr1 r) left (pright maxMon V r right)) ∧ r1.vv = VO V ∧
      r1.cost ≤ 400 ∧ r1.need ≤ P.length + 100 ∧ r1.wk = 0 := by
  have hc := odd_val mv P (VO V) (LP n N h l r left right) 4 r rfl hr
  by_cases hod : r % 2 = 1
  · rw [if_pos hod] at hc
    obtain ⟨hlt, vy⟩ := hodd hod
    have hr1 : 1 ≤ r := by omega
    set y := V.getD (r - 1) 0 with hy
    -- r--
    have E4 : penvN mv.nv (gS P (LP n N h l r left right)) (mv.nv + 4) i32 = some (r : Int) :=
      envs mv P (LP n N h l r left right) 4 (ci r) rfl (i32v r hr)
    have e1 := dec_val mv (VO V) _ (mv.nv + 4) r E4 hr1 hr
    have s1 := gSM_assign mv P (LP n N h l r left right) (VO V) 4 (by simp) i32 _ _ _ e1 (ci r) rfl rfl (i32v r hr)
      (conv_signed i32 rfl rfl _ (i32v (r - 1) (by show r - 1 < 2147483648; omega)))
    have eA : (LP n N h l r left right).set 4 ⟨i32, ((r - 1 : Nat) : Int)⟩ = LP n N h l (r - 1) left right := rfl
    rw [eA] at s1
    have a1 := (pexecM_prim mv fu (decR mv.nv) _ _).trans s1
    -- the apply block
    have hr' : r - 1 < 2147483648 := by omega
    have E4' : penvN mv.nv (gS P (LP n N h l (r - 1) left right)) (mv.nv + 4) i32 = some ((r - 1 : Nat) : Int) :=
      envs mv P (LP n N h l (r - 1) left right) 4 (ci (r - 1)) rfl (i32v (r - 1) hr')
    have hX : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h l (r - 1) left right)))
        (.read s64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 4)))) = some y :=
      rdM_val mv (VO V) _ 0 (by omega) s64 ty0.symm (.cast u64 (.variable i32 (mv.nv + 4))) rfl rfl (r - 1)
        (cidx_den _ _ (r - 1) E4' hr') y (by rw [VO_get0]; exact vec_getI V (r - 1) hlt) (by rw [ty0]; exact vy)
    have hY : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h l (r - 1) left right ++ [cs y]))) (vS mv.nv 8) = some right := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 8 right rfl vR
    have vm : s64.valid (mx y right) = true := by unfold mx; split <;> assumption
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ : ∃ r2 : PRM,
        pexecM mv fu (.sequence (.primitive (aRight mv.nv)) Sk)
          (gS P (LP n N h l (r - 1) left right ++ [cs y, cs right, cs (mx y right), cs (mx y right)])) (VO V) = some r2 ∧
        r2.ret = none ∧ r2.ps = gS P (LP n N h l (r - 1) left (mx y right) ++ [cs y, cs right, cs (mx y right), cs (mx y right)]) ∧
        r2.vv = VO V ∧ r2.cost ≤ 100 ∧ r2.need ≤ P.length + 60 ∧ r2.wk = 0 := by
      have s2 := gSM_assign mv P (LP n N h l (r - 1) left right ++ [cs y, cs right, cs (mx y right), cs (mx y right)]) (VO V) 8
        (by simp) s64 (vS mv.nv 12) (mx y right) (mx y right)
        (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 12 (mx y right) rfl vm) (cs right) rfl rfl vR
        (conv_signed s64 rfl rfl _ vm)
      have eB : (LP n N h l (r - 1) left right ++ [cs y, cs right, cs (mx y right), cs (mx y right)]).set 8 ⟨s64, mx y right⟩ =
          LP n N h l (r - 1) left (mx y right) ++ [cs y, cs right, cs (mx y right), cs (mx y right)] := rfl
      rw [eB] at s2
      have a2 := (pexecM_prim mv fu (aRight mv.nv) _ _).trans s2
      have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
      refine ⟨_, b2, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
    obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P (VO V) fu (LP n N h l (r - 1) left right) 9 rfl
      (.read s64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 4)))) (vS mv.nv 8) y right vy vR hX hY
      (.sequence (.primitive (aRight mv.nv)) Sk) r2 hr2
    have s3 := seqM_some a1 rfl hA
    have b0 := pexecM_scope mv fu _ _ _ _ s3
    have tk := gS_takeC P (LP n N h l r left right) (LP n N h l (r - 1) left (mx y right))
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
theorem prod_iter (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (fu : Nat) (V : List Int)
    (n N h l r : Nat) (left right : Int) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (hlr : l < r) (hr : r < 2147483648) (hrV : r ≤ V.length) (hV : AllV maxMon V)
    (vL : s64.valid left = true) (vR : s64.valid right = true) :
    ∃ r1 : PRM, pexecM mv fu (LoopBodyP mv.nv) (gS P (LP n N h l r left right)) (VO V) = some r1 ∧ r1.ret = none ∧
      r1.ps = gS P (LP n N h (pl1 l / 2) (pr1 r / 2) (pleft maxMon V l left) (pright maxMon V r right)) ∧
      r1.vv = VO V ∧ r1.cost ≤ 1500 ∧ r1.need ≤ P.length + 100 ∧ r1.wk = 0 := by
  have hl : l + 1 < 2147483648 := by omega
  have hoddL : l % 2 = 1 → l < V.length ∧ s64.valid (V.getD l 0) = true :=
    fun _ => ⟨by omega, getD_V maxMon V hV l (by omega)⟩
  obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := br1_exec mv hnv ty0 P fu V n N h l r left right hn hN hh hl hr vL vR hoddL
  have hpl : pl1 l ≤ r := by unfold pl1; split <;> omega
  have vL' : s64.valid (pleft maxMon V l left) = true := pleft_V V hV l left vL (fun _ => by omega)
  have hoddR : r % 2 = 1 → r - 1 < V.length ∧ s64.valid (V.getD (r - 1) 0) = true :=
    fun _ => ⟨by omega, getD_V maxMon V hV (r - 1) (by omega)⟩
  obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := br2_exec mv hnv ty0 P fu V n N h (pl1 l) r (pleft maxMon V l left) right hn hN hh
    (by omega) hr vL' vR hoddR
  -- l = l / 2
  have hpl' : pl1 l < 2147483648 := by omega
  have hpr : pr1 r ≤ r := by unfold pr1; split <;> omega
  have vR' : s64.valid (pright maxMon V r right) = true := pright_V V hV r right vR (fun _ => by omega)
  have E3 := envs mv P (LP n N h (pl1 l) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right)) 3 (ci (pl1 l)) rfl (i32v _ hpl')
  have E3' : penvN mv.nv (gS P (LP n N h (pl1 l) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right))) (mv.nv + 3) i32 =
      some ((pl1 l : Nat) : Int) := E3
  have e3 : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h (pl1 l) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right))))
      (.divrem i32 false (.variable i32 (mv.nv + 3)) (.literal i32 2)) = some ((pl1 l / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, E3', Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some, Proofs.SegmentTreeSet.cdr_i32_div2 _ hpl']
  have s3 := gSM_assign mv P (LP n N h (pl1 l) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right)) (VO V) 3 (by simp) i32 _ _ _ e3
    (ci (pl1 l)) rfl rfl (i32v _ hpl') (conv_signed i32 rfl rfl _ (i32v _ (by show pl1 l / 2 < 2147483648; omega)))
  have eC : (LP n N h (pl1 l) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right)).set 3 ⟨i32, ((pl1 l / 2 : Nat) : Int)⟩ =
      LP n N h (pl1 l / 2) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right) := rfl
  rw [eC] at s3
  have a3 := (pexecM_prim mv fu (halveL mv.nv) _ _).trans s3
  -- r = r / 2
  have hpr' : pr1 r < 2147483648 := by omega
  have E4 := envs mv P (LP n N h (pl1 l / 2) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right)) 4 (ci (pr1 r)) rfl (i32v _ hpr')
  have E4' : penvN mv.nv (gS P (LP n N h (pl1 l / 2) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right))) (mv.nv + 4) i32 =
      some ((pr1 r : Nat) : Int) := E4
  have e4 : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h (pl1 l / 2) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right))))
      (.divrem i32 false (.variable i32 (mv.nv + 4)) (.literal i32 2)) = some ((pr1 r / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, E4', Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some, Proofs.SegmentTreeSet.cdr_i32_div2 _ hpr']
  have s4 := gSM_assign mv P (LP n N h (pl1 l / 2) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right)) (VO V) 4 (by simp) i32 _ _ _ e4
    (ci (pr1 r)) rfl rfl (i32v _ hpr') (conv_signed i32 rfl rfl _ (i32v _ (by show pr1 r / 2 < 2147483648; omega)))
  have eD : (LP n N h (pl1 l / 2) (pr1 r) (pleft maxMon V l left) (pright maxMon V r right)).set 4 ⟨i32, ((pr1 r / 2 : Nat) : Int)⟩ =
      LP n N h (pl1 l / 2) (pr1 r / 2) (pleft maxMon V l left) (pright maxMon V r right) := rfl
  rw [eD] at s4
  have a4 := (pexecM_prim mv fu (halveR mv.nv) _ _).trans s4
  have b4 := seqM_some a4 rfl (pexecM_skip mv fu _ _)
  have b3 := seqM_some a3 rfl b4
  have b2 := seqM_some h2 ret2 (by rw [ps2, vv2]; exact b3)
  have b1 := seqM_some h1 ret1 (by rw [ps1, vv1]; exact b2)
  obtain ⟨rb, hb, hbps, hbret, hbvv, hbw, hbc, hbn⟩ : ∃ rb : PRM,
      pexecM mv fu (.sequence (.branch (oddE mv.nv 3) (Br1 mv.nv) Sk) (.sequence (.branch (oddE mv.nv 4) (Br2 mv.nv) Sk)
        (.sequence (.primitive (halveL mv.nv)) (.sequence (.primitive (halveR mv.nv)) Sk)))) (gS P (LP n N h l r left right)) (VO V) = some rb ∧
      rb.ps = gS P (LP n N h (pl1 l / 2) (pr1 r / 2) (pleft maxMon V l left) (pright maxMon V r right)) ∧ rb.ret = none ∧
      rb.vv = VO V ∧ rb.wk = 0 ∧ rb.cost ≤ 1400 ∧ rb.need ≤ P.length + 100 := by
    refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [w1, w2]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
  have b0 := pexecM_scope mv fu _ _ _ _ hb
  rw [hbps] at b0
  have tk := Proofs.PexecKit.scope_take (gS P (LP n N h l r left right))
    (gS P (LP n N h (pl1 l / 2) (pr1 r / 2) (pleft maxMon V l left) (pright maxMon V r right)))
    (by simp [gS_mem_len]) (by simp [gS_bs_len])
  simp only [tk] at b0
  have b5 := seqM_some b0 hbret (pexecM_skip mv fu _ _)
  refine ⟨_, b5, rfl, rfl, hbvv, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hbc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hbn ⊢; omega
  · simp [hbw]

theorem cond_p_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (n N h l r : Nat) (left right : Int)
    (hl : l < 2147483648) (hr : r < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (LP n N h l r left right))) (condP mv.nv) = some (if l < r then 1 else 0) := by
  have el : penvN mv.nv (gS P (LP n N h l r left right)) (mv.nv + 3) i32 = some (l : Int) :=
    envs mv P (LP n N h l r left right) 3 (ci l) rfl (i32v l hl)
  have er : penvN mv.nv (gS P (LP n N h l r left right)) (mv.nv + 4) i32 = some (r : Int) :=
    envs mv P (LP n N h l r left right) 4 (ci r) rfl (i32v r hr)
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
theorem prod_loop (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (V : List Int) (n N h : Nat) (T : Int)
    (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648) (hV : AllV maxMon V) (hT : TInv maxMon V N)
    (hN2 : 2 * N < 2147483648) :
    ∀ (w l r : Nat) (left right : Int) (fu : Nat), r - l = w → PInv maxMon V N T l r left right → lsteps w + 1 ≤ fu →
      ∃ (res : PRM) (lF rF : Nat) (leftF rightF : Int), pexecM mv fu (.whileLoop (condP mv.nv) (LoopBodyP mv.nv))
          (gS P (LP n N h l r left right)) (VO V) = some res ∧ res.ret = none ∧
        res.ps = gS P (LP n N h lF rF leftF rightF) ∧ res.vv = VO V ∧ PInv maxMon V N T lF rF leftF rightF ∧ ¬ lF < rF ∧
        res.cost ≤ 1600 * lsteps w + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk = 0 := by
  intro w
  induction w using Nat.strongRecOn with
  | _ w ih =>
    intro l r left right fu hw hI hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hlen := hT.2.1
    obtain ⟨h1, h1', h2, h3, h4, h5⟩ := hI
    have hr31 : r < 2147483648 := by omega
    have hl31 : l < 2147483648 := by omega
    have hc := cond_p_val mv P (VO V) n N h l r left right hl31 hr31
    by_cases hlr : l < r
    · rw [if_pos hlr] at hc
      obtain ⟨r1, hr1, ret1, ps1, vv1, c1, n1, w1⟩ := prod_iter mv hnv ty0 P (fu' + 1) V n N h l r left right hn hN hh hlr hr31
        (by omega) hV h3 h4
      have hI0 : PInv maxMon V N T l r left right := ⟨h1, h1', h2, h3, h4, h5⟩
      have hI' := prod_step maxMon V N T hV hT l r left right hI0 hlr
      have hwid := width_half l r hlr
      obtain ⟨r2, lF, rF, leftF, rightF, hr2, ret2, ps2, vv2, hIF, hex, c2, n2, w2⟩ :=
        ih (pr1 r / 2 - pl1 l / 2) (by omega) (pl1 l / 2) (pr1 r / 2) _ _ fu' rfl hI' (by
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

theorem emin_valid : s64.valid EMIN = true := by decide

set_option maxHeartbeats 16000000 in
/-- The whole body of `SegmentTree::product`. -/
theorem body_execProd (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (n N h l0 r0 : Nat) (V : List Int)
    (hn : n < 2147483648) (hN2 : 2 * N < 2147483648) (hh : h < 2147483648) (hT : TInv maxMon V N) (hV : AllV maxMon V)
    (hlr : l0 ≤ r0) (hrN : r0 ≤ N) (fu : Nat) (hfu : Nat.log2 (r0 - l0) + 3 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyProd mv.nv) (gS P [ci n, ci N, ci h, ci l0, ci r0]) (VO V) = some r ∧
      r.ret = some (rfold maxMon V (l0 + N) (r0 - l0)) ∧ r.vv = VO V ∧ (∃ cl : List Cell, r.ps = gS P cl) ∧
      r.cost ≤ 1600 * (Nat.log2 (r0 - l0) + 1) + 400 ∧ r.need ≤ P.length + 100 ∧ r.wk = 0 := by
  have hNpos : 0 < N := hT.1
  have hlenV := hT.2.1
  have hN31 : N < 2147483648 := by omega
  have hl31 : l0 < 2147483648 := by omega
  have hr31 : r0 < 2147483648 := by omega
  -- the four declarations
  have lit : ∀ cl : List Cell, vdenM mv (VO V) (penvN mv.nv (gS P cl)) (.literal s64 EMIN) = some EMIN := by
    intro cl; rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos emin_valid]
  have d1 := gSM_decl mv P [ci n, ci N, ci h, ci l0, ci r0] (VO V) s64 (.literal s64 EMIN) EMIN EMIN (lit _)
    (conv_signed s64 rfl rfl _ emin_valid)
  have a1 := (pexecM_prim mv fu (.declare s64 true (.literal s64 EMIN)) _ _).trans d1
  have d2 := gSM_decl mv P [ci n, ci N, ci h, ci l0, ci r0, cs EMIN] (VO V) s64 (vS mv.nv 5) EMIN EMIN
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 5 EMIN rfl emin_valid) (conv_signed s64 rfl rfl _ emin_valid)
  have a2 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 5)) _ _).trans d2
  have d3 := gSM_decl mv P [ci n, ci N, ci h, ci l0, ci r0, cs EMIN, cs EMIN] (VO V) s64 (.literal s64 EMIN) EMIN EMIN (lit _)
    (conv_signed s64 rfl rfl _ emin_valid)
  have a3 := (pexecM_prim mv fu (.declare s64 true (.literal s64 EMIN)) _ _).trans d3
  have d4 := gSM_decl mv P [ci n, ci N, ci h, ci l0, ci r0, cs EMIN, cs EMIN, cs EMIN] (VO V) s64 (vS mv.nv 7) EMIN EMIN
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 7 EMIN rfl emin_valid) (conv_signed s64 rfl rfl _ emin_valid)
  have a4 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 7)) _ _).trans d4
  -- l += n_node; r += n_node
  have eN := envs mv P (LP n N h l0 r0 EMIN EMIN) 1 (ci N) rfl (i32v N hN31)
  have eN' : penvN mv.nv (gS P (LP n N h l0 r0 EMIN EMIN)) (mv.nv + 1) i32 = some (N : Int) := eN
  have eL : penvN mv.nv (gS P (LP n N h l0 r0 EMIN EMIN)) (mv.nv + 3) i32 = some (l0 : Int) :=
    envs mv P (LP n N h l0 r0 EMIN EMIN) 3 (ci l0) rfl (i32v l0 hl31)
  have vA : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h l0 r0 EMIN EMIN)))
      (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1))) = some ((l0 + N : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eL, Option.bind_some, den_variable, eN', Option.bind_some]
    have : binaryValue .add (l0 : Int) (N : Int) = ((l0 + N : Nat) : Int) := by
      show (l0 : Int) + (N : Int) = _; push_cast; rfl
    rw [this]; exact conv_signed i32 rfl rfl _ (i32v _ (by show l0 + N < 2147483648; omega))
  have s5 := gSM_assign mv P (LP n N h l0 r0 EMIN EMIN) (VO V) 3 (by simp) i32 _ _ _ vA (ci l0) rfl rfl (i32v l0 hl31)
    (conv_signed i32 rfl rfl _ (i32v _ (by show l0 + N < 2147483648; omega)))
  have eS5 : (LP n N h l0 r0 EMIN EMIN).set 3 ⟨i32, ((l0 + N : Nat) : Int)⟩ = LP n N h (l0 + N) r0 EMIN EMIN := rfl
  rw [eS5] at s5
  have a5 := (pexecM_prim mv fu (.assign (mv.nv + 3) i32 (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1)))) _ _).trans s5
  have eR : penvN mv.nv (gS P (LP n N h (l0 + N) r0 EMIN EMIN)) (mv.nv + 4) i32 = some (r0 : Int) :=
    envs mv P (LP n N h (l0 + N) r0 EMIN EMIN) 4 (ci r0) rfl (i32v r0 hr31)
  have eN2 : penvN mv.nv (gS P (LP n N h (l0 + N) r0 EMIN EMIN)) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P (LP n N h (l0 + N) r0 EMIN EMIN) 1 (ci N) rfl (i32v N hN31)
  have vB : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h (l0 + N) r0 EMIN EMIN)))
      (.binary i32 .add (.variable i32 (mv.nv + 4)) (.variable i32 (mv.nv + 1))) = some ((r0 + N : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eR, Option.bind_some, den_variable, eN2, Option.bind_some]
    have : binaryValue .add (r0 : Int) (N : Int) = ((r0 + N : Nat) : Int) := by
      show (r0 : Int) + (N : Int) = _; push_cast; rfl
    rw [this]; exact conv_signed i32 rfl rfl _ (i32v _ (by show r0 + N < 2147483648; omega))
  have s6 := gSM_assign mv P (LP n N h (l0 + N) r0 EMIN EMIN) (VO V) 4 (by simp) i32 _ _ _ vB (ci r0) rfl rfl (i32v r0 hr31)
    (conv_signed i32 rfl rfl _ (i32v _ (by show r0 + N < 2147483648; omega)))
  have eS6 : (LP n N h (l0 + N) r0 EMIN EMIN).set 4 ⟨i32, ((r0 + N : Nat) : Int)⟩ = LP n N h (l0 + N) (r0 + N) EMIN EMIN := rfl
  rw [eS6] at s6
  have a6 := (pexecM_prim mv fu (.assign (mv.nv + 4) i32 (.binary i32 .add (.variable i32 (mv.nv + 4)) (.variable i32 (mv.nv + 1)))) _ _).trans s6
  -- the loop
  set T := rfold maxMon V (l0 + N) (r0 - l0) with hTdef
  have vT : s64.valid T = true := rfold_V maxMon V hV (r0 - l0) (l0 + N) (by omega)
  have hI0 : PInv maxMon V N T (l0 + N) (r0 + N) EMIN EMIN := by
    refine ⟨by omega, by omega, by omega, emin_valid, emin_valid, ?_⟩
    have e : r0 + N - (l0 + N) = r0 - l0 := by omega
    rw [e]
    show maxMon.op (maxMon.op maxMon.e T) maxMon.e = T
    rw [maxMon.lid _ vT, maxMon.rid _ vT]
  have hls : lsteps (r0 - l0) ≤ Nat.log2 (r0 - l0) + 1 := by unfold lsteps; split <;> omega
  obtain ⟨rL, lF, rF, leftF, rightF, hL, retL, psL, vvL, hIF, hex, cL, nL, wL⟩ :=
    prod_loop mv hnv ty0 P V n N h T hn hN31 hh hV hT hN2 (r0 - l0) (l0 + N) (r0 + N) EMIN EMIN fu (by omega) hI0 (by omega)
  have hexit := PInv_exit maxMon V N T lF rF leftF rightF hIF hex
  obtain ⟨_, _, _, vLF, vRF, _⟩ := hIF
  -- the final apply
  have hX : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h lF rF leftF rightF))) (vS mv.nv 6) = some leftF := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 6 leftF rfl vLF
  have hY : vdenM mv (VO V) (penvN mv.nv (gS P (LP n N h lF rF leftF rightF ++ [cs leftF]))) (vS mv.nv 8) = some rightF := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 8 rightF rfl vRF
  have vm : s64.valid (mx leftF rightF) = true := by unfold mx; split <;> assumption
  obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ : ∃ r2 : PRM,
      pexecM mv fu (.sequence (.primitive (.ret (vS mv.nv 12))) Sk)
        (gS P (LP n N h lF rF leftF rightF ++ [cs leftF, cs rightF, cs (mx leftF rightF), cs (mx leftF rightF)])) (VO V) = some r2 ∧
      r2.ret = some (mx leftF rightF) ∧ r2.ps = gS P (LP n N h lF rF leftF rightF ++ [cs leftF, cs rightF, cs (mx leftF rightF), cs (mx leftF rightF)]) ∧
      r2.vv = VO V ∧ r2.cost ≤ 100 ∧ r2.need ≤ P.length + 60 ∧ r2.wk = 0 := by
    have rr := pstmtM_ret_ok mv (gS P (LP n N h lF rF leftF rightF ++ [cs leftF, cs rightF, cs (mx leftF rightF), cs (mx leftF rightF)]))
      (VO V) (vS mv.nv 12) (mx leftF rightF)
      (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 12 (mx leftF rightF) rfl vm)
    have e5 := seqM_ret (b := Sk) ((pexecM_prim mv fu (.ret (vS mv.nv 12)) _ _).trans rr) rfl
    refine ⟨_, e5, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P (VO V) fu (LP n N h lF rF leftF rightF) 9 rfl (vS mv.nv 6) (vS mv.nv 8)
    leftF rightF vLF vRF hX hY (.sequence (.primitive (.ret (vS mv.nv 12))) Sk) r2 hr2
  have s7 := seqM_some hL retL (by rw [psL, vvL]; exact hA)
  have s6 := seqM_some a6 rfl s7
  have s5 := seqM_some a5 rfl s6
  have s4 := seqM_some a4 rfl s5
  have s3 := seqM_some a3 rfl s4
  have s2 := seqM_some a2 rfl s3
  have s1 := seqM_some a1 rfl s2
  have hmx : mx leftF rightF = T := hexit
  refine ⟨_, s1, ?_, ?_, ⟨LP n N h lF rF leftF rightF ++ [cs leftF, cs rightF, cs (mx leftF rightF), cs (mx leftF rightF)], ?_⟩, ?_, ?_, ?_⟩
  · simp [retA, ret2, hmx]
  · simp [vvA, vv2]
  · exact psA.trans ps2
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL cA c2 ⊢; omega
  · have hA' := nA (P.length + 90) (by omega) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' nL n2 ⊢
    omega
  · simp [wA, w2, wL]

end Proofs.SegmentTreeProduct
