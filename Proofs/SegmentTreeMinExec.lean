import Proofs.InvGcdExec
import Proofs.SegTreeMath
import Proofs.Generated.SegmentTree

namespace Proofs.SegmentTreeMinExec
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
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den)

/-! ### The inlined `SegMax<long long>::apply(a, b)`: `a = X; b = Y; r = a; if (a < b) { r = b; } ret = r;`

The cells of the block are `a`, `b`, `r`, `ret` at the positions `k .. k + 3` (slots `nv + k ..`). -/

abbrev AppBlk (nv k : Nat) (X Y : NExpr) (REST : Command) : Command :=
  .sequence (.primitive (.declare s64 true X)) (.sequence (.primitive (.declare s64 true Y))
    (.sequence (.primitive (.declare s64 true (vS nv k)))
      (.sequence (.branch (.binary bT .lt (vS nv (k + 1)) (vS nv k))
          (.sequence (.scope (.sequence (.primitive (.assign (nv + k + 2) s64 (vS nv (k + 1)))) Sk)) Sk) Sk)
        (.sequence (.primitive (.declare s64 true (vS nv (k + 2)))) REST))))

/-- The value of `apply`: the maximum, written as the C++ does. -/
def mn (x y : Int) : Int := if y < x then y else x

theorem lt_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (k : Nat) (x y : Int)
    (hx : cl[k]? = some (cs x)) (hy : cl[k + 1]? = some (cs y)) (vx : s64.valid x = true) (vy : s64.valid y = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .lt (vS mv.nv (k + 1)) (vS mv.nv k)) = some (if y < x then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, vr mv P cl (k + 1) y hy vy, Option.bind_some, vr mv P cl k x hx vx,
    Option.bind_some]
  by_cases h : y < x
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 16000000 in
theorem appblk_exec (mv : MV) (P : List Cell) (vv : Nat → List Int) (fu : Nat) (cl : List Cell) (k : Nat) (hk : cl.length = k)
    (X Y : NExpr) (x y : Int) (vx : s64.valid x = true) (vy : s64.valid y = true)
    (hX : vdenM mv vv (penvN mv.nv (gS P cl)) X = some x)
    (hY : vdenM mv vv (penvN mv.nv (gS P (cl ++ [cs x]))) Y = some y)
    (REST : Command) (r2 : PRM)
    (hr : pexecM mv fu REST (gS P (cl ++ [cs x, cs y, cs (mn x y), cs (mn x y)])) vv = some r2) :
    ∃ r : PRM, pexecM mv fu (AppBlk mv.nv k X Y REST) (gS P cl) vv = some r ∧ r.ret = r2.ret ∧ r.ps = r2.ps ∧ r.vv = r2.vv ∧
      r.cost ≤ r2.cost + (vwp X).1 + (vwp Y).1 + 40 ∧
      (∀ N : Nat, r2.need ≤ N → P.length + 2 * k + (vwp X).2 + (vwp Y).2 + 30 ≤ N → r.need ≤ N) ∧ r.wk = r2.wk := by
  have g0 : ∀ ys : List Cell, (cl ++ ys)[k]? = ys[0]? := by
    intro ys; rw [List.getElem?_append_right (by omega)]; simp [hk]
  have g1 : ∀ ys : List Cell, (cl ++ ys)[k + 1]? = ys[1]? := by
    intro ys; rw [List.getElem?_append_right (by omega)]; simp [hk]
  have g2 : ∀ ys : List Cell, (cl ++ ys)[k + 2]? = ys[2]? := by
    intro ys; rw [List.getElem?_append_right (by omega)]; simp [hk]
  have d1 := gSM_decl mv P cl vv s64 X x x hX (conv_signed s64 rfl rfl _ vx)
  have a1 := (pexecM_prim mv fu (.declare s64 true X) _ _).trans d1
  have d2 := gSM_decl mv P (cl ++ [cs x]) vv s64 Y y y hY (conv_signed s64 rfl rfl _ vy)
  have e2 : cl ++ [cs x] ++ [(⟨s64, y⟩ : Cell)] = cl ++ [cs x, cs y] := by simp
  rw [e2] at d2
  have a2 := (pexecM_prim mv fu (.declare s64 true Y) _ _).trans d2
  have d3 := gSM_decl mv P (cl ++ [cs x, cs y]) vv s64 (vS mv.nv k) x x
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ k x (by rw [g0]; rfl) vx) (conv_signed s64 rfl rfl _ vx)
  have e3 : cl ++ [cs x, cs y] ++ [(⟨s64, x⟩ : Cell)] = cl ++ [cs x, cs y, cs x] := by simp
  rw [e3] at d3
  have a3 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv k)) _ _).trans d3
  -- the branch
  have hc := lt_val mv P vv (cl ++ [cs x, cs y, cs x]) k x y (by rw [g0]; rfl) (by rw [g1]; rfl) vx vy
  obtain ⟨r3, h3, ret3, ps3, vv3, c3, n3, w3⟩ : ∃ r3 : PRM,
      pexecM mv fu (.branch (.binary bT .lt (vS mv.nv (k + 1)) (vS mv.nv k))
          (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + k + 2) s64 (vS mv.nv (k + 1)))) Sk)) Sk) Sk)
        (gS P (cl ++ [cs x, cs y, cs x])) vv = some r3 ∧ r3.ret = none ∧
      r3.ps = gS P (cl ++ [cs x, cs y, cs (mn x y)]) ∧ r3.vv = vv ∧ r3.cost ≤ 30 + (vwp (.binary bT .lt (vS mv.nv (k + 1)) (vS mv.nv k))).1 ∧
      r3.need ≤ P.length + 2 * k + 2 * 3 + 20 + (vwp (.binary bT .lt (vS mv.nv (k + 1)) (vS mv.nv k))).2 ∧ r3.wk = 0 := by
    by_cases h : y < x
    · rw [if_pos h] at hc
      have st := gSM_assign mv P (cl ++ [cs x, cs y, cs x]) vv (k + 2) (by simp [hk]) s64 (vS mv.nv (k + 1)) y y
        (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ (k + 1) y (by rw [g1]; rfl) vy) (cs x)
        (by rw [g2]; rfl) rfl vx (conv_signed s64 rfl rfl _ vy)
      have e : (cl ++ [cs x, cs y, cs x]).set (k + 2) ⟨s64, y⟩ = cl ++ [cs x, cs y, cs y] := by
        rw [← hk]; simp [List.set_append_right]
      rw [e] at st
      have b1 := (pexecM_prim mv fu (.assign (mv.nv + k + 2) s64 (vS mv.nv (k + 1))) _ _).trans st
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      have b3 := pexecM_scope mv fu _ _ _ _ b2
      have tk := Proofs.PexecKit.scope_take (gS P (cl ++ [cs x, cs y, cs x])) (gS P (cl ++ [cs x, cs y, cs y]))
        (by simp [gS_mem_len]) (by simp [gS_bs_len])
      simp only [tk] at b3
      have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
      have b5 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b4
      refine ⟨_, b5, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · simp [mn, h]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; try omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]; try omega
      · simp
    · rw [if_neg h] at hc
      have b5 := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + k + 2) s64
        (vS mv.nv (k + 1)))) Sk)) Sk) Sk _ _ hc _ (pexecM_skip mv fu _ _)
      refine ⟨_, b5, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · simp [mn, h]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]; omega
      · simp
  -- the result
  have vm : s64.valid (mn x y) = true := by unfold mn; split <;> assumption
  have d5 := gSM_decl mv P (cl ++ [cs x, cs y, cs (mn x y)]) vv s64 (vS mv.nv (k + 2)) (mn x y) (mn x y)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ (k + 2) (mn x y) (by rw [g2]; rfl) vm) (conv_signed s64 rfl rfl _ vm)
  have e4 : cl ++ [cs x, cs y, cs (mn x y)] ++ [(⟨s64, mn x y⟩ : Cell)] = cl ++ [cs x, cs y, cs (mn x y), cs (mn x y)] := by simp
  rw [e4] at d5
  have a5 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv (k + 2))) _ _).trans d5
  have s5 := seqM_some (r2 := r2) (b := REST) a5 rfl hr
  have s4 := seqM_some h3 ret3 (by rw [ps3, vv3]; exact s5)
  have s3 := seqM_some a3 rfl (by exact s4)
  have s2 := seqM_some a2 rfl (by exact s3)
  have s1 := seqM_some a1 rfl (by exact s2)
  refine ⟨_, s1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c3 ⊢; omega
  · intro N hN hB
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n3 ⊢
    subst hk
    omega
  · simp [w3]

/-! ### The index expressions `i * 2` and `i * 2 + 1` (the variable first) -/

abbrev ix2 (slot : Nat) : NExpr := .cast u64 (.binary i32 .mul (.variable i32 slot) (.literal i32 2))
abbrev ix21 (slot : Nat) : NExpr :=
  .cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 slot) (.literal i32 2)) (.literal i32 1))

theorem ix2_den (env : Nat → Ty → Option Int) (slot t : Nat) (h : env slot i32 = some (t : Int)) (ht : 2 * t < 2147483648) :
    (ix2 slot).denote env = some ((2 * t : Nat) : Int) := by
  rw [den_cast, den_binary, den_variable, h, Option.bind_some, den_literal, if_pos (show i32.valid 2 = true from rfl),
    Option.bind_some]
  have e : binaryValue .mul (t : Int) 2 = ((2 * t : Nat) : Int) := by
    show (t : Int) * 2 = _; push_cast; ring
  rw [e, conv_signed i32 rfl rfl _ (i32v _ (by show 2 * t < 2147483648; omega)), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)

theorem ix21_den (env : Nat → Ty → Option Int) (slot t : Nat) (h : env slot i32 = some (t : Int)) (ht : 2 * t + 1 < 2147483648) :
    (ix21 slot).denote env = some ((2 * t + 1 : Nat) : Int) := by
  rw [den_cast, den_binary, den_binary, den_variable, h, Option.bind_some, den_literal,
    if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
  have e : binaryValue .mul (t : Int) 2 = ((2 * t : Nat) : Int) := by
    show (t : Int) * 2 = _; push_cast; ring
  rw [e, conv_signed i32 rfl rfl _ (i32v _ (by show 2 * t < 2147483648; omega)), Option.bind_some, den_literal,
    if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have e2 : binaryValue .add ((2 * t : Nat) : Int) 1 = ((2 * t + 1 : Nat) : Int) := by
    show ((2 * t : Nat) : Int) + 1 = _; push_cast; ring
  rw [e2, conv_signed i32 rfl rfl _ (i32v _ (by show 2 * t + 1 < 2147483648; omega)), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)

/-- The inlined `update(i)`: copies of the four arguments (the cells `j0 .. j3`), then `node[i] = apply(node[2i], node[2i+1])`.
`c` is the number of cells before the block; `i` is the fourth copy (the cell `c + 3`). -/
abbrev UpdBlk (nv c j0 j1 j2 j3 : Nat) (REST : Command) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 (nv + j0))))
    (.sequence (.primitive (.declare i32 true (.variable i32 (nv + j1))))
      (.sequence (.primitive (.declare i32 true (.variable i32 (nv + j2))))
        (.sequence (.primitive (.declare i32 true (.variable i32 (nv + j3))))
          (AppBlk nv (c + 4) (.read s64 (.local 0) (ix2 (nv + c + 3))) (.read s64 (.local 0) (ix21 (nv + c + 3)))
            (.sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (nv + c + 3))) (vS nv (c + 4 + 3)))) REST)))))

abbrev ci4 (a b c d : Nat) : List Cell := [ci a, ci b, ci c, ci d]

set_option maxHeartbeats 16000000 in
theorem upd_exec (mv : MV) (hmv0 : 0 < mv.nv) (ty0 : mv.ty 0 = s64) (P : List Cell) (vv : Nat → List Int) (fu : Nat)
    (cl : List Cell) (c : Nat) (hc : cl.length = c) (j0 j1 j2 j3 : Nat) (v0 v1 v2 i : Nat)
    (hj0 : cl[j0]? = some (ci v0)) (hj1 : cl[j1]? = some (ci v1)) (hj2 : cl[j2]? = some (ci v2)) (hj3 : cl[j3]? = some (ci i))
    (hv0 : v0 < 2147483648) (hv1 : v1 < 2147483648) (hv2 : v2 < 2147483648) (hi : 2 * i + 1 < 2147483648)
    (hlt : 2 * i + 1 < (vv 0).length)
    (vx : s64.valid ((vv 0).getD (2 * i) 0) = true) (vy : s64.valid ((vv 0).getD (2 * i + 1) 0) = true)
    (REST : Command) (r2 : PRM)
    (hr : pexecM mv fu REST (gS P (cl ++ [ci v0, ci v1, ci v2, ci i, cs ((vv 0).getD (2 * i) 0), cs ((vv 0).getD (2 * i + 1) 0),
      cs (mn ((vv 0).getD (2 * i) 0) ((vv 0).getD (2 * i + 1) 0)), cs (mn ((vv 0).getD (2 * i) 0) ((vv 0).getD (2 * i + 1) 0))]))
      (upd vv 0 ((vv 0).set i (mn ((vv 0).getD (2 * i) 0) ((vv 0).getD (2 * i + 1) 0)))) = some r2) :
    ∃ r : PRM, pexecM mv fu (UpdBlk mv.nv c j0 j1 j2 j3 REST) (gS P cl) vv = some r ∧ r.ret = r2.ret ∧ r.ps = r2.ps ∧ r.vv = r2.vv ∧
      r.cost ≤ r2.cost + 300 ∧ (∀ N : Nat, r2.need ≤ N → P.length + 2 * c + 75 ≤ N → r.need ≤ N) ∧ r.wk = r2.wk + 1 := by
  have lj0 : j0 < cl.length := (List.getElem?_eq_some_iff.mp hj0).1
  have lj1 : j1 < cl.length := (List.getElem?_eq_some_iff.mp hj1).1
  have lj2 : j2 < cl.length := (List.getElem?_eq_some_iff.mp hj2).1
  have lj3 : j3 < cl.length := (List.getElem?_eq_some_iff.mp hj3).1
  have gA : ∀ (ys : List Cell) (j : Nat), j < cl.length → (cl ++ ys)[j]? = cl[j]? := fun ys j hj => List.getElem?_append_left hj
  -- the four copies
  have E0 := envs mv P cl j0 (ci v0) hj0 (i32v v0 hv0)
  have d0 := gSM_decl mv P cl vv i32 (.variable i32 (mv.nv + j0)) (v0 : Int) (v0 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E0) (conv_signed i32 rfl rfl _ (i32v v0 hv0))
  have a0 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j0))) _ _).trans d0
  have E1 := envs mv P (cl ++ [ci v0]) j1 (ci v1) (by rw [gA _ _ lj1]; exact hj1) (i32v v1 hv1)
  have d1 := gSM_decl mv P (cl ++ [ci v0]) vv i32 (.variable i32 (mv.nv + j1)) (v1 : Int) (v1 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1) (conv_signed i32 rfl rfl _ (i32v v1 hv1))
  have e1 : cl ++ [ci v0] ++ [(⟨i32, (v1 : Int)⟩ : Cell)] = cl ++ [ci v0, ci v1] := by simp
  rw [e1] at d1
  have a1 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j1))) _ _).trans d1
  have E2 := envs mv P (cl ++ [ci v0, ci v1]) j2 (ci v2) (by rw [gA _ _ lj2]; exact hj2) (i32v v2 hv2)
  have d2 := gSM_decl mv P (cl ++ [ci v0, ci v1]) vv i32 (.variable i32 (mv.nv + j2)) (v2 : Int) (v2 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2) (conv_signed i32 rfl rfl _ (i32v v2 hv2))
  have e2 : cl ++ [ci v0, ci v1] ++ [(⟨i32, (v2 : Int)⟩ : Cell)] = cl ++ [ci v0, ci v1, ci v2] := by simp
  rw [e2] at d2
  have a2 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j2))) _ _).trans d2
  have hiM : i < 2147483648 := by omega
  have E3 := envs mv P (cl ++ [ci v0, ci v1, ci v2]) j3 (ci i) (by rw [gA _ _ lj3]; exact hj3) (i32v i hiM)
  have d3 := gSM_decl mv P (cl ++ [ci v0, ci v1, ci v2]) vv i32 (.variable i32 (mv.nv + j3)) (i : Int) (i : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3) (conv_signed i32 rfl rfl _ (i32v i hiM))
  have e3 : cl ++ [ci v0, ci v1, ci v2] ++ [(⟨i32, (i : Int)⟩ : Cell)] = cl ++ [ci v0, ci v1, ci v2, ci i] := by simp
  rw [e3] at d3
  have a3 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j3))) _ _).trans d3
  -- the reads of the children
  set x := (vv 0).getD (2 * i) 0 with hxdef
  set y := (vv 0).getD (2 * i + 1) 0 with hydef
  have cell_i : ∀ ys : List Cell, (cl ++ [ci v0, ci v1, ci v2, ci i] ++ ys)[c + 3]? = some (ci i) := by
    intro ys
    rw [List.getElem?_append_left (by simp [hc])]
    rw [List.getElem?_append_right (by omega)]
    simp [hc]
  have Ei : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i] ++ ys)) (mv.nv + c + 3) i32 = some (i : Int) :=
    fun ys => envs mv P _ (c + 3) (ci i) (cell_i ys) (i32v i hiM)
  have hX : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i]))) (.read s64 (.local 0) (ix2 (mv.nv + c + 3))) = some x := by
    have := Ei []
    rw [List.append_nil] at this
    exact rdM_val mv vv _ 0 hmv0 s64 ty0.symm (ix2 (mv.nv + c + 3)) rfl rfl (2 * i)
      (ix2_den _ _ i this (by omega)) x (vec_getI (vv 0) (2 * i) (by omega)) (by rw [ty0]; exact vx)
  have hY : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i] ++ [cs x]))) (.read s64 (.local 0) (ix21 (mv.nv + c + 3))) = some y :=
    rdM_val mv vv _ 0 hmv0 s64 ty0.symm (ix21 (mv.nv + c + 3)) rfl rfl (2 * i + 1)
      (ix21_den _ _ i (Ei [cs x]) hi) y (vec_getI (vv 0) (2 * i + 1) hlt) (by rw [ty0]; exact vy)
  -- the write
  have vm : s64.valid (mn x y) = true := by unfold mn; split <;> assumption
  have cell8 : (cl ++ [ci v0, ci v1, ci v2, ci i] ++ [cs x, cs y, cs (mn x y), cs (mn x y)]) = cl ++ [ci v0, ci v1, ci v2, ci i, cs x, cs y, cs (mn x y), cs (mn x y)] := by simp
  have Ei8 : penvN mv.nv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i] ++ [cs x, cs y, cs (mn x y), cs (mn x y)])) (mv.nv + c + 3) i32 = some (i : Int) :=
    Ei [cs x, cs y, cs (mn x y), cs (mn x y)]
  have hw := pstmtM_write_ok mv (gS P (cl ++ [ci v0, ci v1, ci v2, ci i] ++ [cs x, cs y, cs (mn x y), cs (mn x y)])) vv 0 hmv0
    (.cast u64 (.variable i32 (mv.nv + c + 3))) (vS mv.nv (c + 4 + 3)) (mn x y) i
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ (c + 4 + 3) (mn x y) (by
        rw [List.getElem?_append_right (by simp [hc])]; simp [hc]) vm)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ _ i Ei8 hiM) (by omega) (by rw [ty0]; exact vm)
  rw [ty0] at hw
  have aw := (pexecM_prim mv fu (.write (.local 0) s64 (.cast u64 (.variable i32 (mv.nv + c + 3))) (vS mv.nv (c + 4 + 3))) _ _).trans hw
  rw [cell8] at aw
  have sw := seqM_some (r2 := r2) (b := REST) aw rfl hr
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P vv fu (cl ++ [ci v0, ci v1, ci v2, ci i]) (c + 4) (by simp [hc])
    (.read s64 (.local 0) (ix2 (mv.nv + c + 3))) (.read s64 (.local 0) (ix21 (mv.nv + c + 3))) x y vx vy hX hY
    (.sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (mv.nv + c + 3))) (vS mv.nv (c + 4 + 3)))) REST) _
    (by rw [cell8]; exact sw)
  have s3 := seqM_some a3 rfl hA
  have s2 := seqM_some a2 rfl s3
  have s1 := seqM_some a1 rfl s2
  have s0 := seqM_some a0 rfl s1
  refine ⟨_, s0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using retA
  · simpa using psA
  · simpa using vvA
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA ⊢; omega
  · intro N hN hB
    have hA' := nA N
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' ⊢
    exact ⟨by omega, hA' (by omega) hN (by omega)⟩
  · simp at wA ⊢
    omega

theorem s64_bounds (x : Int) (h : s64.valid x = true) : -9223372036854775808 ≤ x ∧ x < 9223372036854775808 := by
  simp [Ty.valid, s64] at h
  omega

/-- The monoid of the model: `long long` with the maximum and the smallest value as identity. -/
def minMon : Proofs.SegTreeMath.Mon where
  V := fun x => s64.valid x = true
  op := mn
  e := 9223372036854775807
  closed := by
    intro a b ha hb
    unfold mn
    split <;> assumption
  he := by decide
  assoc := by
    intro a b c ha hb hc
    unfold mn
    split_ifs <;> omega
  lid := by
    intro a ha
    have := s64_bounds a ha
    unfold mn
    split_ifs <;> omega
  rid := by
    intro a ha
    have := s64_bounds a ha
    unfold mn
    split_ifs <;> omega

end Proofs.SegmentTreeMinExec
