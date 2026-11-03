import Proofs.LazySegChmin
import Proofs.SquareMatrixId

namespace Proofs.LazySegBlocks
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
open Proofs.SegmentTreeExec (lt_val)
open Proofs.LazySegChmin (mi)
open Proofs.SquareMatrixId (lt_cells)

/-! ### The inlined `LazyChminMax::mapping(f, x)` and `composition(f, g)`: `a = X; b = Y; r = b; if (a < b) { r = a; } ret = r;` -/

abbrev MinBlk (nv k : Nat) (X Y : NExpr) (REST : Command) : Command :=
  .sequence (.primitive (.declare s64 true X)) (.sequence (.primitive (.declare s64 true Y))
    (.sequence (.primitive (.declare s64 true (vS nv (k + 1))))
      (.sequence (.branch (.binary bT .lt (vS nv k) (vS nv (k + 1)))
          (.sequence (.scope (.sequence (.primitive (.assign (nv + k + 2) s64 (vS nv k))) Sk)) Sk) Sk)
        (.sequence (.primitive (.declare s64 true (vS nv (k + 2)))) REST))))

set_option maxHeartbeats 16000000 in
theorem minblk_exec (mv : MV) (P : List Cell) (vv : Nat → List Int) (fu : Nat) (cl : List Cell) (k : Nat) (hk : cl.length = k)
    (X Y : NExpr) (x y : Int) (vx : s64.valid x = true) (vy : s64.valid y = true)
    (hX : vdenM mv vv (penvN mv.nv (gS P cl)) X = some x)
    (hY : vdenM mv vv (penvN mv.nv (gS P (cl ++ [cs x]))) Y = some y)
    (REST : Command) (r2 : PRM)
    (hr : pexecM mv fu REST (gS P (cl ++ [cs x, cs y, cs (mi x y), cs (mi x y)])) vv = some r2) :
    ∃ r : PRM, pexecM mv fu (MinBlk mv.nv k X Y REST) (gS P cl) vv = some r ∧ r.ret = r2.ret ∧ r.ps = r2.ps ∧ r.vv = r2.vv ∧
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
  have d3 := gSM_decl mv P (cl ++ [cs x, cs y]) vv s64 (vS mv.nv (k + 1)) y y
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ (k + 1) y (by rw [g1]; rfl) vy) (conv_signed s64 rfl rfl _ vy)
  have e3 : cl ++ [cs x, cs y] ++ [(⟨s64, y⟩ : Cell)] = cl ++ [cs x, cs y, cs y] := by simp
  rw [e3] at d3
  have a3 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv (k + 1))) _ _).trans d3
  -- the branch
  have hc := lt_val mv P vv (cl ++ [cs x, cs y, cs y]) k x y (by rw [g0]; rfl) (by rw [g1]; rfl) vx vy
  obtain ⟨r3, h3, ret3, ps3, vv3, c3, n3, w3⟩ : ∃ r3 : PRM,
      pexecM mv fu (.branch (.binary bT .lt (vS mv.nv k) (vS mv.nv (k + 1)))
          (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + k + 2) s64 (vS mv.nv k))) Sk)) Sk) Sk)
        (gS P (cl ++ [cs x, cs y, cs y])) vv = some r3 ∧ r3.ret = none ∧
      r3.ps = gS P (cl ++ [cs x, cs y, cs (mi x y)]) ∧ r3.vv = vv ∧ r3.cost ≤ 30 + (vwp (.binary bT .lt (vS mv.nv k) (vS mv.nv (k + 1)))).1 ∧
      r3.need ≤ P.length + 2 * k + 2 * 3 + 20 + (vwp (.binary bT .lt (vS mv.nv k) (vS mv.nv (k + 1)))).2 ∧ r3.wk = 0 := by
    by_cases h : x < y
    · rw [if_pos h] at hc
      have st := gSM_assign mv P (cl ++ [cs x, cs y, cs y]) vv (k + 2) (by simp [hk]) s64 (vS mv.nv k) x x
        (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ k x (by rw [g0]; rfl) vx) (cs y)
        (by rw [g2]; rfl) rfl vy (conv_signed s64 rfl rfl _ vx)
      have e : (cl ++ [cs x, cs y, cs y]).set (k + 2) ⟨s64, x⟩ = cl ++ [cs x, cs y, cs x] := by
        rw [← hk]; simp [List.set_append_right]
      rw [e] at st
      have b1 := (pexecM_prim mv fu (.assign (mv.nv + k + 2) s64 (vS mv.nv k)) _ _).trans st
      have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
      have b3 := pexecM_scope mv fu _ _ _ _ b2
      have tk := Proofs.PexecKit.scope_take (gS P (cl ++ [cs x, cs y, cs y])) (gS P (cl ++ [cs x, cs y, cs x]))
        (by simp [gS_mem_len]) (by simp [gS_bs_len])
      simp only [tk] at b3
      have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
      have b5 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b4
      refine ⟨_, b5, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · simp [mi, h]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; try omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]; try omega
      · simp
    · rw [if_neg h] at hc
      have b5 := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + k + 2) s64
        (vS mv.nv k))) Sk)) Sk) Sk _ _ hc _ (pexecM_skip mv fu _ _)
      refine ⟨_, b5, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · simp [mi, h]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]; omega
      · simp
  -- the result
  have vm : s64.valid (mi x y) = true := by unfold mi; split <;> assumption
  have d5 := gSM_decl mv P (cl ++ [cs x, cs y, cs (mi x y)]) vv s64 (vS mv.nv (k + 2)) (mi x y) (mi x y)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ (k + 2) (mi x y) (by rw [g2]; rfl) vm) (conv_signed s64 rfl rfl _ vm)
  have e4 : cl ++ [cs x, cs y, cs (mi x y)] ++ [(⟨s64, mi x y⟩ : Cell)] = cl ++ [cs x, cs y, cs (mi x y), cs (mi x y)] := by simp
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


/-! ### The inlined `all_apply(k, f)`: `node[k] = mapping(f, node[k]); if (k < n_node) lazy[k] = composition(f, lazy[k]);`

The five parameter cells are `c .. c + 4`: `n`, `n_node`, `h_node`, `k`, `f` (variables `nv + c ..`). -/

abbrev ixk (nv j : Nat) : NExpr := .cast u64 (.variable i32 (nv + j))

abbrev AAIn (nv c : Nat) (R : Command) : Command :=
  .sequence (.branch (.binary bT .lt (.variable i32 (nv + c + 3)) (.variable i32 (nv + c + 1)))
    (.sequence (.scope (MinBlk nv (c + 9) (vS nv (c + 4)) (.read s64 (.local 1) (ixk nv (c + 3)))
      (.sequence (.primitive (.write (.local 1) s64 (ixk nv (c + 3)) (vS nv (c + 9 + 3)))) Sk))) Sk) Sk) R

abbrev AABody (nv c : Nat) (REST : Command) : Command :=
  MinBlk nv (c + 5) (vS nv (c + 4)) (.read s64 (.local 0) (ixk nv (c + 3)))
    (.sequence (.primitive (.write (.local 0) s64 (ixk nv (c + 3)) (vS nv (c + 5 + 3)))) (AAIn nv c REST))

/-- The vectors after `all_apply(k, f)`: `node[k] = mi f node[k]`, and `lazy[k] = mi f lazy[k]` if `k < n_node`. -/
def aaVV (vv : Nat → List Int) (nn k : Nat) (f : Int) : Nat → List Int :=
  if k < nn then upd (upd vv 0 ((vv 0).set k (mi f ((vv 0).getD k 0)))) 1 ((vv 1).set k (mi f ((vv 1).getD k 0)))
  else upd vv 0 ((vv 0).set k (mi f ((vv 0).getD k 0)))

set_option maxHeartbeats 32000000 in
theorem aabody_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (fu : Nat) (cl : List Cell) (c : Nat) (hc : cl.length = c + 5) (nn k : Nat) (f : Int)
    (hn : cl[c + 1]? = some (ci nn)) (hk : cl[c + 3]? = some (ci k)) (hf : cl[c + 4]? = some (cs f))
    (hnn : nn < 2147483648) (hk31 : k < 2147483648) (vf : s64.valid f = true)
    (hlt0 : k < (vv 0).length) (vx : s64.valid ((vv 0).getD k 0) = true)
    (hlt1 : k < nn → k < (vv 1).length ∧ s64.valid ((vv 1).getD k 0) = true)
    (REST : Command) (r2 : PRM)
    (hr : pexecM mv fu REST (gS P (cl ++ [cs f, cs ((vv 0).getD k 0), cs (mi f ((vv 0).getD k 0)),
      cs (mi f ((vv 0).getD k 0))])) (aaVV vv nn k f) = some r2) :
    ∃ r : PRM, pexecM mv fu (AABody mv.nv c REST) (gS P cl) vv = some r ∧ r.ret = r2.ret ∧ r.ps = r2.ps ∧ r.vv = r2.vv ∧
      r.cost ≤ r2.cost + 400 ∧ (∀ N : Nat, r2.need ≤ N → P.length + 2 * c + 120 ≤ N → r.need ≤ N) ∧ r.wk ≤ r2.wk + 2 := by
  have gA : ∀ (ys : List Cell) (j : Nat), j < cl.length → (cl ++ ys)[j]? = cl[j]? := fun ys j hj => List.getElem?_append_left hj
  have Ek : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ ys)) (mv.nv + c + 3) i32 = some (k : Int) := fun ys =>
    envs mv P (cl ++ ys) (c + 3) (ci k) (by rw [gA ys _ (by omega)]; exact hk) (i32v k hk31)
  have vm : s64.valid (mi f ((vv 0).getD k 0)) = true := by unfold mi; split <;> assumption
  -- the first MinBlk: the continuation
  have cell4 : ∀ ys : List Cell, (cl ++ ys)[c + 4]? = some (cs f) ∨ True := fun _ => Or.inr trivial
  have hX : vdenM mv vv (penvN mv.nv (gS P cl)) (vS mv.nv (c + 4)) = some f := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P cl (c + 4) f hf vf
  have hY : vdenM mv vv (penvN mv.nv (gS P (cl ++ [cs f]))) (.read s64 (.local 0) (ixk mv.nv (c + 3))) = some ((vv 0).getD k 0) :=
    rdM_val mv vv _ 0 (by omega) s64 ty0.symm (ixk mv.nv (c + 3)) rfl rfl k (cidx_den _ _ k (Ek [cs f]) hk31)
      _ (vec_getI (vv 0) k hlt0) (by rw [ty0]; exact vx)
  -- the write of the node
  have hw := pstmtM_write_ok mv (gS P (cl ++ [cs f, cs ((vv 0).getD k 0), cs (mi f ((vv 0).getD k 0)), cs (mi f ((vv 0).getD k 0))]))
    vv 0 (by omega) (ixk mv.nv (c + 3)) (vS mv.nv (c + 5 + 3)) (mi f ((vv 0).getD k 0)) k
    (by rw [vdenM_scalar _ _ _ _ rfl]
        exact vr mv P _ (c + 5 + 3) _ (by rw [List.getElem?_append_right (by omega)]; simp [hc]) vm)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ _ k (Ek _) hk31) hlt0 (by rw [ty0]; exact vm)
  rw [ty0] at hw
  have aw := (pexecM_prim mv fu (.write (.local 0) s64 (ixk mv.nv (c + 3)) (vS mv.nv (c + 5 + 3))) _ _).trans hw
  -- the branch
  have hn' : ∀ ys : List Cell, (cl ++ ys)[c + 1]? = some (ci nn) := fun ys => by rw [gA ys _ (by omega)]; exact hn
  have hk' : ∀ ys : List Cell, (cl ++ ys)[c + 3]? = some (ci k) := fun ys => by rw [gA ys _ (by omega)]; exact hk
  have hcond := lt_cells mv P (upd vv 0 ((vv 0).set k (mi f ((vv 0).getD k 0))))
    (cl ++ [cs f, cs ((vv 0).getD k 0), cs (mi f ((vv 0).getD k 0)), cs (mi f ((vv 0).getD k 0))]) (c + 3) (c + 1) k nn
    (by simpa using hk' [cs f, cs ((vv 0).getD k 0), cs (mi f ((vv 0).getD k 0)), cs (mi f ((vv 0).getD k 0))])
    (by simpa using hn' [cs f, cs ((vv 0).getD k 0), cs (mi f ((vv 0).getD k 0)), cs (mi f ((vv 0).getD k 0))]) hk31 hnn
  set xv := (vv 0).getD k 0 with hxv
  set cl4 := cl ++ [cs f, cs xv, cs (mi f xv), cs (mi f xv)] with hcl4
  set vvW := upd vv 0 ((vv 0).set k (mi f xv)) with hvvW
  have hc4 : cl4.length = c + 9 := by simp [hcl4, hc]
  have Ek4 : ∀ ys : List Cell, penvN mv.nv (gS P (cl4 ++ ys)) (mv.nv + c + 3) i32 = some (k : Int) := fun ys => by
    rw [hcl4, List.append_assoc]; exact Ek _
  have hvv1 : vvW 1 = vv 1 := by simp [hvvW, upd]
  have cell4 : cl4[c + 4]? = some (cs f) := by
    rw [hcl4, List.getElem?_append_left (by omega)]; exact hf
  -- the continuation of the branch
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ : ∃ rA : PRM, pexecM mv fu (AAIn mv.nv c REST) (gS P cl4) vvW = some rA ∧
      rA.ret = r2.ret ∧ rA.ps = r2.ps ∧ rA.vv = r2.vv ∧ rA.cost ≤ r2.cost + 300 ∧
      (∀ N : Nat, r2.need ≤ N → P.length + 2 * c + 110 ≤ N → rA.need ≤ N) ∧ rA.wk ≤ r2.wk + 1 := by
    by_cases hkn : k < nn
    · -- the lazy tag is updated as well
      have hl1 := hlt1 hkn
      rw [if_pos hkn] at hcond
      set yv := (vv 1).getD k 0 with hyv
      have vm1 : s64.valid (mi f yv) = true := by unfold mi; split <;> [exact vf; exact hl1.2]
      have hXi : vdenM mv vvW (penvN mv.nv (gS P cl4)) (vS mv.nv (c + 4)) = some f := by
        rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P cl4 (c + 4) f cell4 vf
      have hYi : vdenM mv vvW (penvN mv.nv (gS P (cl4 ++ [cs f]))) (.read s64 (.local 1) (ixk mv.nv (c + 3))) = some yv :=
        rdM_val mv vvW _ 1 (by omega) s64 ty1.symm (ixk mv.nv (c + 3)) rfl rfl k (cidx_den _ _ k (Ek4 [cs f]) hk31)
          yv (by rw [hvv1]; exact vec_getI (vv 1) k hl1.1) (by rw [ty1]; exact hl1.2)
      have hwi := pstmtM_write_ok mv (gS P (cl4 ++ [cs f, cs yv, cs (mi f yv), cs (mi f yv)])) vvW 1 (by omega)
        (ixk mv.nv (c + 3)) (vS mv.nv (c + 9 + 3)) (mi f yv) k
        (by rw [vdenM_scalar _ _ _ _ rfl]
            exact vr mv P _ (c + 9 + 3) _ (by rw [List.getElem?_append_right (by omega)]; simp [hc4]) vm1)
        (by rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ _ k (Ek4 _) hk31) (by rw [hvv1]; exact hl1.1)
        (by rw [ty1]; exact vm1)
      rw [ty1] at hwi
      have awi := (pexecM_prim mv fu (.write (.local 1) s64 (ixk mv.nv (c + 3)) (vS mv.nv (c + 9 + 3))) _ _).trans hwi
      have swi := seqM_some awi rfl (pexecM_skip mv fu _ _)
      obtain ⟨rI, hI, retI, psI, vvI, cI, nI, wI⟩ := minblk_exec mv P vvW fu cl4 (c + 9) hc4 (vS mv.nv (c + 4))
        (.read s64 (.local 1) (ixk mv.nv (c + 3))) f yv vf hl1.2 hXi hYi _ _ swi
      have b3 := pexecM_scope mv fu _ _ _ _ hI
      have tk := gS_takeC P cl4 cl4 [cs f, cs yv, cs (mi f yv), cs (mi f yv)] rfl
      rw [psI] at b3
      simp only [tk] at b3
      have b4 := seqM_some b3 (by simpa using retI) (pexecM_skip mv fu _ _)
      have b5 := pexecM_branch_true mv fu _ _ Sk _ _ 1 (by rw [hcond]) (by decide) _ b4
      have hvvF : upd vvW 1 ((vvW 1).set k (mi f yv)) = aaVV vv nn k f := by
        unfold aaVV
        rw [if_pos hkn, hvv1]
      have hrr : pexecM mv fu REST (gS P cl4) rI.vv = some r2 := by
        rw [vvI]
        exact (hvvF.symm ▸ hr : pexecM mv fu REST (gS P cl4) (upd vvW 1 ((vvW 1).set k (mi f yv))) = some r2)
      have b6 := seqM_some b5 (by simpa using retI) hrr
      refine ⟨_, b6, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cI ⊢; omega
      · intro N hN hB
        simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nI ⊢
        exact ⟨by omega, nI N (by omega) (by omega) (by omega), by omega, hN⟩
      · simp at wI ⊢; omega
    · -- k >= n_node: no tag
      rw [if_neg hkn] at hcond
      have hvvF : vvW = aaVV vv nn k f := by
        unfold aaVV
        rw [if_neg hkn]
      have b5 := pexecM_branch_false mv fu _ (.sequence (.scope (MinBlk mv.nv (c + 9) (vS mv.nv (c + 4))
        (.read s64 (.local 1) (ixk mv.nv (c + 3))) (.sequence (.primitive (.write (.local 1) s64 (ixk mv.nv (c + 3))
          (vS mv.nv (c + 9 + 3)))) Sk))) Sk) Sk _ _ (by rw [hcond]) _ (pexecM_skip mv fu _ _)
      have hrr : pexecM mv fu REST (gS P cl4) vvW = some r2 := by
        rw [hvvF]; exact hr
      have b6 := seqM_some b5 rfl hrr
      refine ⟨_, b6, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
      · intro N hN hB
        simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
        exact ⟨by omega, by omega, hN⟩
      · simp
  have s1 := seqM_some aw rfl hA
  obtain ⟨rM, hM, retM, psM, vvM, cM, nM, wM⟩ := minblk_exec mv P vv fu cl (c + 5) hc (vS mv.nv (c + 4))
    (.read s64 (.local 0) (ixk mv.nv (c + 3))) f xv vf vx hX hY _ _ s1
  refine ⟨_, hM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using retA ▸ retM
  · simpa using psA ▸ psM
  · simpa using vvA ▸ vvM
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cM cA ⊢; omega
  · intro N hN hB
    have := nM N
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at this ⊢
    exact this (by omega) (nA N hN (by omega)) (by omega)
  · simp [wM] at wA ⊢; omega

/-- A call `all_apply(KE, FE)`: copies of three cells, the two arguments, then the body. -/
abbrev AACall (nv c j0 j1 j2 : Nat) (KE FE : NExpr) (REST : Command) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 (nv + j0))))
    (.sequence (.primitive (.declare i32 true (.variable i32 (nv + j1))))
      (.sequence (.primitive (.declare i32 true (.variable i32 (nv + j2))))
        (.sequence (.primitive (.declare i32 true KE))
          (.sequence (.primitive (.declare s64 true FE)) (AABody nv c REST)))))

set_option maxHeartbeats 32000000 in
theorem aacall_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (fu : Nat) (cl : List Cell) (c : Nat) (hc : cl.length = c) (j0 j1 j2 : Nat)
    (n0 nn h0 : Nat) (hj0 : cl[j0]? = some (ci n0)) (hj1 : cl[j1]? = some (ci nn)) (hj2 : cl[j2]? = some (ci h0))
    (hn0 : n0 < 2147483648) (hnn : nn < 2147483648) (hh0 : h0 < 2147483648)
    (KE FE : NExpr) (kk : Nat) (f : Int)
    (hKE : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci n0, ci nn, ci h0]))) KE = some (kk : Int))
    (hFE : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci n0, ci nn, ci h0, ci kk]))) FE = some f)
    (hk31 : kk < 2147483648) (vf : s64.valid f = true)
    (hlt0 : kk < (vv 0).length) (vx : s64.valid ((vv 0).getD kk 0) = true)
    (hlt1 : kk < nn → kk < (vv 1).length ∧ s64.valid ((vv 1).getD kk 0) = true)
    (REST : Command) (r2 : PRM)
    (hr : pexecM mv fu REST (gS P (cl ++ [ci n0, ci nn, ci h0, ci kk, cs f, cs f, cs ((vv 0).getD kk 0),
      cs (mi f ((vv 0).getD kk 0)), cs (mi f ((vv 0).getD kk 0))])) (aaVV vv nn kk f) = some r2) :
    ∃ r : PRM, pexecM mv fu (AACall mv.nv c j0 j1 j2 KE FE REST) (gS P cl) vv = some r ∧ r.ret = r2.ret ∧ r.ps = r2.ps ∧
      r.vv = r2.vv ∧ r.cost ≤ r2.cost + 450 + (vwp KE).1 + (vwp FE).1 ∧
      (∀ N : Nat, r2.need ≤ N → P.length + 2 * c + 200 + (vwp KE).2 + (vwp FE).2 ≤ N → r.need ≤ N) ∧ r.wk ≤ r2.wk + 2 := by
  have lj0 : j0 < cl.length := (List.getElem?_eq_some_iff.mp hj0).1
  have lj1 : j1 < cl.length := (List.getElem?_eq_some_iff.mp hj1).1
  have lj2 : j2 < cl.length := (List.getElem?_eq_some_iff.mp hj2).1
  have gA : ∀ (ys : List Cell) (j : Nat), j < cl.length → (cl ++ ys)[j]? = cl[j]? := fun ys j hj => List.getElem?_append_left hj
  have E0 := envs mv P cl j0 (ci n0) hj0 (i32v n0 hn0)
  have d0 := gSM_decl mv P cl vv i32 (.variable i32 (mv.nv + j0)) (n0 : Int) (n0 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E0) (conv_signed i32 rfl rfl _ (i32v n0 hn0))
  have a0 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j0))) _ _).trans d0
  have E1 := envs mv P (cl ++ [ci n0]) j1 (ci nn) (by rw [gA _ _ lj1]; exact hj1) (i32v nn hnn)
  have d1 := gSM_decl mv P (cl ++ [ci n0]) vv i32 (.variable i32 (mv.nv + j1)) (nn : Int) (nn : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1) (conv_signed i32 rfl rfl _ (i32v nn hnn))
  have e1 : cl ++ [ci n0] ++ [(⟨i32, (nn : Int)⟩ : Cell)] = cl ++ [ci n0, ci nn] := by simp
  rw [e1] at d1
  have a1 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j1))) _ _).trans d1
  have E2 := envs mv P (cl ++ [ci n0, ci nn]) j2 (ci h0) (by rw [gA _ _ lj2]; exact hj2) (i32v h0 hh0)
  have d2 := gSM_decl mv P (cl ++ [ci n0, ci nn]) vv i32 (.variable i32 (mv.nv + j2)) (h0 : Int) (h0 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2) (conv_signed i32 rfl rfl _ (i32v h0 hh0))
  have e2 : cl ++ [ci n0, ci nn] ++ [(⟨i32, (h0 : Int)⟩ : Cell)] = cl ++ [ci n0, ci nn, ci h0] := by simp
  rw [e2] at d2
  have a2 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + j2))) _ _).trans d2
  have d3 := gSM_decl mv P (cl ++ [ci n0, ci nn, ci h0]) vv i32 KE (kk : Int) (kk : Int) hKE
    (conv_signed i32 rfl rfl _ (i32v kk hk31))
  have e3 : cl ++ [ci n0, ci nn, ci h0] ++ [(⟨i32, (kk : Int)⟩ : Cell)] = cl ++ [ci n0, ci nn, ci h0, ci kk] := by simp
  rw [e3] at d3
  have a3 := (pexecM_prim mv fu (.declare i32 true KE) _ _).trans d3
  have d4 := gSM_decl mv P (cl ++ [ci n0, ci nn, ci h0, ci kk]) vv s64 FE f f hFE (conv_signed s64 rfl rfl _ vf)
  have e4 : cl ++ [ci n0, ci nn, ci h0, ci kk] ++ [(⟨s64, f⟩ : Cell)] = cl ++ [ci n0, ci nn, ci h0, ci kk, cs f] := by simp
  rw [e4] at d4
  have a4 := (pexecM_prim mv fu (.declare s64 true FE) _ _).trans d4
  obtain ⟨rB, hB, retB, psB, vvB, cB, nB, wB⟩ := aabody_exec mv hnv ty0 ty1 P vv fu (cl ++ [ci n0, ci nn, ci h0, ci kk, cs f]) c
    (by simp [hc]) nn kk f (by rw [List.getElem?_append_right (by omega)]; simp [hc]) (by rw [List.getElem?_append_right (by omega)]; simp [hc])
    (by rw [List.getElem?_append_right (by omega)]; simp [hc]) hnn hk31 vf hlt0 vx hlt1 REST r2 (by simpa using hr)
  have s4 := seqM_some a4 rfl hB
  have s3 := seqM_some a3 rfl s4
  have s2 := seqM_some a2 rfl s3
  have s1 := seqM_some a1 rfl s2
  have s0 := seqM_some a0 rfl s1
  refine ⟨_, s0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using retB
  · simpa using psB
  · simpa using vvB
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cB ⊢; omega
  · intro N hN hB'
    have hB2 := nB N
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hB2 ⊢
    exact ⟨by omega, by omega, by omega, hB2 hN (by omega)⟩
  · simp at wB ⊢
    omega

/-- The body of `push(k)`; the cells `c .. c + 3` are `n`, `n_node`, `h_node`, `k`. -/
abbrev PushBody (nv c : Nat) (REST : Command) : Command :=
  AACall nv (c + 4) 0 1 2 (.binary i32 .mul (.literal i32 2) (.variable i32 (nv + c + 3)))
    (.read s64 (.local 1) (ixk nv (c + 3)))
    (AACall nv (c + 13) 0 1 2
      (.binary i32 .add (.binary i32 .mul (.literal i32 2) (.variable i32 (nv + c + 3))) (.literal i32 1))
      (.read s64 (.local 1) (ixk nv (c + 3)))
      (.sequence (.primitive (.declare s64 true (.literal s64 9223372036854775807)))
        (.sequence (.primitive (.write (.local 1) s64 (ixk nv (c + 3)) (vS nv (c + 22)))) REST)))

theorem body_eq_all_apply : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_all_apply.body
    = AABody 2 0 Sk := rfl

theorem body_eq_push : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_push.body
    = PushBody 2 0 Sk := rfl

/-! ### The vectors after `push(k)` -/

open Proofs.LazySegMath in
/-- The vectors after `push(k)` (the abstract `pushNode`/`pushLz`). -/
def pushVV (vv : Nat → List Int) (nn k : Nat) : Nat → List Int :=
  upd (upd vv 0 (pushNode Proofs.LazySegChmin.chminMon (vv 0) (vv 1) k)) 1 (pushLz Proofs.LazySegChmin.chminMon nn (vv 1) k)

theorem aaVV_0 (vv : Nat → List Int) (nn k : Nat) (f : Int) :
    aaVV vv nn k f 0 = (vv 0).set k (mi f ((vv 0).getD k 0)) := by
  unfold aaVV; split_ifs <;> simp [upd]

theorem aaVV_1 (vv : Nat → List Int) (nn k : Nat) (f : Int) :
    aaVV vv nn k f 1 = if k < nn then (vv 1).set k (mi f ((vv 1).getD k 0)) else vv 1 := by
  unfold aaVV; split_ifs <;> simp [upd]

theorem aaVV_other (vv : Nat → List Int) (nn k : Nat) (f : Int) (j : Nat) (h0 : j ≠ 0) (h1 : j ≠ 1) :
    aaVV vv nn k f j = vv j := by
  unfold aaVV; split_ifs <;> simp [upd, h0, h1]

theorem getD_dflt (l : List Int) (i : Nat) (a b : Int) (h : i < l.length) : l.getD i a = l.getD i b := by
  simp [List.getD_eq_getElem?_getD, h]

theorem push_vv_eq (vv : Nat → List Int) (nn k : Nat) (hk1 : 1 ≤ k) (hk2 : k < nn) (hl0 : (vv 0).length = 2 * nn)
    (hl1 : (vv 1).length = nn) :
    upd (aaVV (aaVV vv nn (2 * k) ((vv 1).getD k 0)) nn (2 * k + 1) ((vv 1).getD k 0)) 1
      (((aaVV (aaVV vv nn (2 * k) ((vv 1).getD k 0)) nn (2 * k + 1) ((vv 1).getD k 0)) 1).set k 9223372036854775807)
      = pushVV vv nn k := by
  funext j
  unfold pushVV
  by_cases hj1 : j = 1
  · subst hj1
    simp only [upd, if_true]
    rw [aaVV_1, aaVV_1]
    unfold Proofs.LazySegMath.pushLz Proofs.LazySegMath.alz
    have e1 : (vv 1).getD k Proofs.LazySegChmin.chminMon.fid = (vv 1).getD k 0 := getD_dflt _ _ _ _ (by omega)
    simp only [e1]
    have key : ∀ i, i < nn → (vv 1).getD i Proofs.LazySegChmin.chminMon.fid = (vv 1).getD i 0 :=
      fun i hi => getD_dflt _ _ _ _ (by omega)
    by_cases h1 : 2 * k + 1 < nn <;> by_cases h2 : 2 * k < nn
    · simp only [if_pos h1, if_pos h2, key (2 * k) h2, key (2 * k + 1) h1, Proofs.LazySegMath.getD_set_default]
      simp [Proofs.LazySegChmin.chminMon]
    · omega
    · simp only [if_pos h2, if_neg h1, key (2 * k) h2]
      simp [Proofs.LazySegChmin.chminMon]
    · simp only [if_neg h1, if_neg h2]
      rfl
  · by_cases hj0 : j = 0
    · subst hj0
      simp only [upd, if_true, if_neg (show ¬ (0 = 1) by omega)]
      rw [aaVV_0, aaVV_0]
      unfold Proofs.LazySegMath.pushNode
      have e1 : (vv 1).getD k Proofs.LazySegChmin.chminMon.fid = (vv 1).getD k 0 := getD_dflt _ _ _ _ (by omega)
      have k1 : (vv 0).getD (2 * k) Proofs.LazySegChmin.chminMon.e = (vv 0).getD (2 * k) 0 := getD_dflt _ _ _ _ (by omega)
      have k2 : (vv 0).getD (2 * k + 1) Proofs.LazySegChmin.chminMon.e = (vv 0).getD (2 * k + 1) 0 :=
        getD_dflt _ _ _ _ (by omega)
      simp only [e1, k1, k2, Proofs.LazySegMath.getD_set_default]
      have n1 : ¬ (2 * k + 1 = 2 * k ∧ 2 * k < (vv 0).length) := by omega
      simp [n1, Proofs.LazySegChmin.chminMon]
    · simp only [upd, if_neg hj1, if_neg hj0]
      rw [aaVV_other _ _ _ _ _ hj0 hj1, aaVV_other _ _ _ _ _ hj0 hj1]

/-! ### `2 * k` and `2 * k + 1` with the literal first -/

theorem mul2l_den (env : Nat → Ty → Option Int) (slot t : Nat) (h : env slot i32 = some (t : Int)) (ht : 2 * t < 2147483648) :
    (NExpr.binary i32 .mul (.literal i32 2) (.variable i32 slot)).denote env = some ((2 * t : Nat) : Int) := by
  rw [den_binary, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, den_variable, h, Option.bind_some]
  have e : binaryValue .mul 2 (t : Int) = ((2 * t : Nat) : Int) := by
    show 2 * (t : Int) = _; push_cast; ring
  rw [e]
  exact conv_signed i32 rfl rfl _ (i32v _ (by show 2 * t < 2147483648; omega))

theorem mul2l1_den (env : Nat → Ty → Option Int) (slot t : Nat) (h : env slot i32 = some (t : Int)) (ht : 2 * t + 1 < 2147483648) :
    (NExpr.binary i32 .add (.binary i32 .mul (.literal i32 2) (.variable i32 slot)) (.literal i32 1)).denote env =
      some ((2 * t + 1 : Nat) : Int) := by
  rw [den_binary, mul2l_den env slot t h (by omega), Option.bind_some, den_literal, if_pos (show i32.valid 1 = true from rfl),
    Option.bind_some]
  have e : binaryValue .add ((2 * t : Nat) : Int) 1 = ((2 * t + 1 : Nat) : Int) := by
    show ((2 * t : Nat) : Int) + 1 = _; push_cast; ring
  rw [e]
  exact conv_signed i32 rfl rfl _ (i32v _ (by show 2 * t + 1 < 2147483648; omega))

theorem aaVV_len0 (vv : Nat → List Int) (nn k : Nat) (f : Int) : (aaVV vv nn k f 0).length = (vv 0).length := by
  rw [aaVV_0]; simp

theorem aaVV_len1 (vv : Nat → List Int) (nn k : Nat) (f : Int) : (aaVV vv nn k f 1).length = (vv 1).length := by
  rw [aaVV_1]; split_ifs <;> simp

set_option maxHeartbeats 64000000 in
theorem push_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (fu : Nat) (cl : List Cell) (c : Nat) (hc : cl.length = c + 4)
    (n0 nn h0 k : Nat) (hn0 : cl[0]? = some (ci n0)) (hnn' : cl[1]? = some (ci nn)) (hh0' : cl[2]? = some (ci h0))
    (hk' : cl[c + 3]? = some (ci k)) (hn0b : n0 < 2147483648) (hnnb : nn ≤ 1073741824) (hh0b : h0 < 2147483648)
    (hk1 : 1 ≤ k) (hk2 : k < nn) (hl0 : (vv 0).length = 2 * nn) (hl1 : (vv 1).length = nn)
    (hV0 : ∀ i, i < 2 * nn → s64.valid ((vv 0).getD i 0) = true) (hV1 : ∀ i, i < nn → s64.valid ((vv 1).getD i 0) = true)
    (REST : Command) (r2 : PRM)
    (hr : pexecM mv fu REST (gS P (cl ++ [ci n0, ci nn, ci h0, ci (2 * k), cs ((vv 1).getD k 0), cs ((vv 1).getD k 0),
        cs ((vv 0).getD (2 * k) 0), cs (mi ((vv 1).getD k 0) ((vv 0).getD (2 * k) 0)),
        cs (mi ((vv 1).getD k 0) ((vv 0).getD (2 * k) 0)),
        ci n0, ci nn, ci h0, ci (2 * k + 1), cs ((vv 1).getD k 0), cs ((vv 1).getD k 0),
        cs ((vv 0).getD (2 * k + 1) 0), cs (mi ((vv 1).getD k 0) ((vv 0).getD (2 * k + 1) 0)),
        cs (mi ((vv 1).getD k 0) ((vv 0).getD (2 * k + 1) 0)), cs 9223372036854775807])) (pushVV vv nn k) = some r2) :
    ∃ r : PRM, pexecM mv fu (PushBody mv.nv c REST) (gS P cl) vv = some r ∧ r.ret = r2.ret ∧ r.ps = r2.ps ∧ r.vv = r2.vv ∧
      r.cost ≤ r2.cost + 1100 ∧ (∀ N : Nat, r2.need ≤ N → P.length + 2 * c + 400 ≤ N → r.need ≤ N) ∧ r.wk ≤ r2.wk + 5 := by
  have hk31 : k < 2147483648 := by omega
  have h2k : 2 * k + 1 < 2147483648 := by omega
  have f_ok := hV1 k hk2
  have gA : ∀ (ys : List Cell) (j : Nat), j < cl.length → (cl ++ ys)[j]? = cl[j]? := fun ys j hj => List.getElem?_append_left hj
  have Ek : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ ys)) (mv.nv + c + 3) i32 = some (k : Int) := fun ys =>
    envs mv P (cl ++ ys) (c + 3) (ci k) (by rw [gA ys _ (by omega)]; exact hk') (i32v k hk31)
  -- abbreviations
  set f := (vv 1).getD k 0 with hf
  set x1 := (vv 0).getD (2 * k) 0 with hx1
  set x2 := (vv 0).getD (2 * k + 1) 0 with hx2
  have vx1 : s64.valid x1 = true := hV0 (2 * k) (by omega)
  have vx2 : s64.valid x2 = true := hV0 (2 * k + 1) (by omega)
  have vm1 : s64.valid (mi f x1) = true := by unfold mi; split <;> assumption
  have vm2 : s64.valid (mi f x2) = true := by unfold mi; split <;> assumption
  set cl1 := cl ++ [ci n0, ci nn, ci h0, ci (2 * k), cs f, cs f, cs x1, cs (mi f x1), cs (mi f x1)] with hcl1
  have hc1 : cl1.length = c + 13 := by simp [hcl1, hc]
  have Ek1 : ∀ ys : List Cell, penvN mv.nv (gS P (cl1 ++ ys)) (mv.nv + c + 3) i32 = some (k : Int) := fun ys => by
    rw [hcl1, List.append_assoc]; exact Ek _
  -- the vectors after the first call
  have hA0 : (aaVV vv nn (2 * k) f 0).getD (2 * k + 1) 0 = x2 := by
    rw [aaVV_0, Proofs.LazySegMath.getD_set_default, if_neg (by omega)]
  have hA1 : (aaVV vv nn (2 * k) f 1).getD k 0 = f := by
    rw [aaVV_1]
    split_ifs
    · rw [Proofs.LazySegMath.getD_set_default, if_neg (by omega)]
    · rfl
  -- the tail: the literal and the write of `lazy[k]`
  set vvB := aaVV (aaVV vv nn (2 * k) f) nn (2 * k + 1) f with hvvB
  set cl2 := cl1 ++ [ci n0, ci nn, ci h0, ci (2 * k + 1), cs f, cs f, cs x2, cs (mi f x2), cs (mi f x2)] with hcl2
  have hc2 : cl2.length = c + 22 := by simp [hcl2, hc1]
  have Ek2 : ∀ ys : List Cell, penvN mv.nv (gS P (cl2 ++ ys)) (mv.nv + c + 3) i32 = some (k : Int) := fun ys => by
    rw [hcl2, List.append_assoc]; exact Ek1 _
  have dL := gSM_decl mv P cl2 vvB s64 (.literal s64 9223372036854775807) 9223372036854775807 9223372036854775807
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (by decide)]) (conv_signed s64 rfl rfl _ (by decide))
  have aL := (pexecM_prim mv fu (.declare s64 true (.literal s64 9223372036854775807)) _ _).trans dL
  have hlt3 : k < (vvB 1).length := by rw [hvvB, aaVV_len1, aaVV_len1]; omega
  have hw := pstmtM_write_ok mv (gS P (cl2 ++ [(⟨s64, 9223372036854775807⟩ : Cell)])) vvB 1 (by omega) (ixk mv.nv (c + 3))
    (vS mv.nv (c + 22)) 9223372036854775807 k
    (by rw [vdenM_scalar _ _ _ _ rfl]
        exact vr mv P _ (c + 22) _ (by rw [List.getElem?_append_right (by omega)]; simp [hc2]) (by decide))
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ _ k (Ek2 _) hk31) hlt3 (by rw [ty1]; decide)
  rw [ty1] at hw
  have aW := (pexecM_prim mv fu (.write (.local 1) s64 (ixk mv.nv (c + 3)) (vS mv.nv (c + 22))) _ _).trans hw
  have hvvF : upd vvB 1 ((vvB 1).set k 9223372036854775807) = pushVV vv nn k := push_vv_eq vv nn k hk1 hk2 hl0 hl1
  have hrr : pexecM mv fu REST (gS P (cl2 ++ [(⟨s64, 9223372036854775807⟩ : Cell)]))
      (upd vvB 1 ((vvB 1).set k 9223372036854775807)) = some r2 := by
    rw [hvvF]
    have : cl2 ++ [(⟨s64, 9223372036854775807⟩ : Cell)] = cl ++ [ci n0, ci nn, ci h0, ci (2 * k), cs f, cs f, cs x1,
        cs (mi f x1), cs (mi f x1), ci n0, ci nn, ci h0, ci (2 * k + 1), cs f, cs f, cs x2, cs (mi f x2), cs (mi f x2),
        cs 9223372036854775807] := by simp [hcl2, hcl1]
    rw [this]; exact hr
  have sW := seqM_some aW rfl hrr
  have sL := seqM_some aL rfl sW
  -- the second call
  have c1n : ∀ j, j < cl.length → cl1[j]? = cl[j]? := fun j hj => by rw [hcl1]; exact List.getElem?_append_left hj
  have hKE2 : vdenM mv (aaVV vv nn (2 * k) f) (penvN mv.nv (gS P (cl1 ++ [ci n0, ci nn, ci h0])))
      (.binary i32 .add (.binary i32 .mul (.literal i32 2) (.variable i32 (mv.nv + c + 3))) (.literal i32 1)) =
      some ((2 * k + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact mul2l1_den _ _ k (Ek1 [ci n0, ci nn, ci h0]) h2k
  have hFE2 : vdenM mv (aaVV vv nn (2 * k) f) (penvN mv.nv (gS P (cl1 ++ [ci n0, ci nn, ci h0, ci (2 * k + 1)])))
      (.read s64 (.local 1) (ixk mv.nv (c + 3))) = some f :=
    rdM_val mv _ _ 1 (by omega) s64 ty1.symm (ixk mv.nv (c + 3)) rfl rfl k (cidx_den _ _ k (Ek1 _) hk31) f
      (by have h := vec_getI (aaVV vv nn (2 * k) f 1) k (by rw [aaVV_len1 vv nn (2 * k) f]; omega); rw [hA1] at h; exact h)
      (by rw [ty1]; exact f_ok)
  obtain ⟨r3, h3, ret3, ps3, vv3, c3, n3, w3⟩ := aacall_exec mv hnv ty0 ty1 P (aaVV vv nn (2 * k) f) fu cl1 (c + 13) hc1
    0 1 2 n0 nn h0 (by rw [c1n _ (by omega)]; exact hn0) (by rw [c1n _ (by omega)]; exact hnn')
    (by rw [c1n _ (by omega)]; exact hh0') hn0b (by omega) hh0b
    (.binary i32 .add (.binary i32 .mul (.literal i32 2) (.variable i32 (mv.nv + c + 3))) (.literal i32 1))
    (.read s64 (.local 1) (ixk mv.nv (c + 3))) (2 * k + 1) f hKE2 hFE2 h2k f_ok
    (by rw [aaVV_len0 vv nn (2 * k) f]; omega)
    (by rw [aaVV_0, Proofs.LazySegMath.getD_set_default, if_neg (by omega)]; exact hV0 _ (by omega))
    (fun h => ⟨by rw [aaVV_len1 vv nn (2 * k) f]; omega, by
      rw [aaVV_1]; split_ifs
      · rw [Proofs.LazySegMath.getD_set_default, if_neg (by omega)]; exact hV1 _ h
      · exact hV1 _ h⟩)
    (.sequence (.primitive (.declare s64 true (.literal s64 9223372036854775807)))
      (.sequence (.primitive (.write (.local 1) s64 (ixk mv.nv (c + 3)) (vS mv.nv (c + 22)))) REST)) _
    (by rw [hA0]; exact sL)
  -- the first call
  have hKE1 : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci n0, ci nn, ci h0])))
      (.binary i32 .mul (.literal i32 2) (.variable i32 (mv.nv + c + 3))) = some ((2 * k : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact mul2l_den _ _ k (Ek [ci n0, ci nn, ci h0]) (by omega)
  have hFE1 : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci n0, ci nn, ci h0, ci (2 * k)])))
      (.read s64 (.local 1) (ixk mv.nv (c + 3))) = some f :=
    rdM_val mv vv _ 1 (by omega) s64 ty1.symm (ixk mv.nv (c + 3)) rfl rfl k (cidx_den _ _ k (Ek _) hk31) f
      (vec_getI (vv 1) k (by omega)) (by rw [ty1]; exact f_ok)
  obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := aacall_exec mv hnv ty0 ty1 P vv fu cl (c + 4) hc 0 1 2
    n0 nn h0 hn0 hnn' hh0' hn0b (by omega) hh0b
    (.binary i32 .mul (.literal i32 2) (.variable i32 (mv.nv + c + 3))) (.read s64 (.local 1) (ixk mv.nv (c + 3))) (2 * k) f
    hKE1 hFE1 (by omega) f_ok (by omega) vx1
    (fun h => ⟨by omega, hV1 _ h⟩) _ r3 h3
  refine ⟨_, h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ret1, ret3]
  · rw [ps1, ps3]
  · rw [vv1, vv3]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c3 ⊢; omega
  · intro N hN hB
    have h3N := n3 N
    have h1N := n1 N
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at h3N h1N ⊢
    exact h1N (h3N (by omega) (by omega) hN (by omega)) (by omega)
  · simp at w1 w3 ⊢; omega

/-! ### Division and decrement of `int` cells -/

theorem cdr_i32_div (x y : Nat) (hx : x < 2147483648) (hy0 : 0 < y) (hy : y < 2147483648) :
    checkedDivRem i32 false (x : Int) (y : Int) = some ((x / y : Nat) : Int) := by
  have hq : (x : Int).tdiv (y : Int) = ((x / y : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg x)]; omega
  have hv : i32.valid ((x / y : Nat) : Int) = true := i32v _ (by show x / y < 2147483648; have := Nat.div_le_self x y; omega)
  unfold checkedDivRem
  have h0 : ((y : Int) == 0) = false := by
    have : (y : Int) ≠ 0 := by omega
    simpa using this
  simp only [h0, hq, hv, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  exact conv_signed i32 rfl rfl _ hv

theorem divvar_den (env : Nat → Ty → Option Int) (a b x y : Nat) (ha : env a i32 = some (x : Int)) (hb : env b i32 = some (y : Int))
    (hx : x < 2147483648) (hy0 : 0 < y) (hy : y < 2147483648) :
    (NExpr.divrem i32 false (.variable i32 a) (.variable i32 b)).denote env = some ((x / y : Nat) : Int) := by
  rw [den_divrem, den_variable, ha, Option.bind_some, den_variable, hb, Option.bind_some, cdr_i32_div x y hx hy0 hy]

theorem dec_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (slot k : Nat)
    (h : env slot i32 = some (k : Int)) (hk : 1 ≤ k) (hk2 : k < 2147483648) :
    vdenM mv vv env (.binary i32 .sub (.variable i32 slot) (.literal i32 1)) = some ((k - 1 : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, h, Option.bind_some,
    den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .sub (k : Int) 1 = ((k - 1 : Nat) : Int) := by
    show (k : Int) - 1 = _; omega
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ (by omega))

/-- A call `push(KE)`: copies of `n`, `n_node`, `h_node` and the argument `KE`, then the body. -/
abbrev PushCall (nv c : Nat) (KE : NExpr) (REST : Command) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 (nv + 0))))
    (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 1))))
      (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 2))))
        (.sequence (.primitive (.declare i32 true KE)) (PushBody nv c REST))))

set_option maxHeartbeats 64000000 in
theorem pushcall_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (fu : Nat) (cl : List Cell) (c : Nat) (hc : cl.length = c)
    (n0 nn h0 k : Nat) (hn0 : cl[0]? = some (ci n0)) (hnn' : cl[1]? = some (ci nn)) (hh0' : cl[2]? = some (ci h0))
    (hn0b : n0 < 2147483648) (hnnb : nn ≤ 1073741824) (hh0b : h0 < 2147483648) (KE : NExpr)
    (hKE : vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci n0, ci nn, ci h0]))) KE = some (k : Int))
    (hk1 : 1 ≤ k) (hk2 : k < nn) (hl0 : (vv 0).length = 2 * nn) (hl1 : (vv 1).length = nn)
    (hV0 : ∀ i, i < 2 * nn → s64.valid ((vv 0).getD i 0) = true) (hV1 : ∀ i, i < nn → s64.valid ((vv 1).getD i 0) = true)
    (REST : Command) (r2 : PRM)
    (hr : pexecM mv fu REST (gS P (cl ++ [ci n0, ci nn, ci h0, ci k] ++ [ci n0, ci nn, ci h0, ci (2 * k), cs ((vv 1).getD k 0), cs ((vv 1).getD k 0),
        cs ((vv 0).getD (2 * k) 0), cs (mi ((vv 1).getD k 0) ((vv 0).getD (2 * k) 0)),
        cs (mi ((vv 1).getD k 0) ((vv 0).getD (2 * k) 0)),
        ci n0, ci nn, ci h0, ci (2 * k + 1), cs ((vv 1).getD k 0), cs ((vv 1).getD k 0),
        cs ((vv 0).getD (2 * k + 1) 0), cs (mi ((vv 1).getD k 0) ((vv 0).getD (2 * k + 1) 0)),
        cs (mi ((vv 1).getD k 0) ((vv 0).getD (2 * k + 1) 0)), cs 9223372036854775807])) (pushVV vv nn k) = some r2) :
    ∃ r : PRM, pexecM mv fu (PushCall mv.nv c KE REST) (gS P cl) vv = some r ∧ r.ret = r2.ret ∧ r.ps = r2.ps ∧ r.vv = r2.vv ∧
      r.cost ≤ r2.cost + 1200 + (vwp KE).1 ∧
      (∀ N : Nat, r2.need ≤ N → P.length + 2 * c + 420 + (vwp KE).2 ≤ N → r.need ≤ N) ∧ r.wk ≤ r2.wk + 5 := by
  have hk31 : k < 2147483648 := by omega
  have lj0 : 0 < cl.length := (List.getElem?_eq_some_iff.mp hn0).1
  have lj1 : 1 < cl.length := (List.getElem?_eq_some_iff.mp hnn').1
  have lj2 : 2 < cl.length := (List.getElem?_eq_some_iff.mp hh0').1
  have gA : ∀ (ys : List Cell) (j : Nat), j < cl.length → (cl ++ ys)[j]? = cl[j]? := fun ys j hj => List.getElem?_append_left hj
  have E0 := envs mv P cl 0 (ci n0) hn0 (i32v n0 hn0b)
  have d0 := gSM_decl mv P cl vv i32 (.variable i32 (mv.nv + 0)) (n0 : Int) (n0 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E0) (conv_signed i32 rfl rfl _ (i32v n0 hn0b))
  have a0 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 0))) _ _).trans d0
  have E1 := envs mv P (cl ++ [ci n0]) 1 (ci nn) (by rw [gA _ _ lj1]; exact hnn') (i32v nn (by show nn < 2147483648; omega))
  have d1 := gSM_decl mv P (cl ++ [ci n0]) vv i32 (.variable i32 (mv.nv + 1)) (nn : Int) (nn : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1) (conv_signed i32 rfl rfl _ (i32v nn (by show nn < 2147483648; omega)))
  have e1 : cl ++ [ci n0] ++ [(⟨i32, (nn : Int)⟩ : Cell)] = cl ++ [ci n0, ci nn] := by simp
  rw [e1] at d1
  have a1 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 1))) _ _).trans d1
  have E2 := envs mv P (cl ++ [ci n0, ci nn]) 2 (ci h0) (by rw [gA _ _ lj2]; exact hh0') (i32v h0 hh0b)
  have d2 := gSM_decl mv P (cl ++ [ci n0, ci nn]) vv i32 (.variable i32 (mv.nv + 2)) (h0 : Int) (h0 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2) (conv_signed i32 rfl rfl _ (i32v h0 hh0b))
  have e2 : cl ++ [ci n0, ci nn] ++ [(⟨i32, (h0 : Int)⟩ : Cell)] = cl ++ [ci n0, ci nn, ci h0] := by simp
  rw [e2] at d2
  have a2 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 2))) _ _).trans d2
  have d3 := gSM_decl mv P (cl ++ [ci n0, ci nn, ci h0]) vv i32 KE (k : Int) (k : Int) hKE (conv_signed i32 rfl rfl _ (i32v k hk31))
  have e3 : cl ++ [ci n0, ci nn, ci h0] ++ [(⟨i32, (k : Int)⟩ : Cell)] = cl ++ [ci n0, ci nn, ci h0, ci k] := by simp
  rw [e3] at d3
  have a3 := (pexecM_prim mv fu (.declare i32 true KE) _ _).trans d3
  have hc4 : (cl ++ [ci n0, ci nn, ci h0, ci k]).length = c + 4 := by simp [hc]
  have hcell : ∀ j, j < 4 → (cl ++ [ci n0, ci nn, ci h0, ci k])[c + j]? = [ci n0, ci nn, ci h0, ci k][j]? := by
    intro j hj; rw [List.getElem?_append_right (by omega)]; simp [hc]
  obtain ⟨rP, hP, retP, psP, vvP, cP, nP, wP⟩ := push_exec mv hnv ty0 ty1 P vv fu (cl ++ [ci n0, ci nn, ci h0, ci k]) c hc4
    n0 nn h0 k (by rw [List.getElem?_append_left (by omega)]; exact hn0) (by rw [List.getElem?_append_left (by omega)]; exact hnn')
    (by rw [List.getElem?_append_left (by omega)]; exact hh0') (hcell 3 (by omega)) hn0b hnnb hh0b hk1 hk2 hl0 hl1 hV0 hV1
    REST r2 hr
  have s3 := seqM_some a3 rfl hP
  have s2 := seqM_some a2 rfl s3
  have s1 := seqM_some a1 rfl s2
  have s0 := seqM_some a0 rfl s1
  refine ⟨_, s0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using retP
  · simpa using psP
  · simpa using vvP
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cP ⊢; omega
  · intro N hN hB
    have hP2 := nP N
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hP2 ⊢
    exact ⟨by omega, by omega, hP2 hN (by omega)⟩
  · simp at wP ⊢; omega

/-! ### The loop `for (i = h_node; i >= 1; i--) { push(idx / pw); pw = pw / 2; }`

The cells are `pre` (length `m`, with `n`, `n_node`, `h_node`, `idx` first), then `pw` (cell `m`) and `i` (cell `m + 1`). -/

abbrev PwHalf (nv m : Nat) : Command :=
  .sequence (.primitive (.assign (nv + m) i32 (.divrem i32 false (.variable i32 (nv + m)) (.literal i32 2)))) Sk

abbrev PathBody (nv m : Nat) : Command :=
  .sequence (.scope (PushCall nv (m + 2) (.divrem i32 false (.variable i32 (nv + 3)) (.variable i32 (nv + m))) (PwHalf nv m)))
    (.sequence (.primitive (.assign (nv + m + 1) i32 (.binary i32 .sub (.variable i32 (nv + m + 1)) (.literal i32 1)))) Sk)

abbrev PathLoop (nv m : Nat) : Command :=
  .whileLoop (.binary bT .ge (.variable i32 (nv + m + 1)) (.literal i32 1)) (PathBody nv m)

theorem pwhalf_exec (mv : MV) (P : List Cell) (vv : Nat → List Int) (fu : Nat) (pre zs : List Cell) (m : Nat)
    (hpre : pre.length = m) (pw i : Nat) (hpw : pw < 2147483648) :
    ∃ r : PRM, pexecM mv fu (PwHalf mv.nv m) (gS P (pre ++ [ci pw, ci i] ++ zs)) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (pre ++ [ci (pw / 2), ci i] ++ zs) ∧ r.vv = vv ∧ r.cost ≤ 20 ∧
      r.need ≤ P.length + 2 * (m + 2 + zs.length) + 12 ∧ r.wk = 0 := by
  have hcell : (pre ++ [ci pw, ci i] ++ zs)[m]? = some (ci pw) := by
    rw [List.getElem?_append_left (by simp [hpre]), List.getElem?_append_right (by omega)]; simp [hpre]
  have E := envs mv P (pre ++ [ci pw, ci i] ++ zs) m (ci pw) hcell (i32v pw hpw)
  have e1 : vdenM mv vv (penvN mv.nv (gS P (pre ++ [ci pw, ci i] ++ zs)))
      (.divrem i32 false (.variable i32 (mv.nv + m)) (.literal i32 2)) = some ((pw / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, E, Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
    simpa using cdr_i32_div pw 2 hpw (by omega) (by omega)
  have s1 := gSM_assign mv P (pre ++ [ci pw, ci i] ++ zs) vv m (by simp [hpre]) i32 _ _ _ e1 (ci pw) hcell rfl
    (i32v pw hpw) (conv_signed i32 rfl rfl _ (i32v _ (by show pw / 2 < 2147483648; omega)))
  have eS : (pre ++ [ci pw, ci i] ++ zs).set m ⟨i32, ((pw / 2 : Nat) : Int)⟩ = pre ++ [ci (pw / 2), ci i] ++ zs := by
    rw [List.set_append_left _ _ (by simp [hpre]), List.set_append_right _ _ (by omega)]
    simp [hpre]
  rw [eS] at s1
  have a1 := (pexecM_prim mv fu (.assign (mv.nv + m) i32 (.divrem i32 false (.variable i32 (mv.nv + m)) (.literal i32 2))) _ _).trans s1
  have b1 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hpre]; omega
  · simp

set_option maxHeartbeats 64000000 in
/-- One iteration of the path loop: `push(idx / pw); pw = pw / 2; i--`. -/
theorem path_iter (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (fu : Nat) (pre : List Cell) (m : Nat) (hm : 4 ≤ m) (hpre : pre.length = m)
    (n0 nn h0 idx pw i : Nat) (hp0 : pre[0]? = some (ci n0)) (hp1 : pre[1]? = some (ci nn)) (hp2 : pre[2]? = some (ci h0))
    (hp3 : pre[3]? = some (ci idx)) (hn0b : n0 < 2147483648) (hnnb : nn ≤ 1073741824) (hh0b : h0 < 2147483648)
    (hidx : idx < 2147483648) (hpw : 0 < pw) (hpw31 : pw < 2147483648) (hi1 : 1 ≤ i) (hi31 : i < 2147483648)
    (hk1 : 1 ≤ idx / pw) (hk2 : idx / pw < nn) (hl0 : (vv 0).length = 2 * nn) (hl1 : (vv 1).length = nn)
    (hV0 : ∀ j, j < 2 * nn → s64.valid ((vv 0).getD j 0) = true) (hV1 : ∀ j, j < nn → s64.valid ((vv 1).getD j 0) = true) :
    ∃ r : PRM, pexecM mv fu (PathBody mv.nv m) (gS P (pre ++ [ci pw, ci i])) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (pre ++ [ci (pw / 2), ci (i - 1)]) ∧ r.vv = pushVV vv nn (idx / pw) ∧ r.cost ≤ 1400 ∧
      r.need ≤ P.length + 2 * m + 600 ∧ r.wk ≤ 5 := by
  have gA : ∀ (ys : List Cell) (j : Nat), j < pre.length → (pre ++ ys)[j]? = pre[j]? := fun ys j hj => List.getElem?_append_left hj
  have hc : (pre ++ [ci pw, ci i]).length = m + 2 := by simp [hpre]
  have c0 : (pre ++ [ci pw, ci i])[0]? = some (ci n0) := by rw [gA _ _ (by omega)]; exact hp0
  have c1 : (pre ++ [ci pw, ci i])[1]? = some (ci nn) := by rw [gA _ _ (by omega)]; exact hp1
  have c2 : (pre ++ [ci pw, ci i])[2]? = some (ci h0) := by rw [gA _ _ (by omega)]; exact hp2
  have hKE : vdenM mv vv (penvN mv.nv (gS P (pre ++ [ci pw, ci i] ++ [ci n0, ci nn, ci h0])))
      (.divrem i32 false (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + m))) = some ((idx / pw : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    refine divvar_den _ _ _ idx pw ?_ ?_ hidx hpw hpw31
    · exact envs mv P (pre ++ [ci pw, ci i] ++ [ci n0, ci nn, ci h0]) 3 (ci idx)
        (by rw [List.getElem?_append_left (by simp [hpre]; omega), gA _ _ (by omega)]; exact hp3) (i32v idx hidx)
    · exact envs mv P (pre ++ [ci pw, ci i] ++ [ci n0, ci nn, ci h0]) m (ci pw)
        (by rw [List.getElem?_append_left (by simp [hpre]), List.getElem?_append_right (by omega)]; simp [hpre]) (i32v pw hpw31)
  obtain ⟨rH, hH, retH, psH, vvH, cH, nH, wH⟩ := pwhalf_exec mv P (pushVV vv nn (idx / pw)) fu pre
    ([ci n0, ci nn, ci h0, ci (idx / pw)] ++ [ci n0, ci nn, ci h0, ci (2 * (idx / pw)), cs ((vv 1).getD (idx / pw) 0),
      cs ((vv 1).getD (idx / pw) 0), cs ((vv 0).getD (2 * (idx / pw)) 0),
      cs (mi ((vv 1).getD (idx / pw) 0) ((vv 0).getD (2 * (idx / pw)) 0)),
      cs (mi ((vv 1).getD (idx / pw) 0) ((vv 0).getD (2 * (idx / pw)) 0)),
      ci n0, ci nn, ci h0, ci (2 * (idx / pw) + 1), cs ((vv 1).getD (idx / pw) 0), cs ((vv 1).getD (idx / pw) 0),
      cs ((vv 0).getD (2 * (idx / pw) + 1) 0), cs (mi ((vv 1).getD (idx / pw) 0) ((vv 0).getD (2 * (idx / pw) + 1) 0)),
      cs (mi ((vv 1).getD (idx / pw) 0) ((vv 0).getD (2 * (idx / pw) + 1) 0)), cs 9223372036854775807])
    m hpre pw i hpw31
  obtain ⟨rC, hC, retC, psC, vvC, cC, nC, wC⟩ := pushcall_exec mv hnv ty0 ty1 P vv fu (pre ++ [ci pw, ci i]) (m + 2) hc
    n0 nn h0 (idx / pw) c0 c1 c2 hn0b hnnb hh0b _ hKE hk1 hk2 hl0 hl1 hV0 hV1 _ rH (by simpa using hH)
  have b0 := pexecM_scope mv fu _ _ _ _ hC
  have tk := gS_takeC P (pre ++ [ci pw, ci i]) (pre ++ [ci (pw / 2), ci i])
    ([ci n0, ci nn, ci h0, ci (idx / pw)] ++ [ci n0, ci nn, ci h0, ci (2 * (idx / pw)), cs ((vv 1).getD (idx / pw) 0),
      cs ((vv 1).getD (idx / pw) 0), cs ((vv 0).getD (2 * (idx / pw)) 0),
      cs (mi ((vv 1).getD (idx / pw) 0) ((vv 0).getD (2 * (idx / pw)) 0)),
      cs (mi ((vv 1).getD (idx / pw) 0) ((vv 0).getD (2 * (idx / pw)) 0)),
      ci n0, ci nn, ci h0, ci (2 * (idx / pw) + 1), cs ((vv 1).getD (idx / pw) 0), cs ((vv 1).getD (idx / pw) 0),
      cs ((vv 0).getD (2 * (idx / pw) + 1) 0), cs (mi ((vv 1).getD (idx / pw) 0) ((vv 0).getD (2 * (idx / pw) + 1) 0)),
      cs (mi ((vv 1).getD (idx / pw) 0) ((vv 0).getD (2 * (idx / pw) + 1) 0)), cs 9223372036854775807]) (by simp [hpre])
  rw [psC, psH] at b0
  simp only [tk] at b0
  -- the decrement
  have cI : (pre ++ [ci (pw / 2), ci i])[m + 1]? = some (ci i) := by
    rw [List.getElem?_append_right (by omega)]; simp [hpre]
  have EI := envs mv P (pre ++ [ci (pw / 2), ci i]) (m + 1) (ci i) cI (i32v i hi31)
  have e2 := dec_val mv (pushVV vv nn (idx / pw)) (penvN mv.nv (gS P (pre ++ [ci (pw / 2), ci i]))) (mv.nv + (m + 1)) i EI hi1 hi31
  have s2 := gSM_assign mv P (pre ++ [ci (pw / 2), ci i]) (pushVV vv nn (idx / pw)) (m + 1) (by simp [hpre]) i32 _ _ _ e2
    (ci i) cI rfl (i32v i hi31) (conv_signed i32 rfl rfl _ (i32v _ (by show i - 1 < 2147483648; omega)))
  have eS : (pre ++ [ci (pw / 2), ci i]).set (m + 1) ⟨i32, ((i - 1 : Nat) : Int)⟩ = pre ++ [ci (pw / 2), ci (i - 1)] := by
    rw [List.set_append_right _ _ (by omega)]
    simp [hpre]
  rw [eS] at s2
  have a2 := (pexecM_prim mv fu (.assign (mv.nv + m + 1) i32 (.binary i32 .sub (.variable i32 (mv.nv + m + 1)) (.literal i32 1))) _ _).trans s2
  have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  have b3 := seqM_some b0 (by simpa using retC ▸ retH) (by rw [vvC, vvH]; exact b2)
  refine ⟨_, b3, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [vvC, vvH]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cC cH ⊢; omega
  · have hn := nC (P.length + 2 * m + 600) (by
      have := nH
      simp [gS_mem_len, gS_bs_len, hpre] at this ⊢
      omega) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega)
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hpre] at hn ⊢
    omega
  · simp at wC wH ⊢; omega

theorem cond_ge1 (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (m i : Nat)
    (hcell : cl[m + 1]? = some (ci i)) (hi : i < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .ge (.variable i32 (mv.nv + m + 1)) (.literal i32 1)) =
      some (if 1 ≤ i then 1 else 0) := by
  have E := envs mv P cl (m + 1) (ci i) hcell (i32v i hi)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable]
  have E' : penvN mv.nv (gS P cl) (mv.nv + m + 1) i32 = some (i : Int) := E
  rw [E', Option.bind_some, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  by_cases h : 1 ≤ i
  · have : (1 : Int) ≤ (i : Int) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((1 : Int) ≤ (i : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

/-! ### The invariant of the path loop -/

open Proofs.LazySegMath in
/-- The vectors represent `A`, and the ancestors `p / 2^t` (`i < t <= h`) of the leaf `p` have no pending action. -/
def PInv (nn : Nat) (A : List Int) (p h i : Nat) (vv : Nat → List Int) : Prop :=
  Rep Proofs.LazySegChmin.chminMon nn A (vv 0) (vv 1) ∧
    LzFid Proofs.LazySegChmin.chminMon (fun s => ∃ t, i < t ∧ t ≤ h ∧ s = p / 2 ^ t) (vv 1)

theorem pushVV_0 (vv : Nat → List Int) (nn k : Nat) :
    pushVV vv nn k 0 = Proofs.LazySegMath.pushNode Proofs.LazySegChmin.chminMon (vv 0) (vv 1) k := by
  simp [pushVV, upd]

theorem pushVV_1 (vv : Nat → List Int) (nn k : Nat) :
    pushVV vv nn k 1 = Proofs.LazySegMath.pushLz Proofs.LazySegChmin.chminMon nn (vv 1) k := by
  simp [pushVV, upd]

theorem lzfid_mono (S1 S2 : Nat → Prop) (lz : List Int) (h : Proofs.LazySegMath.LzFid Proofs.LazySegChmin.chminMon S1 lz)
    (hs : ∀ s, S2 s → S1 s) : Proofs.LazySegMath.LzFid Proofs.LazySegChmin.chminMon S2 lz :=
  fun s hs2 => h s (hs s hs2)

theorem k_bounds (nn h p i : Nat) (hN : nn = 2 ^ h) (hp1 : nn ≤ p) (hp2 : p < 2 * nn) (hi1 : 1 ≤ i) (hih : i ≤ h) :
    1 ≤ p / 2 ^ i ∧ p / 2 ^ i < nn := by
  have h2i : 2 ^ i ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) hih
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have h1 : 2 ^ 1 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi1
  constructor
  · rw [Nat.le_div_iff_mul_le hpos]; omega
  · rw [Nat.div_lt_iff_lt_mul hpos]
    have : nn * 2 ≤ nn * 2 ^ i := Nat.mul_le_mul_left nn (by simpa using h1)
    omega

theorem pInv_step (nn : Nat) (A : List Int) (p h i : Nat) (vv : Nat → List Int) (hN : nn = 2 ^ h) (hp1 : nn ≤ p) (hp2 : p < 2 * nn)
    (hi1 : 1 ≤ i) (hih : i ≤ h) (hI : PInv nn A p h i vv) :
    PInv nn A p h (i - 1) (pushVV vv nn (p / 2 ^ i)) := by
  obtain ⟨hR, hF⟩ := hI
  have hk := k_bounds nn h p i hN hp1 hp2 hi1 hih
  refine ⟨?_, ?_⟩
  · rw [pushVV_0, pushVV_1]
    exact Proofs.LazySegMath.rep_push _ nn A _ _ _ hk.1 hk.2 hR
  · rw [pushVV_1]
    refine lzfid_mono _ _ _ (Proofs.LazySegMath.pushLz_fid _ nn (vv 1) (p / 2 ^ i) _ hk.1 hk.2 hR.2.1 ?_ hF) ?_
    · rintro s ⟨t, ht1, ht2, rfl⟩
      have h2 : 2 ^ i ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht1.le
      have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
      have e : p / 2 ^ t = p / 2 ^ i / 2 ^ (t - i) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]; congr 2; omega
      rw [e]
      apply Nat.div_lt_self (by omega)
      have : 2 ^ 1 ≤ 2 ^ (t - i) := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.lt_of_lt_of_le (by decide) this
    · rintro s ⟨t, ht1, ht2, rfl⟩
      by_cases hti : t = i
      · right; rw [hti]
      · left; exact ⟨t, by omega, ht2, rfl⟩

theorem rep_valid0 (nn : Nat) (A node lz : List Int)
    (hR : Proofs.LazySegMath.Rep Proofs.LazySegChmin.chminMon nn A node lz) :
    ∀ j, j < 2 * nn → s64.valid (node.getD j 0) = true := by
  intro j hj
  obtain ⟨hn, hl, hA, hV, hF, hAV, hE⟩ := hR
  have := Proofs.LazySegMath.getD_Ve Proofs.LazySegChmin.chminMon node hV j (by omega)
  rw [getD_dflt node j 0 Proofs.LazySegChmin.chminMon.e (by omega)]
  exact this

theorem rep_valid1 (nn : Nat) (A node lz : List Int)
    (hR : Proofs.LazySegMath.Rep Proofs.LazySegChmin.chminMon nn A node lz) :
    ∀ j, j < nn → s64.valid (lz.getD j 0) = true := by
  intro j hj
  obtain ⟨hn, hl, hA, hV, hF, hAV, hE⟩ := hR
  have := Proofs.LazySegMath.getD_F Proofs.LazySegChmin.chminMon lz hF j
  rw [getD_dflt lz j 0 Proofs.LazySegChmin.chminMon.fid (by omega)]
  exact this

set_option maxHeartbeats 64000000 in
theorem path_loop (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (pre : List Cell) (m : Nat) (hm : 4 ≤ m) (hpre : pre.length = m) (n0 h idx : Nat) (hn0b : n0 < 2147483648) (A : List Int)
    (hp0 : pre[0]? = some (ci n0)) (hp1 : pre[1]? = some (ci (2 ^ h))) (hp2 : pre[2]? = some (ci h))
    (hp3 : pre[3]? = some (ci idx)) (hh30 : h ≤ 30) (hidx1 : 2 ^ h ≤ idx) (hidx2 : idx < 2 * 2 ^ h) :
    ∀ (d i : Nat) (vv : Nat → List Int) (fu : Nat), i = d → i ≤ h → PInv (2 ^ h) A idx h i vv → d + 1 ≤ fu →
      ∃ (res : PRM) (vf : Nat → List Int), pexecM mv fu (PathLoop mv.nv m) (gS P (pre ++ [ci (2 ^ i), ci i])) vv = some res ∧
        res.ret = none ∧ res.ps = gS P (pre ++ [ci (2 ^ 0), ci 0]) ∧ res.vv = vf ∧ PInv (2 ^ h) A idx h 0 vf ∧
        res.cost ≤ 1500 * d + 30 ∧ res.need ≤ P.length + 2 * m + 600 ∧ res.wk ≤ 5 * d := by
  have hN30 : 2 ^ h ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hh30
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  intro d
  induction d with
  | zero =>
    intro i vv fu hid hih hI hfu
    have him : i = 0 := hid
    subst him
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_ge1 mv P vv (pre ++ [ci (2 ^ 0), ci 0]) m 0 (by
      rw [List.getElem?_append_right (by omega)]; simp [hpre]) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, vv, rfl, rfl, rfl, rfl, hI, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hpre]; omega
    · simp
  | succ d ih =>
    intro i vv fu hid hih hI hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_ge1 mv P vv (pre ++ [ci (2 ^ i), ci i]) m i (by
      rw [List.getElem?_append_right (by omega)]; simp [hpre]) (by omega)
    rw [if_pos (by omega)] at hc
    have hk := k_bounds (2 ^ h) h idx i rfl hidx1 hidx2 (by omega) hih
    have hRp := hI.1
    have hpw : 2 ^ i ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) hih
    have hpwpos : 0 < 2 ^ i := Nat.two_pow_pos i
    have hdiv : 2 ^ i / 2 = 2 ^ d := by
      rw [show i = d + 1 from hid, Nat.pow_succ]; omega
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := path_iter mv hnv ty0 ty1 P vv (fu' + 1) pre m hm hpre n0 (2 ^ h) h idx
      (2 ^ i) i hp0 hp1 hp2 hp3 hn0b (by omega) (by omega) (by omega) hpwpos (by omega) (by omega) (by omega)
      hk.1 hk.2 hRp.1 hRp.2.1 (rep_valid0 _ A _ _ hRp) (rep_valid1 _ A _ _ hRp)
    have hnext := pInv_step (2 ^ h) A idx h i vv rfl hidx1 hidx2 (by omega) hih hI
    have e1 : i - 1 = d := by omega
    rw [e1] at hnext
    have ps1' : r1.ps = gS P (pre ++ [ci (2 ^ d), ci d]) := by rw [ps1, hdiv, e1]
    obtain ⟨r2, vf, h2, ret2, ps2, vv2, hIf, c2, n2, w2⟩ := ih d (pushVV vv (2 ^ h) (idx / 2 ^ i)) fu' rfl (by omega) hnext (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1', vv1, h2]
    refine ⟨_, vf, rfl, ret2, ps2, vv2, hIf, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hpre] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

end Proofs.LazySegBlocks
