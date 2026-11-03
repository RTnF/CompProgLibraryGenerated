import Proofs.MultiVecCallN
import Proofs.ForLoopBN
import Proofs.BellmanFordExec
import Proofs.Generated.Vector2dSum

namespace Proofs.Vector2dSumExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVecN Proofs.MultiKitN Proofs.ForLoopMN Proofs.ForLoopCN
open Proofs.ForLoopBN Proofs.VecStmtX
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (cidx_den M31 i32_valid_nat s64_valid_of)

/-! ### `vector2d_sum<long long>` (nv = 1: the nested vector is slot 0).  Cells: 0 = s, 1 = rows, 2 = i, 3 = cols, 4 = j,
5 = x -/

abbrev cs64 (x : Int) : Cell := ⟨s64, x⟩
abbrev iIdx (nv : Nat) : NExpr := .cast u64 (.variable i32 (nv + 2))
abbrev jIdx (nv : Nat) : NExpr := .cast u64 (.variable i32 (nv + 4))
abbrev readE (nv : Nat) : NExpr := .read s64 (.row (.local 0) (.integer s64) (iIdx nv)) (jIdx nv)
abbrev bodyIn (nv : Nat) : Command :=
  .sequence (.primitive (.declare s64 true (readE nv)))
    (.sequence (.primitive (.assign (nv + 0) s64 (.binary s64 .add (.variable s64 (nv + 0)) (.variable s64 (nv + 5))))) Sk)
abbrev innerFor (nv : Nat) : Command := forStmtB nv 4 3 (bodyIn nv)
abbrev colsE (nv : Nat) : NExpr := .cast i32 (.size (.integer s64) (.row (.local 0) (.integer s64) (iIdx nv)))
abbrev bodyOut (nv : Nat) : Command := .sequence (.primitive (.declare i32 true (colsE nv))) (.sequence (innerFor nv) Sk)
abbrev outerFor (nv : Nat) : Command := forStmtB nv 2 1 (bodyOut nv)
abbrev rowsE : NExpr := .cast i32 (.size (.vector (.integer s64)) (.local 0))
abbrev prog2 (nv : Nat) : Command :=
  .sequence (.primitive (.declare s64 true (.cast s64 (.literal i32 0))))
    (.sequence (.primitive (.declare i32 true rowsE))
      (.sequence (outerFor nv) (.sequence (.primitive (.ret (.variable s64 (nv + 0)))) Sk)))

theorem body_eq2 : Proofs.Vector2dSumInstance.vector2d_sum_std_vector_std_vector_long_long.body = prog2 1 := rfl


theorem readE_val (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = s64)
    (vv : Nat → List Int) (P cells : List Cell) (t j : Nat) (r : List Int) (x : Int)
    (ht : cells[2]? = some (ci t)) (hj : cells[4]? = some (ci j)) (htl : t < M31) (hjl : j < M31)
    (hwr : t < mv.wrows 0) (hr : vv (rowKey 0 t) = r) (hx : r[j]? = some x) (hxv : s64.valid x = true) :
    vdenN mv vv (penvN mv.nv (gS P cells)) (readE mv.nv) = some x := by
  have e1 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + 2) t
    (gSM_env mv.nv P cells 2 (ci t) ht (BellmanFordExec.i32_valid_nat t htl)) htl
  have e2 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + 4) j
    (gSM_env mv.nv P cells 4 (ci j) hj (BellmanFordExec.i32_valid_nat j hjl)) hjl
  simp only [readE, vdenN]
  rw [if_pos ⟨by omega, hfl, hty.symm, hty.symm, rfl, rfl⟩]
  rw [iIdx, jIdx] 
  rw [e1, Option.bind_some, e2, Option.bind_some, if_pos ⟨Int.natCast_nonneg t, by rw [Int.toNat_natCast]; exact hwr⟩,
    Int.toNat_natCast, hr]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg j), Int.toNat_natCast, hx, Option.bind_some, hty, if_pos hxv]


theorem body_in_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = s64)
    (vv : Nat → List Int) (P : List Cell) (fu : Nat) (a : Int) (R t j cols : Nat) (r : List Int)
    (x : Int) (htl : t < M31) (hjl : j < M31) (hwr : t < mv.wrows 0) (hr : vv (rowKey 0 t) = r) (hx : r[j]? = some x) (hxv : s64.valid x = true)
    (hav : s64.valid a = true) (hsum : s64.valid (a + x) = true) :
    ∃ res : PRM, pexecM mv fu (bodyIn mv.nv) (gS P ([cs64 a, ci R, ci t, ci cols] ++ [ci j])) vv = some res ∧
      res.ret = none ∧ res.ps = gS P ([cs64 (a + x), ci R, ci t, ci cols] ++ [ci j] ++ [cs64 x]) ∧ res.vv = vv ∧
      res.cost ≤ 30 ∧ res.need ≤ P.length + 40 ∧ res.wk = 0 := by
  have hv := readE_val mv hnv hfl hty vv P ([cs64 a, ci R, ci t, ci cols] ++ [ci j]) t j r x rfl rfl htl hjl hwr hr hx hxv
  have d1 := gSM_decl mv P ([cs64 a, ci R, ci t, ci cols] ++ [ci j]) vv s64 (readE mv.nv) x x hv (conv_signed s64 rfl rfl x hxv)
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have ea := gSM_env mv.nv P ([cs64 a, ci R, ci t, ci cols] ++ [ci j] ++ [cs64 x]) 0 (cs64 a) rfl hav
  have ex := gSM_env mv.nv P ([cs64 a, ci R, ci t, ci cols] ++ [ci j] ++ [cs64 x]) 5 (cs64 x) rfl hxv
  have hv2 : vdenN mv vv (penvN mv.nv (gS P ([cs64 a, ci R, ci t, ci cols] ++ [ci j] ++ [cs64 x]))) 
      (.binary s64 .add (.variable s64 (mv.nv + 0)) (.variable s64 (mv.nv + 5))) = some (a + x) := by
    rw [vdenN_scalar _ _ _ _ rfl, den_binary, den_variable, ea, Option.bind_some, den_variable, ex, Option.bind_some]
    exact (by simpa [binaryValue] using conv_signed s64 rfl rfl (a + x) hsum)
  have d2 := gSM_assign mv P ([cs64 a, ci R, ci t, ci cols] ++ [ci j] ++ [cs64 x]) vv 0 (by simp) s64
    (.binary s64 .add (.variable s64 (mv.nv + 0)) (.variable s64 (mv.nv + 5))) (a + x) (a + x) hv2 (cs64 a) rfl rfl hav
    (conv_signed s64 rfl rfl (a + x) hsum)
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  have hset : ([cs64 a, ci R, ci t, ci cols] ++ [ci j] ++ [cs64 x]).set 0 ⟨s64, a + x⟩ =
      [cs64 (a + x), ci R, ci t, ci cols] ++ [ci j] ++ [cs64 x] := rfl
  rw [hset] at q2
  have q3 := seqM_some q2 rfl (pexecM_skip mv fu _ vv)
  have q4 := seqM_some q1 rfl q3
  refine ⟨_, q4, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [vwp, NExpr.nodes]
  · simp [vwp, NExpr.nodes, gS_mem_len, gS_bs_len]


theorem cols_val (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = s64)
    (vv : Nat → List Int) (P cells : List Cell) (t : Nat) (r : List Int)
    (ht : cells[2]? = some (ci t)) (htl : t < M31) (hwr : t < mv.wrows 0) (hr : vv (rowKey 0 t) = r) (hl : r.length < 2147483648) :
    vdenN mv vv (penvN mv.nv (gS P cells)) (colsE mv.nv) = some (r.length : Int) := by
  have e1 := cidx_den (penvN mv.nv (gS P cells)) (mv.nv + 2) t
    (gSM_env mv.nv P cells 2 (ci t) ht (BellmanFordExec.i32_valid_nat t htl)) htl
  have hsz : vdenN mv vv (penvN mv.nv (gS P cells)) (.size (.integer s64) (.row (.local 0) (.integer s64) (iIdx mv.nv))) =
      some (r.length : Int) := by
    simp only [vdenN]
    rw [if_pos ⟨by omega, hfl, hty.symm, hty.symm, rfl⟩]
    rw [iIdx, e1, Option.bind_some, if_pos ⟨Int.natCast_nonneg t, by rw [Int.toNat_natCast]; exact hwr⟩, Int.toNat_natCast, hr]
  have hc := conv_signed i32 rfl rfl (r.length : Int) (validN _ hl)
  have hcast : vdenN mv vv (penvN mv.nv (gS P cells)) (colsE mv.nv) =
      (vdenN mv vv (penvN mv.nv (gS P cells)) (.size (.integer s64) (.row (.local 0) (.integer s64) (iIdx mv.nv)))).bind
        i32.convert := by
    simp only [colsE]; rw [vdenN]
  rw [hcast, hsz, Option.bind_some]
  exact hc

theorem take_sum_succ (r : List Int) (j : Nat) (x : Int) (h : r[j]? = some x) :
    ((r.take (j + 1)).sum) = (r.take j).sum + x := by
  rw [List.take_succ, h]
  simp [List.sum_append]

theorem inner_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = s64)
    (vv : Nat → List Int) (P : List Cell) (fu : Nat) (a : Int) (R t : Nat) (r : List Int)
    (htl : t < M31) (hwr : t < mv.wrows 0) (hr : vv (rowKey 0 t) = r) (hl : r.length < 2147483647)
    (hvalid : ∀ x ∈ r, s64.valid x = true) (hav : ∀ j, j ≤ r.length → s64.valid (a + (r.take j).sum) = true)
    (hfu : r.length + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (innerFor mv.nv) (gS P [cs64 a, ci R, ci t, ci r.length]) vv = some res ∧
      res.ret = none ∧ res.ps = gS P [cs64 (a + r.sum), ci R, ci t, ci r.length] ∧ res.vv = vv ∧
      res.cost ≤ 50 * r.length + 40 ∧ res.need ≤ P.length + 40 ∧ res.wk = 0 := by
  have hlt : r.length < 2147483647 := hl
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 4 3 r.length (by omega) hlt (bodyIn mv.nv)
    (fun j vv' C => vv' = vv ∧ C = [cs64 (a + (r.take j).sum), ci R, ci t, ci r.length]) 30 40 0 0 (by omega)
    (by
      intro j vv' C fu' hj hCl hC3 hIv hfu
      obtain ⟨hvv, hCe⟩ := hIv
      subst hvv
      subst hCe
      have hjr : j < r.length := hj
      obtain ⟨x, hx⟩ : ∃ x, r[j]? = some x := ⟨r[j], by simp [hjr]⟩
      have hjM : j < M31 := by have : r.length < 2147483647 := hl; show j < 2147483648; omega
      have hxv : s64.valid x = true := hvalid x (List.mem_of_getElem? hx)
      have hs1 := hav (j + 1) (by omega)
      rw [take_sum_succ r j x hx, ← Int.add_assoc] at hs1
      obtain ⟨r2, hr2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := body_in_exec mv hnv hfl hty vv' P fu' (a + (r.take j).sum) R t j
        r.length r x htl hjM hwr hr hx hxv (hav j (by omega)) hs1
      refine ⟨r2, [cs64 x], [cs64 (a + (r.take j).sum + x), ci R, ci t, ci r.length], hr2, hret2, hps2, rfl, rfl, ?_, hc2, hn2, hw2.le⟩
      refine ⟨hvv2, ?_⟩
      rw [take_sum_succ r j x hx, Int.add_assoc])
    vv [cs64 (a + (r.take 0).sum), ci R, ci t, ci r.length] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hCe⟩ := hI
  have hfull : r.take r.length = r := List.take_length
  have h0 : (r.take 0).sum = 0 := by simp
  rw [hfull] at hCe
  subst hCe
  rw [h0, Int.add_zero] at hr'
  refine ⟨res, hr', hret, hps, hvv, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega


theorem vwp_colsE (nv : Nat) : vwp (colsE nv) = (7, 7) := by
  have h : (colsE nv).scalarOnly = false := rfl
  simp [colsE, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]

/-- The sum of the rows `rows`. -/
def sumRows (rows : List (List Int)) : Int := (rows.map List.sum).sum

theorem sumRows_succ (rows : List (List Int)) (t : Nat) (r : List Int) (h : rows[t]? = some r) :
    sumRows (rows.take (t + 1)) = sumRows (rows.take t) + r.sum := by
  unfold sumRows
  rw [List.take_succ, h]
  simp [List.sum_append]

theorem body_out_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = s64)
    (vv : Nat → List Int) (P : List Cell) (fu : Nat) (a : Int) (R t : Nat) (r : List Int)
    (htl : t < M31) (hwr : t < mv.wrows 0) (hr : vv (rowKey 0 t) = r) (hl : r.length < 2147483647)
    (hvalid : ∀ x ∈ r, s64.valid x = true) (hav : ∀ j, j ≤ r.length → s64.valid (a + (r.take j).sum) = true)
    (hfu : r.length + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (bodyOut mv.nv) (gS P ([cs64 a, ci R] ++ [ci t])) vv = some res ∧
      res.ret = none ∧ res.ps = gS P ([cs64 (a + r.sum), ci R] ++ [ci t] ++ [ci r.length]) ∧ res.vv = vv ∧
      res.cost ≤ 50 * r.length + 80 ∧ res.need ≤ P.length + 60 ∧ res.wk = 0 := by
  have hl' : r.length < 2147483648 := by omega
  have hv := cols_val mv hnv hfl hty vv P ([cs64 a, ci R] ++ [ci t]) t r rfl htl hwr hr hl'
  have d1 := gSM_decl mv P ([cs64 a, ci R] ++ [ci t]) vv i32 (colsE mv.nv) (r.length : Int) (r.length : Int) hv
    (conv_signed i32 rfl rfl _ (validN _ hl'))
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  obtain ⟨r2, hr2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := inner_exec mv hnv hfl hty vv P fu a R t r htl hwr hr hl hvalid hav hfu
  have hq : ([cs64 a, ci R] ++ [ci t] ++ [(⟨i32, (r.length : Int)⟩ : Cell)]) = [cs64 a, ci R, ci t, ci r.length] := rfl
  rw [hq] at q1
  have q2 := seqM_some hr2 hret2 (pexecM_skip mv fu _ _)
  rw [hps2, hvv2] at q2
  have q3 := seqM_some q1 rfl q2
  refine ⟨_, q3, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_colsE]
    omega
  · simp [vwp_colsE, gS_mem_len, gS_bs_len]
    omega
  · simp [hw2]


theorem outer_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = s64) (rows : List (List Int))
    (vv : Nat → List Int) (hw : mv.wrows 0 = rows.length) (hvv : ∀ i (h : i < rows.length), vv (rowKey 0 i) = rows[i])
    (P : List Cell) (fu : Nat) (L : Nat)
    (hR : rows.length < 2147483647) (hL : ∀ r ∈ rows, r.length ≤ L) (hL' : L < 2147483647)
    (hvalid : ∀ r ∈ rows, ∀ x ∈ r, s64.valid x = true)
    (hOK : ∀ t j r, rows[t]? = some r → j ≤ r.length → s64.valid (sumRows (rows.take t) + (r.take j).sum) = true)
    (hfu : L + 1 + rows.length + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (outerFor mv.nv) (gS P [cs64 0, ci rows.length]) vv = some res ∧
      res.ret = none ∧ res.ps = gS P [cs64 (sumRows rows), ci rows.length] ∧ res.vv = vv ∧
      res.cost ≤ (50 * L + 100) * rows.length + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk = 0 := by
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 2 1 rows.length (by omega) hR (bodyOut mv.nv)
    (fun t vv' C => vv' = vv ∧ C = [cs64 (sumRows (rows.take t)), ci rows.length]) (50 * L + 80) 60 0 (L + 1) (by omega)
    (by
      intro t vv' C fu' ht hCl hC1 hIv hfu'
      obtain ⟨hvvE, hCe⟩ := hIv
      subst hCe
      have htr : t < rows.length := ht
      obtain ⟨r, hr⟩ : ∃ r, rows[t]? = some r := ⟨rows[t], by simp [htr]⟩
      have hrm : r ∈ rows := List.mem_of_getElem? hr
      have htM : t < M31 := by have : rows.length < 2147483647 := hR; show t < 2147483648; omega
      have hrl : r.length ≤ L := hL r hrm
      obtain ⟨r2, hr2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := body_out_exec mv hnv hfl hty vv' P fu'
        (sumRows (rows.take t)) rows.length t r htM (by rw [hw]; exact htr)
        (by rw [hvvE, hvv t htr]; simpa [htr] using hr) (by omega) (hvalid r hrm) (fun j hj => hOK t j r hr hj) (by omega)
      refine ⟨r2, [ci r.length], [cs64 (sumRows (rows.take t) + r.sum), ci rows.length], hr2, hret2, hps2, rfl, rfl, ?_,
        by omega, hn2, hw2.le⟩
      refine ⟨hvv2.trans hvvE, ?_⟩
      rw [sumRows_succ rows t r hr])
    vv [cs64 (sumRows (rows.take 0)), ci rows.length] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvvF, hCe⟩ := hI
  have hfull : rows.take rows.length = rows := List.take_length
  have h0 : sumRows (rows.take 0) = 0 := by simp [sumRows]
  rw [hfull] at hCe
  subst hCe
  rw [h0] at hr'
  refine ⟨res, hr', hret, hps, hvvF, hc, hnd, ?_⟩
  omega


theorem zero_val (mv : MV) (vv : Nat → List Int) (ps : PS) :
    vdenN mv vv (penvN mv.nv ps) (.cast s64 (.literal i32 0)) = some 0 := by
  rw [vdenN_scalar _ _ _ _ rfl]
  have a : i32.valid 0 = true := by simp [Ty.valid]
  have b : s64.valid 0 = true := by simp [Ty.valid]
  simp [NExpr.denote, a, Ty.convert_of_valid _ _ b]

theorem rowsE_val (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = s64) (rows : List (List Int))
    (hw : mv.wrows 0 = rows.length) (vv : Nat → List Int) (ps : PS) (hR : rows.length < 2147483648) :
    vdenN mv vv (penvN mv.nv ps) rowsE = some (rows.length : Int) := by
  have hsz : vdenN mv vv (penvN mv.nv ps) (.size (.vector (.integer s64)) (.local 0)) = some (rows.length : Int) := by
    simp only [vdenN]
    rw [if_pos ⟨by omega, hfl, hty.symm⟩, hw]
  have hcast : vdenN mv vv (penvN mv.nv ps) rowsE =
      (vdenN mv vv (penvN mv.nv ps) (.size (.vector (.integer s64)) (.local 0))).bind i32.convert := by
    simp only [rowsE]; rw [vdenN]
  rw [hcast, hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hR)

theorem vwp_rowsE : vwp rowsE = (4, 4) := by
  simp [rowsE, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]

theorem vwp_var (ty : Ty) (k : Nat) : vwp (.variable ty k) = (1, 1) := by simp [vwp, NExpr.nodes]
theorem vwp_zero : vwp (.cast s64 (.literal i32 0)) = (2, 2) := by simp [vwp, NExpr.nodes, NExpr.scalarOnly]

theorem seqM_ret_after {mv : MV} {fu : Nat} {a b : Command} {ps : PS} {vv : Nat → List Int} {r r2 : PRM}
    (h1 : pexecM mv fu a ps vv = some r) (hr : r.ret = none) (h2 : pexecM mv fu b r.ps r.vv = some r2) :
    pexecM mv fu (.sequence a b) ps vv = some ⟨r2.ps,r2.vv,r2.ret,r.cost+r2.cost,max r.need r2.need,r.wk+r2.wk⟩ :=
  seqM_some h1 hr h2

theorem prog_exec (mv : MV) (hnv : mv.nv = 1) (hfl : mv.flat 0 = false) (hty : mv.ty 0 = s64) (rows : List (List Int))
    (vv : Nat → List Int) (hw : mv.wrows 0 = rows.length) (hvv : ∀ i (h : i < rows.length), vv (rowKey 0 i) = rows[i])
    (P : List Cell) (fu : Nat) (L : Nat)
    (hR : rows.length < 2147483647) (hL : ∀ r ∈ rows, r.length ≤ L) (hL' : L < 2147483647)
    (hvalid : ∀ r ∈ rows, ∀ x ∈ r, s64.valid x = true)
    (hOK : ∀ t j r, rows[t]? = some r → j ≤ r.length → s64.valid (sumRows (rows.take t) + (r.take j).sum) = true)
    (hfin : s64.valid (sumRows rows) = true) (hfu : L + 1 + rows.length + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (prog2 mv.nv) (gS P []) vv = some res ∧ res.ret = some (sumRows rows) ∧ res.vv = vv ∧
      res.ps = gS P [cs64 (sumRows rows), ci rows.length] ∧
      res.cost ≤ (50 * L + 100) * rows.length + 60 ∧ res.need ≤ P.length + 60 ∧ res.wk = 0 := by
  have hR' : rows.length < 2147483648 := by omega
  have d1 := gSM_decl mv P [] vv s64 (.cast s64 (.literal i32 0)) 0 0 (zero_val mv vv _) (conv_signed s64 rfl rfl 0 (by simp [Ty.valid]))
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have d2 := gSM_decl mv P [(⟨s64, 0⟩ : Cell)] vv i32 rowsE (rows.length : Int) (rows.length : Int)
    (rowsE_val mv hnv hfl hty rows hw vv _ hR') (conv_signed i32 rfl rfl _ (validN _ hR'))
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  obtain ⟨r3, hr3, hret3, hps3, hvv3, hc3, hn3, hw3⟩ := outer_exec mv hnv hfl hty rows vv hw hvv P fu L hR hL hL' hvalid hOK hfu
  have hcell : ([] ++ [(⟨s64, 0⟩ : Cell)] ++ [(⟨i32, (rows.length : Int)⟩ : Cell)]) = [cs64 0, ci rows.length] := rfl
  have hcell1 : ([] ++ [(⟨s64, 0⟩ : Cell)]) = [(⟨s64, 0⟩ : Cell)] := rfl
  have e1 := gSM_env mv.nv P [cs64 (sumRows rows), ci rows.length] 0 (cs64 (sumRows rows)) rfl hfin
  have hret : vdenM mv vv (penvN mv.nv (gS P [cs64 (sumRows rows), ci rows.length])) (.variable s64 (mv.nv + 0)) =
      some (sumRows rows) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e1
  have r4 := pstmtM_ret_ok mv (gS P [cs64 (sumRows rows), ci rows.length]) vv _ _ hret
  have q4 := seqM_ret (mv := mv) (fu := fu) (b := Sk) (a := .primitive (.ret (.variable s64 (mv.nv + 0)))) (by rw [pexecM_prim, r4]) rfl
  have A := seqM_ret_after hr3 hret3 (by rw [hps3, hvv3]; exact q4)
  have q2' : pexecM mv fu (.primitive (.declare i32 true rowsE)) (gS P [(⟨s64, 0⟩ : Cell)]) vv = _ := q2
  have B := seqM_some q2' rfl A
  have q1' : pexecM mv fu (.primitive (.declare s64 true (.cast s64 (.literal i32 0)))) (gS P []) vv = _ := q1
  have C := seqM_some q1' rfl B
  refine ⟨_, C, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_rowsE, vwp_var, vwp_zero]
    omega
  · simp [vwp_rowsE, vwp_var, vwp_zero, gS_mem_len, gS_bs_len]
    omega
  · simp [hw3]

end Proofs.Vector2dSumExec
