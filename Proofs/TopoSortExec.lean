import Proofs.ForLoopB
import Proofs.TopoSortMath
import Proofs.BellmanFordExec
import Proofs.Generated.TopologicalSort

namespace Proofs.TopoSortExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getM vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false getD_mem)

/-! ### The program: variable `nv + c` is the scalar cell `c`
0 = n, 1 = m, 2 = qt, then (loop 1) 2 = p, 3 = w; (loop 2) 3 = i; (loop 3) 3 = qh, 4 = v, 5 = start, 6 = cnt, 7 = d, 8 = w -/

abbrev ix (nv c : Nat) : NExpr := .cast u64 (.variable i32 (nv + c))
abbrev lit1 : NExpr := .literal i32 1
abbrev lit0 : NExpr := .literal i32 0
-- loop 1: `int w = target[p]; indeg[w] = indeg[w] + 1;`
abbrev l1W (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 1) (ix nv 2))
abbrev l1Wr (nv : Nat) : NStmt :=
  .write (.local 2) i32 (ix nv 3) (.binary i32 .add (.read i32 (.local 2) (ix nv 3)) lit1)
abbrev B1 (nv : Nat) : Command := .sequence (.primitive (l1W nv)) (.sequence (.primitive (l1Wr nv)) Sk)
-- loop 2: `if (indeg[i] == 0) { order[qt] = i; qt = qt + 1; }`
abbrev c2 (nv : Nat) : NExpr := .binary bT .eq (.read i32 (.local 2) (ix nv 3)) lit0
abbrev w2 (nv : Nat) : NStmt := .write (.local 3) i32 (ix nv 2) (.variable i32 (nv + 3))
abbrev a2 (nv : Nat) : NStmt := .assign (nv + 2) i32 (.binary i32 .add (.variable i32 (nv + 2)) lit1)
abbrev Y2 (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (w2 nv)) (.sequence (.primitive (a2 nv)) Sk))) Sk
abbrev B2 (nv : Nat) : Command := .sequence (.branch (c2 nv) (Y2 nv) Sk) Sk
-- loop 3
abbrev dV (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 3) (ix nv 3))
abbrev dS (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 0) (ix nv 4))
abbrev dC (nv : Nat) : NStmt :=
  .declare i32 true (.binary i32 .sub (.read i32 (.local 0) (.cast u64 (.binary i32 .add (.variable i32 (nv + 4)) lit1)))
    (.variable i32 (nv + 5)))
abbrev dW (nv : Nat) : NStmt :=
  .declare i32 true (.read i32 (.local 1) (.cast u64 (.binary i32 .add (.variable i32 (nv + 5)) (.variable i32 (nv + 7)))))
abbrev wI (nv : Nat) : NStmt :=
  .write (.local 2) i32 (ix nv 8) (.binary i32 .sub (.read i32 (.local 2) (ix nv 8)) lit1)
abbrev c4 (nv : Nat) : NExpr := .binary bT .eq (.read i32 (.local 2) (ix nv 8)) lit0
abbrev w4 (nv : Nat) : NStmt := .write (.local 3) i32 (ix nv 2) (.variable i32 (nv + 8))
abbrev Y4 (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (w4 nv)) (.sequence (.primitive (a2 nv)) Sk))) Sk
abbrev Xin (nv : Nat) : Command :=
  .sequence (.primitive (dW nv)) (.sequence (.primitive (wI nv)) (.sequence (.branch (c4 nv) (Y4 nv) Sk) Sk))
abbrev Z3 (nv : Nat) : Command :=
  .sequence (.primitive (dV nv)) (.sequence (.primitive (dS nv)) (.sequence (.primitive (dC nv))
    (.sequence (forStmtB nv 7 6 (Xin nv)) Sk)))
abbrev c3 (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 3)) (.variable i32 (nv + 2))
abbrev B3 (nv : Nat) : Command := .sequence (.branch (c3 nv) (.sequence (.scope (Z3 nv)) Sk) Sk) Sk
abbrev declM : NStmt := .declare i32 true (.cast i32 (.size (.integer i32) (.local 1)))
abbrev bodyTS (nv : Nat) : Command :=
  .sequence (.primitive declM) (.sequence (forStmtB nv 2 1 (B1 nv)) (.sequence (.primitive (.declare i32 true lit0))
    (.sequence (forStmtB nv 3 0 (B2 nv)) (.sequence (forStmtB nv 3 0 (B3 nv))
      (.sequence (.primitive (.ret (.variable i32 (nv + 2)))) Sk)))))

theorem body_eqTS : Proofs.TopoInstance.topological_sort.body = bodyTS 4 := rfl


/-- The contents of the four vectors `head`, `target`, `indeg`, `order`. -/
def VT (H T I O : List Nat) : Nat → List Int := fun k =>
  if k = 0 then H.map (fun x : Nat => (x : Int)) else if k = 1 then T.map (fun x : Nat => (x : Int))
  else if k = 2 then I.map (fun x : Nat => (x : Int)) else if k = 3 then O.map (fun x : Nat => (x : Int)) else []

theorem i32v (x : Nat) (h : x < M31) : i32.valid (x : Int) = true := validN x h

theorem VT_get0 (H T I O : List Nat) : VT H T I O 0 = H.map (fun x : Nat => (x : Int)) := by simp [VT]
theorem VT_get1 (H T I O : List Nat) : VT H T I O 1 = T.map (fun x : Nat => (x : Int)) := by simp [VT]
theorem VT_get2 (H T I O : List Nat) : VT H T I O 2 = I.map (fun x : Nat => (x : Int)) := by simp [VT]
theorem VT_get3 (H T I O : List Nat) : VT H T I O 3 = O.map (fun x : Nat => (x : Int)) := by simp [VT]

theorem VT_write2 (H T I O : List Nat) (p x : Nat) :
    upd (VT H T I O) 2 ((VT H T I O 2).set p (x : Int)) = VT H T (I.set p x) O := by
  funext k
  unfold upd VT
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · by_cases h2 : k = 2
      · subst h2; simp [List.map_set]
      · by_cases h3 : k = 3
        · subst h3; simp
        · simp [h0, h1, h2, h3]

theorem VT_write3 (H T I O : List Nat) (p x : Nat) :
    upd (VT H T I O) 3 ((VT H T I O 3).set p (x : Int)) = VT H T I (O.set p x) := by
  funext k
  unfold upd VT
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · by_cases h2 : k = 2
      · subst h2; simp
      · by_cases h3 : k = 3
        · subst h3; simp [List.map_set]
        · simp [h0, h1, h2, h3]

theorem getD_lt (l : List Nat) (j : Nat) (h : j < l.length) : l.getD j 0 = l[j] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem natList_get (l : List Nat) (j : Nat) (h : j < l.length) :
    (l.map (fun x : Nat => (x : Int)))[j]? = some ((l.getD j 0 : Nat) : Int) := by
  simp [List.getElem?_map, h, List.getD_eq_getElem?_getD]


theorem one_den (env : Nat → Ty → Option Int) : (NExpr.literal i32 1).denote env = some 1 := by
  rw [den_literal, if_pos (show i32.valid 1 = true from rfl)]

theorem zero_den (env : Nat → Ty → Option Int) : (NExpr.literal i32 0).denote env = some 0 := by
  rw [den_literal, if_pos (show i32.valid 0 = true from rfl)]

/-- `int w = target[p]; indeg[w] = indeg[w] + 1;` -/
theorem b1_body (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = i32) (H T I O : List Nat) (P : List Cell)
    (n m t : Nat) (hn : n < M31) (hm : m < M31) (ht : t < m) (hTl : T.length = m) (hTn : ∀ x ∈ T, x < n)
    (hIl : I.length = n) (hIv : I.getD (T.getD t 0) 0 + 1 < M31) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (B1 mv.nv) (gS P [ci n, ci m, ci t]) (VT H T I O) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, ci m, ci t, ci (T.getD t 0)] ∧
      r.vv = VT H T (I.set (T.getD t 0) (I.getD (T.getD t 0) 0 + 1)) O ∧
      r.cost ≤ 100 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 1 := by
  have hw : T.getD t 0 < n := by
    have : T.getD t 0 = T[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, ht]
    rw [this]; exact hTn _ (List.getElem_mem _)
  have E2 := envs mv P [ci n, ci m, ci t] 2 (ci t) rfl (i32v t (by omega))
  have vr := rdM_val mv (VT H T I O) (penvN mv.nv (gS P [ci n, ci m, ci t])) 1 (by omega) i32 (hty 1).symm
    (ix mv.nv 2) rfl rfl t (cidx_den _ (mv.nv + 2) t E2 (by omega)) ((T.getD t 0 : Nat) : Int)
    (by rw [VT_get1]; exact natList_get T t (by omega)) (by rw [hty]; exact i32v _ (by omega))
  have d1 := gSM_decl mv P [ci n, ci m, ci t] (VT H T I O) i32 _ _ _ vr
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q1 := (pexecM_prim mv fu (l1W mv.nv) _ _).trans d1
  have E3 := envs mv P [ci n, ci m, ci t, ci (T.getD t 0)] 3 (ci (T.getD t 0)) rfl (i32v _ (by omega))
  have hp : vdenM mv (VT H T I O) (penvN mv.nv (gS P [ci n, ci m, ci t, ci (T.getD t 0)])) (ix mv.nv 3) =
      some ((T.getD t 0 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 3) _ E3 (by omega)
  have vi := rdM_val mv (VT H T I O) (penvN mv.nv (gS P [ci n, ci m, ci t, ci (T.getD t 0)])) 2 (by omega) i32 (hty 2).symm
    (ix mv.nv 3) rfl rfl (T.getD t 0) (cidx_den _ (mv.nv + 3) _ E3 (by omega)) ((I.getD (T.getD t 0) 0 : Nat) : Int)
    (by rw [VT_get2]; exact natList_get I _ (by omega)) (by rw [hty]; exact i32v _ (by
      have : I.getD (T.getD t 0) 0 + 1 < M31 := hIv; omega))
  have hx : vdenM mv (VT H T I O) (penvN mv.nv (gS P [ci n, ci m, ci t, ci (T.getD t 0)]))
      (.binary i32 .add (.read i32 (.local 2) (ix mv.nv 3)) lit1) = some ((I.getD (T.getD t 0) 0 + 1 : Nat) : Int) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vi, Option.bind_some, vdenM_scalar _ _ _ _ rfl, one_den, Option.bind_some]
    have : binaryValue .add ((I.getD (T.getD t 0) 0 : Nat) : Int) 1 = ((I.getD (T.getD t 0) 0 + 1 : Nat) : Int) := by
      show _ + _ = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ hIv)
  have w := pstmtM_write_ok mv (gS P [ci n, ci m, ci t, ci (T.getD t 0)]) (VT H T I O) 2 (by omega) (ix mv.nv 3)
    (.binary i32 .add (.read i32 (.local 2) (ix mv.nv 3)) lit1) ((I.getD (T.getD t 0) 0 + 1 : Nat) : Int) (T.getD t 0) hx hp
    (by rw [VT_get2]; simp [hIl]; exact hw) (by rw [hty]; exact i32v _ hIv)
  rw [hty 2, VT_write2] at w
  have a1 := (pexecM_prim mv fu (l1Wr mv.nv) _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
  have a3 := seqM_some q1 rfl a2
  refine ⟨_, a3, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


/-- The in-degree counters after the first `t` edges were counted. -/
def cntList (n : Nat) (T : List Nat) (t : Nat) : List Nat := (List.range n).map (fun w => (T.take t).count w)

theorem cntList_length (n : Nat) (T : List Nat) (t : Nat) : (cntList n T t).length = n := by simp [cntList]

theorem cntList_getD (n : Nat) (T : List Nat) (t w : Nat) (hw : w < n) : (cntList n T t).getD w 0 = (T.take t).count w := by
  simp [cntList, List.getD_eq_getElem?_getD, hw]

theorem cntList_succ (n : Nat) (T : List Nat) (t : Nat) (ht : t < T.length) (hw : T.getD t 0 < n) :
    cntList n T (t + 1) = (cntList n T t).set (T.getD t 0) ((cntList n T t).getD (T.getD t 0) 0 + 1) := by
  apply List.ext_getElem
  · simp [cntList]
  · intro j h1 h2
    have hj : j < n := by simpa [cntList] using h1
    have hT : T.take (t + 1) = T.take t ++ [T.getD t 0] := by
      rw [List.take_succ]
      simp [List.getD_eq_getElem?_getD, ht]
    rw [List.getElem_set]
    by_cases hjw : T.getD t 0 = j
    · rw [if_pos hjw]
      subst hjw
      rw [cntList_getD n T t _ hw]
      simp [cntList, hT, List.count_append, hw]
    · rw [if_neg hjw]
      have hz : List.count j [T.getD t 0] = 0 := List.count_eq_zero.mpr (by
        simp only [List.mem_singleton]; intro h; exact hjw h.symm)
      simp only [cntList, List.getElem_map, List.getElem_range, hT, List.count_append, hz, Nat.add_zero]

theorem cnt_le_t (T : List Nat) (t w : Nat) : (T.take t).count w ≤ t := by
  have := List.count_le_length (a := w) (l := T.take t)
  have h2 := List.length_take_le t T
  omega

/-- Loop 1: counting the in-degrees. -/
theorem l1_loop (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = i32) (H T O : List Nat) (P : List Cell)
    (n m : Nat) (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hTl : T.length = m) (hTn : ∀ x ∈ T, x < n)
    (fu : Nat) (hfu : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 2 1 (B1 mv.nv)) (gS P [ci n, ci m]) (VT H T (List.replicate n 0) O) = some res ∧
      res.ps = gS P [ci n, ci m] ∧ res.vv = VT H T (cntList n T m) O ∧ res.ret = none ∧ res.cost ≤ 120 * m + 30 ∧
      res.need ≤ P.length + 60 ∧ res.wk ≤ m := by
  have hrep : List.replicate n 0 = cntList n T 0 := by
    apply List.ext_getElem
    · simp [cntList]
    · intro j h1 h2
      simp [cntList]
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 2 1 m (by omega) hm2 (B1 mv.nv)
    (fun t vv C => vv = VT H T (cntList n T t) O ∧ C = [ci n, ci m]) 100 60 1 0 (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hw : T.getD t 0 < n := by
        have : T.getD t 0 = T[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, ht]
        rw [this]; exact hTn _ (List.getElem_mem _)
      have hIv : (cntList n T t).getD (T.getD t 0) 0 + 1 < M31 := by
        rw [cntList_getD n T t _ hw]
        have := cnt_le_t T t (T.getD t 0)
        have : t + 1 ≤ m := by omega
        have : m < M31 := hm
        omega
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := b1_body mv hnv hty H T (cntList n T t) O P n m t hn hm ht hTl hTn
        (cntList_length n T t) hIv fu
      refine ⟨r, [ci (T.getD t 0)], [ci n, ci m], hr, hret, hps, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      rw [hvv, cntList_succ n T t (by omega) hw])
    (VT H T (cntList n T 0) O) [ci n, ci m] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI
  subst hC
  rw [hrep]
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega


theorem eq_conv (x y : Int) : bT.convert (binaryValue .eq x y) = some (if x = y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

/-- `if (indeg[i] == 0) { order[qt] = i; qt = qt + 1; }` -/
theorem b2_body (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = i32) (H T I O : List Nat) (P : List Cell)
    (n m qt t : Nat) (hn : n < M31) (hm : m < M31) (hqt : qt < M31) (ht : t < n) (hIl : I.length = n)
    (hIv : I.getD t 0 < M31) (hfire : I.getD t 0 = 0 → qt < O.length ∧ qt + 1 < M31) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (B2 mv.nv) (gS P [ci n, ci m, ci qt, ci t]) (VT H T I O) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, ci m, ci (if I.getD t 0 = 0 then qt + 1 else qt), ci t] ∧
      r.vv = VT H T I (if I.getD t 0 = 0 then O.set qt t else O) ∧
      r.cost ≤ 200 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 1 := by
  have E3 := envs mv P [ci n, ci m, ci qt, ci t] 3 (ci t) rfl (i32v t (by omega))
  have vi := rdM_val mv (VT H T I O) (penvN mv.nv (gS P [ci n, ci m, ci qt, ci t])) 2 (by omega) i32 (hty 2).symm
    (ix mv.nv 3) rfl rfl t (cidx_den _ (mv.nv + 3) t E3 (by omega)) ((I.getD t 0 : Nat) : Int)
    (by rw [VT_get2]; exact natList_get I t (by omega)) (by rw [hty]; exact i32v _ hIv)
  have vc : vdenM mv (VT H T I O) (penvN mv.nv (gS P [ci n, ci m, ci qt, ci t])) (c2 mv.nv) =
      some (if ((I.getD t 0 : Nat) : Int) = 0 then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vi, Option.bind_some, vdenM_scalar _ _ _ _ rfl, zero_den, Option.bind_some]
    exact eq_conv _ _
  by_cases h0 : I.getD t 0 = 0
  · obtain ⟨hq, hq1⟩ := hfire h0
    have hc1 : (if ((I.getD t 0 : Nat) : Int) = 0 then (1 : Int) else 0) = 1 := by rw [h0]; simp
    rw [hc1] at vc
    -- the write
    have E2 := envs mv P [ci n, ci m, ci qt, ci t] 2 (ci qt) rfl (i32v qt hqt)
    have hp : vdenM mv (VT H T I O) (penvN mv.nv (gS P [ci n, ci m, ci qt, ci t])) (ix mv.nv 2) = some (qt : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact cidx_den _ (mv.nv + 2) qt E2 (by omega)
    have hx : vdenM mv (VT H T I O) (penvN mv.nv (gS P [ci n, ci m, ci qt, ci t])) (.variable i32 (mv.nv + 3)) = some (t : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3
    have w := pstmtM_write_ok mv (gS P [ci n, ci m, ci qt, ci t]) (VT H T I O) 3 (by omega) (ix mv.nv 2)
      (.variable i32 (mv.nv + 3)) (t : Int) qt hx hp (by rw [VT_get3]; simpa using hq) (by rw [hty]; exact i32v t (by omega))
    rw [hty 3, VT_write3] at w
    have a1 := (pexecM_prim mv fu (w2 mv.nv) _ _).trans w
    -- the assignment
    have hq' : vdenM mv (VT H T I (O.set qt t)) (penvN mv.nv (gS P [ci n, ci m, ci qt, ci t]))
        (.binary i32 .add (.variable i32 (mv.nv + 2)) lit1) = some ((qt + 1 : Nat) : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E2, Option.bind_some, one_den, Option.bind_some]
      have : binaryValue .add (qt : Int) 1 = ((qt + 1 : Nat) : Int) := by
        show (qt : Int) + 1 = _; push_cast; rfl
      rw [this]
      exact conv_signed i32 rfl rfl _ (i32v _ hq1)
    have as := gSM_assign mv P [ci n, ci m, ci qt, ci t] (VT H T I (O.set qt t)) 2 (by simp) i32 _ _ _ hq' (ci qt) rfl rfl
      (i32v qt hqt) (conv_signed i32 rfl rfl _ (i32v _ hq1))
    have a2 := (pexecM_prim mv fu (a2 mv.nv) _ _).trans as
    have a3 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
    have a4 := seqM_some a1 rfl a3
    have a5 := pexecM_scope mv fu _ _ _ _ a4
    have tk := gS_takeC P [ci n, ci m, ci qt, ci t] ([ci n, ci m, ci qt, ci t].set 2 ⟨i32, ((qt + 1 : Nat) : Int)⟩) [] rfl
    simp only [List.append_nil] at tk
    simp only [tk] at a5
    have a6 := seqM_some a5 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu (c2 mv.nv) (Y2 mv.nv) Sk _ _ 1 vc (by decide) _ a6
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos h0]; rfl
    · rw [if_pos h0]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp
  · have hc0 : (if ((I.getD t 0 : Nat) : Int) = 0 then (1 : Int) else 0) = 0 := by
      have : ((I.getD t 0 : Nat) : Int) ≠ 0 := by omega
      rw [if_neg this]
    rw [hc0] at vc
    have b1 := pexecM_branch_false mv fu (c2 mv.nv) (Y2 mv.nv) Sk _ _ vc _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg h0]
    · rw [if_neg h0]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp


/-- The vertices below `t` without predecessors. -/
def zs (I : List Nat) (t : Nat) : List Nat := (List.range t).filter (fun w => I.getD w 0 = 0)

theorem zs_succ (I : List Nat) (t : Nat) :
    zs I (t + 1) = zs I t ++ (if I.getD t 0 = 0 then [t] else []) := by
  unfold zs
  rw [List.range_succ, List.filter_append]
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : I[t]?.getD 0 = 0
  · simp [h]
  · simp [h]

theorem zs_len (I : List Nat) (t : Nat) : (zs I t).length ≤ t := by
  unfold zs
  have := List.length_filter_le (fun w => decide (I.getD w 0 = 0)) (List.range t)
  simpa using this

theorem set_pad (A O : List Nat) (L t : Nat) (hA : A.length = L) (hL : L < O.length) :
    (A ++ O.drop L).set L t = (A ++ [t]) ++ O.drop (L + 1) := by
  have hd : O.drop L = O[L] :: O.drop (L + 1) := List.drop_eq_getElem_cons hL
  rw [List.set_append_right _ _ (by omega), hA, Nat.sub_self, hd, List.append_assoc]
  rfl

/-- Loop 2: enqueue the vertices without predecessors. -/
theorem l2_loop (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = i32) (H T I O : List Nat) (P : List Cell)
    (n m : Nat) (hn : n < M31) (hm : m < M31) (hn2 : n < 2147483647) (hIl : I.length = n) (hIv : ∀ j, I.getD j 0 < M31)
    (hOl : O.length = n) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 3 0 (B2 mv.nv)) (gS P [ci n, ci m, ci 0]) (VT H T I O) = some res ∧
      res.ps = gS P [ci n, ci m, ci (zs I n).length] ∧ res.vv = VT H T I (zs I n ++ O.drop (zs I n).length) ∧
      res.ret = none ∧ res.cost ≤ 220 * n + 30 ∧ res.need ≤ P.length + 60 ∧ res.wk ≤ n := by
  obtain ⟨res, C2, hr', hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 3 0 n (by omega) hn2 (B2 mv.nv)
    (fun t vv C => vv = VT H T I (zs I t ++ O.drop (zs I t).length) ∧ C = [ci n, ci m, ci (zs I t).length]) 200 60 1 0
    (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hzl := zs_len I t
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := b2_body mv hnv hty H T I (zs I t ++ O.drop (zs I t).length) P n m
        (zs I t).length t hn hm (by have : n < M31 := hn; omega) ht hIl (hIv t)
        (fun _ => ⟨by simp [List.length_append, List.length_drop]; omega, by have : n < M31 := hn; omega⟩) fu
      refine ⟨r, [], [ci n, ci m, ci (if I.getD t 0 = 0 then (zs I t).length + 1 else (zs I t).length)], hr, hret,
        hps, rfl, rfl, ⟨?_, ?_⟩, hc, hnd, hwk⟩
      · rw [hvv, zs_succ]
        by_cases h0 : I.getD t 0 = 0
        · rw [if_pos h0, if_pos h0, set_pad _ O _ t rfl (by omega)]
          simp [List.length_append]
        · rw [if_neg h0, if_neg h0]
          simp
      · rw [zs_succ]
        by_cases h0 : I.getD t 0 = 0
        · rw [if_pos h0, if_pos h0]; simp
        · rw [if_neg h0, if_neg h0]; simp)
    (VT H T I (zs I 0 ++ O.drop (zs I 0).length)) [ci n, ci m, ci 0] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI
  subst hC
  refine ⟨res, ?_, hps, hvv, hret, ?_, ?_, ?_⟩
  · exact hr'
  · omega
  · omega
  · omega


open Proofs.TopoSortMath (decr getD_set_same)

/-- The index `(unsigned long long)(a + b)` of two `int` variables. -/
theorem sumIdx_den (env : Nat → Ty → Option Int) (ka kb x y : Nat) (ha : env ka i32 = some (x : Int))
    (hb : env kb i32 = some (y : Int)) (hxy : x + y < M31) :
    (NExpr.cast u64 (.binary i32 .add (.variable i32 ka) (.variable i32 kb))).denote env = some ((x + y : Nat) : Int) := by
  rw [den_cast, den_binary, den_variable, ha, Option.bind_some, den_variable, hb, Option.bind_some]
  have e : binaryValue .add (x : Int) (y : Int) = ((x + y : Nat) : Int) := by
    show (x : Int) + (y : Int) = _; push_cast; rfl
  rw [e, conv_signed i32 rfl rfl _ (i32v _ hxy), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have : x + y < 2147483648 := hxy; omega)

abbrev cells8 (n m qt qh v st cnt d : Nat) : List Cell :=
  [ci n, ci m, ci qt, ci qh, ci v, ci st, ci cnt, ci d]
abbrev cells9 (n m qt qh v st cnt d w : Nat) : List Cell :=
  [ci n, ci m, ci qt, ci qh, ci v, ci st, ci cnt, ci d, ci w]

set_option maxHeartbeats 4000000 in
/-- One iteration of the inner loop: subtract one from the counter of the target and enqueue it when it reaches 0. -/
theorem xin_body (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = i32) (H T I Q O : List Nat) (P : List Cell)
    (n m qh v st cnt d : Nat) (hn : n < M31) (hm : m < M31) (hqh : qh < M31) (hv : v < M31) (hcnt : cnt < M31)
    (hd : d < M31) (hst : st + d < T.length) (hmT : T.length = m) (hIl : I.length = n) (hw : T.getD (st + d) 0 < n)
    (hIpos : 1 ≤ I.getD (T.getD (st + d) 0) 0) (hIv : I.getD (T.getD (st + d) 0) 0 < M31) (hstM : st < M31)
    (hQ : Q.length < M31) (hfire : I.getD (T.getD (st + d) 0) 0 - 1 = 0 → Q.length < O.length ∧ Q.length + 1 < M31)
    (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Xin mv.nv) (gS P (cells8 n m Q.length qh v st cnt d)) (VT H T I O) = some r ∧ r.ret = none ∧
      r.ps = gS P (cells9 n m (decr (T.getD (st + d) 0) (I, Q)).2.length qh v st cnt d (T.getD (st + d) 0)) ∧
      r.vv = VT H T (decr (T.getD (st + d) 0) (I, Q)).1
        (if I.getD (T.getD (st + d) 0) 0 - 1 = 0 then O.set Q.length (T.getD (st + d) 0) else O) ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 80 ∧ r.wk ≤ 2 := by
  generalize hwdef : T.getD (st + d) 0 = w at *
  have E5 := envs mv P (cells8 n m Q.length qh v st cnt d) 5 (ci st) rfl (i32v st hstM)
  have E7 := envs mv P (cells8 n m Q.length qh v st cnt d) 7 (ci d) rfl (i32v d hd)
  have hsum : st + d < M31 := by have : T.length = m := hmT; have : m < M31 := hm; omega
  have hidx : (NExpr.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 5)) (.variable i32 (mv.nv + 7)))).denote
      (penvN mv.nv (gS P (cells8 n m Q.length qh v st cnt d))) = some ((st + d : Nat) : Int) :=
    sumIdx_den _ _ _ st d E5 E7 hsum
  have vr := rdM_val mv (VT H T I O) (penvN mv.nv (gS P (cells8 n m Q.length qh v st cnt d))) 1 (by omega) i32 (hty 1).symm
    (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 5)) (.variable i32 (mv.nv + 7)))) rfl rfl (st + d) hidx
    ((w : Nat) : Int) (by rw [VT_get1]; have := natList_get T (st + d) hst; rw [hwdef] at this; exact this)
    (by rw [hty]; exact i32v _ (by omega))
  have d1 := gSM_decl mv P (cells8 n m Q.length qh v st cnt d) (VT H T I O) i32 _ _ _ vr
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q1 := (pexecM_prim mv fu (dW mv.nv) _ _).trans d1
  -- the decrement
  have E8 := envs mv P (cells9 n m Q.length qh v st cnt d w) 8 (ci w) rfl (i32v w (by omega))
  have hp : vdenM mv (VT H T I O) (penvN mv.nv (gS P (cells9 n m Q.length qh v st cnt d w))) (ix mv.nv 8) = some (w : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + 8) w E8 (by omega)
  have vi := rdM_val mv (VT H T I O) (penvN mv.nv (gS P (cells9 n m Q.length qh v st cnt d w))) 2 (by omega) i32 (hty 2).symm
    (ix mv.nv 8) rfl rfl w (cidx_den _ (mv.nv + 8) w E8 (by omega)) ((I.getD w 0 : Nat) : Int)
    (by rw [VT_get2]; exact natList_get I w (by omega)) (by rw [hty]; exact i32v _ hIv)
  have hx : vdenM mv (VT H T I O) (penvN mv.nv (gS P (cells9 n m Q.length qh v st cnt d w)))
      (.binary i32 .sub (.read i32 (.local 2) (ix mv.nv 8)) lit1) = some ((I.getD w 0 - 1 : Nat) : Int) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vi, Option.bind_some, vdenM_scalar _ _ _ _ rfl, one_den, Option.bind_some]
    have : binaryValue .sub ((I.getD w 0 : Nat) : Int) 1 = ((I.getD w 0 - 1 : Nat) : Int) := by
      show (I.getD w 0 : Int) - 1 = _; omega
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ (by omega))
  have w1 := pstmtM_write_ok mv (gS P (cells9 n m Q.length qh v st cnt d w)) (VT H T I O) 2 (by omega) (ix mv.nv 8)
    (.binary i32 .sub (.read i32 (.local 2) (ix mv.nv 8)) lit1) ((I.getD w 0 - 1 : Nat) : Int) w hx hp
    (by rw [VT_get2]; simp [hIl]; exact hw) (by rw [hty]; exact i32v _ (by omega))
  rw [hty 2, VT_write2] at w1
  have q2 := (pexecM_prim mv fu (wI mv.nv) _ _).trans w1
  -- the test after the decrement
  have hwl : w < I.length := by omega
  have hg : (I.set w (I.getD w 0 - 1)).getD w 0 = I.getD w 0 - 1 := Proofs.TopoSortMath.getD_set_same I w _ hwl
  have vi2 := rdM_val mv (VT H T (I.set w (I.getD w 0 - 1)) O) (penvN mv.nv (gS P (cells9 n m Q.length qh v st cnt d w))) 2
    (by omega) i32 (hty 2).symm (ix mv.nv 8) rfl rfl w (cidx_den _ (mv.nv + 8) w E8 (by omega))
    ((I.getD w 0 - 1 : Nat) : Int)
    (by rw [VT_get2]
        have := natList_get (I.set w (I.getD w 0 - 1)) w (by rw [List.length_set]; exact hwl)
        rw [hg] at this; exact this)
    (by rw [hty]; exact i32v _ (by omega))
  have vc : vdenM mv (VT H T (I.set w (I.getD w 0 - 1)) O) (penvN mv.nv (gS P (cells9 n m Q.length qh v st cnt d w))) (c4 mv.nv) =
      some (if ((I.getD w 0 - 1 : Nat) : Int) = 0 then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vi2, Option.bind_some, vdenM_scalar _ _ _ _ rfl, zero_den, Option.bind_some]
    exact eq_conv _ _
  have E2 := envs mv P (cells9 n m Q.length qh v st cnt d w) 2 (ci Q.length) rfl (i32v _ hQ)
  by_cases hz : I.getD w 0 - 1 = 0
  · obtain ⟨hq, hq1⟩ := hfire hz
    have hc1 : (if ((I.getD w 0 - 1 : Nat) : Int) = 0 then (1 : Int) else 0) = 1 := by rw [hz]; simp
    rw [hc1] at vc
    have hpq : vdenM mv (VT H T (I.set w (I.getD w 0 - 1)) O) (penvN mv.nv (gS P (cells9 n m Q.length qh v st cnt d w)))
        (ix mv.nv 2) = some (Q.length : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact cidx_den _ (mv.nv + 2) _ E2 (by omega)
    have hxw : vdenM mv (VT H T (I.set w (I.getD w 0 - 1)) O) (penvN mv.nv (gS P (cells9 n m Q.length qh v st cnt d w)))
        (.variable i32 (mv.nv + 8)) = some (w : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E8
    have w2' := pstmtM_write_ok mv (gS P (cells9 n m Q.length qh v st cnt d w)) (VT H T (I.set w (I.getD w 0 - 1)) O) 3
      (by omega) (ix mv.nv 2) (.variable i32 (mv.nv + 8)) (w : Int) Q.length hxw hpq
      (by rw [VT_get3]; simpa using hq) (by rw [hty]; exact i32v w (by omega))
    rw [hty 3, VT_write3] at w2'
    have a1 := (pexecM_prim mv fu (w4 mv.nv) _ _).trans w2'
    have hq' : vdenM mv (VT H T (I.set w (I.getD w 0 - 1)) (O.set Q.length w)) (penvN mv.nv (gS P (cells9 n m Q.length qh v st cnt d w)))
        (.binary i32 .add (.variable i32 (mv.nv + 2)) lit1) = some ((Q.length + 1 : Nat) : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E2, Option.bind_some, one_den, Option.bind_some]
      have : binaryValue .add (Q.length : Int) 1 = ((Q.length + 1 : Nat) : Int) := by
        show (Q.length : Int) + 1 = _; push_cast; rfl
      rw [this]
      exact conv_signed i32 rfl rfl _ (i32v _ hq1)
    have as := gSM_assign mv P (cells9 n m Q.length qh v st cnt d w) (VT H T (I.set w (I.getD w 0 - 1)) (O.set Q.length w)) 2
      (by simp) i32 _ _ _ hq' (ci Q.length) rfl rfl (i32v _ hQ) (conv_signed i32 rfl rfl _ (i32v _ hq1))
    have a2' := (pexecM_prim mv fu (a2 mv.nv) _ _).trans as
    have a3 := seqM_some a2' rfl (pexecM_skip mv fu _ _)
    have a4 := seqM_some a1 rfl a3
    have a5 := pexecM_scope mv fu _ _ _ _ a4
    have tk := gS_takeC P (cells9 n m Q.length qh v st cnt d w)
      ((cells9 n m Q.length qh v st cnt d w).set 2 ⟨i32, ((Q.length + 1 : Nat) : Int)⟩) [] (by simp)
    simp only [List.append_nil] at tk
    simp only [tk] at a5
    have a6 := seqM_some a5 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu (c4 mv.nv) (Y4 mv.nv) Sk _ _ 1 vc (by decide) _ a6
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q2 rfl b2
    have b4 := seqM_some q1 rfl b3
    have hdq : (decr w (I, Q)).2.length = Q.length + 1 := by
      unfold decr; dsimp only; rw [if_pos hz]; simp
    refine ⟨_, b4, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdq]; rfl
    · rw [if_pos hz]; rfl
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp
  · have hc0 : (if ((I.getD w 0 - 1 : Nat) : Int) = 0 then (1 : Int) else 0) = 0 := by
      have : ((I.getD w 0 - 1 : Nat) : Int) ≠ 0 := by omega
      rw [if_neg this]
    rw [hc0] at vc
    have b1 := pexecM_branch_false mv fu (c4 mv.nv) (Y4 mv.nv) Sk _ _ vc _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q2 rfl b2
    have b4 := seqM_some q1 rfl b3
    have hdq : (decr w (I, Q)).2.length = Q.length := by
      unfold decr; dsimp only; rw [if_neg hz]
    refine ⟨_, b4, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdq]
    · rw [if_neg hz]; rfl
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp


open Proofs.TopoSortMath (Inv outL procV decr_inv Inv.ord_len outL_getD fold_take_succ HeadOK)

/-- The queue vector: the queue itself followed by the untouched old contents. -/
def ordPad (Q O0 : List Nat) : List Nat := Q ++ O0.drop Q.length

/-- State of the inner loop after `d` targets of `outL H T v` were subtracted. -/
def foldD (H T : List Nat) (v d : Nat) (s : List Nat × List Nat) : List Nat × List Nat :=
  ((outL H T v).take d).foldl (fun s w => decr w s) s

set_option maxHeartbeats 8000000 in
theorem getD_set_gen (l : List Nat) (w y j : Nat) :
    (l.set w y).getD j 0 = if j = w ∧ w < l.length then y else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : w = j
  · subst h
    by_cases hl : w < l.length
    · simp [hl]
    · simp [hl]
  · have : ¬ (j = w) := fun e => h e.symm
    simp [h, this]

theorem foldD_succ (H T : List Nat) (v d : Nat) (s : List Nat × List Nat) (hd : d < (outL H T v).length) :
    foldD H T v (d + 1) s = decr (outL H T v)[d] (foldD H T v d s) := by
  unfold foldD
  exact fold_take_succ (fun s w => decr w s) (outL H T v) s d hd

theorem ordPad_push (Q O0 : List Nat) (x : Nat) (hQ : Q.length < O0.length) :
    ordPad (Q ++ [x]) O0 = (ordPad Q O0).set Q.length x := by
  unfold ordPad
  rw [set_pad Q O0 Q.length x rfl hQ]
  simp

theorem foldD_full (H T : List Nat) (v : Nat) (s : List Nat × List Nat) :
    foldD H T v (outL H T v).length s = procV H T v s := by
  unfold foldD procV; rw [List.take_length]

/-- The inner loop `for (int d = 0; d < cnt; d++) {...}`: subtract all targets of the vertex `v`. -/
theorem xin_loop (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = i32) (H T O0 : List Nat) (P : List Cell)
    (n m qh v : Nat) (S : List Nat) (st0 : List Nat × List Nat) (hn : n < M31) (hm : m < M31) (hqh : qh < M31)
    (hv : v < M31) (hmT : T.length = m) (hTn : ∀ x ∈ T, x < n) (hOl : O0.length = n)
    (HK : HeadOK H T n) (hvn : v < n) (hI : Inv H T n S (outL H T v) st0) (hIall : ∀ j, st0.1.getD j 0 < M31)
    (hcnt2 : (outL H T v).length < 2147483647) (hstm : H.getD v 0 ≤ m) (hcm : (outL H T v).length ≤ m)
    (hstcnt : H.getD v 0 + (outL H T v).length ≤ m) (fu : Nat) (hfu : (outL H T v).length + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 7 6 (Xin mv.nv))
      (gS P [ci n, ci m, ci st0.2.length, ci qh, ci v, ci (H.getD v 0), ci (outL H T v).length])
      (VT H T st0.1 (ordPad st0.2 O0)) = some res ∧
      res.ps = gS P [ci n, ci m, ci (procV H T v st0).2.length, ci qh, ci v, ci (H.getD v 0), ci (outL H T v).length] ∧
      res.vv = VT H T (procV H T v st0).1 (ordPad (procV H T v st0).2 O0) ∧ res.ret = none ∧
      Inv H T n S [] (procV H T v st0) ∧ (∀ j, (procV H T v st0).1.getD j 0 < M31) ∧
      res.cost ≤ 420 * (outL H T v).length + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ 2 * (outL H T v).length := by
  have hnM : n < 2147483648 := hn
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 7 6 (outL H T v).length (by omega) hcnt2 (Xin mv.nv)
    (fun d vv C => vv = VT H T (foldD H T v d st0).1 (ordPad (foldD H T v d st0).2 O0) ∧
      C = [ci n, ci m, ci (foldD H T v d st0).2.length, ci qh, ci v, ci (H.getD v 0), ci (outL H T v).length] ∧
      Inv H T n S ((outL H T v).drop d) (foldD H T v d st0) ∧ (∀ j, (foldD H T v d st0).1.getD j 0 < M31))
    400 80 2 0 (by omega)
    (by
      intro d vv C fu hd hCl' hC6 ⟨hvv, hC, hJ, hJall⟩ _
      subst hvv; subst hC
      obtain ⟨x, hx⟩ : ∃ x, x = (outL H T v)[d]'hd := ⟨_, rfl⟩
      have hdrop : (outL H T v).drop d = x :: (outL H T v).drop (d + 1) := by rw [hx]; exact List.drop_eq_getElem_cons hd
      rw [hdrop] at hJ
      have hxn : x < n := Proofs.TopoSortMath.outL_lt H T n hTn v x (by rw [hx]; exact List.getElem_mem hd)
      have hxT : T.getD (H.getD v 0 + d) 0 = x := by
        rw [← Proofs.TopoSortMath.outL_getD H T v d hd, getD_lt _ _ hd, hx]
      have J' := Proofs.TopoSortMath.decr_inv H T n S x _ (foldD H T v d st0) hxn hJ
      have hsucc : foldD H T v (d + 1) st0 = decr x (foldD H T v d st0) := by rw [foldD_succ H T v d st0 hd, hx]
      have hord := hJ.ord_len
      have hQlen : (ordPad (foldD H T v d st0).2 O0).length = n := by
        unfold ordPad; simp [List.length_append, List.length_drop]; omega
      have hc1 := hJ.cnt x hxn
      have hIpos : 1 ≤ (foldD H T v d st0).1.getD x 0 := by
        have : List.count x (x :: (outL H T v).drop (d + 1)) = List.count x ((outL H T v).drop (d + 1)) + 1 := List.count_cons_self
        omega
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := xin_body mv hnv hty H T (foldD H T v d st0).1 (foldD H T v d st0).2
        (ordPad (foldD H T v d st0).2 O0) P n m qh v (H.getD v 0) (outL H T v).length d hn hm hqh hv (by omega) (by omega)
        (by omega) hmT hJ.len (by rw [hxT]; exact hxn) (by rw [hxT]; exact hIpos) (by rw [hxT]; exact hJall x)
        (by omega) (by omega) (by
          rw [hxT]
          intro hz
          have hdq : (decr x (foldD H T v d st0)).2 = (foldD H T v d st0).2 ++ [x] := by
            unfold decr; dsimp only; rw [if_pos hz]
          have := J'.ord_len
          rw [hdq] at this
          simp only [List.length_append, List.length_singleton] at this
          omega) fu
      rw [hxT] at hps hvv
      have hset : (decr x (foldD H T v d st0)).2.length ≤ n := J'.ord_len
      refine ⟨r, [ci x], [ci n, ci m, ci (decr x (foldD H T v d st0)).2.length, ci qh, ci v, ci (H.getD v 0),
        ci (outL H T v).length], hr, hret, hps, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, hc, hnd, hwk⟩
      · rw [hvv, hsucc]
        congr 1
        by_cases hz : (foldD H T v d st0).1.getD x 0 - 1 = 0
        · have hdq : (decr x (foldD H T v d st0)).2 = (foldD H T v d st0).2 ++ [x] := by
            unfold decr; dsimp only; rw [if_pos hz]
          have hlt : (foldD H T v d st0).2.length < O0.length := by
            rw [hdq] at hset
            simp only [List.length_append, List.length_singleton] at hset
            omega
          rw [if_pos hz, hdq, ordPad_push _ O0 x hlt]
        · have hdq : (decr x (foldD H T v d st0)).2 = (foldD H T v d st0).2 := by
            unfold decr; dsimp only; rw [if_neg hz]
          rw [if_neg hz, hdq]
      · rw [hsucc]
      · rw [hsucc]; exact J'
      · rw [hsucc]
        intro j
        unfold decr
        dsimp only
        rw [getD_set_gen]
        by_cases hjx : j = x ∧ x < (foldD H T v d st0).1.length
        · rw [if_pos hjx]
          have := hJall x
          omega
        · rw [if_neg hjx]
          exact hJall j)
    (VT H T st0.1 (ordPad st0.2 O0)) [ci n, ci m, ci st0.2.length, ci qh, ci v, ci (H.getD v 0), ci (outL H T v).length]
    rfl rfl ⟨by simp [foldD, ordPad], rfl, by simpa [foldD] using hI, by simpa [foldD] using hIall⟩ fu (by omega)
  obtain ⟨hvv, hC, hJ, hJall⟩ := hIn
  rw [foldD_full] at hvv hC hJ hJall
  rw [hC] at hps
  refine ⟨res, hr', hps, hvv, hret, ?_, hJall, ?_, ?_, ?_⟩
  · simpa using hJ
  · omega
  · omega
  · omega


theorem succIdx_den (env : Nat → Ty → Option Int) (k x : Nat) (h : env k i32 = some (x : Int)) (hx : x + 1 < M31) :
    (NExpr.cast u64 (.binary i32 .add (.variable i32 k) lit1)).denote env = some ((x + 1 : Nat) : Int) := by
  rw [den_cast, den_binary, den_variable, h, Option.bind_some, one_den, Option.bind_some]
  have e : binaryValue .add (x : Int) 1 = ((x + 1 : Nat) : Int) := by
    show (x : Int) + 1 = _; push_cast; rfl
  rw [e, conv_signed i32 rfl rfl _ (i32v _ hx), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have : x + 1 < 2147483648 := hx; omega)

theorem outL_length (H T : List Nat) (v : Nat) (hle : H.getD (v + 1) 0 ≤ T.length) (hmono : H.getD v 0 ≤ H.getD (v + 1) 0) :
    (outL H T v).length = H.getD (v + 1) 0 - H.getD v 0 := by
  unfold outL
  simp only [List.length_take, List.length_drop]
  omega

theorem ordPad_getD (Q O0 : List Nat) (j : Nat) (hj : j < Q.length) : (ordPad Q O0).getD j 0 = Q[j] := by
  unfold ordPad
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, hj]

theorem ordPad_length (Q O0 : List Nat) (hQ : Q.length ≤ O0.length) : (ordPad Q O0).length = O0.length := by
  unfold ordPad
  simp [List.length_append, List.length_drop]
  omega


open Proofs.TopoSortMath (Inv0 stepQ step_pre)

set_option maxHeartbeats 8000000 in
/-- The body of the main loop: `if (qh < qt) { int v = order[qh]; ...; for (...) {...} }`. -/
theorem b3_body (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = i32) (H T I Q O0 : List Nat) (P : List Cell)
    (n m qh : Nat) (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647) (hqh : qh < n) (hmT : T.length = m)
    (hTn : ∀ x ∈ T, x < n) (hOl : O0.length = n) (HK : HeadOK H T n) (hI : Inv0 H T n qh (I, Q))
    (hIall : ∀ j, I.getD j 0 < M31) (fu : Nat) (hfu : m + 2 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (B3 mv.nv) (gS P [ci n, ci m, ci Q.length, ci qh]) (VT H T I (ordPad Q O0)) = some r ∧
      r.ret = none ∧ r.ps = gS P [ci n, ci m, ci (stepQ H T qh (I, Q)).2.length, ci qh] ∧
      r.vv = VT H T (stepQ H T qh (I, Q)).1 (ordPad (stepQ H T qh (I, Q)).2 O0) ∧
      Inv0 H T n (qh + 1) (stepQ H T qh (I, Q)) ∧ (∀ j, (stepQ H T qh (I, Q)).1.getD j 0 < M31) ∧
      r.cost ≤ 420 * m + 600 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 * m := by
  have hnM : n < 2147483648 := hn
  have hQn : Q.length ≤ n := hI.ord_len
  have hc3 : ∀ (E3 : penvN mv.nv (gS P [ci n, ci m, ci Q.length, ci qh]) (mv.nv + 3) i32 = some (qh : Int))
      (E2 : penvN mv.nv (gS P [ci n, ci m, ci Q.length, ci qh]) (mv.nv + 2) i32 = some (Q.length : Int)),
      vdenM mv (VT H T I (ordPad Q O0)) (penvN mv.nv (gS P [ci n, ci m, ci Q.length, ci qh])) (c3 mv.nv) =
        some (if qh < Q.length then 1 else 0) := by
    intro E3 E2
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E3, Option.bind_some, den_variable, E2, Option.bind_some]
    have : binaryValue .lt (qh : Int) (Q.length : Int) = if qh < Q.length then 1 else 0 := by
      show (if (qh : Int) < (Q.length : Int) then 1 else 0) = _
      by_cases h : qh < Q.length
      · have : (qh : Int) < (Q.length : Int) := by omega
        simp [h]
      · have : ¬ ((qh : Int) < (Q.length : Int)) := by omega
        simp [h]
    rw [this]
    simp only [bT]; unfold Ty.convert
    by_cases h : qh < Q.length <;> simp [h]
  have E3 := envs mv P [ci n, ci m, ci Q.length, ci qh] 3 (ci qh) rfl (i32v qh (by omega))
  have E2 := envs mv P [ci n, ci m, ci Q.length, ci qh] 2 (ci Q.length) rfl (i32v _ (by omega))
  have vc := hc3 E3 E2
  by_cases hq : qh < Q.length
  · rw [if_pos hq] at vc
    have J := step_pre H T n qh (I, Q) hI hq
    have hvn : Q[qh] < n := hI.lt _ (List.getElem_mem hq)
    have hHl : H.length = n + 1 := HK.len
    have hHle : ∀ j, j ≤ n → H.getD j 0 ≤ m := by
      intro j hj
      have := HeadOK.le H T n HK n (Nat.le_refl _) j hj
      rw [HK.last] at this
      omega
    have hmono := HK.mono Q[qh] hvn
    have hcntEq : (outL H T Q[qh]).length = H.getD (Q[qh] + 1) 0 - H.getD Q[qh] 0 :=
      outL_length H T Q[qh] (by have := hHle (Q[qh] + 1) (by omega); omega) hmono
    -- v = order[qh]
    have vv1 := rdM_val mv (VT H T I (ordPad Q O0)) (penvN mv.nv (gS P [ci n, ci m, ci Q.length, ci qh])) 3 (by omega) i32
      (hty 3).symm (ix mv.nv 3) rfl rfl qh (cidx_den _ (mv.nv + 3) qh E3 (by omega)) ((Q[qh] : Nat) : Int)
      (by rw [VT_get3]; have := natList_get (ordPad Q O0) qh (by rw [ordPad_length Q O0 (by omega)]; omega)
          rw [ordPad_getD Q O0 qh hq] at this; exact this)
      (by rw [hty]; exact i32v _ (by omega))
    have d1 := gSM_decl mv P [ci n, ci m, ci Q.length, ci qh] (VT H T I (ordPad Q O0)) i32 _ _ _ vv1
      (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
    have q1 := (pexecM_prim mv fu (dV mv.nv) _ _).trans d1
    -- start = head[v]
    have E4 := envs mv P [ci n, ci m, ci Q.length, ci qh, ci Q[qh]] 4 (ci Q[qh]) rfl (i32v _ (by omega))
    have vs := rdM_val mv (VT H T I (ordPad Q O0)) (penvN mv.nv (gS P [ci n, ci m, ci Q.length, ci qh, ci Q[qh]])) 0
      (by omega) i32 (hty 0).symm (ix mv.nv 4) rfl rfl Q[qh] (cidx_den _ (mv.nv + 4) _ E4 (by omega))
      ((H.getD Q[qh] 0 : Nat) : Int)
      (by rw [VT_get0]; exact natList_get H _ (by omega))
      (by rw [hty]; exact i32v _ (by have := hHle Q[qh] (by omega); omega))
    have d2 := gSM_decl mv P [ci n, ci m, ci Q.length, ci qh, ci Q[qh]] (VT H T I (ordPad Q O0)) i32 _ _ _ vs
      (conv_signed i32 rfl rfl _ (i32v _ (by have := hHle Q[qh] (by omega); omega)))
    have q2 := (pexecM_prim mv fu (dS mv.nv) _ _).trans d2
    -- cnt = head[v+1] - start
    have E4' := envs mv P [ci n, ci m, ci Q.length, ci qh, ci Q[qh], ci (H.getD Q[qh] 0)] 4 (ci Q[qh]) rfl (i32v _ (by omega))
    have E5 := envs mv P [ci n, ci m, ci Q.length, ci qh, ci Q[qh], ci (H.getD Q[qh] 0)] 5 (ci (H.getD Q[qh] 0)) rfl
      (i32v _ (by have := hHle Q[qh] (by omega); omega))
    have hv1 : Q[qh] + 1 < M31 := by have : n < M31 := hn; omega
    have vh1 := rdM_val mv (VT H T I (ordPad Q O0))
      (penvN mv.nv (gS P [ci n, ci m, ci Q.length, ci qh, ci Q[qh], ci (H.getD Q[qh] 0)])) 0 (by omega) i32 (hty 0).symm
      (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 4)) lit1)) rfl rfl (Q[qh] + 1)
      (succIdx_den _ (mv.nv + 4) Q[qh] E4' hv1) ((H.getD (Q[qh] + 1) 0 : Nat) : Int)
      (by rw [VT_get0]; exact natList_get H _ (by omega))
      (by rw [hty]; exact i32v _ (by have := hHle (Q[qh] + 1) (by omega); omega))
    have vcnt : vdenM mv (VT H T I (ordPad Q O0)) (penvN mv.nv (gS P [ci n, ci m, ci Q.length, ci qh, ci Q[qh],
        ci (H.getD Q[qh] 0)])) (.binary i32 .sub (.read i32 (.local 0) (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 4)) lit1)))
        (.variable i32 (mv.nv + 5))) = some ((H.getD (Q[qh] + 1) 0 - H.getD Q[qh] 0 : Nat) : Int) := by
      rw [vdenM_binary _ _ _ _ _ _ _ rfl, vh1, Option.bind_some, vdenM_scalar _ _ _ _ rfl, den_variable, E5, Option.bind_some]
      have : binaryValue .sub ((H.getD (Q[qh] + 1) 0 : Nat) : Int) ((H.getD Q[qh] 0 : Nat) : Int) =
          ((H.getD (Q[qh] + 1) 0 - H.getD Q[qh] 0 : Nat) : Int) := by
        show _ - _ = _; omega
      rw [this]
      exact conv_signed i32 rfl rfl _ (i32v _ (by have := hHle (Q[qh] + 1) (by omega); omega))
    have d3 := gSM_decl mv P [ci n, ci m, ci Q.length, ci qh, ci Q[qh], ci (H.getD Q[qh] 0)] (VT H T I (ordPad Q O0)) i32 _ _ _ vcnt
      (conv_signed i32 rfl rfl _ (i32v _ (by have := hHle (Q[qh] + 1) (by omega); omega)))
    have q3 := (pexecM_prim mv fu (dC mv.nv) _ _).trans d3
    have hcntq : H.getD (Q[qh] + 1) 0 - H.getD Q[qh] 0 = (outL H T Q[qh]).length := hcntEq.symm
    rw [hcntq] at q3
    have hb1 := hHle (Q[qh] + 1) (by omega)
    have hb0 := hHle Q[qh] (by omega)
    obtain ⟨rf, hrf, hrfps, hrfvv, hrfret, hrfI, hrfall, hrfc, hrfn, hrfw⟩ := xin_loop mv hnv hty H T O0 P n m qh Q[qh]
      (Q.take (qh + 1)) (I, Q) hn hm (by omega) (by omega) hmT hTn hOl HK hvn J hIall (by omega) (by omega)
      (by omega) (by omega) fu (by omega)
    have f1 := seqM_some hrf hrfret (pexecM_skip mv fu _ _)
    have f2 := seqM_some q3 rfl f1
    have f3 := seqM_some q2 rfl f2
    have f4 := seqM_some q1 rfl f3
    have f5 := pexecM_scope mv fu _ _ _ _ f4
    have tk := gS_takeC P [ci n, ci m, ci Q.length, ci qh]
      [ci n, ci m, ci (procV H T Q[qh] (I, Q)).2.length, ci qh] [ci Q[qh], ci (H.getD Q[qh] 0), ci (outL H T Q[qh]).length]
      (by simp)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at tk
    rw [hrfps] at f5
    simp only [tk] at f5
    have f6 := seqM_some f5 rfl (pexecM_skip mv fu _ _)
    have g1 := pexecM_branch_true mv fu (c3 mv.nv) (.sequence (.scope (Z3 mv.nv)) Sk) Sk _ _ 1 vc (by decide) _ f6
    have g2 := seqM_some g1 rfl (pexecM_skip mv fu _ _)
    have hst : stepQ H T qh (I, Q) = procV H T Q[qh] (I, Q) := by
      unfold stepQ
      rw [if_pos hq]
      show procV H T (Q.getD qh 0) (I, Q) = _
      rw [getD_lt Q qh hq]
    have hT : ∀ x ∈ T, x < n := hTn
    refine ⟨_, g2, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hst]
    · rw [hst]; exact hrfvv
    · exact Proofs.TopoSortMath.stepQ_inv H T n hT qh (I, Q) hI
    · rw [hst]; exact hrfall
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrfc ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrfn ⊢; omega
    · simp at hrfw ⊢; omega
  · rw [if_neg hq] at vc
    have b1 := pexecM_branch_false mv fu (c3 mv.nv) (.sequence (.scope (Z3 mv.nv)) Sk) Sk _ _ vc _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have hst : stepQ H T qh (I, Q) = (I, Q) := by unfold stepQ; rw [if_neg hq]
    refine ⟨_, b2, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hst]
    · rw [hst]
    · rw [hst]; unfold Inv0 at hI ⊢
      have h1 : Q.take (qh + 1) = Q.take qh := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simpa [h1] using hI
    · rw [hst]; exact hIall
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]


open Proofs.TopoSortMath (kahnL kahnL_inv initSt init_inv)

theorem kahnL_succ (H T : List Nat) (st : List Nat × List Nat) (t : Nat) :
    kahnL H T (t + 1) st = stepQ H T t (kahnL H T t st) := by
  unfold kahnL
  rw [List.range_succ, List.foldl_append]
  rfl

set_option maxHeartbeats 8000000 in
/-- Loop 3: the main loop `for (int qh = 0; qh < n; qh++) {...}`. -/
theorem l3_loop (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = i32) (H T O0 : List Nat) (P : List Cell)
    (n m : Nat) (st0 : List Nat × List Nat) (hn : n < M31) (hm : m < M31) (hm2 : m < 2147483647)
    (hn2 : n < 2147483647) (hmT : T.length = m) (hTn : ∀ x ∈ T, x < n) (hOl : O0.length = n)
    (HK : HeadOK H T n) (hI0 : Inv0 H T n 0 st0) (hIall : ∀ j, st0.1.getD j 0 < M31) (fu : Nat) (hfu : m + 2 + n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 3 0 (B3 mv.nv)) (gS P [ci n, ci m, ci st0.2.length])
      (VT H T st0.1 (ordPad st0.2 O0)) = some res ∧
      res.ps = gS P [ci n, ci m, ci (kahnL H T n st0).2.length] ∧
      res.vv = VT H T (kahnL H T n st0).1 (ordPad (kahnL H T n st0).2 O0) ∧ res.ret = none ∧
      res.cost ≤ (420 * m + 620) * n + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ 2 * m * n := by
  have hT : ∀ x ∈ T, x < n := hTn
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 3 0 n (by omega) hn2 (B3 mv.nv)
    (fun t vv C => vv = VT H T (kahnL H T t st0).1 (ordPad (kahnL H T t st0).2 O0) ∧
      C = [ci n, ci m, ci (kahnL H T t st0).2.length] ∧ Inv0 H T n t (kahnL H T t st0) ∧
      (∀ j, (kahnL H T t st0).1.getD j 0 < M31))
    (420 * m + 600) 100 (2 * m) (m + 2) (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC, hJ, hJall⟩ hfu'
      subst hvv; subst hC
      obtain ⟨r, hr, hret, hps, hvv, hI', hall', hc, hnd, hwk⟩ := b3_body mv hnv hty H T (kahnL H T t st0).1 (kahnL H T t st0).2
        O0 P n m t hn hm hm2 ht hmT hTn hOl HK hJ hJall fu hfu'
      refine ⟨r, [], [ci n, ci m, ci (stepQ H T t (kahnL H T t st0)).2.length], hr, hret, hps, rfl, rfl,
        ⟨?_, ?_, ?_, ?_⟩, hc, hnd, hwk⟩
      · rw [hvv, kahnL_succ]
      · rw [kahnL_succ]
      · rw [kahnL_succ]; exact hI'
      · rw [kahnL_succ]; exact hall')
    (VT H T st0.1 (ordPad st0.2 O0)) [ci n, ci m, ci st0.2.length] rfl rfl
    ⟨by simp [kahnL], by simp [kahnL], by simpa [kahnL] using hI0, by simpa [kahnL] using hIall⟩ fu (by omega)
  obtain ⟨hvv, hC, hJ, hJall⟩ := hIn
  subst hC
  refine ⟨res, ?_, hps, hvv, hret, ?_, ?_, ?_⟩
  · simpa [kahnL] using hr'
  · omega
  · omega
  · omega


theorem size_val1 (mv : MV) (hnv : mv.nv = 4) (hty1 : mv.ty 1 = i32) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (hn : (vv 1).length < 2147483648) :
    vdenM mv vv env (.cast i32 (.size (.integer i32) (.local 1))) = some ((vv 1).length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer i32) (.local 1))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer i32) (.local 1)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer i32) (.local 1)) = some ((vv 1).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨by omega, hty1.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

theorem cntList_full (n : Nat) (T : List Nat) : cntList n T T.length = (initSt T n).1 := by
  unfold cntList initSt
  rw [List.take_length]

theorem zs_init (n : Nat) (T : List Nat) : zs (cntList n T T.length) n = (initSt T n).2 := by
  unfold zs initSt
  apply List.filter_congr
  intro w hw
  have hw' := List.mem_range.mp hw
  rw [cntList_getD n T T.length w hw', List.take_length]

theorem cntList_lt (n : Nat) (T : List Nat) (hm : T.length < M31) : ∀ j, (cntList n T T.length).getD j 0 < M31 := by
  intro j
  by_cases hj : j < n
  · rw [cntList_getD n T _ j hj]
    have := cnt_le_t T T.length j
    have h2 : (T.take T.length).count j ≤ T.length := this
    omega
  · have : (cntList n T T.length).getD j 0 = 0 := by
      have hn : (List.range n)[j]? = none := by
        rw [List.getElem?_eq_none]; simp; omega
      simp [List.getD_eq_getElem?_getD, cntList, hn]
    rw [this]; show 0 < 2147483648; omega

theorem wr_bodyTS : WrM (fun k => decide (k = 2 ∨ k = 3)) (bodyTS 4) = true := by decide


set_option maxHeartbeats 8000000 in
/-- The whole body of `topological_sort` for a zero-filled `indeg`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = i32) (H T O : List Nat) (P : List Cell) (n : Nat)
    (hn : n < 2147483647) (hm : T.length < 2147483647) (hTn : ∀ x ∈ T, x < n) (hOl : O.length = n)
    (HK : HeadOK H T n) (fu : Nat) (hfu : T.length + 2 + n + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyTS mv.nv) (gS P [ci n]) (VT H T (List.replicate n 0) O) = some r ∧
      r.ret = some (((kahnL H T n (initSt T n)).2.length : Nat) : Int) ∧
      r.ps = gS P [ci n, ci T.length, ci (kahnL H T n (initSt T n)).2.length] ∧
      r.vv = VT H T (kahnL H T n (initSt T n)).1 (ordPad (kahnL H T n (initSt T n)).2 O) ∧
      r.cost ≤ 420 * (T.length * n) + 840 * n + 120 * T.length + 400 ∧ r.need ≤ P.length + 100 ∧
      r.wk ≤ T.length + n + 2 * (T.length * n) := by
  have hnM : n < M31 := by show n < 2147483648; omega
  have hmM : T.length < M31 := by show T.length < 2147483648; omega
  -- m = target.size()
  have hlen1 : (VT H T (List.replicate n 0) O 1).length = T.length := by rw [VT_get1]; simp
  have hsz := size_val1 mv hnv (hty 1) (VT H T (List.replicate n 0) O) (penvN mv.nv (gS P [ci n]))
    (by rw [hlen1]; exact hmM)
  rw [hlen1] at hsz
  have d1 := gSM_decl mv P [ci n] (VT H T (List.replicate n 0) O) i32 _ _ _ hsz (conv_signed i32 rfl rfl _ (i32v _ hmM))
  have q1 := (pexecM_prim mv fu declM _ _).trans d1
  -- loop 1
  obtain ⟨r1, h1, h1ps, h1vv, h1ret, h1c, h1n, h1w⟩ := l1_loop mv hnv hty H T O P n T.length hnM hmM hm rfl hTn fu (by omega)
  -- the declaration of qt
  have d2 := gSM_decl mv P [ci n, ci T.length] (VT H T (cntList n T T.length) O) i32 lit0 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact zero_den _) (conv_signed i32 rfl rfl _ (i32v _ (by decide)))
  have q3 := (pexecM_prim mv fu (.declare i32 true lit0) _ _).trans d2
  -- loop 2
  obtain ⟨r2, h2, h2ps, h2vv, h2ret, h2c, h2n, h2w⟩ := l2_loop mv hnv hty H T (cntList n T T.length) O P n T.length hnM hmM hn
    (cntList_length n T _) (cntList_lt n T hmM) hOl fu (by omega)
  have e1 : (initSt T n).1 = cntList n T T.length := (cntList_full n T).symm
  have e2 : (initSt T n).2 = zs (cntList n T T.length) n := (zs_init n T).symm
  have h2ps' : r2.ps = gS P [ci n, ci T.length, ci (initSt T n).2.length] := by rw [h2ps, e2]
  have h2vv' : r2.vv = VT H T (initSt T n).1 (ordPad (initSt T n).2 O) := by
    rw [h2vv, e1]; unfold ordPad; rw [e2]
  have hI0 := init_inv H T n HK hTn
  have hIall : ∀ j, (initSt T n).1.getD j 0 < M31 := by rw [e1]; exact cntList_lt n T hmM
  obtain ⟨r3, h3, h3ps, h3vv, h3ret, h3c, h3n, h3w⟩ := l3_loop mv hnv hty H T O P n T.length (initSt T n) hnM hmM hm hn rfl hTn hOl HK
    hI0 hIall fu (by omega)
  have hv3 : penvN mv.nv (gS P [ci n, ci T.length, ci (kahnL H T n (initSt T n)).2.length]) (mv.nv + 2) i32 =
      some (((kahnL H T n (initSt T n)).2.length : Nat) : Int) :=
    envs mv P [ci n, ci T.length, ci (kahnL H T n (initSt T n)).2.length] 2 _ rfl
      (i32v _ (by
        have := (Proofs.TopoSortMath.kahnL_inv H T n (fun x hx => hTn x hx) (initSt T n) hI0 n).ord_len
        have : n < M31 := hnM; omega))
  have rr := pstmtM_ret_ok mv (gS P [ci n, ci T.length, ci (kahnL H T n (initSt T n)).2.length])
    (VT H T (kahnL H T n (initSt T n)).1 (ordPad (kahnL H T n (initSt T n)).2 O)) (.variable i32 (mv.nv + 2))
    (((kahnL H T n (initSt T n)).2.length : Nat) : Int) (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact hv3)
  have e6 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have c5 := seqM_some h3 h3ret (by rw [h3ps, h3vv]; exact e6)
  have c4 := seqM_some h2 h2ret (by rw [h2ps', h2vv']; exact c5)
  have c3 := seqM_some q3 rfl c4
  have c2 := seqM_some h1 h1ret (by rw [h1ps, h1vv]; exact c3)
  have c1 := seqM_some q1 rfl c2
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at h1c h2c h3c ⊢
    rw [Nat.add_mul, Nat.mul_assoc] at h3c
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at h1n h2n h3n ⊢
    omega
  · simp at h1w h2w h3w ⊢
    rw [Nat.mul_assoc] at h3w
    omega

end Proofs.TopoSortExec
