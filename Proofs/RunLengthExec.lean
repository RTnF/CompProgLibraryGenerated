import Proofs.CompressExec
import Proofs.RunLengthMath

namespace Proofs.RunLengthExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.MatMulExec (vdenM_binary idx_lt n_small)
open Proofs.CompressExec (V3 V3_get0 V3_get1 V3_get2 V3_upd1 V3_upd2 rdM_valI pexecM_branch_true pexecM_branch_false idxC_den)
open Proofs.RunLengthMath

/-- A cell holding a `long long`. -/
abbrev cs64 (x : Int) : Cell := ⟨s64, x⟩

abbrev condEq (nv : Nat) : NExpr :=
  .binary bT .eq (.variable s64 (nv + 1)) (.read s64 (.local 0) (.cast u64 (.variable i32 (nv + 4))))
abbrev incCnt (nv : Nat) : NStmt := .assign (nv + 2) i32 (.binary i32 .add (.variable i32 (nv + 2)) (.literal i32 1))
abbrev yesR (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (incCnt nv)) (.primitive .skip))) (.primitive .skip)
abbrev w1R (nv : Nat) : NStmt := .write (.local 1) s64 (.cast u64 (.variable i32 (nv + 3))) (.variable s64 (nv + 1))
abbrev w2R (nv : Nat) : NStmt := .write (.local 2) i32 (.cast u64 (.variable i32 (nv + 3))) (.variable i32 (nv + 2))
abbrev incMR (nv : Nat) : NStmt := .assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.literal i32 1))
abbrev setPreR (nv : Nat) : NStmt := .assign (nv + 1) s64 (.read s64 (.local 0) (.cast u64 (.variable i32 (nv + 4))))
abbrev setCnt1R (nv : Nat) : NStmt := .assign (nv + 2) i32 (.literal i32 1)
abbrev noR (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (w1R nv)) (.sequence (.primitive (w2R nv)) (.sequence (.primitive (incMR nv))
    (.sequence (.primitive (setPreR nv)) (.sequence (.primitive (setCnt1R nv)) (.primitive .skip))))))) (.primitive .skip)
abbrev brR (nv : Nat) : Command := .branch (condEq nv) (yesR nv) (noR nv)
abbrev B3 (nv : Nat) : Command := .sequence (brR nv) (.primitive .skip)

/-- The cells `n`, `pre`, `cnt`, `m`. -/
abbrev D4 (n : Nat) (pre : Int) (cnt m : Nat) : List Cell := [ci n, cs64 pre, ci cnt, ci m]

theorem envR (mv : MV) (P : List Cell) (n : Nat) (pre : Int) (cnt m t : Nat) (hn : n < 2147483648)
    (hpre : s64.valid pre = true) (hcnt : cnt < 2147483648) (hm : m < 2147483648) (ht : t < 2147483648) :
    penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t])) (mv.nv + 1) s64 = some pre ∧
    penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t])) (mv.nv + 2) i32 = some (cnt : Int) ∧
    penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t])) (mv.nv + 3) i32 = some (m : Int) ∧
    penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t])) (mv.nv + 4) i32 = some (t : Int) :=
  ⟨gSM_env mv.nv P _ 1 (cs64 pre) rfl hpre, gSM_env mv.nv P _ 2 (ci cnt) rfl (validN cnt hcnt),
   gSM_env mv.nv P _ 3 (ci m) rfl (validN m hm), gSM_env mv.nv P _ 4 (ci t) rfl (validN t ht)⟩

theorem cond_valR (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (X U Y : List Int) (P : List Cell) (n : Nat) (pre : Int)
    (cnt m t : Nat) (hn : n < 2147483648) (hpre : s64.valid pre = true) (hcnt : cnt < 2147483648)
    (hm : m < 2147483648) (ht : t < 2147483648) (x : Int) (hx : X[t]? = some x) (hxv : s64.valid x = true) :
    vdenM mv (V3 X U Y) (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t]))) (condEq mv.nv) =
      some (if pre = x then 1 else 0) := by
  obtain ⟨E1, E2, E3, E4⟩ := envR mv P n pre cnt m t hn hpre hcnt hm ht
  have hb : (condEq mv.nv).scalarOnly = false := rfl
  have r2 := rdM_valI mv (V3 X U Y) (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t]))) 0 (by omega) s64 hty0.symm
    (.cast u64 (.variable i32 (mv.nv + 4))) rfl rfl t (idxC_den _ _ _ E4 ht) x (by rw [V3_get0]; exact hx)
    (by rw [hty0]; exact hxv)
  have hv : vdenM mv (V3 X U Y) (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t]))) (NExpr.variable s64 (mv.nv + 1)) =
      some pre := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1
  rw [vdenM_binary _ _ _ _ _ _ _ hb, hv, r2, Option.bind_some, Option.bind_some]
  have : binaryValue .eq pre x = if pre = x then 1 else 0 := by
    show (if (pre == x) = true then 1 else 0) = _
    by_cases h : pre = x <;> simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases hh : pre = x <;> simp [hh]

theorem inc_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (slot k : Nat)
    (h : env slot i32 = some (k : Int)) (hk : k + 1 < 2147483648) :
    vdenM mv vv env (.binary i32 .add (.variable i32 slot) (.literal i32 1)) = some ((k + 1 : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, h, Option.bind_some,
    den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .add (k : Int) 1 = ((k + 1 : Nat) : Int) := by
    show (k : Int) + 1 = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ hk)

theorem iterEqR (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (X U Y : List Int) (P : List Cell) (n : Nat) (pre : Int)
    (cnt m t : Nat) (hn : n < 2147483648) (hpre : s64.valid pre = true) (hcnt : cnt + 1 < 2147483648)
    (hm : m < 2147483648) (ht : t < 2147483648) (x : Int) (hx : X[t]? = some x) (hxv : s64.valid x = true)
    (heq : pre = x) (fu : Nat) :
    ∃ r1 : PRM, pexecM mv fu (B3 mv.nv) (gS P (D4 n pre cnt m ++ [ci t])) (V3 X U Y) = some r1 ∧
      r1.ps = gS P (D4 n pre (cnt + 1) m ++ [ci t] ++ []) ∧ r1.vv = V3 X U Y ∧ r1.ret = none ∧ r1.cost ≤ 200 ∧
      r1.need ≤ P.length + 100 ∧ r1.wk = 0 := by
  obtain ⟨E1, E2, E3, E4⟩ := envR mv P n pre cnt m t hn hpre (by omega) hm ht
  have cv := cond_valR mv hnv hty0 X U Y P n pre cnt m t hn hpre (by omega) hm ht x hx hxv
  rw [if_pos heq] at cv
  have lv := inc_val mv (V3 X U Y) (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t]))) (mv.nv + 2) cnt E2 hcnt
  have stA := gSM_assign mv P (D4 n pre cnt m ++ [ci t]) (V3 X U Y) 2 (by simp) i32 _ _ _ lv (ci cnt) rfl rfl
    (validN cnt (by omega)) (conv_signed i32 rfl rfl _ (validN _ hcnt))
  have e2 : (D4 n pre cnt m ++ [ci t]).set 2 ⟨i32, ((cnt + 1 : Nat) : Int)⟩ = D4 n pre (cnt + 1) m ++ [ci t] := rfl
  rw [e2] at stA
  have a1 := (pexecM_prim mv fu (incCnt mv.nv) _ _).trans stA
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (D4 n pre (cnt + 1) m ++ [ci t])) (V3 X U Y))
  have a3 := pexecM_scope mv fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (gS P (D4 n pre cnt m ++ [ci t])) (gS P (D4 n pre (cnt + 1) m ++ [ci t]))
    (by simp [gS]) (by simp [gS])
  simp only [a4] at a3
  have a5 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (D4 n pre (cnt + 1) m ++ [ci t])) (V3 X U Y))
  have br := pexecM_branch_true mv fu (condEq mv.nv) (yesR mv.nv) (noR mv.nv) (gS P (D4 n pre cnt m ++ [ci t])) (V3 X U Y)
    1 cv (by simp) _ a5
  have e1 := seqM_some br rfl (pexecM_skip mv fu _ _)
  refine ⟨_, e1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp

theorem iterNeR (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hty2 : mv.ty 2 = i32)
    (X U Y : List Int) (P : List Cell) (n : Nat) (pre : Int) (cnt m t : Nat) (hn : n < 2147483648)
    (hpre : s64.valid pre = true) (hcnt : cnt < 2147483648) (hm : m + 1 < 2147483648) (ht : t < 2147483648)
    (hmU : m < U.length) (hmY : m < Y.length) (x : Int) (hx : X[t]? = some x) (hxv : s64.valid x = true)
    (hne : ¬ pre = x) (fu : Nat) :
    ∃ r1 : PRM, pexecM mv fu (B3 mv.nv) (gS P (D4 n pre cnt m ++ [ci t])) (V3 X U Y) = some r1 ∧
      r1.ps = gS P (D4 n x 1 (m + 1) ++ [ci t] ++ []) ∧
      r1.vv = V3 X (U.set m pre) (Y.set m (cnt : Int)) ∧ r1.ret = none ∧ r1.cost ≤ 400 ∧
      r1.need ≤ P.length + 100 ∧ r1.wk = 2 := by
  obtain ⟨E1, E2, E3, E4⟩ := envR mv P n pre cnt m t hn hpre hcnt (by omega) ht
  have cv := cond_valR mv hnv hty0 X U Y P n pre cnt m t hn hpre hcnt (by omega) ht x hx hxv
  rw [if_neg hne] at cv
  -- U[m] = pre
  have hidx := idxC_den (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t]))) (mv.nv + 3) m E3 (by omega)
  have hpI : vdenM mv (V3 X U Y) (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t]))) (.cast u64 (.variable i32 (mv.nv + 3))) =
      some ((m : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact hidx
  have hxp : vdenM mv (V3 X U Y) (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t]))) (.variable s64 (mv.nv + 1)) = some pre := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1
  have w1 := pstmtM_write_ok mv (gS P (D4 n pre cnt m ++ [ci t])) (V3 X U Y) 1 (by omega) (.cast u64 (.variable i32 (mv.nv + 3)))
    (.variable s64 (mv.nv + 1)) pre m hxp hpI (by rw [V3_get1]; exact hmU) (by rw [hty1]; exact hpre)
  rw [hty1] at w1
  have e1 : upd (V3 X U Y) 1 ((V3 X U Y 1).set m pre) = V3 X (U.set m pre) Y := by
    rw [V3_get1]; exact V3_upd1 X U Y (fun l => l.set m pre)
  rw [e1] at w1
  have p1 := (pexecM_prim mv fu (w1R mv.nv) _ _).trans w1
  -- Y[m] = cnt
  have hxc : vdenM mv (V3 X (U.set m pre) Y) (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t]))) (.variable i32 (mv.nv + 2)) =
      some (cnt : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2
  have hpI2 : vdenM mv (V3 X (U.set m pre) Y) (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t])))
      (.cast u64 (.variable i32 (mv.nv + 3))) = some ((m : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact hidx
  have w2 := pstmtM_write_ok mv (gS P (D4 n pre cnt m ++ [ci t])) (V3 X (U.set m pre) Y) 2 (by omega)
    (.cast u64 (.variable i32 (mv.nv + 3))) (.variable i32 (mv.nv + 2)) (cnt : Int) m hxc hpI2
    (by rw [V3_get2]; exact hmY) (by rw [hty2]; exact validN cnt hcnt)
  rw [hty2] at w2
  have e2 : upd (V3 X (U.set m pre) Y) 2 ((V3 X (U.set m pre) Y 2).set m (cnt : Int)) =
      V3 X (U.set m pre) (Y.set m (cnt : Int)) := by
    rw [V3_get2]; exact V3_upd2 X (U.set m pre) Y (fun l => l.set m (cnt : Int))
  rw [e2] at w2
  have p2 := (pexecM_prim mv fu (w2R mv.nv) _ _).trans w2
  -- m := m + 1
  have lvm := inc_val mv (V3 X (U.set m pre) (Y.set m (cnt : Int))) (penvN mv.nv (gS P (D4 n pre cnt m ++ [ci t])))
    (mv.nv + 3) m E3 hm
  have stM := gSM_assign mv P (D4 n pre cnt m ++ [ci t]) (V3 X (U.set m pre) (Y.set m (cnt : Int))) 3 (by simp) i32 _ _ _ lvm
    (ci m) rfl rfl (validN m (by omega)) (conv_signed i32 rfl rfl _ (validN _ hm))
  have e3 : (D4 n pre cnt m ++ [ci t]).set 3 ⟨i32, ((m + 1 : Nat) : Int)⟩ = D4 n pre cnt (m + 1) ++ [ci t] := rfl
  rw [e3] at stM
  have p3 := (pexecM_prim mv fu (incMR mv.nv) _ _).trans stM
  -- pre := x[t]
  obtain ⟨F1, F2, F3, F4⟩ := envR mv P n pre cnt (m + 1) t hn hpre hcnt hm ht
  have rdx := rdM_valI mv (V3 X (U.set m pre) (Y.set m (cnt : Int)))
    (penvN mv.nv (gS P (D4 n pre cnt (m + 1) ++ [ci t]))) 0 (by omega) s64 hty0.symm
    (.cast u64 (.variable i32 (mv.nv + 4))) rfl rfl t (idxC_den _ _ _ F4 ht) x (by rw [V3_get0]; exact hx)
    (by rw [hty0]; exact hxv)
  have stP := gSM_assign mv P (D4 n pre cnt (m + 1) ++ [ci t]) (V3 X (U.set m pre) (Y.set m (cnt : Int))) 1 (by simp) s64 _ x x
    rdx (cs64 pre) rfl rfl hpre (conv_signed s64 rfl rfl _ hxv)
  have e4 : (D4 n pre cnt (m + 1) ++ [ci t]).set 1 ⟨s64, x⟩ = D4 n x cnt (m + 1) ++ [ci t] := rfl
  rw [e4] at stP
  have p4 := (pexecM_prim mv fu (setPreR mv.nv) _ _).trans stP
  -- cnt := 1
  have hone : vdenM mv (V3 X (U.set m pre) (Y.set m (cnt : Int))) (penvN mv.nv (gS P (D4 n x cnt (m + 1) ++ [ci t])))
      (.literal i32 1) = some 1 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 1 = true from rfl)]
  have stC := gSM_assign mv P (D4 n x cnt (m + 1) ++ [ci t]) (V3 X (U.set m pre) (Y.set m (cnt : Int))) 2 (by simp) i32 _ 1 1
    hone (ci cnt) rfl rfl (validN cnt hcnt) (conv_signed i32 rfl rfl _ rfl)
  have e5 : (D4 n x cnt (m + 1) ++ [ci t]).set 2 ⟨i32, (1 : Int)⟩ = D4 n x 1 (m + 1) ++ [ci t] := rfl
  rw [e5] at stC
  have p5 := (pexecM_prim mv fu (setCnt1R mv.nv) _ _).trans stC
  have s5 := seqM_some p5 rfl (pexecM_skip mv fu (gS P (D4 n x 1 (m + 1) ++ [ci t]))
    (V3 X (U.set m pre) (Y.set m (cnt : Int))))
  have s4 := seqM_some p4 rfl s5
  have s3 := seqM_some p3 rfl s4
  have s2 := seqM_some p2 rfl s3
  have s1 := seqM_some p1 rfl s2
  have sc := pexecM_scope mv fu _ _ _ _ s1
  have tk := Proofs.PexecKit.scope_take (gS P (D4 n pre cnt m ++ [ci t])) (gS P (D4 n x 1 (m + 1) ++ [ci t]))
    (by simp [gS]) (by simp [gS])
  simp only [tk] at sc
  have a5 := seqM_some sc rfl (pexecM_skip mv fu (gS P (D4 n x 1 (m + 1) ++ [ci t]))
    (V3 X (U.set m pre) (Y.set m (cnt : Int))))
  have br := pexecM_branch_false mv fu (condEq mv.nv) (yesR mv.nv) (noR mv.nv) (gS P (D4 n pre cnt m ++ [ci t]))
    (V3 X U Y) cv _ a5
  have e6 := seqM_some br rfl (pexecM_skip mv fu _ _)
  refine ⟨_, e6, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp

/-- The first `m` runs stored in the buffers. -/
def pairsOf (U Y : List Int) (m : Nat) : List (Int × Nat) :=
  (List.range m).map (fun k => (U.getD k 0, (Y.getD k 0).toNat))

theorem pairsOf_length (U Y : List Int) (m : Nat) : (pairsOf U Y m).length = m := by simp [pairsOf]

theorem pairsOf_succ_set (U Y : List Int) (m : Nat) (pre : Int) (cnt : Nat) (hU : m < U.length) (hY : m < Y.length) :
    pairsOf (U.set m pre) (Y.set m (cnt : Int)) (m + 1) = pairsOf U Y m ++ [(pre, cnt)] := by
  unfold pairsOf
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro k hk
    have hk' : k < m := List.mem_range.mp hk
    rw [Proofs.CompressExec.getD_setI, Proofs.CompressExec.getD_setI, if_neg (fun h => by omega), if_neg (fun h => by omega)]
  · simp [Proofs.CompressExec.getD_setI, hU, hY]

theorem rleAdd_snoc_eq (closed : List (Int × Nat)) (pre : Int) (cnt : Nat) (x : Int) (h : pre = x) :
    rleAdd (closed ++ [(pre, cnt)]) x = closed ++ [(pre, cnt + 1)] := by
  simp [rleAdd, h]

theorem rleAdd_snoc_ne (closed : List (Int × Nat)) (pre : Int) (cnt : Nat) (x : Int) (h : ¬ pre = x) :
    rleAdd (closed ++ [(pre, cnt)]) x = closed ++ [(pre, cnt), (x, 1)] := by
  simp [rleAdd, h]

theorem rl_loop (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hty2 : mv.ty 2 = i32)
    (X U Y : List Int) (hX : ∀ x ∈ X, s64.valid x = true) (P : List Cell) (n : Nat) (hlX : X.length = n)
    (hlU : U.length = n) (hlY : Y.length = n) (hn : n < 2147483647) (hn1 : 1 ≤ n) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ (res : PRM) (pre : Int) (cnt m : Nat) (U' Y' : List Int),
      pexecM mv fu (forStmt mv.nv 4 (B3 mv.nv)) (gS P (D4 n (X.getD 0 0) 0 0)) (V3 X U Y) = some res ∧
      res.ps = gS P (D4 n pre cnt m) ∧ res.vv = V3 X U' Y' ∧ res.ret = none ∧ U'.length = n ∧ Y'.length = n ∧
      rle X = pairsOf U' Y' m ++ [(pre, cnt)] ∧ s64.valid pre = true ∧ cnt ≤ n ∧
      res.cost ≤ 420 * n + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ 2 * n := by
  have hx0 : s64.valid (X.getD 0 0) = true := by
    apply hX
    have : X.getD 0 0 = X[0]'(by omega) := by simp [List.getD_eq_getElem?_getD, show 0 < X.length by omega]
    rw [this]; exact List.getElem_mem _
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runC mv P 4 n (by omega) hn (B3 mv.nv)
    (fun t vv C => ∃ (pre : Int) (cnt m : Nat) (U' Y' : List Int), C = D4 n pre cnt m ∧ vv = V3 X U' Y' ∧
      U'.length = n ∧ Y'.length = n ∧ rleExt X t = pairsOf U' Y' m ++ [(pre, cnt)] ∧ s64.valid pre = true ∧ cnt ≤ t ∧ m ≤ t)
    400 100 2 0 (by omega)
    (by
      intro t vv C fu ht hCl hC0 ⟨pre, cnt, m, U', Y', hC, hvv, hlU', hlY', hext, hpre, hcnt, hmt⟩ _
      subst hC; subst hvv
      have htX : t < X.length := by omega
      have hxt : X[t]? = some (X.getD t 0) := by simp [List.getD_eq_getElem?_getD, htX]
      have hxv : s64.valid (X.getD t 0) = true := by
        apply hX
        have : X.getD t 0 = X[t]'htX := by simp [List.getD_eq_getElem?_getD, htX]
        rw [this]; exact List.getElem_mem _
      by_cases hpx : pre = X.getD t 0
      · obtain ⟨r, hr, hps, hvv, hret, hc, hnd, hwk⟩ :=
          iterEqR mv hnv hty0 X U' Y' P n pre cnt m t (by omega) hpre (by omega) (by omega) (by omega) (X.getD t 0) hxt hxv hpx fu
        refine ⟨r, [], D4 n pre (cnt + 1) m, hr, hret, hps, rfl, rfl, ⟨pre, cnt + 1, m, U', Y', rfl, hvv, hlU', hlY', ?_, hpre, by omega, by omega⟩,
          by omega, hnd, by omega⟩
        rw [rleExt_succ X t htX, hext, rleAdd_snoc_eq _ _ _ _ hpx]
      · have ht0 : t ≠ 0 := by
          intro h0
          subst h0
          apply hpx
          simp only [rleExt, if_pos rfl] at hext
          have hl := congrArg List.length hext
          simp [pairsOf_length] at hl
          have hm : m = 0 := by omega
          subst hm
          simp [pairsOf] at hext
          exact hext.1.symm
        have hlen : m + 1 ≤ t := by
          have h1 : (rleExt X t).length = m + 1 := by rw [hext]; simp [pairsOf_length]
          simp only [rleExt, if_neg ht0] at h1
          have h2 := rle_length_le (X.take t)
          simp [List.length_take] at h2
          omega
        obtain ⟨r, hr, hps, hvv, hret, hc, hnd, hwk⟩ :=
          iterNeR mv hnv hty0 hty1 hty2 X U' Y' P n pre cnt m t (by omega) hpre (by omega) (by omega) (by omega)
            (by omega) (by omega) (X.getD t 0) hxt hxv hpx fu
        refine ⟨r, [], D4 n (X.getD t 0) 1 (m + 1), hr, hret, hps, rfl, rfl,
          ⟨X.getD t 0, 1, m + 1, U'.set m pre, Y'.set m (cnt : Int), rfl, hvv, by simp [hlU'], by simp [hlY'], ?_, hxv, by omega, by omega⟩,
          hc, hnd, by omega⟩
        rw [rleExt_succ X t htX, hext, rleAdd_snoc_ne _ _ _ _ hpx, pairsOf_succ_set U' Y' m pre cnt (by omega) (by omega)]
        simp)
    (V3 X U Y) (D4 n (X.getD 0 0) 0 0) rfl rfl
    ⟨X.getD 0 0, 0, 0, U, Y, rfl, rfl, hlU, hlY, by simp [rleExt, pairsOf], hx0, by omega, by omega⟩ fu (by omega)
  obtain ⟨pre, cnt, m, U', Y', hC, hvv, hlU', hlY', hext, hpre, hcnt, hmt⟩ := hI
  subst hC
  refine ⟨res, pre, cnt, m, U', Y', hr, hps, hvv, hret, hlU', hlY', ?_, hpre, hcnt, hc, hnd, hw⟩
  have : rleExt X n = rle X := by
    simp only [rleExt, if_neg (show n ≠ 0 by omega)]
    rw [← hlX, List.take_length]
  rw [← this, hext]

abbrev brN (nv : Nat) : Command :=
  .branch (.binary bT .eq (.variable i32 nv) (.literal i32 0))
    (.sequence (.scope (.sequence (.primitive (.ret (.literal i32 0))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)
abbrev declPre : NStmt := .declare s64 true (.read s64 (.local 0) (.cast u64 (.literal i32 0)))
abbrev declI0 : NStmt := .declare i32 true (.literal i32 0)
abbrev retMR (nv : Nat) : NStmt := .ret (.variable i32 (nv + 3))
abbrev restRL (nv : Nat) : Command :=
  .sequence (.primitive declPre)
    (.sequence (.primitive declI0) (.sequence (.primitive declI0) (.sequence (forStmt nv 4 (B3 nv))
      (.sequence (.primitive (w1R nv)) (.sequence (.primitive (w2R nv)) (.sequence (.primitive (incMR nv))
        (.sequence (.primitive (retMR nv)) (.primitive .skip))))))))
abbrev bodyRL (nv : Nat) : Command :=
  .sequence (.primitive Proofs.CompressExec.declN) (.sequence (brN nv) (restRL nv))

theorem body_execRL (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hty2 : mv.ty 2 = i32)
    (X U Y : List Int) (hX : ∀ x ∈ X, s64.valid x = true) (P : List Cell) (n : Nat) (hlX : X.length = n)
    (hlU : U.length = n) (hlY : Y.length = n) (hn : n < 2147483647) (fu : Nat) (hfu : n + 2 ≤ fu) :
    ∃ (r : PRM) (U' Y' : List Int), pexecM mv fu (bodyRL mv.nv) (gS P []) (V3 X U Y) = some r ∧
      r.ret = some (((rle X).length : Nat) : Int) ∧ (∃ cs, r.ps = gS P cs) ∧ r.vv = V3 X U' Y' ∧
      U'.length = n ∧ Y'.length = n ∧ pairsOf U' Y' (rle X).length = rle X ∧
      r.cost ≤ 420 * n + 200 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 * n + 2 := by
  have hv0 : vdenM mv (V3 X U Y) (penvN mv.nv (gS P [])) (.cast i32 (.size (.integer s64) (.local 0))) = some (n : Int) := by
    rw [Proofs.CompressExec.size_valMk mv 0 (by omega) hty0 _ _ (by rw [V3_get0]; omega), V3_get0, hlX]
  have d0 := gSM_decl mv P [] (V3 X U Y) i32 _ (n : Int) (n : Int) hv0 (conv_signed i32 rfl rfl _ (validN n (by omega)))
  have q0 := (pexecM_prim mv fu Proofs.CompressExec.declN _ _).trans d0
  have hcond : vdenM mv (V3 X U Y) (penvN mv.nv (gS P [ci n])) (.binary bT .eq (.variable i32 mv.nv) (.literal i32 0)) =
      some (if n = 0 then 1 else 0) := by
    have E0 : penvN mv.nv (gS P [ci n]) mv.nv i32 = some (n : Int) := gSM_env mv.nv P [ci n] 0 (ci n) rfl (validN n (by omega))
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E0, Option.bind_some,
      den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
    have : binaryValue .eq (n : Int) 0 = if n = 0 then 1 else 0 := by
      show (if ((n : Int) == 0) = true then 1 else 0) = _
      by_cases h : n = 0 <;> simp [h]
    rw [this]
    simp only [bT]; unfold Ty.convert
    by_cases h : n = 0 <;> simp [h]
  by_cases hn0 : n = 0
  · subst hn0
    rw [if_pos rfl] at hcond
    have hX0 : X = [] := List.length_eq_zero_iff.mp hlX
    have ret0 := pstmtM_ret_ok mv (gS P [ci 0]) (V3 X U Y) (.literal i32 0) 0
      (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)])
    have p1 := (pexecM_prim mv fu (.ret (.literal i32 0)) _ _).trans ret0
    have p2 := seqM_ret (b := .primitive .skip) p1 rfl
    have p3 := pexecM_scope mv fu _ _ _ _ p2
    have p4 := seqM_ret (b := .primitive .skip) p3 rfl
    have br := pexecM_branch_true mv fu _ _ (.primitive .skip) (gS P [ci 0]) (V3 X U Y) 1 hcond (by simp) _ p4
    have t1 := seqM_ret (b := restRL mv.nv) br rfl
    have t2 := seqM_some q0 rfl t1
    refine ⟨_, U, Y, t2, ?_, ⟨[ci 0], ?_⟩, rfl, hlU, hlY, ?_, ?_, ?_, ?_⟩
    · simp [hX0, rle]
    · simp
    · simp [hX0, rle, pairsOf]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp
  · have hX1 : 1 ≤ n := by omega
    rw [if_neg hn0] at hcond
    have hx0 : s64.valid (X.getD 0 0) = true := by
      apply hX
      have : X.getD 0 0 = X[0]'(by omega) := by simp [List.getD_eq_getElem?_getD, show 0 < X.length by omega]
      rw [this]; exact List.getElem_mem _
    have hxt0 : X[0]? = some (X.getD 0 0) := by simp [List.getD_eq_getElem?_getD, show 0 < X.length by omega]
    have zero_val : ∀ (vv : Nat → List Int) (env : Nat → Ty → Option Int),
        vdenM mv vv env (.literal i32 0) = some 0 := by
      intro vv env
      rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]
    -- declarations
    have hidx0 : (NExpr.cast u64 (.literal i32 0)).denote (penvN mv.nv (gS P [ci n])) = some ((0 : Nat) : Int) := by
      rw [den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some, convert_u64]
      rfl
    have rd0 := rdM_valI mv (V3 X U Y) (penvN mv.nv (gS P [ci n])) 0 (by omega) s64 hty0.symm
      (.cast u64 (.literal i32 0)) rfl rfl 0 hidx0 (X.getD 0 0) (by rw [V3_get0]; exact hxt0) (by rw [hty0]; exact hx0)
    have dP := gSM_decl mv P [ci n] (V3 X U Y) s64 _ (X.getD 0 0) (X.getD 0 0) rd0 (conv_signed s64 rfl rfl _ hx0)
    have qP := (pexecM_prim mv fu declPre _ _).trans dP
    have dC := gSM_decl mv P [ci n, cs64 (X.getD 0 0)] (V3 X U Y) i32 _ 0 0 (zero_val _ _) (conv_signed i32 rfl rfl _ rfl)
    have qC := (pexecM_prim mv fu declI0 _ _).trans dC
    have dM := gSM_decl mv P [ci n, cs64 (X.getD 0 0), (⟨i32, (0 : Int)⟩ : Cell)] (V3 X U Y) i32 _ 0 0 (zero_val _ _)
      (conv_signed i32 rfl rfl _ rfl)
    have qM := (pexecM_prim mv fu declI0 _ _).trans dM
    obtain ⟨res, pre, cnt, m, U', Y', hr, hps, hvv, hretL, hlU', hlY', hrle, hpre, hcnt, hcL, hndL, hwL⟩ :=
      rl_loop mv hnv hty0 hty1 hty2 X U Y hX P n hlX hlU hlY hn hX1 fu (by omega)
    have hlenR : (rle X).length = m + 1 := by rw [hrle]; simp [pairsOf_length]
    have hle : (rle X).length ≤ n := by rw [← hlX]; exact rle_length_le X
    -- the final statements
    obtain ⟨E1, E2, E3⟩ : penvN mv.nv (gS P (D4 n pre cnt m)) (mv.nv + 1) s64 = some pre ∧
        penvN mv.nv (gS P (D4 n pre cnt m)) (mv.nv + 2) i32 = some (cnt : Int) ∧
        penvN mv.nv (gS P (D4 n pre cnt m)) (mv.nv + 3) i32 = some (m : Int) :=
      ⟨gSM_env mv.nv P _ 1 (cs64 pre) rfl hpre, gSM_env mv.nv P _ 2 (ci cnt) rfl (validN cnt (by omega)),
       gSM_env mv.nv P _ 3 (ci m) rfl (validN m (by omega))⟩
    have hidx := idxC_den (penvN mv.nv (gS P (D4 n pre cnt m))) (mv.nv + 3) m E3 (by omega)
    have hpI : ∀ vv : Nat → List Int, vdenM mv vv (penvN mv.nv (gS P (D4 n pre cnt m)))
        (.cast u64 (.variable i32 (mv.nv + 3))) = some ((m : Nat) : Int) := by
      intro vv; rw [vdenM_scalar _ _ _ _ rfl]; exact hidx
    have hxp : vdenM mv (V3 X U' Y') (penvN mv.nv (gS P (D4 n pre cnt m))) (.variable s64 (mv.nv + 1)) = some pre := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1
    have w1 := pstmtM_write_ok mv (gS P (D4 n pre cnt m)) (V3 X U' Y') 1 (by omega) (.cast u64 (.variable i32 (mv.nv + 3)))
      (.variable s64 (mv.nv + 1)) pre m hxp (hpI _) (by rw [V3_get1]; omega) (by rw [hty1]; exact hpre)
    rw [hty1] at w1
    have e1 : upd (V3 X U' Y') 1 ((V3 X U' Y' 1).set m pre) = V3 X (U'.set m pre) Y' := by
      rw [V3_get1]; exact V3_upd1 X U' Y' (fun l => l.set m pre)
    rw [e1] at w1
    have p1 := (pexecM_prim mv fu (w1R mv.nv) _ _).trans w1
    have hxc : vdenM mv (V3 X (U'.set m pre) Y') (penvN mv.nv (gS P (D4 n pre cnt m))) (.variable i32 (mv.nv + 2)) =
        some (cnt : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2
    have w2 := pstmtM_write_ok mv (gS P (D4 n pre cnt m)) (V3 X (U'.set m pre) Y') 2 (by omega)
      (.cast u64 (.variable i32 (mv.nv + 3))) (.variable i32 (mv.nv + 2)) (cnt : Int) m hxc (hpI _)
      (by rw [V3_get2]; omega) (by rw [hty2]; exact validN cnt (by omega))
    rw [hty2] at w2
    have e2 : upd (V3 X (U'.set m pre) Y') 2 ((V3 X (U'.set m pre) Y' 2).set m (cnt : Int)) =
        V3 X (U'.set m pre) (Y'.set m (cnt : Int)) := by
      rw [V3_get2]; exact V3_upd2 X (U'.set m pre) Y' (fun l => l.set m (cnt : Int))
    rw [e2] at w2
    have p2 := (pexecM_prim mv fu (w2R mv.nv) _ _).trans w2
    have lvm := inc_val mv (V3 X (U'.set m pre) (Y'.set m (cnt : Int))) (penvN mv.nv (gS P (D4 n pre cnt m)))
      (mv.nv + 3) m E3 (by omega)
    have stM := gSM_assign mv P (D4 n pre cnt m) (V3 X (U'.set m pre) (Y'.set m (cnt : Int))) 3 (by simp) i32 _ _ _ lvm
      (ci m) rfl rfl (validN m (by omega)) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
    have e3 : (D4 n pre cnt m).set 3 ⟨i32, ((m + 1 : Nat) : Int)⟩ = D4 n pre cnt (m + 1) := rfl
    rw [e3] at stM
    have p3 := (pexecM_prim mv fu (incMR mv.nv) _ _).trans stM
    have F3 : penvN mv.nv (gS P (D4 n pre cnt (m + 1))) (mv.nv + 3) i32 = some ((m + 1 : Nat) : Int) :=
      gSM_env mv.nv P _ 3 (ci (m + 1)) rfl (validN (m + 1) (by omega))
    have hret : vdenM mv (V3 X (U'.set m pre) (Y'.set m (cnt : Int))) (penvN mv.nv (gS P (D4 n pre cnt (m + 1))))
        (.variable i32 (mv.nv + 3)) = some ((m + 1 : Nat) : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact F3
    have rr := pstmtM_ret_ok mv (gS P (D4 n pre cnt (m + 1))) (V3 X (U'.set m pre) (Y'.set m (cnt : Int))) _ _ hret
    have p4 := (pexecM_prim mv fu (retMR mv.nv) _ _).trans rr
    have s4 := seqM_ret (b := .primitive .skip) p4 rfl
    have s3 := seqM_some p3 rfl s4
    have s2 := seqM_some p2 rfl s3
    have s1 := seqM_some p1 rfl s2
    have s0 := seqM_some hr hretL (by rw [hps, hvv]; exact s1)
    have c3 := seqM_some qM rfl s0
    have c2 := seqM_some qC rfl c3
    have c1 := seqM_some qP rfl c2
    have br := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (.ret (.literal i32 0))) (.primitive .skip))) (.primitive .skip))
      (.primitive .skip) (gS P [ci n]) (V3 X U Y) hcond _ (pexecM_skip mv fu _ _)
    have t1 := seqM_some br rfl c1
    have t2 := seqM_some q0 rfl t1
    have hpairs : pairsOf (U'.set m pre) (Y'.set m (cnt : Int)) (m + 1) = rle X := by
      rw [pairsOf_succ_set U' Y' m pre cnt (by omega) (by omega), ← hrle]
    refine ⟨_, U'.set m pre, Y'.set m (cnt : Int), t2, ?_, ⟨D4 n pre cnt (m + 1), ?_⟩, ?_, by simp [hlU'], by simp [hlY'], ?_, ?_, ?_, ?_⟩
    · simp [hlenR]
    · simp
    · simp
    · rw [hlenR]; exact hpairs
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at *
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
      omega
    · dsimp only
      omega

end Proofs.RunLengthExec
