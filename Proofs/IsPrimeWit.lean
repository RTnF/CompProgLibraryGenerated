import Proofs.IsPrimeExec

namespace Proofs.IsPrimeWit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.BellmanFordExec (envs pexecM_branch_true pexecM_branch_false lt_conv ne_conv)
open Proofs.IsPrimeBody
open Proofs.IsPrimeExec

abbrev Wd (C0 : List Cell) (n d r a pm bbf x : Nat) (w cf : Bool) (i : Nat) : List Cell := C0 ++ Wc n d r a pm bbf x w cf i
abbrev WSd (C0 : List Cell) (n d r a pm bbf x : Nat) (w : Bool) : List Cell := C0 ++ WS n d r a pm bbf x w

abbrev witKB (nv b : Nat) : Command :=
  .sequence (.primitive (.assign (nv + (b + 12)) u64 (vU nv (b + 22))))
    (.sequence (.branch (.binary bT .eq (vU nv (b + 12)) (.binary u64 .sub (vU nv b) oU))
      (.sequence (.scope (.sequence (.primitive (.assign (nv + (b + 13)) bT (.literal bT 0))) Sk)) Sk) Sk)
    (.sequence (.primitive (.assign (nv + (b + 14)) i32 (.binary i32 .add (.variable i32 (nv + (b + 14))) (.literal i32 1)))) Sk))

abbrev witLoopB (nv b : Nat) : Command :=
  .sequence (.scope (callMulD nv (b + 15) (b + 12) (b + 12) b (witKB nv b))) Sk

abbrev witCondB (nv b : Nat) : NExpr :=
  .logical true (.binary bT .lt (.variable i32 (nv + (b + 14))) (.binary i32 .sub (.variable i32 (nv + (b + 2))) (.literal i32 1)))
    (.variable bT (nv + (b + 13)))

abbrev witW2B (nv b : Nat) : Command :=
  .sequence (.primitive (.declare bT true (.literal bT 1)))
    (.sequence (.primitive (.declare i32 true (.literal i32 0)))
      (.sequence (.whileLoop (witCondB nv b) (witLoopB nv b))
        (.sequence (.branch (.variable bT (nv + (b + 13)))
          (.sequence (.scope (.sequence (.primitive (.assign (nv + (b + 4)) bT (.literal bT 1))) Sk)) Sk) Sk) Sk)))

abbrev witC1B (nv b : Nat) : Command :=
  .branch (.binary bT .ne (vU nv (b + 12)) oU)
    (.sequence (.scope (.sequence (.branch (.binary bT .ne (vU nv (b + 12)) (.binary u64 .sub (vU nv b) oU))
      (.sequence (.scope (witW2B nv b)) Sk) Sk) Sk)) Sk) Sk

def mrX (n r x : Nat) : Nat :=
  if x = 1 then x else if x = n - 1 then x else (wrun n r r (x, true, 0)).1

abbrev witPreK (nv b : Nat) (R : Command) : Command :=
  .sequence (.primitive (.declare bT true (.literal bT 0)))
    (callPowD nv (b + 5) (b + 3) (b + 1) b (.sequence (witC1B nv b) R))

abbrev witBodyB (nv b : Nat) : Command :=
  .sequence (.primitive (.declare bT true (.literal bT 0)))
    (callPowD nv (b + 5) (b + 3) (b + 1) b
      (.sequence (witC1B nv b) (.sequence (.primitive (.ret (.variable bT (nv + (b + 4))))) Sk)))


/-- The part after the multiplication: `x = nx; if (x == n - 1) cf = false; i = i + 1;`. -/
theorem wit_K (mv : MV) (P C0 : List Cell) (b : Nat) (hC : C0.length = b) (n d r a pm bbf x i : Nat) (w : Bool) (hn : 2 ≤ n) (hnm : n < M64) (hx : x < n)
    (hi : i < 2147483640) (vv : Nat → List Int) (fu : Nat) :
    ∃ res : PRM, pexecM mv fu (witKB mv.nv b) (gS P (callCellsD (Wd C0 n d r a pm bbf x w true i) x x n ((x * x) % n)
        (mrun n 64 (0, x, x)).2.1)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (callCellsD (Wd C0 n d r a pm bbf ((x * x) % n) w (decide ((x * x) % n ≠ n - 1)) (i + 1)) x x n ((x * x) % n)
        (mrun n 64 (0, x, x)).2.1) ∧ res.vv = vv ∧ res.cost ≤ 200 ∧ res.need ≤ P.length + 2 * (b + 40) + 60 ∧ res.wk = 0 := by
  have hr' : (x * x) % n < n := Nat.mod_lt _ (by omega)
  have hr64 : (x * x) % n < M64 := by omega
  have hx64 : x < M64 := by omega
  set R := (x * x) % n with hR
  set XF := (mrun n 64 (0, x, x)).2.1 with hXF
  -- the last step: i = i + 1
  have hcl3 : ∀ (cf : Bool), (callCellsD (Wd C0 n d r a pm bbf R w cf i) x x n R XF)[b + 14]? = some (cI i) := by
    intro cf; simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have fin3 : ∀ (cf : Bool), ∃ r3 : PRM, pexecM mv fu (.sequence (.primitive (.assign (mv.nv + (b + 14)) i32
        (.binary i32 .add (.variable i32 (mv.nv + (b + 14))) (.literal i32 1)))) Sk)
      (gS P (callCellsD (Wd C0 n d r a pm bbf R w cf i) x x n R XF)) vv = some r3 ∧ r3.ret = none ∧
      r3.ps = gS P (callCellsD (Wd C0 n d r a pm bbf R w cf (i + 1)) x x n R XF) ∧ r3.vv = vv ∧ r3.cost ≤ 50 ∧
      r3.need ≤ P.length + 2 * (b + 40) + 60 ∧ r3.wk = 0 := by
    intro cf
    obtain ⟨r3, h3, ret3, ps3, vv3, c3, n3, w3⟩ := inc_exec mv P _ (b + 14) i (hcl3 cf) (by omega) vv fu Sk _
      (pexecM_skip mv fu _ _)
    refine ⟨r3, h3, by rw [ret3], ?_, by rw [vv3], ?_, ?_, w3.trans rfl⟩
    · rw [ps3]; simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC, List.set_append_right, List.set, hC]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c3; omega
    · simp [gS_mem_len, gS_bs_len, callCellsD, Wd, WSd, Wc, WS, hC] at n3; omega
  -- the branch `if (x == n - 1) cf = false`
  have hS12 : (callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF)[b + 12]? = some (cu R) := by
    simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have hS0 : (callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF)[b + 0]? = some (cu n) := by
    simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have hsub : (NExpr.binary u64 .sub (vU mv.nv (b + 0)) oU).denote (penvN mv.nv (gS P (callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF))) =
      some ((n - 1 : Nat) : Int) :=
    sub_den _ _ _ n 1 (var_den mv P _ (b + 0) n hS0 hnm) (oU_den _) (by omega) hnm
  have hcond : vdenM mv vv (penvN mv.nv (gS P (callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF)))
      (.binary bT .eq (vU mv.nv (b + 12)) (.binary u64 .sub (vU mv.nv (b + 0)) oU)) = some (if R = n - 1 then 1 else 0) := by
    rw [vdenM_scalar mv vv _ _ rfl, den_binary, var_den mv P _ (b + 12) R hS12 hr64, Option.bind_some, hsub, Option.bind_some]
    by_cases h : R = n - 1
    · simp [binaryValue, Ty.convert, bT, Ty.valid, h]
    · have : (R : Int) ≠ ((n - 1 : Nat) : Int) := by omega
      simp [binaryValue, Ty.convert, bT, Ty.valid, h, this]
  have hc13 : (callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF)[b + 13]? = some (cb true) := by
    simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have hKbr : ∃ rb : PRM, pexecM mv fu (.sequence (.branch (.binary bT .eq (vU mv.nv (b + 12)) (.binary u64 .sub (vU mv.nv (b + 0)) oU))
      (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + (b + 13)) bT (.literal bT 0))) Sk)) Sk) Sk)
      (.sequence (.primitive (.assign (mv.nv + (b + 14)) i32 (.binary i32 .add (.variable i32 (mv.nv + (b + 14))) (.literal i32 1)))) Sk))
      (gS P (callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF)) vv = some rb ∧ rb.ret = none ∧
      rb.ps = gS P (callCellsD (Wd C0 n d r a pm bbf R w (decide (R ≠ n - 1)) (i + 1)) x x n R XF) ∧ rb.vv = vv ∧ rb.cost ≤ 160 ∧
      rb.need ≤ P.length + 2 * (b + 40) + 60 ∧ rb.wk = 0 := by
    by_cases h : R = n - 1
    · rw [if_pos h] at hcond
      have hv0 : vdenM mv vv (penvN mv.nv (gS P (callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF))) (.literal bT 0) = some 0 := by
        rw [vdenM_scalar mv vv _ _ rfl, den_literal, if_pos (show bT.valid 0 = true from rfl)]
      have hs := gSM_assign mv P (callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF) vv (b + 13) (by simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC]) bT
        (.literal bT 0) 0 0 hv0 (cb true) hc13 rfl (by decide) (by decide)
      have ha := (pexecM_prim mv fu _ _ _).trans hs
      have hb := seqM_some ha rfl (pexecM_skip mv fu _ _)
      have hsc := pexecM_scope mv fu _ _ _ _ hb
      have hset : (callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF).set (b + 13) ⟨bT, 0⟩ =
          callCellsD (Wd C0 n d r a pm bbf R w false i) x x n R XF := by
        simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC, List.set_append_right, List.set, hC]
      rw [hset, scope_same P _ _ (by simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC])] at hsc
      have hb2 := seqM_some hsc (by simp) (pexecM_skip mv fu _ _)
      have hbr := pexecM_branch_true mv fu _ _ Sk _ _ 1 hcond (by decide) _ hb2
      obtain ⟨r3, h3, ret3, ps3, vv3, c3, n3, w3⟩ := fin3 false
      have hseq := seqM_some hbr (by simp) h3
      refine ⟨_, hseq, by rw [ret3], ?_, by rw [vv3], ?_, ?_, ?_⟩
      · rw [ps3]; simp [h]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c3 ⊢; omega
      · simp [gS_mem_len, gS_bs_len, callCellsD, Wd, WSd, Wc, WS, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at n3 ⊢; omega
      · simp [w3]
    · rw [if_neg h] at hcond
      have hbr := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + (b + 13)) bT (.literal bT 0))) Sk)) Sk) Sk
        _ _ hcond _ (pexecM_skip mv fu _ _)
      obtain ⟨r3, h3, ret3, ps3, vv3, c3, n3, w3⟩ := fin3 true
      have hseq := seqM_some hbr (by simp) h3
      refine ⟨_, hseq, by rw [ret3], ?_, by rw [vv3], ?_, ?_, ?_⟩
      · rw [ps3]; simp [h]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c3 ⊢; omega
      · simp [gS_mem_len, gS_bs_len, callCellsD, Wd, WSd, Wc, WS, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at n3 ⊢; omega
      · simp [w3]
  obtain ⟨rb, hb, retb, psb, vvb, cb_, nb, wb⟩ := hKbr
  -- the copy `x = nx`
  have hcs : (callCellsD (Wd C0 n d r a pm bbf x w true i) x x n R XF)[b + 22]? = some (cu R) := by
    simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have hct : (callCellsD (Wd C0 n d r a pm bbf x w true i) x x n R XF)[b + 12]? = some (cu x) := by
    simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have hset12 : (callCellsD (Wd C0 n d r a pm bbf x w true i) x x n R XF).set (b + 12) (cu R) =
      callCellsD (Wd C0 n d r a pm bbf R w true i) x x n R XF := by
    simp [callCellsD, Wd, WSd, Wc, WS, List.getElem?_append_right, hC, List.set_append_right, List.set, hC]
  obtain ⟨rc, hc, retc, psc, vvc, cc, nc, wc⟩ := copy_exec mv P (callCellsD (Wd C0 n d r a pm bbf x w true i) x x n R XF) (b + 12) (b + 22) x R hcs hct
    hr64 (by omega) vv fu _ rb (by rw [hset12]; exact hb)
  refine ⟨rc, hc, by rw [retc, retb], by rw [psc, psb], by rw [vvc, vvb], ?_, ?_, ?_⟩
  · omega
  · first | omega | (simp [gS_mem_len, gS_bs_len, callCellsD, Wd, WSd, Wc, WS, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at nc; omega)
  · rw [wc, wb]

set_option maxHeartbeats 64000000 in
theorem wit_iter (mv : MV) (P C0 : List Cell) (b : Nat) (hC : C0.length = b) (n d r a pm bbf x i : Nat) (w : Bool) (hn : 2 ≤ n) (hnm : n < M64) (hx : x < n)
    (hi : i < 2147483640) (vv : Nat → List Int) (fu : Nat) (hfu : 65 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (witLoopB mv.nv b) (gS P (Wd C0 n d r a pm bbf x w true i)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (Wd C0 n d r a pm bbf ((x * x) % n) w (decide ((x * x) % n ≠ n - 1)) (i + 1)) ∧ res.vv = vv ∧
      res.cost ≤ 64 * 420 + 800 ∧ res.need ≤ P.length + 2 * (b + 40) + 400 ∧ res.wk = 0 := by
  obtain ⟨rk, hk, retk, psk, vvk, ck, nk, wk⟩ := wit_K mv P C0 b hC n d r a pm bbf x i w hn hnm hx hi vv fu
  have hlen : (Wd C0 n d r a pm bbf x w true i).length = b + 15 := by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have g12 : (Wd C0 n d r a pm bbf x w true i)[b + 12]? = some (cu x) := by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have g0 : (Wd C0 n d r a pm bbf x w true i)[b + 0]? = some (cu n) := by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  obtain ⟨rm, hm, retm, psm, vvm, cm, nm, wm⟩ := mulcallD_exec mv P (Wd C0 n d r a pm bbf x w true i) (b + 12) (b + 12) b x x n g12 g12 g0 hx hx hnm vv fu hfu
    (witKB mv.nv b) rk hk
  rw [hlen] at hm
  have t1 := pexecM_scope mv fu _ _ _ _ hm
  have tk : (⟨(gS P (callCellsD (Wd C0 n d r a pm bbf ((x * x) % n) w (decide ((x * x) % n ≠ n - 1)) (i + 1)) x x n ((x * x) % n)
          (mrun n 64 (0, x, x)).2.1)).mem.take (gS P (Wd C0 n d r a pm bbf x w true i)).mem.length,
        (gS P (callCellsD (Wd C0 n d r a pm bbf ((x * x) % n) w (decide ((x * x) % n ≠ n - 1)) (i + 1)) x x n ((x * x) % n)
          (mrun n 64 (0, x, x)).2.1)).bs.take (gS P (Wd C0 n d r a pm bbf x w true i)).bs.length⟩ : PS) =
      gS P (Wd C0 n d r a pm bbf ((x * x) % n) w (decide ((x * x) % n ≠ n - 1)) (i + 1)) :=
    gS_takeC P (Wd C0 n d r a pm bbf x w true i) (Wd C0 n d r a pm bbf ((x * x) % n) w (decide ((x * x) % n ≠ n - 1)) (i + 1))
      [cu x, cu x, cu n, cu ((x * x) % n), cu (mrun n 64 (0, x, x)).2.1, cu 0, cu ((x * x) % n), cu ((x * x) % n)] (by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC])
  simp only [psm, psk, tk] at t1
  have t2 := seqM_some t1 (by simp [retm, retk]) (pexecM_skip mv fu _ _)
  refine ⟨_, t2, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [vvm, vvk]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cm ⊢; omega
  · simp [gS_mem_len, gS_bs_len, hC, hlen, vwp, NExpr.nodes, NExpr.scalarOnly] at nm ⊢; omega
  · simp [wm, wk]

theorem witCond_den (mv : MV) (P C0 : List Cell) (b : Nat) (hC : C0.length = b) (n d r a pm bbf x i : Nat) (w cf : Bool) (hr : r < 2147483648) (hi : i < 2147483648) :
    (witCondB mv.nv b).denote (penvN mv.nv (gS P (Wd C0 n d r a pm bbf x w cf i))) =
      some (if i + 1 < r ∧ cf = true then 1 else 0) := by
  have h14 : (Wd C0 n d r a pm bbf x w cf i)[b + 14]? = some (cI i) := by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have h2 : (Wd C0 n d r a pm bbf x w cf i)[b + 2]? = some (cI r) := by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have h13 : (Wd C0 n d r a pm bbf x w cf i)[b + 13]? = some (cb cf) := by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have e14 := vari_den mv P _ (b + 14) i h14 hi
  have e2 := vari_den mv P _ (b + 2) r h2 hr
  have e13 := varb_den mv P _ (b + 13) cf h13
  have hs : (NExpr.binary i32 .sub (.variable i32 (mv.nv + (b + 2))) (.literal i32 1)).denote (penvN mv.nv (gS P (Wd C0 n d r a pm bbf x w cf i)))
      = some ((r : Int) - 1) := by
    rw [den_binary, e2, Option.bind_some, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
    have e : binaryValue .sub (r : Int) 1 = (r : Int) - 1 := rfl
    have hv : i32.valid ((r : Int) - 1) = true := by
      show Ty.valid ⟨32, true, false⟩ _ = true
      simp [Ty.valid]; omega
    rw [e, conv_signed i32 rfl rfl _ hv]
  rw [den_and_b, den_binary, e14, Option.bind_some, hs, Option.bind_some]
  by_cases h1 : (i : Int) < (r : Int) - 1
  · have h1' : i + 1 < r := by omega
    rw [lt_conv, if_pos h1]
    simp only [Option.bind_some]
    rw [e13]
    cases cf <;> simp [h1']
  · have h1' : ¬ i + 1 < r := by omega
    rw [lt_conv, if_neg h1]
    simp [h1']


set_option maxHeartbeats 64000000 in
theorem wit_while (mv : MV) (P C0 : List Cell) (b : Nat) (hC : C0.length = b) (n d r a pm bbf : Nat) (w : Bool) (hn : 2 ≤ n) (hnm : n < M64)
    (hr : r < 2147483640) (vv : Nat → List Int) (G : Nat) (hG : 64 * 420 + 900 ≤ G) :
    ∀ (k x i fu : Nat) (cf : Bool), x < n → r ≤ i + k + 1 → i < 2147483640 → k + 65 ≤ fu →
      ∃ res : PRM, pexecM mv fu (.whileLoop (witCondB mv.nv b) (witLoopB mv.nv b)) (gS P (Wd C0 n d r a pm bbf x w cf i)) vv = some res ∧
        res.ret = none ∧
        res.ps = gS P (Wd C0 n d r a pm bbf (wrun n r k (x, cf, i)).1 w (wrun n r k (x, cf, i)).2.1 (wrun n r k (x, cf, i)).2.2) ∧
        res.vv = vv ∧ res.cost ≤ k * G + 30 ∧ res.need ≤ P.length + 2 * (b + 40) + 400 ∧ res.wk = 0 := by
  intro k
  induction k with
  | zero =>
    intro x i fu cf hx hk hi hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc : vdenM mv vv (penvN mv.nv (gS P (Wd C0 n d r a pm bbf x w cf i))) (witCondB mv.nv b) = some 0 := by
      rw [vdenM_scalar _ _ _ _ rfl, witCond_den mv P C0 b hC n d r a pm bbf x i w cf (by omega) (by omega)]
      rw [if_neg (by omega)]
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] <;> omega
  | succ k ih =>
    intro x i fu cf hx hk hi hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc0 := witCond_den mv P C0 b hC n d r a pm bbf x i w cf (by omega) (by omega)
    by_cases hcond : i + 1 < r ∧ cf = true
    · obtain ⟨hlt, rfl⟩ := hcond
      have hc : vdenM mv vv (penvN mv.nv (gS P (Wd C0 n d r a pm bbf x w true i))) (witCondB mv.nv b) = some 1 := by
        rw [vdenM_scalar _ _ _ _ rfl, hc0, if_pos ⟨hlt, rfl⟩]
      obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := wit_iter mv P C0 b hC n d r a pm bbf x i w hn hnm hx (by omega) vv (fu' + 1) (by omega)
      obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := ih ((x * x) % n) (i + 1) fu' (decide ((x * x) % n ≠ n - 1))
        (Nat.mod_lt _ (by omega)) (by omega) (by omega) (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
      rw [h1]
      simp only [ret1, ps1, vv1]
      rw [h2]
      simp only
      refine ⟨_, rfl, ret2, ?_, vv2, ?_, ?_, ?_⟩
      · rw [ps2]
        have e : wrun n r (k + 1) (x, true, i) = wrun n r k ((x * x) % n, decide ((x * x) % n ≠ n - 1), i + 1) := by
          simp [wrun, hlt]
        rw [e]
      · rw [Nat.succ_mul]
        have hCWL : CWL = 64 * 420 + 1500 := rfl
        simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c1 c2 ⊢; omega
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at n1 n2 ⊢; omega
      · simp [w1, w2]
    · have hc : vdenM mv vv (penvN mv.nv (gS P (Wd C0 n d r a pm bbf x w cf i))) (witCondB mv.nv b) = some 0 := by
        rw [vdenM_scalar _ _ _ _ rfl, hc0, if_neg hcond]
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩
      · have e : wrun n r (k + 1) (x, cf, i) = (x, cf, i) := by simp [wrun, hcond]
        rw [e]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] <;> omega



theorem takeW (P C0 : List Cell) (n d r a pm bbf x : Nat) (w : Bool) (XF : Nat) (WF CF : Bool) (IF : Nat) :
    (⟨(gS P (Wd C0 n d r a pm bbf XF WF CF IF)).mem.take (gS P (WSd C0 n d r a pm bbf x w)).mem.length,
      (gS P (Wd C0 n d r a pm bbf XF WF CF IF)).bs.take (gS P (WSd C0 n d r a pm bbf x w)).bs.length⟩ : PS) =
      gS P (WSd C0 n d r a pm bbf XF WF) := by
  have e : WSd C0 n d r a pm bbf XF WF ++ [cb CF, cI IF] = Wd C0 n d r a pm bbf XF WF CF IF := by simp [Wd, WSd, Wc]
  have tk := gS_takeC P (WSd C0 n d r a pm bbf x w) (WSd C0 n d r a pm bbf XF WF) [cb CF, cI IF] (by simp [WSd, WS])
  rw [e] at tk; exact tk

set_option maxHeartbeats 64000000 in
theorem wit_brs (mv : MV) (P C0 : List Cell) (b : Nat) (hC : C0.length = b) (n d r a pm bbf : Nat) (w : Bool)
    (vv : Nat → List Int) (fu : Nat) :
    ∀ (xf ifin : Nat) (cff : Bool), ∃ rb : PRM, pexecM mv fu (.sequence (.branch (.variable bT (mv.nv + (b + 13)))
        (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + (b + 4)) bT (.literal bT 1))) Sk)) Sk) Sk) Sk)
      (gS P (Wd C0 n d r a pm bbf xf w cff ifin)) vv = some rb ∧ rb.ret = none ∧
      rb.ps = gS P (Wd C0 n d r a pm bbf xf (if cff then true else w) cff ifin) ∧ rb.vv = vv ∧ rb.cost ≤ 100 ∧
      rb.need ≤ P.length + 2 * (b + 40) + 100 ∧ rb.wk = 0 := by
  intro xf ifin cff
  have g13 : (Wd C0 n d r a pm bbf xf w cff ifin)[b + 13]? = some (cb cff) := by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
  have hv := varb_den mv P _ (b + 13) cff g13
  have hcv : vdenM mv vv (penvN mv.nv (gS P (Wd C0 n d r a pm bbf xf w cff ifin))) (.variable bT (mv.nv + (b + 13))) =
      some (if cff then 1 else 0) := by rw [vdenM_scalar _ _ _ _ rfl]; exact hv
  cases cff
  · simp only [Bool.false_eq_true, if_false] at hcv ⊢
    have hbr := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + (b + 4)) bT (.literal bT 1))) Sk)) Sk) Sk
      _ _ hcv _ (pexecM_skip mv fu _ _)
    have hs := seqM_some hbr (by simp) (pexecM_skip mv fu _ _)
    refine ⟨_, hs, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [gS_mem_len, gS_bs_len, hC, Wc, WS, vwp, NExpr.nodes, NExpr.scalarOnly] <;> omega
  · simp only [if_true] at hcv ⊢
    have g4 : (Wd C0 n d r a pm bbf xf w true ifin)[b + 4]? = some (cb w) := by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC]
    have hv1 : vdenM mv vv (penvN mv.nv (gS P (Wd C0 n d r a pm bbf xf w true ifin))) (.literal bT 1) = some 1 := by
      rw [vdenM_scalar mv vv _ _ rfl, den_literal, if_pos (show bT.valid 1 = true from rfl)]
    have hs := gSM_assign mv P (Wd C0 n d r a pm bbf xf w true ifin) vv (b + 4) (by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC]) bT
      (.literal bT 1) 1 1 hv1 (cb w) g4 rfl (by cases w <;> decide) (by decide)
    have ha := (pexecM_prim mv fu _ _ _).trans hs
    have hb := seqM_some ha rfl (pexecM_skip mv fu _ _)
    have hsc := pexecM_scope mv fu _ _ _ _ hb
    have hset : (Wd C0 n d r a pm bbf xf w true ifin).set (b + 4) ⟨bT, 1⟩ = Wd C0 n d r a pm bbf xf true true ifin := by
      simp only [Wd]; rw [cells_set C0 _ b 4 _ hC]; simp [Wc, WS, cb, List.set]
    rw [hset, scope_same P _ _ (by simp [Wd, WSd, Wc, WS, List.getElem?_append_right, hC])] at hsc
    have hb2 := seqM_some hsc (by simp) (pexecM_skip mv fu _ _)
    have hbr := pexecM_branch_true mv fu _ _ Sk _ _ 1 hcv (by decide) _ hb2
    have hs2 := seqM_some hbr (by simp) (pexecM_skip mv fu _ _)
    refine ⟨_, hs2, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [gS_mem_len, gS_bs_len, hC, Wc, WS, vwp, NExpr.nodes, NExpr.scalarOnly] <;> omega

set_option maxHeartbeats 64000000 in
theorem wit_W2 (mv : MV) (P C0 : List Cell) (b : Nat) (hC : C0.length = b) (n d r a pm bbf x : Nat) (w : Bool) (hn : 2 ≤ n) (hnm : n < M64)
    (hr : r < 2147483640) (hx : x < n) (vv : Nat → List Int) (fu : Nat) (hfu : r + 65 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (.scope (witW2B mv.nv b)) (gS P (WSd C0 n d r a pm bbf x w)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (WSd C0 n d r a pm bbf (wrun n r r (x, true, 0)).1 (if (wrun n r r (x, true, 0)).2.1 then true else w)) ∧
      res.vv = vv ∧ res.cost ≤ CWr r + 400 ∧ res.need ≤ P.length + 2 * (b + 40) + 400 ∧ res.wk = 0 := by
  have d1 := gSM_decl mv P (WSd C0 n d r a pm bbf x w) vv bT (.literal bT 1) 1 1
    (by rw [vdenM_scalar _ _ _ _ rfl]; rw [den_literal, if_pos (show bT.valid 1 = true from rfl)])
    (show bT.convert 1 = some 1 from rfl)
  have a1 := (pexecM_prim mv fu (.declare bT true (.literal bT 1)) _ _).trans d1
  have d2 := gSM_decl mv P (WSd C0 n d r a pm bbf x w ++ [⟨bT, 1⟩]) vv i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; rw [den_literal, if_pos (show i32.valid 0 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a2 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d2
  have hW : WSd C0 n d r a pm bbf x w ++ [⟨bT, 1⟩] ++ [⟨i32, 0⟩] = Wd C0 n d r a pm bbf x w true 0 := by
    simp [Wd, WSd, Wc, cb, cI]
  rw [hW] at a2
  obtain ⟨rw_, hw, hret, hps, hvv, hc, hn', hwk⟩ := wit_while mv P C0 b hC n d r a pm bbf w hn hnm hr vv CWL (by have : CWL = 64 * 420 + 1500 := rfl; omega) r x 0 fu true hx
    (by omega) (by omega) (by omega)
  have eCW : r * CWL = CWr r := rfl
  rw [eCW] at hc
  have brs := wit_brs mv P C0 b hC n d r a pm bbf w vv fu
  obtain ⟨rb, hb, retb, psb, vvb, cbb, nb, wb⟩ := brs (wrun n r r (x, true, 0)).1 (wrun n r r (x, true, 0)).2.2 (wrun n r r (x, true, 0)).2.1
  have s3 := seqM_some hw hret (by rw [hps, hvv]; exact hb)
  have s2 := seqM_some a2 rfl (by exact s3)
  have s1 := seqM_some a1 rfl (by exact s2)
  have hsc := pexecM_scope mv fu _ _ _ _ s1
  refine ⟨_, hsc, by simp [retb], ?_, by simp [vvb], ?_, ?_, by simp [wb, hwk]⟩
  · simp only [psb]
    exact takeW P C0 n d r a pm bbf x w _ _ _ _
  · dsimp only [vwp, NExpr.nodes, NExpr.scalarOnly] at hc cbb ⊢; omega
  · simp [gS_mem_len, gS_bs_len, hC, Wc, WS, vwp, NExpr.nodes, NExpr.scalarOnly] at hn' nb ⊢; omega



theorem ne1_den (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (b : Nat) (x : Nat) (hx : x < M64) (h : cl[b + 12]? = some (cu x)) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .ne (vU mv.nv (b + 12)) oU) = some (if x ≠ 1 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, var_den mv P cl (b + 12) x h hx, Option.bind_some, oU_den, Option.bind_some]
  have := ne_conv (x : Int) 1
  simpa using this

theorem nen1_den (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (b : Nat) (n x : Nat) (hn : 1 ≤ n) (hnm : n < M64) (hx : x < M64)
    (h : cl[b + 12]? = some (cu x)) (h0 : cl[b + 0]? = some (cu n)) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .ne (vU mv.nv (b + 12)) (.binary u64 .sub (vU mv.nv (b + 0)) oU)) =
      some (if x ≠ n - 1 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, var_den mv P cl (b + 12) x h hx, Option.bind_some,
    sub_den _ _ _ n 1 (var_den mv P cl (b + 0) n h0 hnm) (oU_den _) hn hnm, Option.bind_some]
  have := ne_conv (x : Int) ((n - 1 : Nat) : Int)
  simpa using this

set_option maxHeartbeats 64000000 in
theorem wit_C1 (mv : MV) (P C0 : List Cell) (b : Nat) (hC : C0.length = b) (n d r a pm bbf x : Nat) (hn : 2 ≤ n) (hnm : n < M64)
    (hr : r < 2147483640) (hx : x < n) (vv : Nat → List Int) (fu : Nat) (hfu : r + 65 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (witC1B mv.nv b) (gS P (WSd C0 n d r a pm bbf x false)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (WSd C0 n d r a pm bbf (mrX n r x) (mrwx n r x)) ∧
      res.vv = vv ∧ res.cost ≤ CWr r + 800 ∧ res.need ≤ P.length + 2 * (b + 40) + 400 ∧ res.wk = 0 := by
  have hx64 : x < M64 := by omega
  have g12 : (WSd C0 n d r a pm bbf x false)[b + 12]? = some (cu x) := by simp [WSd, WS, List.getElem?_append_right, hC]
  have g0 : (WSd C0 n d r a pm bbf x false)[b + 0]? = some (cu n) := by simp [WSd, WS, List.getElem?_append_right, hC]
  have c1 := ne1_den mv vv P _ b x hx64 g12
  by_cases h1 : x = 1
  · subst h1
    rw [if_neg (by simp)] at c1
    have hbr := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.branch (.binary bT .ne (vU mv.nv (b + 12)) (.binary u64 .sub (vU mv.nv (b + 0)) oU))
      (.sequence (.scope (witW2B mv.nv b)) Sk) Sk) Sk)) Sk) Sk _ _ c1 _ (pexecM_skip mv fu _ _)
    refine ⟨_, hbr, rfl, ?_, rfl, ?_, ?_, rfl⟩
    · simp [mrwx, mrX]
    · exact Nat.le_trans (show _ ≤ 100 by simp [vwp, NExpr.nodes, NExpr.scalarOnly]) (by omega)
    · simp [gS_mem_len, gS_bs_len, hC, WS, vwp, NExpr.nodes, NExpr.scalarOnly] <;> omega
  · rw [if_pos h1] at c1
    have c2 := nen1_den mv vv P _ b n x (by omega) hnm hx64 g12 g0
    by_cases h2 : x = n - 1
    · rw [if_neg (by simp [h2])] at c2
      have b2 := pexecM_branch_false mv fu _ (.sequence (.scope (witW2B mv.nv b)) Sk) Sk _ _ c2 _ (pexecM_skip mv fu _ _)
      have b2s := seqM_some b2 (by simp) (pexecM_skip mv fu _ _)
      have sc := pexecM_scope mv fu _ _ _ _ b2s
      rw [scope_same P _ _ (by simp [WSd, WS])] at sc
      have b3 := seqM_some sc (by simp) (pexecM_skip mv fu _ _)
      have hbr := pexecM_branch_true mv fu _ _ Sk _ _ 1 c1 (by decide) _ b3
      refine ⟨_, hbr, rfl, ?_, rfl, ?_, ?_, rfl⟩
      · simp [mrwx, mrX, h1, h2]
      · exact Nat.le_trans (show _ ≤ 100 by simp [vwp, NExpr.nodes, NExpr.scalarOnly]) (by omega)
      · simp [gS_mem_len, gS_bs_len, hC, WS, vwp, NExpr.nodes, NExpr.scalarOnly] <;> omega
    · rw [if_pos h2] at c2
      obtain ⟨rw_, hw, hret, hps, hvv, hc, hn', hwk⟩ := wit_W2 mv P C0 b hC n d r a pm bbf x false hn hnm hr hx vv fu hfu
      have b2 := pexecM_branch_true mv fu _ _ Sk _ _ 1 c2 (by decide) _ (seqM_some hw hret (pexecM_skip mv fu _ _))
      have b2s := seqM_some b2 (by simp) (pexecM_skip mv fu _ _)
      have sc := pexecM_scope mv fu _ _ _ _ b2s
      simp only [hps] at sc
      rw [scope_same P _ _ (by simp [WSd, WS])] at sc
      have b3 := seqM_some sc (by simp) (pexecM_skip mv fu _ _)
      have hbr := pexecM_branch_true mv fu _ _ Sk _ _ 1 c1 (by decide) _ b3
      refine ⟨_, hbr, rfl, ?_, hvv, ?_, ?_, ?_⟩
      · simp [mrwx, mrX, h1, h2]
      · exact Nat.le_trans (show _ ≤ rw_.cost + 100 by simp [vwp, NExpr.nodes, NExpr.scalarOnly]) (by omega)
      · have hl : (WSd C0 n d r a pm bbf x false).length = b + 13 := by simp [WSd, WS, hC]
        simp [gS_mem_len, gS_bs_len, hC, hl, vwp, NExpr.nodes, NExpr.scalarOnly] at hn' ⊢; omega
      · simp [hwk]


set_option maxHeartbeats 64000000 in
theorem wit_pre_exec (mv : MV) (P C0 : List Cell) (b : Nat) (hC : C0.length = b) (n d r a : Nat) (hn : 2 ≤ n) (hnm : n < M64)
    (hr : r < 2147483640) (ha : a < n) (hd : d < M64) (vv : Nat → List Int) (fu : Nat) (hfu : r + 200 ≤ fu)
    (R : Command) (rR : PRM)
    (hR : pexecM mv fu R (gS P (WSd C0 n d r a (a ^ d % n) ((prun n 64 (1, a, d)).2.1) (mrX n r (a ^ d % n)) (mrwx n r (a ^ d % n)))) vv = some rR) :
    ∃ res : PRM, pexecM mv fu (witPreK mv.nv b R) (gS P (C0 ++ [cu n, cu d, cI r, cu a])) vv = some res ∧
      res.ret = rR.ret ∧ res.ps = rR.ps ∧ res.vv = rR.vv ∧
      res.cost ≤ rR.cost + 64 * CPW 0 + CWr r + 2000 ∧ res.need ≤ max rR.need (P.length + 2 * (b + 40) + 800) ∧ res.wk = rR.wk := by
  have d1 := gSM_decl mv P (C0 ++ [cu n, cu d, cI r, cu a]) vv bT (.literal bT 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; rw [den_literal, if_pos (show bT.valid 0 = true from rfl)])
    (show bT.convert 0 = some 0 from rfl)
  have a1 := (pexecM_prim mv fu (.declare bT true (.literal bT 0)) _ _).trans d1
  have hx0 : a ^ d % n < n := Nat.mod_lt _ (by omega)
  obtain ⟨rc, hc1, retc, psc, vvc, cc, nc, wkc⟩ := wit_C1 mv P C0 b hC n d r a (a ^ d % n) ((prun n 64 (1, a, d)).2.1) (a ^ d % n) hn hnm hr hx0 vv fu
    (by omega)
  have hcc : callCellsP (C0 ++ [cu n, cu d, cI r, cu a] ++ [(⟨bT, 0⟩ : Cell)]) a d n = WSd C0 n d r a (a ^ d % n) ((prun n 64 (1, a, d)).2.1) (a ^ d % n) false := by
    simp [callCellsP, CLp, WSd, WS, cb]
  have hK := seqM_some hc1 retc (by rw [psc, vvc]; exact hR)
  have hl4 : (C0 ++ [cu n, cu d, cI r, cu a] ++ [(⟨bT, 0⟩ : Cell)]).length = b + 5 := by simp [hC]
  have hp := powcallD_exec mv P (C0 ++ [cu n, cu d, cI r, cu a] ++ [(⟨bT, 0⟩ : Cell)]) (b + 3) (b + 1) b a d n (by simp [List.getElem?_append_right, hC])
    (by simp [List.getElem?_append_right, hC]) (by simp [List.getElem?_append_right, hC]) ha hn hnm hd vv fu
    (by omega) _ _ (by rw [hcc]; exact hK)
  rw [hl4] at hp
  obtain ⟨rp, hp1, retp, psp, vvp, cp, np, wkp⟩ := hp
  have s1 := seqM_some a1 rfl (by exact hp1)
  refine ⟨_, s1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [retp]
  · simp [psp]
  · simp [vvp]
  · dsimp only [vwp, NExpr.nodes] at cp cc ⊢
    omega
  · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes] at np nc ⊢
    omega
  · simp [wkp, wkc]

theorem witLoopB_eq (nv : Nat) : IsPrimeBody.witLoop nv = witLoopB nv 0 := rfl
theorem witW2B_eq (nv : Nat) : IsPrimeBody.witW2 nv = witW2B nv 0 := rfl
theorem witKB_eq (nv : Nat) : IsPrimeExec.witK nv = witKB nv 0 := rfl
theorem witBodyB_eq (nv : Nat) : IsPrimeBody.witBody nv = witBodyB nv 0 := rfl
theorem witBodyB_pre (nv b : Nat) : witBodyB nv b = witPreK nv b (.sequence (.primitive (.ret (.variable bT (nv + (b + 4))))) Sk) := rfl

end Proofs.IsPrimeWit
