import Proofs.IsPrimeSpec

/-! The five public functions of `is_prime.hpp`, each run as a whole function body (parameters in the first cells). -/
namespace Proofs.IsPrimeFun
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.BellmanFordExec (envs)
open Proofs.IsPrimeBody Proofs.IsPrimeExec Proofs.IsPrimeWit Proofs.IsPrimeTop Proofs.IsPrimeRun

set_option maxHeartbeats 64000000 in
theorem mul_fun (mv : MV) (P : List Cell) (a bb m : Nat) (ha : a < m) (hb : bb < m) (hm : m < M64) (vv : Nat → List Int)
    (fu : Nat) (hfu : 65 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (mulBody mv.nv 0 (.sequence (.primitive (.ret (vU mv.nv 3))) Sk)) (gS P [cu a, cu bb, cu m]) vv = some res ∧
      res.ret = some (((a * bb) % m : Nat) : Int) ∧ res.vv = vv ∧ (∃ cl : List Cell, res.ps = gS P cl) ∧
      res.cost ≤ 64 * 420 + 400 ∧ res.need ≤ P.length + 2 * 20 + 300 ∧ res.wk = 0 := by
  have hr : (a * bb) % m < M64 := by have := Nat.mod_lt (a * bb) (show 0 < m by omega); omega
  have key : ∀ xf : Nat, ∃ e3 : PRM, pexecM mv fu (.sequence (.primitive (.ret (vU mv.nv 3))) Sk)
      (gS P (CLm [] a bb m ((a * bb) % m) xf 0)) vv = some e3 ∧ e3.ret = some (((a * bb) % m : Nat) : Int) ∧
      e3.ps = gS P (CLm [] a bb m ((a * bb) % m) xf 0) ∧ e3.vv = vv ∧ e3.cost ≤ 10 ∧ e3.need ≤ P.length + 2 * 7 + 10 ∧ e3.wk = 0 := by
    intro xf
    have g3 : (CLm [] a bb m ((a * bb) % m) xf 0)[3]? = some (cu ((a * bb) % m)) := by simp
    have rr := pstmtM_ret_ok mv (gS P (CLm [] a bb m ((a * bb) % m) xf 0)) vv (vU mv.nv 3) (((a * bb) % m : Nat) : Int)
      (by rw [vdenM_scalar _ _ _ _ rfl]; exact var_den mv P _ 3 _ g3 hr)
    have e3 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
    refine ⟨_, e3, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes]
    · simp [gS_mem_len, gS_bs_len, CLm, vwp, NExpr.nodes]
  obtain ⟨e3, he3, ret3, ps3, vv3, c3, n3, w3⟩ := key (mrun m 64 (0, a, bb)).2.1
  obtain ⟨res, h1, h2, h3, h4, h5, h6, h7⟩ := mul_block mv P [] 0 a bb m rfl ha hb hm vv fu hfu _ _ he3
  have hl : ([] ++ [cu a, cu bb, cu m] : List Cell) = [cu a, cu bb, cu m] := rfl
  rw [hl] at h1
  refine ⟨res, h1, by simp [h2, ret3], by rw [h4, vv3], ⟨_, by rw [h3, ps3]⟩, ?_, ?_, by simp [h7, w3]⟩
  · omega
  · omega


set_option maxHeartbeats 64000000 in
theorem pow_fun (mv : MV) (P : List Cell) (x y m : Nat) (hx : x < m) (hm : 2 ≤ m) (hm64 : m < M64) (hy : y < M64)
    (vv : Nat → List Int) (fu : Nat) (hfu : 64 + 65 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (powBody mv.nv 0 (.sequence (.primitive (.ret (vU mv.nv 3))) Sk)) (gS P [cu x, cu y, cu m]) vv = some res ∧
      res.ret = some (((x ^ y) % m : Nat) : Int) ∧ res.vv = vv ∧ (∃ cl : List Cell, res.ps = gS P cl) ∧
      res.cost ≤ 64 * CPW 0 + 400 ∧ res.need ≤ P.length + 2 * 20 + 500 ∧ res.wk = 0 := by
  have hr : (x ^ y) % m < M64 := by have := Nat.mod_lt (x ^ y) (show 0 < m by omega); omega
  have key : ∀ xf : Nat, ∃ e3 : PRM, pexecM mv fu (.sequence (.primitive (.ret (vU mv.nv 3))) Sk)
      (gS P (CLp [] x y m ((x ^ y) % m) xf 0)) vv = some e3 ∧ e3.ret = some (((x ^ y) % m : Nat) : Int) ∧
      e3.ps = gS P (CLp [] x y m ((x ^ y) % m) xf 0) ∧ e3.vv = vv ∧ e3.cost ≤ 10 ∧ e3.need ≤ P.length + 2 * 7 + 10 ∧ e3.wk = 0 := by
    intro xf
    have g3 : (CLp [] x y m ((x ^ y) % m) xf 0)[3]? = some (cu ((x ^ y) % m)) := by simp
    have rr := pstmtM_ret_ok mv (gS P (CLp [] x y m ((x ^ y) % m) xf 0)) vv (vU mv.nv 3) (((x ^ y) % m : Nat) : Int)
      (by rw [vdenM_scalar _ _ _ _ rfl]; exact var_den mv P _ 3 _ g3 hr)
    have e3 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
    refine ⟨_, e3, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes]
    · simp [gS_mem_len, gS_bs_len, CLp, vwp, NExpr.nodes]
  obtain ⟨e3, he3, ret3, ps3, vv3, c3, n3, w3⟩ := key (prun m 64 (1, x, y)).2.1
  obtain ⟨res, h1, h2, h3, h4, h5, h6, h7⟩ := pow_block mv P [] 0 x y m rfl hx hm hm64 hy vv fu hfu _ _ he3
  have hl : ([] ++ [cu x, cu y, cu m] : List Cell) = [cu x, cu y, cu m] := rfl
  rw [hl] at h1
  refine ⟨res, h1, by simp [h2, ret3], by rw [h4, vv3], ⟨_, by rw [h3, ps3]⟩, ?_, ?_, by simp [h7, w3]⟩
  · omega
  · omega

set_option maxHeartbeats 64000000 in
theorem base_fun (mv : MV) (P : List Cell) (i : Nat) (hi : i < 2147483648) (vv : Nat → List Int) (fu : Nat) :
    ∃ res : PRM, pexecM mv fu (mrBaseBody mv.nv) (gS P [cI i]) vv = some res ∧
      res.ret = some ((mrb i : Nat) : Int) ∧ res.vv = vv ∧ (∃ cl : List Cell, res.ps = gS P cl) ∧
      res.cost ≤ 800 ∧ res.need ≤ P.length + 2 * 2 + 100 ∧ res.wk = 0 := by
  have hM : (2147483648 : Nat) < M64 := by decide
  have h37 : mrb i ≤ 37 := by unfold mrb; repeat' (first | split | omega)
  have hpb : mrb i < M64 := by omega
  have d1 := gSM_decl mv P [cI i] vv u64 (cU 37) 37 37
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact cU_den _ 37 (by decide) (by decide)) (Ty.convert_of_valid _ _ (u64v 37 (by omega)))
  have a1 := (pexecM_prim mv fu (.declare u64 true (cU 37)) _ _).trans d1
  have g1 : ([cI i] ++ [(⟨u64, 37⟩ : Cell)])[1]? = some (cu 37) := by simp [cu]
  have g0 : ([cI i] ++ [(⟨u64, 37⟩ : Cell)])[0]? = some (cI i) := by simp
  have gr : ([cI i] ++ [(⟨u64, 37⟩ : Cell)]).set 1 (cu (mrb i)) = [cI i, cu (mrb i)] := by simp [List.set]
  have g3 : ([cI i, cu (mrb i)] : List Cell)[1]? = some (cu (mrb i)) := by simp
  have rr := pstmtM_ret_ok mv (gS P [cI i, cu (mrb i)]) vv (.variable u64 (mv.nv + 1)) ((mrb i : Nat) : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact var_den mv P _ 1 _ g3 hpb)
  have e3 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  obtain ⟨rc, hc, retc, psc, vvc, cc, nc, wkc⟩ := base_chain_exec mv P 0 1 i (by decide) hi vv fu ([cI i] ++ [(⟨u64, 37⟩ : Cell)]) g0 g1 _ _
    (by rw [gr]; exact e3)
  have s1 := seqM_some a1 rfl hc
  refine ⟨_, s1, by simp [retc], by simp [vvc], ⟨[cI i, cu (mrb i)], by simp [psc]⟩, ?_, ?_, by simp [wkc]⟩
  · simp [vwp, NExpr.nodes] at cc ⊢; omega
  · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes] at nc ⊢; omega


set_option maxHeartbeats 64000000 in
theorem wit_fun (mv : MV) (P : List Cell) (n d r a : Nat) (hn : 2 ≤ n) (hnm : n < M64) (hr : r < 2147483640) (ha : a < n)
    (hd : d < M64) (vv : Nat → List Int) (fu : Nat) (hfu : r + 200 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (witBodyB mv.nv 0) (gS P [cu n, cu d, cI r, cu a]) vv = some res ∧
      res.ret = some (if mrwx n r (a ^ d % n) then 1 else 0) ∧ res.vv = vv ∧ (∃ cl : List Cell, res.ps = gS P cl) ∧
      res.cost ≤ 64 * CPW 0 + CWr r + 2100 ∧ res.need ≤ P.length + 2 * 40 + 900 ∧ res.wk = 0 := by
  have key : ∃ e3 : PRM, pexecM mv fu (.sequence (.primitive (.ret (.variable bT (mv.nv + (0 + 4))))) Sk)
      (gS P (WSd [] n d r a (a ^ d % n) ((prun n 64 (1, a, d)).2.1) (mrX n r (a ^ d % n)) (mrwx n r (a ^ d % n)))) vv = some e3 ∧
      e3.ret = some (if mrwx n r (a ^ d % n) then 1 else 0) ∧
      e3.ps = gS P (WSd [] n d r a (a ^ d % n) ((prun n 64 (1, a, d)).2.1) (mrX n r (a ^ d % n)) (mrwx n r (a ^ d % n))) ∧
      e3.vv = vv ∧ e3.cost ≤ 10 ∧ e3.need ≤ P.length + 2 * 13 + 10 ∧ e3.wk = 0 := by
    have g4 : (WSd [] n d r a (a ^ d % n) ((prun n 64 (1, a, d)).2.1) (mrX n r (a ^ d % n)) (mrwx n r (a ^ d % n)))[0 + 4]? =
        some (cb (mrwx n r (a ^ d % n))) := by simp [WSd, WS]
    have rv := varb_den mv P _ (0 + 4) _ g4
    have rr := pstmtM_ret_ok mv (gS P (WSd [] n d r a (a ^ d % n) ((prun n 64 (1, a, d)).2.1) (mrX n r (a ^ d % n)) (mrwx n r (a ^ d % n)))) vv
      (.variable bT (mv.nv + (0 + 4))) (if mrwx n r (a ^ d % n) then 1 else 0)
      (by rw [vdenM_scalar _ _ _ _ rfl]; exact rv)
    have e3 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
    refine ⟨_, e3, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes]
    · simp [gS_mem_len, gS_bs_len, WSd, WS, vwp, NExpr.nodes]
  obtain ⟨e3, he3, ret3, ps3, vv3, c3, n3, w3⟩ := key
  obtain ⟨res, h1, h2, h3, h4, h5, h6, h7⟩ := wit_pre_exec mv P [] 0 rfl n d r a hn hnm hr ha hd vv fu hfu _ _ he3
  have hl : ([] ++ [cu n, cu d, cI r, cu a] : List Cell) = [cu n, cu d, cI r, cu a] := rfl
  rw [hl] at h1
  refine ⟨res, h1, by simp [h2, ret3], by rw [h4, vv3], ⟨_, by rw [h3, ps3]⟩, ?_, ?_, by simp [h7, w3]⟩
  · omega
  · omega

theorem is_prime_fun (mv : MV) (P : List Cell) (n : Nat) (hnm : n < M64) (vv : Nat → List Int) (fu : Nat) (hfu : 400 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (isBodyT mv.nv) (gS P [cu n]) vv = some res ∧
      res.ret = some (if ispSpec n then 1 else 0) ∧ res.vv = vv ∧ (∃ cl : List Cell, res.ps = gS P cl) ∧
      res.cost ≤ TOPC + 200 ∧ res.need ≤ P.length + 2 * 60 + 1000 ∧ res.wk = 0 :=
  top_exec mv P n hnm vv fu hfu

end Proofs.IsPrimeFun
