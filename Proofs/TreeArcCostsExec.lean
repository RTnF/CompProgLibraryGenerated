import Proofs.TreeArcsExec
import Proofs.Generated.TreeArcCosts

namespace Proofs.TreeArcCostsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs)
open Proofs.TopoSortExec (i32v)
open Proofs.TreeEdgesExec (pair_pad flat2_len)
open Proofs.TreeArcsExec (idxE idx2 idx21 idx2_den idx21_den)

/-! ### `tree_arc_costs<long long>` (nv = 2: cost, ac).  Cells: 0 = m, 1 = i, 2 = c -/

abbrev dC (nv : Nat) : NStmt := .declare s64 true (.read s64 (.local 0) (idxE nv))
abbrev wC1 (nv : Nat) : NStmt := .write (.local 1) s64 (idx2 nv) (.variable s64 (nv + 2))
abbrev wC2 (nv : Nat) : NStmt := .write (.local 1) s64 (idx21 nv) (.variable s64 (nv + 2))
abbrev Bc (nv : Nat) : Command :=
  .sequence (.primitive (dC nv)) (.sequence (.primitive (wC1 nv)) (.sequence (.primitive (wC2 nv)) Sk))
abbrev bodyAC (nv : Nat) : Command := .sequence (forStmtB nv 1 0 (Bc nv)) Sk

theorem body_eqAC : Proofs.TreeArcCostsInstance.tree_arc_costs_std_vector_long_long.body = bodyAC 2 := rfl

def VC (C AC : List Int) : Nat → List Int := fun k => if k = 0 then C else if k = 1 then AC else []
theorem VC_get0 (C AC : List Int) : VC C AC 0 = C := by simp [VC]
theorem VC_get1 (C AC : List Int) : VC C AC 1 = AC := by simp [VC]
theorem VC_set1 (C AC x : List Int) : upd (VC C AC) 1 x = VC C x := by
  funext k; unfold upd VC; split <;> simp_all

def ilvC (C : List Int) (t : Nat) : List Int := (List.range t).flatMap (fun i => [C.getD i 0, C.getD i 0])

theorem ilvC_succ (C : List Int) (t : Nat) : ilvC C (t + 1) = ilvC C t ++ [C.getD t 0, C.getD t 0] := by
  unfold ilvC
  rw [List.range_succ, List.flatMap_append]
  simp

theorem ilvC_len (C : List Int) (t : Nat) : (ilvC C t).length = 2 * t := by
  unfold ilvC
  rw [flat2_len (fun i => [C.getD i 0, C.getD i 0]) (fun i => rfl)]
  simp

def ACt (C AC : List Int) (t : Nat) : List Int := ilvC C t ++ AC.drop (2 * t)

theorem ACt_len (C AC : List Int) (t : Nat) (h : 2 * t ≤ AC.length) : (ACt C AC t).length = AC.length := by
  unfold ACt; rw [List.length_append, ilvC_len, List.length_drop]; omega

theorem ACt_succ (C AC : List Int) (t : Nat) (h : 2 * t + 1 < AC.length) :
    ((ACt C AC t).set (2 * t) (C.getD t 0)).set (2 * t + 1) (C.getD t 0) = ACt C AC (t + 1) := by
  unfold ACt
  rw [pair_pad _ AC (2 * t) _ _ (ilvC_len C t) h, ilvC_succ]
  simp [List.append_assoc]
  rfl

set_option maxHeartbeats 16000000 in
/-- One iteration of the loop. -/
theorem b_body (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (C AC : List Int) (P : List Cell)
    (m t : Nat) (hm : m < M31) (ht : t < m) (h2 : 2 * t + 1 < M31) (hC : t < C.length) (hAC : 2 * t + 1 < AC.length)
    (hcv : s64.valid (C.getD t 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Bc mv.nv) (gS P [ci m, ci t]) (VC C AC) = some r ∧ r.ret = none ∧
      r.ps = gS P ([ci m] ++ [ci t] ++ [cs (C.getD t 0)]) ∧
      r.vv = VC C ((AC.set (2 * t) (C.getD t 0)).set (2 * t + 1) (C.getD t 0)) ∧
      r.cost ≤ 200 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 2 := by
  have htM : t < M31 := Nat.lt_trans ht hm
  generalize hcdef : C.getD t 0 = c at hcv ⊢
  have E1 := envs mv P [ci m, ci t] 1 (ci t) rfl (i32v t htM)
  have r1 := rdM_val mv (VC C AC) (penvN mv.nv (gS P [ci m, ci t])) 0 (by omega) s64 ty0.symm (idxE mv.nv) rfl rfl t
    (cidx_den _ (mv.nv + 1) t E1 htM) c (by rw [VC_get0, ← hcdef]; exact vec_getI C t hC) (by rw [ty0]; exact hcv)
  have d1 := gSM_decl mv P [ci m, ci t] (VC C AC) s64 _ _ _ r1 (conv_signed s64 rfl rfl _ hcv)
  have q1 := (pexecM_prim mv fu (dC mv.nv) _ _).trans d1
  have E1' := envs mv P [ci m, ci t, cs c] 1 (ci t) rfl (i32v t htM)
  have E2 := envs mv P [ci m, ci t, cs c] 2 (cs c) rfl hcv
  have hi2 : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci m, ci t, cs c])) (idx2 mv.nv) = some ((2 * t : Nat) : Int) := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl]; exact idx2_den _ (mv.nv + 1) t E1' h2
  have hi21 : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci m, ci t, cs c])) (idx21 mv.nv) = some ((2 * t + 1 : Nat) : Int) := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl]; exact idx21_den _ (mv.nv + 1) t E1' h2
  have hvc : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci m, ci t, cs c])) (.variable s64 (mv.nv + 2)) = some c := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2
  have w1 := pstmtM_write_ok mv (gS P [ci m, ci t, cs c]) (VC C AC) 1 (by omega) (idx2 mv.nv) (.variable s64 (mv.nv + 2)) c (2 * t)
    (hvc _) (hi2 _) (by rw [VC_get1]; omega) (by rw [ty1]; exact hcv)
  rw [ty1, VC_get1, VC_set1] at w1
  have a1 := (pexecM_prim mv fu (wC1 mv.nv) _ _).trans w1
  have w2 := pstmtM_write_ok mv (gS P [ci m, ci t, cs c]) (VC C (AC.set (2 * t) c)) 1 (by omega) (idx21 mv.nv)
    (.variable s64 (mv.nv + 2)) c (2 * t + 1) (hvc _) (hi21 _) (by rw [VC_get1]; simp; omega) (by rw [ty1]; exact hcv)
  rw [ty1, VC_get1, VC_set1] at w2
  have a2 := (pexecM_prim mv fu (wC2 mv.nv) _ _).trans w2
  have b3 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  have b2 := seqM_some a1 rfl b3
  have b1 := seqM_some q1 rfl b2
  refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

set_option maxHeartbeats 16000000 in
/-- The whole body of `tree_arc_costs<long long>`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (C AC : List Int) (P : List Cell)
    (m : Nat) (hm : m < 536870912) (hC : m ≤ C.length) (hAC : 2 * m ≤ AC.length) (hCv : ∀ x ∈ C, s64.valid x = true)
    (fu : Nat) (hfu : m + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyAC mv.nv) (gS P [ci m]) (VC C AC) = some r ∧ r.ret = none ∧
      r.vv = VC C (ACt C AC m) ∧ (∃ cs : List Cell, r.ps = gS P cs) ∧
      r.cost ≤ 220 * m + 40 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 2 * m := by
  have hmM : m < M31 := by show m < 2147483648; omega
  have memC : ∀ j, j < C.length → s64.valid (C.getD j 0) = true := fun j hj => hCv _ (getD_mem _ _ hj)
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 1 0 m (by omega) (by omega) (Bc mv.nv)
    (fun t vv Cc => vv = VC C (ACt C AC t) ∧ Cc = [ci m]) 200 60 2 0 (by omega)
    (by
      intro t vv Cc fu ht hCl' hC0 ⟨hvv, hCc⟩ _
      subst hvv; subst hCc
      have hlA := ACt_len C AC t (by omega)
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := b_body mv hnv ty0 ty1 C (ACt C AC t) P m t hmM ht
        (by show 2 * t + 1 < 2147483648; omega) (by omega) (by omega) (memC t (by omega)) fu
      refine ⟨r, [cs (C.getD t 0)], [ci m], hr, hret, hps, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      rw [hvv, ACt_succ C AC t (by omega)])
    (VC C (ACt C AC 0)) [ci m] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hCc⟩ := hIn
  subst hCc
  have t1 := seqM_some hr' hret (pexecM_skip mv fu _ _)
  refine ⟨_, t1, by simp [hret], ?_, ⟨[ci m], by simp [hps]⟩, ?_, ?_, ?_⟩
  · simp [hvv]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hps] at hnd ⊢; omega
  · simp at hw ⊢; omega

end Proofs.TreeArcCostsExec
