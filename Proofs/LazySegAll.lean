import Proofs.LazySegCtorRep

namespace Proofs.LazySegAll
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI envs cs)
open Proofs.InvGcdExec (vS vr)
open Proofs.SegTreeMath
open Proofs.LazySegMath (Rep Cl)
open Proofs.LazySegChmin (chminMon)
open Proofs.SegmentTreeExec (maxMon)
open Proofs.LazySegRange (treeVec treeVec_len treeVec_get treeVec_allV treeVec_TInv rfold_leaves node_clean)

theorem root_fold (A : List Int) (N h : Nat) (hN : N = 2 ^ h) (hA : A.length = N) (hAV : AllV chminMon.toMon A) :
    rfold maxMon (treeVec A N) 1 1 = rfold maxMon A 0 N := by
  have hNpos : 0 < N := by rw [hN]; exact Nat.two_pow_pos h
  have hV := treeVec_allV A N hNpos hA hAV
  have hT := treeVec_TInv A N hNpos
  have key : ∀ j, j ≤ h → rfold maxMon (treeVec A N) (2 ^ j) (2 ^ j) = rfold maxMon (treeVec A N) 1 1 := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have h1 := rfold_pairs maxMon (treeVec A N) N hV hT (2 ^ j) (2 ^ j) (Nat.two_pow_pos j) (by
        have : 2 ^ (j + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) hj
        rw [Nat.pow_succ] at this; omega)
      have e : 2 * 2 ^ j = 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
      rw [e] at h1
      rw [h1, ih (by omega)]
  have := key h le_rfl
  rw [← hN] at this
  have h2 := rfold_leaves A N hA N 0 (by omega)
  rw [Nat.add_zero] at h2
  rw [← this, h2]

abbrev bodyAll (nv : Nat) : Command :=
  .sequence (.primitive (.ret (.read s64 (.local 0) (.cast u64 (.literal i32 1))))) Sk

theorem body_eqAll : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product_all.body
    = bodyAll 2 := rfl

theorem body_execAll (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (P : List Cell) (vv : Nat → List Int) (n h : Nat)
    (A : List Int) (hh : 1 ≤ h) (hR : Rep chminMon (2 ^ h) A (vv 0) (vv 1)) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (bodyAll mv.nv) (gS P [ci n, ci (2 ^ h), ci h]) vv = some r ∧
      r.ret = some (rfold maxMon A 0 (2 ^ h)) ∧ r.vv = vv ∧ (∃ cl : List Cell, r.ps = gS P cl) ∧ r.cost ≤ 40 ∧
      r.need ≤ P.length + 40 ∧ r.wk = 0 := by
  have hNpos : 0 < 2 ^ h := Nat.two_pow_pos h
  have hN2 : 2 ≤ 2 ^ h := by
    have : 2 ^ 1 ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) hh
    simpa using this
  have hlen := hR.1
  have hd : (NExpr.cast u64 (.literal i32 1)).denote (penvN mv.nv (gS P [ci n, ci (2 ^ h), ci h])) = some ((1 : Nat) : Int) := by
    rw [den_cast, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some, convert_u64]
    rfl
  have hCl : Cl chminMon (vv 1) 1 := by
    intro t ht h1
    have h2t : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht
    have : 1 / 2 ^ t = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hx := Proofs.LazySegRange.node_clean (2 ^ h) A (vv 0) (vv 1) 1 hR hCl (by omega) (by omega)
  have hxV := Proofs.LazySegMath.getD_Ve chminMon (vv 0) hR.2.2.2.1 1 (by omega)
  have hxv : s64.valid ((vv 0).getD 1 0) = true := by
    rw [Proofs.LazySegBlocks.getD_dflt (vv 0) 1 0 chminMon.e (by omega)]; exact hxV
  have hrd := rdM_val mv vv _ 0 (by omega) s64 ty0.symm (.cast u64 (.literal i32 1)) rfl rfl 1 hd
    ((vv 0).getD 1 0) (vec_getI (vv 0) 1 (by omega)) (by rw [ty0]; exact hxv)
  have rr := pstmtM_ret_ok mv (gS P [ci n, ci (2 ^ h), ci h]) vv _ _ hrd
  have e1 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have hval : (vv 0).getD 1 0 = rfold maxMon A 0 (2 ^ h) := by
    rw [Proofs.LazySegBlocks.getD_dflt (vv 0) 1 0 chminMon.e (by omega), hx, ← root_fold A (2 ^ h) h rfl hR.2.2.1 hR.2.2.2.2.2.1,
      ← treeVec_get A (2 ^ h) 1 (by omega)]
    show (treeVec A (2 ^ h)).getD 1 0 = maxMon.op ((treeVec A (2 ^ h)).getD 1 0) maxMon.e
    have hV := treeVec_allV A (2 ^ h) hNpos hR.2.2.1 hR.2.2.2.2.2.1
    rw [maxMon.rid _ (Proofs.SegTreeMath.getD_V maxMon _ hV 1 (by rw [treeVec_len]; omega))]
  refine ⟨_, e1, ?_, rfl, ⟨_, rfl⟩, ?_, ?_, rfl⟩
  · show some ((vv 0).getD 1 0) = _
    rw [hval]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]

end Proofs.LazySegAll
