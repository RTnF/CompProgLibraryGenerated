import Proofs.LazySegUpdE
import Proofs.LazySegApplyLoop

namespace Proofs.LazySegApplyExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.ForLoopC (gS_takeC)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs pexecM_branch_true pexecM_branch_false)
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den)
open Proofs.RunLengthExec (inc_val)
open Proofs.LazySegBlocks
open Proofs.SegTreeMath
open Proofs.LazySegMath
open Proofs.LazySegChmin (chminMon mi)
open Proofs.LazySegApplyLoop (stepN stepZ cu)
open Proofs.LazySegProduct (oddE incL decR halveL halveR odd_val dec_val)

/-- The cells of `update(l, r, f)` while the `all_apply` loop runs:
`n`, `n_node`, `h_node`, `l`, `r`, `f`, `pw`, `l2`, `r2`. -/
abbrev AL (n N h l r : Nat) (f : Int) (pw l2 r2 : Nat) : List Cell :=
  [ci n, ci N, ci h, ci l, ci r, cs f, ci pw, ci l2, ci r2]

abbrev BrL (nv : Nat) : Command :=
  .sequence (.scope (AACall nv 9 0 1 2 (.variable i32 (nv + 3)) (.variable s64 (nv + 5))
    (.sequence (.primitive (incL nv)) Sk))) Sk

abbrev BrR (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (decR nv))
    (AACall nv 9 0 1 2 (.variable i32 (nv + 4)) (.variable s64 (nv + 5)) Sk))) Sk

abbrev LoopBodyU (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (oddE nv 3) (BrL nv) Sk) (.sequence (.branch (oddE nv 4) (BrR nv) Sk)
    (.sequence (.primitive (halveL nv)) (.sequence (.primitive (halveR nv)) Sk))))) Sk

/-- Shape of the vectors the loop works on. -/
def VOK (N : Nat) (vv : Nat → List Int) : Prop :=
  (vv 0).length = 2 * N ∧ (vv 1).length = N ∧ AllV chminMon.toMon (vv 0) ∧ AllF chminMon (vv 1)

theorem aaVV_ok (N k : Nat) (f : Int) (vv : Nat → List Int) (hV : VOK N vv) (hk : k < 2 * N) (hf : s64.valid f = true) :
    VOK N (aaVV vv N k f) ∧ aaVV vv N k f 0 = applyNode chminMon (vv 0) k f ∧
      aaVV vv N k f 1 = alz chminMon N (vv 1) k f ∧ (∀ j, j ≠ 0 → j ≠ 1 → aaVV vv N k f j = vv j) := by
  obtain ⟨h0, h1, hv0, hf1⟩ := hV
  have e0 : aaVV vv N k f 0 = applyNode chminMon (vv 0) k f := by
    rw [aaVV_0]
    unfold applyNode
    rw [getD_dflt (vv 0) k 0 chminMon.e (by omega)]
    rfl
  have e1 : aaVV vv N k f 1 = alz chminMon N (vv 1) k f := by
    rw [aaVV_1]
    unfold alz
    by_cases hk' : k < N
    · rw [if_pos hk', if_pos hk', getD_dflt (vv 1) k 0 chminMon.fid (by omega)]
      rfl
    · rw [if_neg hk', if_neg hk']
  refine ⟨⟨?_, ?_, ?_, ?_⟩, e0, e1, fun j hj0 hj1 => aaVV_other _ _ _ _ _ hj0 hj1⟩
  · rw [aaVV_len0]; exact h0
  · rw [aaVV_len1]; exact h1
  · rw [e0]; exact allV_applyNode chminMon (vv 0) hv0 k f hf (by omega)
  · rw [e1]; exact allF_alz chminMon N (vv 1) hf1 k f hf

/-- The vectors after one round of the `all_apply` loop. -/
def stepVV (N : Nat) (f : Int) (a b : Nat) (vv : Nat → List Int) : Nat → List Int :=
  let v1 := if a % 2 = 1 then aaVV vv N a f else vv
  if b % 2 = 1 then aaVV v1 N (b - 1) f else v1

theorem stepVV_ok (N : Nat) (f : Int) (a b : Nat) (vv : Nat → List Int) (hV : VOK N vv) (ha : a % 2 = 1 → a < 2 * N)
    (hb : b % 2 = 1 → b - 1 < 2 * N) (hf : s64.valid f = true) :
    VOK N (stepVV N f a b vv) ∧ stepVV N f a b vv 0 = stepN N f a b (vv 0) ∧ stepVV N f a b vv 1 = stepZ N f a b (vv 1) ∧
      (∀ j, j ≠ 0 → j ≠ 1 → stepVV N f a b vv j = vv j) := by
  by_cases hao : a % 2 = 1
  · obtain ⟨o1, e01, e11, ot1⟩ := aaVV_ok N a f vv hV (ha hao) hf
    by_cases hbo : b % 2 = 1
    · obtain ⟨o2, e02, e12, ot2⟩ := aaVV_ok N (b - 1) f _ o1 (hb hbo) hf
      unfold stepVV stepN stepZ
      simp only [if_pos hao, if_pos hbo]
      refine ⟨o2, ?_, ?_, fun j hj0 hj1 => by rw [ot2 j hj0 hj1, ot1 j hj0 hj1]⟩
      · rw [e02, e01]
      · rw [e12, e11]
    · unfold stepVV stepN stepZ
      simp only [if_pos hao, if_neg hbo]
      exact ⟨o1, e01, e11, ot1⟩
  · by_cases hbo : b % 2 = 1
    · obtain ⟨o2, e02, e12, ot2⟩ := aaVV_ok N (b - 1) f vv hV (hb hbo) hf
      unfold stepVV stepN stepZ
      simp only [if_neg hao, if_pos hbo]
      exact ⟨o2, e02, e12, ot2⟩
    · unfold stepVV stepN stepZ
      simp only [if_neg hao, if_neg hbo]
      simp [hV]

set_option maxHeartbeats 64000000 in
/-- `if (l % 2 == 1) { all_apply(l, f); l++; }` -/
theorem brL_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell) (fu : Nat)
    (vv : Nat → List Int) (n N h l r pw lo ro : Nat) (f : Int) (hn : n < 2147483648) (hN : N < 2147483648)
    (hh : h < 2147483648) (hl : l + 1 < 2147483648) (vf : s64.valid f = true)
    (hodd : l % 2 = 1 → l < (vv 0).length ∧ s64.valid ((vv 0).getD l 0) = true ∧
      (l < N → l < (vv 1).length ∧ s64.valid ((vv 1).getD l 0) = true)) :
    ∃ r1 : PRM, pexecM mv fu (.branch (oddE mv.nv 3) (BrL mv.nv) Sk) (gS P (AL n N h l r f pw lo ro)) vv = some r1 ∧
      r1.ret = none ∧ r1.ps = gS P (AL n N h (pl1 l) r f pw lo ro) ∧
      r1.vv = (if l % 2 = 1 then aaVV vv N l f else vv) ∧ r1.cost ≤ 1200 ∧ r1.need ≤ P.length + 300 ∧ r1.wk ≤ 2 := by
  have hl' : l < 2147483648 := by omega
  have hc := odd_val mv P vv (AL n N h l r f pw lo ro) 3 l rfl hl'
  by_cases hod : l % 2 = 1
  · rw [if_pos hod] at hc
    obtain ⟨hlt0, vx, hlt1⟩ := hodd hod
    obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ : ∃ r2 : PRM,
        pexecM mv fu (.sequence (.primitive (incL mv.nv)) Sk)
          (gS P (AL n N h l r f pw lo ro ++ [ci n, ci N, ci h, ci l, cs f, cs f, cs ((vv 0).getD l 0),
            cs (mi f ((vv 0).getD l 0)), cs (mi f ((vv 0).getD l 0))])) (aaVV vv N l f) = some r2 ∧
        r2.ret = none ∧ r2.ps = gS P (AL n N h (l + 1) r f pw lo ro ++ [ci n, ci N, ci h, ci l, cs f, cs f, cs ((vv 0).getD l 0),
            cs (mi f ((vv 0).getD l 0)), cs (mi f ((vv 0).getD l 0))]) ∧
        r2.vv = aaVV vv N l f ∧ r2.cost ≤ 100 ∧ r2.need ≤ P.length + 100 ∧ r2.wk = 0 := by
      have E3' : penvN mv.nv (gS P (AL n N h l r f pw lo ro ++ [ci n, ci N, ci h, ci l, cs f, cs f, cs ((vv 0).getD l 0),
            cs (mi f ((vv 0).getD l 0)), cs (mi f ((vv 0).getD l 0))])) (mv.nv + 3) i32 = some (l : Int) :=
        envs mv P _ 3 (ci l) rfl (i32v l hl')
      have e2 := inc_val mv (aaVV vv N l f) _ (mv.nv + 3) l E3' hl
      have s2 := gSM_assign mv P (AL n N h l r f pw lo ro ++ [ci n, ci N, ci h, ci l, cs f, cs f, cs ((vv 0).getD l 0),
            cs (mi f ((vv 0).getD l 0)), cs (mi f ((vv 0).getD l 0))]) (aaVV vv N l f) 3
        (by simp) i32 _ _ _ e2 (ci l) rfl rfl (i32v l hl') (conv_signed i32 rfl rfl _ (i32v (l + 1) (by show l + 1 < 2147483648; omega)))
      have eB : (AL n N h l r f pw lo ro ++ [ci n, ci N, ci h, ci l, cs f, cs f, cs ((vv 0).getD l 0),
            cs (mi f ((vv 0).getD l 0)), cs (mi f ((vv 0).getD l 0))]).set 3 ⟨i32, ((l + 1 : Nat) : Int)⟩ =
          AL n N h (l + 1) r f pw lo ro ++ [ci n, ci N, ci h, ci l, cs f, cs f, cs ((vv 0).getD l 0),
            cs (mi f ((vv 0).getD l 0)), cs (mi f ((vv 0).getD l 0))] := rfl
      rw [eB] at s2
      have a2 := (pexecM_prim mv fu (incL mv.nv) _ _).trans s2
      have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
      refine ⟨_, b2, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
    have hKE : vdenM mv vv (penvN mv.nv (gS P (AL n N h l r f pw lo ro ++ [ci n, ci N, ci h]))) (.variable i32 (mv.nv + 3)) =
        some (l : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact envs mv P _ 3 (ci l) rfl (i32v l hl')
    have hFE : vdenM mv vv (penvN mv.nv (gS P (AL n N h l r f pw lo ro ++ [ci n, ci N, ci h, ci l]))) (.variable s64 (mv.nv + 5)) =
        some f := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 5 f rfl vf
    obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := aacall_exec mv hnv ty0 ty1 P vv fu (AL n N h l r f pw lo ro) 9 rfl 0 1 2
      n N h rfl rfl rfl hn hN hh (.variable i32 (mv.nv + 3)) (.variable s64 (mv.nv + 5)) l f hKE hFE hl' vf hlt0 vx hlt1
      (.sequence (.primitive (incL mv.nv)) Sk) r2 hr2
    have b0 := pexecM_scope mv fu _ _ _ _ hA
    have tk := gS_takeC P (AL n N h l r f pw lo ro) (AL n N h (l + 1) r f pw lo ro)
      [ci n, ci N, ci h, ci l, cs f, cs f, cs ((vv 0).getD l 0), cs (mi f ((vv 0).getD l 0)), cs (mi f ((vv 0).getD l 0))] rfl
    rw [psA, ps2] at b0
    simp only [tk] at b0
    have b1 := seqM_some b0 (by rw [retA, ret2]) (pexecM_skip mv fu _ _)
    have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b1
    refine ⟨_, b3, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · have e1 : pl1 l = l + 1 := by simp [pl1, hod]
      rw [e1]
    · rw [if_pos hod]; simp [vvA, vv2]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA c2 ⊢; omega
    · have hA' := nA (P.length + 300) (by omega) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' n2 ⊢
      omega
    · simp at wA ⊢; omega
  · rw [if_neg hod] at hc
    have b3 := pexecM_branch_false mv fu _ (BrL mv.nv) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    refine ⟨_, b3, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · have e1 : pl1 l = l := by simp [pl1, hod]
      rw [e1]
    · rw [if_neg hod]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp

set_option maxHeartbeats 64000000 in
/-- `if (r % 2 == 1) { r--; all_apply(r, f); }` -/
theorem brR_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell) (fu : Nat)
    (vv : Nat → List Int) (n N h l r pw lo ro : Nat) (f : Int) (hn : n < 2147483648) (hN : N < 2147483648)
    (hh : h < 2147483648) (hr : r < 2147483648) (vf : s64.valid f = true)
    (hodd : r % 2 = 1 → r - 1 < (vv 0).length ∧ s64.valid ((vv 0).getD (r - 1) 0) = true ∧
      (r - 1 < N → r - 1 < (vv 1).length ∧ s64.valid ((vv 1).getD (r - 1) 0) = true)) :
    ∃ r1 : PRM, pexecM mv fu (.branch (oddE mv.nv 4) (BrR mv.nv) Sk) (gS P (AL n N h l r f pw lo ro)) vv = some r1 ∧
      r1.ret = none ∧ r1.ps = gS P (AL n N h l (pr1 r) f pw lo ro) ∧
      r1.vv = (if r % 2 = 1 then aaVV vv N (r - 1) f else vv) ∧ r1.cost ≤ 1200 ∧ r1.need ≤ P.length + 300 ∧ r1.wk ≤ 2 := by
  have hc := odd_val mv P vv (AL n N h l r f pw lo ro) 4 r rfl hr
  by_cases hod : r % 2 = 1
  · rw [if_pos hod] at hc
    obtain ⟨hlt0, vx, hlt1⟩ := hodd hod
    have hr1 : 1 ≤ r := by omega
    have hr' : r - 1 < 2147483648 := by omega
    have E4 : penvN mv.nv (gS P (AL n N h l r f pw lo ro)) (mv.nv + 4) i32 = some (r : Int) :=
      envs mv P (AL n N h l r f pw lo ro) 4 (ci r) rfl (i32v r hr)
    have e1 := Proofs.LazySegBlocks.dec_val mv vv _ (mv.nv + 4) r E4 hr1 hr
    have s1 := gSM_assign mv P (AL n N h l r f pw lo ro) vv 4 (by simp) i32 _ _ _ e1 (ci r) rfl rfl (i32v r hr)
      (conv_signed i32 rfl rfl _ (i32v (r - 1) (by show r - 1 < 2147483648; omega)))
    have eA : (AL n N h l r f pw lo ro).set 4 ⟨i32, ((r - 1 : Nat) : Int)⟩ = AL n N h l (r - 1) f pw lo ro := rfl
    rw [eA] at s1
    have a1 := (pexecM_prim mv fu (decR mv.nv) _ _).trans s1
    have hKE : vdenM mv vv (penvN mv.nv (gS P (AL n N h l (r - 1) f pw lo ro ++ [ci n, ci N, ci h]))) (.variable i32 (mv.nv + 4)) =
        some ((r - 1 : Nat) : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact envs mv P _ 4 (ci (r - 1)) rfl (i32v (r - 1) hr')
    have hFE : vdenM mv vv (penvN mv.nv (gS P (AL n N h l (r - 1) f pw lo ro ++ [ci n, ci N, ci h, ci (r - 1)])))
        (.variable s64 (mv.nv + 5)) = some f := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 5 f rfl vf
    obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := aacall_exec mv hnv ty0 ty1 P vv fu (AL n N h l (r - 1) f pw lo ro) 9 rfl 0 1 2
      n N h rfl rfl rfl hn hN hh (.variable i32 (mv.nv + 4)) (.variable s64 (mv.nv + 5)) (r - 1) f hKE hFE hr' vf hlt0 vx hlt1
      Sk _ (pexecM_skip mv fu _ _)
    have s3 := seqM_some a1 rfl hA
    have b0 := pexecM_scope mv fu _ _ _ _ s3
    have tk := gS_takeC P (AL n N h l r f pw lo ro) (AL n N h l (r - 1) f pw lo ro)
      [ci n, ci N, ci h, ci (r - 1), cs f, cs f, cs ((vv 0).getD (r - 1) 0), cs (mi f ((vv 0).getD (r - 1) 0)),
        cs (mi f ((vv 0).getD (r - 1) 0))] rfl
    rw [psA] at b0
    simp only [tk] at b0
    have b1 := seqM_some b0 (by rw [retA]) (pexecM_skip mv fu _ _)
    have b3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ b1
    refine ⟨_, b3, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · have e1 : pr1 r = r - 1 := by simp [pr1, hod]
      rw [e1]
    · rw [if_pos hod]; simp [vvA]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA ⊢; omega
    · have hA' := nA (P.length + 300) (by simp [gS_mem_len, gS_bs_len]) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' ⊢
      omega
    · simp at wA ⊢; omega
  · rw [if_neg hod] at hc
    have b3 := pexecM_branch_false mv fu _ (BrR mv.nv) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    refine ⟨_, b3, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · have e1 : pr1 r = r := by simp [pr1, hod]
      rw [e1]
    · rw [if_neg hod]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp

theorem vok_read (N : Nat) (vv : Nat → List Int) (hV : VOK N vv) (k : Nat) :
    (k < 2 * N → s64.valid ((vv 0).getD k 0) = true) ∧
      (k < N → k < (vv 1).length ∧ s64.valid ((vv 1).getD k 0) = true) := by
  obtain ⟨h0, h1, hv0, hf1⟩ := hV
  refine ⟨fun hk => ?_, fun hk => ⟨by omega, ?_⟩⟩
  · exact Proofs.SegTreeMath.getD_V _ (vv 0) hv0 k (by omega)
  · rw [getD_dflt (vv 1) k 0 chminMon.fid (by omega)]
    exact getD_F chminMon (vv 1) hf1 k

set_option maxHeartbeats 64000000 in
/-- One iteration of the `all_apply` loop of `update(l, r, f)`. -/
theorem iterU (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell) (fu : Nat)
    (vv : Nat → List Int) (n N h l r pw lo ro : Nat) (f : Int) (hn : n < 2147483648) (hN : N < 2147483648)
    (hh : h < 2147483648) (hlr : l < r) (hr2 : r ≤ 2 * N) (hN2 : 2 * N < 2147483648) (hV : VOK N vv)
    (vf : s64.valid f = true) :
    ∃ r1 : PRM, pexecM mv fu (LoopBodyU mv.nv) (gS P (AL n N h l r f pw lo ro)) vv = some r1 ∧ r1.ret = none ∧
      r1.ps = gS P (AL n N h (pl1 l / 2) (pr1 r / 2) f pw lo ro) ∧ r1.vv = stepVV N f l r vv ∧
      r1.cost ≤ 3000 ∧ r1.need ≤ P.length + 300 ∧ r1.wk ≤ 4 := by
  have hl1 : l + 1 < 2147483648 := by omega
  have hr31 : r < 2147483648 := by omega
  have hlen0 := hV.1
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := brL_exec mv hnv ty0 ty1 P fu vv n N h l r pw lo ro f hn hN hh hl1 vf
    (fun ho => ⟨by omega, (vok_read N vv hV l).1 (by omega), fun hk => (vok_read N vv hV l).2 hk⟩)
  have hV1 : VOK N (if l % 2 = 1 then aaVV vv N l f else vv) := by
    by_cases ho : l % 2 = 1
    · rw [if_pos ho]; exact (aaVV_ok N l f vv hV (by omega) vf).1
    · rw [if_neg ho]; exact hV
  obtain ⟨rB, hB, retB, psB, vvB, cB, nB, wB⟩ := brR_exec mv hnv ty0 ty1 P fu (if l % 2 = 1 then aaVV vv N l f else vv) n N h
    (pl1 l) r pw lo ro f hn hN hh hr31 vf
    (fun ho => ⟨by have := hV1.1; omega, (vok_read N _ hV1 (r - 1)).1 (by omega), fun hk => (vok_read N _ hV1 (r - 1)).2 hk⟩)
  have hpl : pl1 l ≤ r := by unfold pl1; split <;> omega
  have hpl' : pl1 l < 2147483648 := by omega
  have hpr : pr1 r ≤ r := by unfold pr1; split <;> omega
  have hpr' : pr1 r < 2147483648 := by omega
  have E3 := envs mv P (AL n N h (pl1 l) (pr1 r) f pw lo ro) 3 (ci (pl1 l)) rfl (i32v _ hpl')
  have E3' : penvN mv.nv (gS P (AL n N h (pl1 l) (pr1 r) f pw lo ro)) (mv.nv + 3) i32 = some ((pl1 l : Nat) : Int) := E3
  have e3 : vdenM mv (stepVV N f l r vv) (penvN mv.nv (gS P (AL n N h (pl1 l) (pr1 r) f pw lo ro)))
      (.divrem i32 false (.variable i32 (mv.nv + 3)) (.literal i32 2)) = some ((pl1 l / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, E3', Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
    simpa using cdr_i32_div _ 2 hpl' (by omega) (by omega)
  have s3 := gSM_assign mv P (AL n N h (pl1 l) (pr1 r) f pw lo ro) (stepVV N f l r vv) 3 (by simp) i32 _ _ _ e3
    (ci (pl1 l)) rfl rfl (i32v _ hpl') (conv_signed i32 rfl rfl _ (i32v _ (by show pl1 l / 2 < 2147483648; omega)))
  have eC : (AL n N h (pl1 l) (pr1 r) f pw lo ro).set 3 ⟨i32, ((pl1 l / 2 : Nat) : Int)⟩ =
      AL n N h (pl1 l / 2) (pr1 r) f pw lo ro := rfl
  rw [eC] at s3
  have a3 := (pexecM_prim mv fu (halveL mv.nv) _ _).trans s3
  have E4 := envs mv P (AL n N h (pl1 l / 2) (pr1 r) f pw lo ro) 4 (ci (pr1 r)) rfl (i32v _ hpr')
  have E4' : penvN mv.nv (gS P (AL n N h (pl1 l / 2) (pr1 r) f pw lo ro)) (mv.nv + 4) i32 = some ((pr1 r : Nat) : Int) := E4
  have e4 : vdenM mv (stepVV N f l r vv) (penvN mv.nv (gS P (AL n N h (pl1 l / 2) (pr1 r) f pw lo ro)))
      (.divrem i32 false (.variable i32 (mv.nv + 4)) (.literal i32 2)) = some ((pr1 r / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, E4', Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
    simpa using cdr_i32_div _ 2 hpr' (by omega) (by omega)
  have s4 := gSM_assign mv P (AL n N h (pl1 l / 2) (pr1 r) f pw lo ro) (stepVV N f l r vv) 4 (by simp) i32 _ _ _ e4
    (ci (pr1 r)) rfl rfl (i32v _ hpr') (conv_signed i32 rfl rfl _ (i32v _ (by show pr1 r / 2 < 2147483648; omega)))
  have eD : (AL n N h (pl1 l / 2) (pr1 r) f pw lo ro).set 4 ⟨i32, ((pr1 r / 2 : Nat) : Int)⟩ =
      AL n N h (pl1 l / 2) (pr1 r / 2) f pw lo ro := rfl
  rw [eD] at s4
  have a4 := (pexecM_prim mv fu (halveR mv.nv) _ _).trans s4
  have b4 := seqM_some a4 rfl (pexecM_skip mv fu _ _)
  have b3 := seqM_some a3 rfl b4
  have hvv : stepVV N f l r vv = (if r % 2 = 1 then aaVV (if l % 2 = 1 then aaVV vv N l f else vv) N (r - 1) f
      else (if l % 2 = 1 then aaVV vv N l f else vv)) := rfl
  have b2 := seqM_some hB retB (by rw [psB, vvB, ← hvv]; exact b3)
  have b1 := seqM_some hA retA (by rw [psA, vvA]; exact b2)
  obtain ⟨rb, hb, hbps, hbret, hbvv, hbw, hbc, hbn⟩ : ∃ rb : PRM,
      pexecM mv fu (.sequence (.branch (oddE mv.nv 3) (BrL mv.nv) Sk) (.sequence (.branch (oddE mv.nv 4) (BrR mv.nv) Sk)
        (.sequence (.primitive (halveL mv.nv)) (.sequence (.primitive (halveR mv.nv)) Sk)))) (gS P (AL n N h l r f pw lo ro)) vv = some rb ∧
      rb.ps = gS P (AL n N h (pl1 l / 2) (pr1 r / 2) f pw lo ro) ∧ rb.ret = none ∧
      rb.vv = stepVV N f l r vv ∧ rb.wk ≤ 4 ∧ rb.cost ≤ 2900 ∧ rb.need ≤ P.length + 300 := by
    refine ⟨_, b1, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp at wA wB ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA cB ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nA nB ⊢; omega
  have b0 := pexecM_scope mv fu _ _ _ _ hb
  rw [hbps] at b0
  have tk := Proofs.PexecKit.scope_take (gS P (AL n N h l r f pw lo ro))
    (gS P (AL n N h (pl1 l / 2) (pr1 r / 2) f pw lo ro))
    (by simp [gS_mem_len]) (by simp [gS_bs_len])
  simp only [tk] at b0
  have b5 := seqM_some b0 hbret (pexecM_skip mv fu _ _)
  refine ⟨_, b5, rfl, rfl, hbvv, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hbc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hbn ⊢; omega
  · simp [hbw]

theorem cond_u_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (n N h l r : Nat) (f : Int) (pw lo ro : Nat)
    (hl : l < 2147483648) (hr : r < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (AL n N h l r f pw lo ro))) (Proofs.LazySegProduct.condP mv.nv) =
      some (if l < r then 1 else 0) := by
  have el : penvN mv.nv (gS P (AL n N h l r f pw lo ro)) (mv.nv + 3) i32 = some (l : Int) :=
    envs mv P (AL n N h l r f pw lo ro) 3 (ci l) rfl (i32v l hl)
  have er : penvN mv.nv (gS P (AL n N h l r f pw lo ro)) (mv.nv + 4) i32 = some (r : Int) :=
    envs mv P (AL n N h l r f pw lo ro) 4 (ci r) rfl (i32v r hr)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, el, Option.bind_some, den_variable, er, Option.bind_some]
  by_cases hlt : l < r
  · have : (l : Int) < (r : Int) := by omega
    simp [binaryValue, hlt, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((l : Int) < (r : Int)) := by omega
    simp [binaryValue, hlt, this, Ty.convert, bT, Ty.valid]

open Proofs.LazySegProduct (condP lsteps lsteps_step width_half)

set_option maxHeartbeats 64000000 in
/-- The loop `while (l < r) {...}` of `update(l, r, f)`; `Q` is the abstract invariant on the vectors. -/
theorem loopU (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (n N h pw lo ro : Nat) (f : Int) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (hN2 : 2 * N < 2147483648) (vf : s64.valid f = true)
    (Q : Nat → Nat → (Nat → List Int) → Prop)
    (hQ : ∀ l r vv, Q l r vv → l < r → Q (pl1 l / 2) (pr1 r / 2) (stepVV N f l r vv)) :
    ∀ (w l r : Nat) (vv : Nat → List Int) (fu : Nat), r - l = w → l ≤ 2 * N → r ≤ 2 * N → VOK N vv → Q l r vv → lsteps w + 1 ≤ fu →
      ∃ (res : PRM) (lF rF : Nat) (vvF : Nat → List Int), pexecM mv fu (.whileLoop (condP mv.nv) (LoopBodyU mv.nv))
          (gS P (AL n N h l r f pw lo ro)) vv = some res ∧ res.ret = none ∧
        res.ps = gS P (AL n N h lF rF f pw lo ro) ∧ res.vv = vvF ∧ VOK N vvF ∧ Q lF rF vvF ∧ ¬ lF < rF ∧ rF ≤ 2 * N ∧
        res.cost ≤ 3100 * lsteps w + 30 ∧ res.need ≤ P.length + 300 ∧ res.wk ≤ 4 * lsteps w := by
  intro w
  induction w using Nat.strongRecOn with
  | _ w ih =>
    intro l r vv fu hw hl2 hr2 hV hQl hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hr31 : r < 2147483648 := by omega
    have hl31 : l < 2147483648 := by omega
    have hc := cond_u_val mv P vv n N h l r f pw lo ro hl31 hr31
    by_cases hlr : l < r
    · rw [if_pos hlr] at hc
      obtain ⟨r1, hr1, ret1, ps1, vv1, c1, n1, w1⟩ := iterU mv hnv ty0 ty1 P (fu' + 1) vv n N h l r pw lo ro f hn hN hh hlr hr2 hN2 hV vf
      have hwid := width_half l r hlr
      have hpr : pr1 r ≤ r := by unfold pr1; split <;> omega
      have hS := stepVV_ok N f l r vv hV (fun _ => by omega) (fun _ => by omega) vf
      obtain ⟨r2, lF, rF, vvF, hr2', ret2, ps2, vv2, hVF, hQF, hex, hrF, c2, n2, w2⟩ :=
        ih (pr1 r / 2 - pl1 l / 2) (by omega) (pl1 l / 2) (pr1 r / 2) (stepVV N f l r vv) fu' rfl (by unfold pl1; split <;> omega) (by omega) hS.1
          (hQ l r vv hQl hlr) (by
            have := lsteps_step w (pr1 r / 2 - pl1 l / 2) (by omega) (by omega); omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, hr1, ret1, ps1, vv1, hr2']
      have hls := lsteps_step w (pr1 r / 2 - pl1 l / 2) (by omega) (by omega)
      refine ⟨_, lF, rF, vvF, rfl, ret2, ps2, vv2, hVF, hQF, hex, hrF, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
      · simp at w1 w2 ⊢; omega
    · rw [if_neg hlr] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      have hw0 : w = 0 := by omega
      refine ⟨_, l, r, vv, rfl, rfl, rfl, rfl, hV, hQl, hlr, hr2, ?_, ?_, ?_⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, lsteps, hw0]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp

/-! ### The final bottom-up loop `for (i = 1; i <= h; i++) { if (l / pw * pw != l) update(l / pw); ...; pw = pw * 2; }`

Cells: `n`, `n_node`, `h_node`, `l`, `r`, `f`, `pw`, `l2`, `r2`, `i`. -/

abbrev UL (n N h l r : Nat) (f : Int) (pw lo ro i : Nat) : List Cell := AL n N h l r f pw lo ro ++ [ci i]

open Proofs.LazySegUpdE (UpdBlkE updE_exec)
open Proofs.LazySegRange (NeE KEl KEr ne_val kEr_den)
open Proofs.SegmentTreeExec (mx)

abbrev UpdL (nv : Nat) : Command := .sequence (.scope (UpdBlkE nv 10 0 1 2 (KEl nv 6) Sk)) Sk
abbrev UpdR (nv : Nat) : Command := .sequence (.scope (UpdBlkE nv 10 0 1 2 (KEr nv 6) Sk)) Sk
abbrev PwDouble (nv : Nat) : Command :=
  .sequence (.primitive (.assign (nv + 6) i32 (.binary i32 .mul (.variable i32 (nv + 6)) (.literal i32 2)))) Sk
abbrev IncI (nv : Nat) : Command :=
  .sequence (.primitive (.assign (nv + 9) i32 (.binary i32 .add (.variable i32 (nv + 9)) (.literal i32 1)))) Sk
abbrev FinBody (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (NeE nv 3 6) (UpdL nv) Sk) (.sequence (.branch (NeE nv 4 6) (UpdR nv) Sk) (PwDouble nv))))
    (IncI nv)
abbrev FinLoop (nv : Nat) : Command :=
  .whileLoop (.binary bT .le (.variable i32 (nv + 9)) (.variable i32 (nv + 2))) (FinBody nv)

/-- `update(k)`: the vectors. -/
def updVV (vv : Nat → List Int) (k : Nat) : Nat → List Int :=
  upd vv 0 ((vv 0).set k (mx ((vv 0).getD (2 * k) 0) ((vv 0).getD (2 * k + 1) 0)))

def cuVV (c : Prop) [Decidable c] (vv : Nat → List Int) (k : Nat) : Nat → List Int := if c then updVV vv k else vv

theorem updVV_ok (N k : Nat) (vv : Nat → List Int) (hV : VOK N vv) (hk : 2 * k + 1 < 2 * N) :
    VOK N (updVV vv k) ∧ updVV vv k 0 = updNode chminMon (vv 0) k ∧ updVV vv k 1 = vv 1 ∧
      (∀ j, j ≠ 0 → updVV vv k j = vv j) := by
  obtain ⟨h0, h1, hv0, hf1⟩ := hV
  have e0 : updVV vv k 0 = updNode chminMon (vv 0) k := by
    unfold updVV updNode
    simp only [upd, if_true]
    rw [getD_dflt (vv 0) (2 * k) 0 chminMon.e (by omega), getD_dflt (vv 0) (2 * k + 1) 0 chminMon.e (by omega)]
    rfl
  have e1 : ∀ j, j ≠ 0 → updVV vv k j = vv j := by
    intro j hj
    unfold updVV
    simp [upd, hj]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, e0, e1 1 (by omega), e1⟩
  · rw [e0]; unfold updNode; simp [h0]
  · rw [e1 1 (by omega)]; exact h1
  · rw [e0]; exact allV_updNode chminMon (vv 0) hv0 k (by omega)
  · rw [e1 1 (by omega)]; exact hf1

theorem cuVV_ok (N : Nat) (c : Prop) [Decidable c] (k : Nat) (vv : Nat → List Int) (hV : VOK N vv) (hk : c → 2 * k + 1 < 2 * N) :
    VOK N (cuVV c vv k) ∧ cuVV c vv k 0 = cu c (vv 0) k ∧ cuVV c vv k 1 = vv 1 := by
  by_cases hc : c
  · obtain ⟨o, e0, e1, _⟩ := updVV_ok N k vv hV (hk hc)
    unfold cuVV cu
    simp only [if_pos hc]
    exact ⟨o, e0, e1⟩
  · unfold cuVV cu
    simp only [if_neg hc]
    first | exact ⟨hV, trivial, trivial⟩ | exact hV | exact ⟨hV, rfl, rfl⟩

set_option maxHeartbeats 64000000 in
/-- `if (cond) { update(k); }` -/
theorem cupd_exec (mv : MV) (hmv0 : 0 < mv.nv) (ty0 : mv.ty 0 = s64) (P : List Cell) (vv : Nat → List Int) (fu : Nat)
    (cl : List Cell) (c : Nat) (hc : cl.length = c) (n N h : Nat) (hj0 : cl[0]? = some (ci n)) (hj1 : cl[1]? = some (ci N))
    (hj2 : cl[2]? = some (ci h)) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648)
    (NE KE : NExpr) (k : Nat) (cnd : Prop) [Decidable cnd]
    (hcnd : vdenM mv vv (penvN mv.nv (gS P cl)) NE = some (if cnd then 1 else 0))
    (hKE : cnd → vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci n, ci N, ci h]))) KE = some (k : Int))
    (hk : cnd → 2 * k + 1 < 2147483648 ∧ 2 * k + 1 < (vv 0).length ∧ s64.valid ((vv 0).getD (2 * k) 0) = true ∧
      s64.valid ((vv 0).getD (2 * k + 1) 0) = true) :
    ∃ r : PRM, pexecM mv fu (.branch NE (.sequence (.scope (UpdBlkE mv.nv c 0 1 2 KE Sk)) Sk) Sk) (gS P cl) vv = some r ∧
      r.ret = none ∧ r.ps = gS P cl ∧ r.vv = cuVV cnd vv k ∧ r.cost ≤ 400 + (vwp NE).1 + (vwp KE).1 ∧
      r.need ≤ P.length + 2 * c + 200 + (vwp NE).2 + (vwp KE).2 ∧ r.wk ≤ 1 := by
  by_cases hcc : cnd
  · rw [if_pos hcc] at hcnd
    obtain ⟨hk31, hlt, vx, vy⟩ := hk hcc
    obtain ⟨rU, hU, retU, psU, vvU, cU, nU, wU⟩ := updE_exec mv hmv0 ty0 P vv fu cl c hc 0 1 2 n N h k KE hj0 hj1 hj2 (hKE hcc) hn hN hh
      hk31 hlt vx vy Sk _ (pexecM_skip mv fu _ _)
    have b0 := pexecM_scope mv fu _ _ _ _ hU
    rw [psU] at b0
    simp only [gS_take] at b0
    have b1 := seqM_some b0 (by simpa using retU) (pexecM_skip mv fu _ _)
    have b2 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hcnd (by decide) _ b1
    refine ⟨_, b2, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · simpa using retU
    · simp [cuVV, updVV, hcc, vvU]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cU ⊢; omega
    · have hn' := nU (P.length + 2 * c + 200 + (vwp NE).2 + (vwp KE).2) (by simp [gS_mem_len, gS_bs_len, hc]; omega) (by omega)
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hc] at hn' ⊢
      omega
    · simp at wU ⊢; omega
  · rw [if_neg hcc] at hcnd
    have b2 := pexecM_branch_false mv fu _ (.sequence (.scope (UpdBlkE mv.nv c 0 1 2 KE Sk)) Sk) Sk _ _ hcnd _
      (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [cuVV, hcc]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hc]; omega
    · simp

/-- The vectors after one round of the final loop. -/
def stepUV (N l0 r0 pw : Nat) (vv : Nat → List Int) : Nat → List Int :=
  cuVV (r0 % pw ≠ 0) (cuVV (l0 % pw ≠ 0) vv (l0 / pw)) ((r0 - 1) / pw)

theorem mul2_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (slot k : Nat)
    (h : env slot i32 = some (k : Int)) (hk : k * 2 < 2147483648) :
    vdenM mv vv env (.binary i32 .mul (.variable i32 slot) (.literal i32 2)) = some ((k * 2 : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, h, Option.bind_some, den_literal,
    if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
  have : binaryValue .mul (k : Int) 2 = ((k * 2 : Nat) : Int) := by
    show (k : Int) * 2 = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32v _ (by show k * 2 < 2147483648; omega))

set_option maxHeartbeats 128000000 in
/-- One iteration of the final loop. -/
theorem finIter (mv : MV) (hmv0 : 0 < mv.nv) (ty0 : mv.ty 0 = s64) (P : List Cell) (vv : Nat → List Int) (fu : Nat)
    (n h l0 r0 lo ro i : Nat) (f : Int) (hn : n < 2147483648) (hh29 : h ≤ 29) (hi : 1 ≤ i) (hih : i ≤ h)
    (hl : 2 ^ h ≤ l0 ∧ l0 ≤ 2 * 2 ^ h) (hr : 2 ^ h ≤ r0 ∧ r0 ≤ 2 * 2 ^ h) (hV : VOK (2 ^ h) vv) :
    ∃ r : PRM, pexecM mv fu (FinBody mv.nv) (gS P (UL n (2 ^ h) h l0 r0 f (2 ^ i) lo ro i)) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (UL n (2 ^ h) h l0 r0 f (2 ^ (i + 1)) lo ro (i + 1)) ∧ r.vv = stepUV (2 ^ h) l0 r0 (2 ^ i) vv ∧
      r.cost ≤ 3500 ∧ r.need ≤ P.length + 400 ∧ r.wk ≤ 2 := by
  have hN30 : 2 ^ h ≤ 536870912 := by
    have : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
    have h30 : 2 ^ 29 = 536870912 := by norm_num
    omega
  have hpow : 2 ^ i ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) hih
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have hpw31 : 2 ^ i < 2147483648 := by omega
  have hpw2 : 2 ^ i * 2 < 2147483648 := by omega
  have hnnpos : 0 < 2 ^ h := Nat.two_pow_pos h
  have hN31 : 2 ^ h < 2147483648 := by omega
  have hl31 : l0 < 2147483648 := by omega
  have hr31 : r0 < 2147483648 := by omega
  have hi31 : i < 2147483648 := by omega
  set cl := UL n (2 ^ h) h l0 r0 f (2 ^ i) lo ro i with hcl
  have hc : cl.length = 10 := by simp [hcl]
  have c3 : cl[3]? = some (ci l0) := by simp [hcl]
  have c4 : cl[4]? = some (ci r0) := by simp [hcl]
  have c6 : cl[6]? = some (ci (2 ^ i)) := by simp [hcl]
  have env3 : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ ys)) (mv.nv + 3) i32 = some (l0 : Int) := fun ys =>
    envs mv P (cl ++ ys) 3 (ci l0) (by rw [List.getElem?_append_left (by omega)]; exact c3) (i32v l0 (by show l0 < 2147483648; omega))
  have env4 : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ ys)) (mv.nv + 4) i32 = some (r0 : Int) := fun ys =>
    envs mv P (cl ++ ys) 4 (ci r0) (by rw [List.getElem?_append_left (by omega)]; exact c4) (i32v r0 (by show r0 < 2147483648; omega))
  have env6 : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ ys)) (mv.nv + 6) i32 = some ((2 ^ i : Nat) : Int) := fun ys =>
    envs mv P (cl ++ ys) 6 (ci (2 ^ i)) (by rw [List.getElem?_append_left (by omega)]; exact c6) (i32v _ (by show 2 ^ i < 2147483648; omega))
  have hhalf : ∀ k, k < 2 ^ (h - i + 1) → 2 * k + 1 < 2 * 2 ^ h := by
    intro k hk
    have : 2 ^ (h - i + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  -- the left update
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := cupd_exec mv hmv0 ty0 P vv fu cl 10 hc n (2 ^ h) h rfl rfl rfl hn hN31 (by omega)
    (NeE mv.nv 3 6) (KEl mv.nv 6) (l0 / 2 ^ i) (l0 % 2 ^ i ≠ 0)
    (ne_val mv P vv cl 3 6 l0 (2 ^ i) c3 c6 hl31 hpos hpw31)
    (fun _ => by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact divvar_den _ _ _ l0 (2 ^ i) (env3 _) (env6 _) hl31 hpos hpw31)
    (fun hc' => by
      have hb := Proofs.LazySegRange.left_bounds (2 ^ h) h i l0 rfl hi hih hl hc'
      have := hhalf _ hb.2
      refine ⟨by omega, by rw [hV.1]; exact this, ?_, ?_⟩
      · exact (vok_read _ vv hV _).1 (by omega)
      · exact (vok_read _ vv hV _).1 (by omega))
  have hV1 := (cuVV_ok (2 ^ h) (l0 % 2 ^ i ≠ 0) (l0 / 2 ^ i) vv hV
    (fun hc' => hhalf _ (Proofs.LazySegRange.left_bounds (2 ^ h) h i l0 rfl hi hih hl hc').2)).1
  -- the right update
  obtain ⟨rB, hB, retB, psB, vvB, cB, nB, wB⟩ := cupd_exec mv hmv0 ty0 P (cuVV (l0 % 2 ^ i ≠ 0) vv (l0 / 2 ^ i)) fu cl 10 hc n
    (2 ^ h) h rfl rfl rfl hn hN31 (by omega)
    (NeE mv.nv 4 6) (KEr mv.nv 6) ((r0 - 1) / 2 ^ i) (r0 % 2 ^ i ≠ 0)
    (ne_val mv P _ cl 4 6 r0 (2 ^ i) c4 c6 hr31 hpos hpw31)
    (fun hc' => by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact kEr_den _ _ _ r0 (2 ^ i) (env4 _) (env6 _) (by omega) hr31 hpos hpw31)
    (fun hc' => by
      have hb := Proofs.LazySegRange.right_bounds (2 ^ h) h i r0 rfl hi hih hr hc'
      have := hhalf _ hb.2
      refine ⟨by omega, by rw [hV1.1]; exact this, ?_, ?_⟩
      · exact (vok_read _ _ hV1 _).1 (by omega)
      · exact (vok_read _ _ hV1 _).1 (by omega))
  have hV2 := (cuVV_ok (2 ^ h) (r0 % 2 ^ i ≠ 0) ((r0 - 1) / 2 ^ i) _ hV1
    (fun hc' => hhalf _ (Proofs.LazySegRange.right_bounds (2 ^ h) h i r0 rfl hi hih hr hc').2)).1
  -- pw = pw * 2
  have eP := mul2_val mv (stepUV (2 ^ h) l0 r0 (2 ^ i) vv) (penvN mv.nv (gS P cl)) (mv.nv + 6) (2 ^ i) (by
      have := env6 []; rw [List.append_nil] at this; exact this) hpw2
  have sP := gSM_assign mv P cl (stepUV (2 ^ h) l0 r0 (2 ^ i) vv) 6 (by simp [hcl]) i32 _ _ _ eP (ci (2 ^ i)) rfl rfl
    (i32v _ (by show 2 ^ i < 2147483648; omega)) (conv_signed i32 rfl rfl _ (i32v _ (by show 2 ^ i * 2 < 2147483648; omega)))
  have eS : cl.set 6 ⟨i32, ((2 ^ i * 2 : Nat) : Int)⟩ = UL n (2 ^ h) h l0 r0 f (2 ^ (i + 1)) lo ro i := rfl
  rw [eS] at sP
  have aP := (pexecM_prim mv fu (.assign (mv.nv + 6) i32 (.binary i32 .mul (.variable i32 (mv.nv + 6)) (.literal i32 2))) _ _).trans sP
  have bP := seqM_some aP rfl (pexecM_skip mv fu _ _)
  have s2 := seqM_some hB retB (by rw [psB, vvB]; exact bP)
  have s1 := seqM_some hA retA (by rw [psA, vvA]; exact s2)
  have b0 := pexecM_scope mv fu _ _ _ _ s1
  have tk := Proofs.PexecKit.scope_take (gS P cl) (gS P (UL n (2 ^ h) h l0 r0 f (2 ^ (i + 1)) lo ro i))
    (by simp [gS_mem_len, hcl]) (by simp [gS_bs_len, hcl])
  simp only [tk] at b0
  -- i++
  have cI : (UL n (2 ^ h) h l0 r0 f (2 ^ (i + 1)) lo ro i)[9]? = some (ci i) := by simp
  have EI := envs mv P (UL n (2 ^ h) h l0 r0 f (2 ^ (i + 1)) lo ro i) 9 (ci i) cI (i32v i hi31)
  have eI := inc_val mv (stepUV (2 ^ h) l0 r0 (2 ^ i) vv)
    (penvN mv.nv (gS P (UL n (2 ^ h) h l0 r0 f (2 ^ (i + 1)) lo ro i))) (mv.nv + 9) i EI (by omega)
  have sI := gSM_assign mv P (UL n (2 ^ h) h l0 r0 f (2 ^ (i + 1)) lo ro i) (stepUV (2 ^ h) l0 r0 (2 ^ i) vv) 9
    (by simp) i32 _ _ _ eI (ci i) cI rfl (i32v i hi31)
    (conv_signed i32 rfl rfl _ (i32v _ (by show i + 1 < 2147483648; omega)))
  have eT : (UL n (2 ^ h) h l0 r0 f (2 ^ (i + 1)) lo ro i).set 9 ⟨i32, ((i + 1 : Nat) : Int)⟩ =
      UL n (2 ^ h) h l0 r0 f (2 ^ (i + 1)) lo ro (i + 1) := rfl
  rw [eT] at sI
  have aI := (pexecM_prim mv fu (.assign (mv.nv + 9) i32 (.binary i32 .add (.variable i32 (mv.nv + 9)) (.literal i32 1))) _ _).trans sI
  have bI := seqM_some aI rfl (pexecM_skip mv fu _ _)
  have b3 := seqM_some b0 (by simp) bI
  refine ⟨_, b3, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA cB ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nA nB ⊢; omega
  · simp at wA wB ⊢; omega

theorem cond_le_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (i h : Nat)
    (hi : cl[9]? = some (ci i)) (hh : cl[2]? = some (ci h)) (hi31 : i < 2147483648) (hh31 : h < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .le (.variable i32 (mv.nv + 9)) (.variable i32 (mv.nv + 2))) =
      some (if i ≤ h then 1 else 0) := by
  have ei : penvN mv.nv (gS P cl) (mv.nv + 9) i32 = some (i : Int) := envs mv P cl 9 (ci i) hi (i32v i hi31)
  have eh : penvN mv.nv (gS P cl) (mv.nv + 2) i32 = some (h : Int) := envs mv P cl 2 (ci h) hh (i32v h hh31)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, ei, Option.bind_some, den_variable, eh, Option.bind_some]
  by_cases hlt : i ≤ h
  · have : (i : Int) ≤ (h : Int) := by omega
    simp [binaryValue, hlt, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((i : Int) ≤ (h : Int)) := by omega
    simp [binaryValue, hlt, this, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 128000000 in
/-- The final loop; `Q` is the abstract invariant on the vectors. -/
theorem finLoop (mv : MV) (hmv0 : 0 < mv.nv) (ty0 : mv.ty 0 = s64) (P : List Cell)
    (n h l0 r0 lo ro : Nat) (f : Int) (hn : n < 2147483648) (hh29 : h ≤ 29)
    (hl : 2 ^ h ≤ l0 ∧ l0 ≤ 2 * 2 ^ h) (hr : 2 ^ h ≤ r0 ∧ r0 ≤ 2 * 2 ^ h)
    (Q : Nat → (Nat → List Int) → Prop)
    (hQ : ∀ i vv, 1 ≤ i → i ≤ h → Q i vv → Q (i + 1) (stepUV (2 ^ h) l0 r0 (2 ^ i) vv)) :
    ∀ (d i : Nat) (vv : Nat → List Int) (fu : Nat), h + 1 - i = d → 1 ≤ i → i ≤ h + 1 → VOK (2 ^ h) vv → Q i vv →
      d + 1 ≤ fu →
      ∃ (res : PRM) (vF : Nat → List Int), pexecM mv fu (FinLoop mv.nv) (gS P (UL n (2 ^ h) h l0 r0 f (2 ^ i) lo ro i)) vv = some res ∧
        res.ret = none ∧ res.ps = gS P (UL n (2 ^ h) h l0 r0 f (2 ^ (h + 1)) lo ro (h + 1)) ∧ res.vv = vF ∧ VOK (2 ^ h) vF ∧
        Q (h + 1) vF ∧ res.cost ≤ 3600 * d + 30 ∧ res.need ≤ P.length + 400 ∧ res.wk ≤ 2 * d := by
  intro d
  induction d with
  | zero =>
    intro i vv fu hd hi1 hih hV hQi hfu
    have hih' : i = h + 1 := by omega
    subst hih'
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_le_val mv P vv (UL n (2 ^ h) h l0 r0 f (2 ^ (h + 1)) lo ro (h + 1)) (h + 1) h (by simp) (by simp)
      (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, vv, rfl, rfl, rfl, rfl, hV, hQi, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ d ih =>
    intro i vv fu hd hi1 hih hV hQi hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hih' : i ≤ h := by omega
    have hc := cond_le_val mv P vv (UL n (2 ^ h) h l0 r0 f (2 ^ i) lo ro i) i h (by simp) (by simp) (by omega) (by omega)
    rw [if_pos hih'] at hc
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := finIter mv hmv0 ty0 P vv (fu' + 1) n h l0 r0 lo ro i f hn hh29 hi1 hih' hl hr hV
    have hS : VOK (2 ^ h) (stepUV (2 ^ h) l0 r0 (2 ^ i) vv) := by
      have hhalf : ∀ k, k < 2 ^ (h - i + 1) → 2 * k + 1 < 2 * 2 ^ h := by
        intro k hk
        have : 2 ^ (h - i + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hV1 := (cuVV_ok (2 ^ h) (l0 % 2 ^ i ≠ 0) (l0 / 2 ^ i) vv hV
        (fun hc' => hhalf _ (Proofs.LazySegRange.left_bounds (2 ^ h) h i l0 rfl hi1 hih' hl hc').2)).1
      exact (cuVV_ok (2 ^ h) (r0 % 2 ^ i ≠ 0) ((r0 - 1) / 2 ^ i) _ hV1
        (fun hc' => hhalf _ (Proofs.LazySegRange.right_bounds (2 ^ h) h i r0 rfl hi1 hih' hr hc').2)).1
    obtain ⟨r2, vF, h2, ret2, ps2, vv2, hVF, hQF, c2, n2, w2⟩ :=
      ih (i + 1) (stepUV (2 ^ h) l0 r0 (2 ^ i) vv) fu' (by omega) (by omega) (by omega) hS (hQ i vv hi1 hih' hQi) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1, vv1, h2]
    refine ⟨_, vF, rfl, ret2, ps2, vv2, hVF, hQF, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

end Proofs.LazySegApplyExec
