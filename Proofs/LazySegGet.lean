import Proofs.LazySegBlocks

namespace Proofs.LazySegGet
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
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den VO VO_get0 VO_set0)
open Proofs.RunLengthExec (inc_val)
open Proofs.LazySegBlocks
open Proofs.LazySegMath (Rep LzFid Cl)
open Proofs.LazySegChmin (chminMon)

/-! ### `LazySegmentTree::get` (nv = 2).  Cells: 0 = n, 1 = n_node, 2 = h_node, 3 = idx -/

abbrev bodyGet (nv : Nat) : Command :=
  .sequence (.primitive (.assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.variable i32 (nv + 1)))))
    (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 1))))
      (.sequence (.scope (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 2)))) (.sequence (PathLoop nv 4) Sk)))
        (.sequence (.primitive (.ret (.read s64 (.local 0) (.cast u64 (.variable i32 (nv + 3)))))) Sk)))

theorem body_eqGet : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_get.body
    = bodyGet 2 := rfl

theorem cl_of_lzfid (N h p : Nat) (hN : N = 2 ^ h) (hp1 : N ≤ p) (hp2 : p < 2 * N) (lz : List Int)
    (hF : LzFid chminMon (fun s => ∃ t, 0 < t ∧ t ≤ h ∧ s = p / 2 ^ t) lz) : Cl chminMon lz p := by
  intro t ht h1
  apply hF
  refine ⟨t, ht, ?_, rfl⟩
  by_contra hth
  have : 2 ^ (h + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : p < 2 ^ t := by rw [Nat.pow_succ] at this; omega
  rw [Nat.div_eq_of_lt hlt] at h1
  omega

set_option maxHeartbeats 64000000 in
theorem body_execGet (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (n h idx : Nat) (A : List Int) (hh30 : h ≤ 30) (hn : n < 2147483648) (hidx : idx < 2 ^ h)
    (hR : Rep chminMon (2 ^ h) A (vv 0) (vv 1)) (fu : Nat) (hfu : h + 3 ≤ fu) :
    ∃ (r : PRM) (vf : Nat → List Int), pexecM mv fu (bodyGet mv.nv) (gS P [ci n, ci (2 ^ h), ci h, ci idx]) vv = some r ∧
      r.ret = some (A.getD idx 0) ∧ r.vv = vf ∧ Rep chminMon (2 ^ h) A (vf 0) (vf 1) ∧ (∃ cl : List Cell, r.ps = gS P cl) ∧
      r.cost ≤ 1500 * h + 200 ∧ r.need ≤ P.length + 700 ∧ r.wk ≤ 5 * h := by
  have hN30 : 2 ^ h ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hh30
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  have hNpos : 0 < 2 ^ h := Nat.two_pow_pos h
  set N := 2 ^ h with hNdef
  have hidxN : idx + N < 2147483648 := by omega
  -- idx += n_node
  have eI : penvN mv.nv (gS P [ci n, ci N, ci h, ci idx]) (mv.nv + 3) i32 = some (idx : Int) :=
    envs mv P [ci n, ci N, ci h, ci idx] 3 (ci idx) rfl (i32v idx (by show idx < 2147483648; omega))
  have eN : penvN mv.nv (gS P [ci n, ci N, ci h, ci idx]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci idx] 1 (ci N) rfl (i32v N (by show N < 2147483648; omega))
  have e1 : vdenM mv vv (penvN mv.nv (gS P [ci n, ci N, ci h, ci idx]))
      (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1))) = some ((idx + N : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eI, Option.bind_some, den_variable, eN, Option.bind_some]
    have : binaryValue .add (idx : Int) (N : Int) = ((idx + N : Nat) : Int) := by
      show (idx : Int) + (N : Int) = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ (by show idx + N < 2147483648; omega))
  have s1 := gSM_assign mv P [ci n, ci N, ci h, ci idx] vv 3 (by simp) i32 _ _ _ e1 (ci idx) rfl rfl
    (i32v idx (by show idx < 2147483648; omega)) (conv_signed i32 rfl rfl _ (i32v _ (by show idx + N < 2147483648; omega)))
  have eA : [ci n, ci N, ci h, ci idx].set 3 ⟨i32, ((idx + N : Nat) : Int)⟩ = [ci n, ci N, ci h, ci (idx + N)] := rfl
  rw [eA] at s1
  have a1 := (pexecM_prim mv fu (.assign (mv.nv + 3) i32 (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1)))) _ _).trans s1
  -- pw = n_node
  have eN2 : penvN mv.nv (gS P [ci n, ci N, ci h, ci (idx + N)]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci (idx + N)] 1 (ci N) rfl (i32v N (by show N < 2147483648; omega))
  have d2 := gSM_decl mv P [ci n, ci N, ci h, ci (idx + N)] vv i32 (.variable i32 (mv.nv + 1)) (N : Int) (N : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eN2) (conv_signed i32 rfl rfl _ (i32v N (by show N < 2147483648; omega)))
  have a2 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 1))) _ _).trans d2
  -- i = h_node
  have eH3 : penvN mv.nv (gS P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci N])) (mv.nv + 2) i32 = some (h : Int) :=
    envs mv P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci N]) 2 (ci h) rfl (i32v h (by show h < 2147483648; omega))
  have d3 := gSM_decl mv P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci N]) vv i32 (.variable i32 (mv.nv + 2)) (h : Int) (h : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eH3) (conv_signed i32 rfl rfl _ (i32v h (by show h < 2147483648; omega)))
  have a3 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 2))) _ _).trans d3
  -- the loop
  have hI0 : PInv N A (idx + N) h h vv := ⟨hR, fun s ⟨t, ht1, ht2, _⟩ => absurd ht2 (by omega)⟩
  obtain ⟨rL, vf, hL, retL, psL, vvL, hIf, cL, nL, wL⟩ := path_loop mv hnv ty0 ty1 P [ci n, ci N, ci h, ci (idx + N)] 4 (by omega) rfl n h
    (idx + N) hn A rfl rfl rfl rfl hh30 (by omega) (by omega) h h vv fu rfl le_rfl hI0 (by omega)
  have hL' : pexecM mv fu (PathLoop mv.nv 4) (gS P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci N] ++ [ci h])) vv = some rL := hL
  have sLoop := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have sIn := seqM_some a3 rfl sLoop
  have b0 := pexecM_scope mv fu _ _ _ _ sIn
  have tk : (⟨(gS P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci (2 ^ 0), ci 0])).mem.take
      (gS P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci N])).mem.length,
      (gS P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci (2 ^ 0), ci 0])).bs.take
      (gS P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci N])).bs.length⟩ : PS) = gS P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci (2 ^ 0)]) :=
    gS_takeC P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci N]) ([ci n, ci N, ci h, ci (idx + N)] ++ [ci (2 ^ 0)]) [ci 0] rfl
  rw [psL] at b0
  simp only [tk] at b0
  -- the return
  have cI : ([ci n, ci N, ci h, ci (idx + N)] ++ [ci (2 ^ 0)])[3]? = some (ci (idx + N)) := rfl
  have E3 := envs mv P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci (2 ^ 0)]) 3 (ci (idx + N)) cI (i32v _ (by show idx + N < 2147483648; omega))
  have hRf := hIf.1
  have hlt : idx + N < (vf 0).length := by rw [hRf.1]; omega
  have hv := rep_valid0 N A (vf 0) (vf 1) hRf (idx + N) (by omega)
  have hrd := rdM_val mv vf _ 0 (by omega) s64 ty0.symm (.cast u64 (.variable i32 (mv.nv + 3))) rfl rfl (idx + N)
    (cidx_den _ _ (idx + N) E3 (by show idx + N < 2147483648; omega)) ((vf 0).getD (idx + N) 0)
    (vec_getI (vf 0) (idx + N) hlt) (by rw [ty0]; exact hv)
  have hCl : Cl chminMon (vf 1) (idx + N) := cl_of_lzfid N h (idx + N) hNdef (by omega) (by omega) (vf 1) hIf.2
  have hleaf := Proofs.LazySegMath.rep_leaf chminMon N A (vf 0) (vf 1) (idx + N) (by omega) (by omega) hRf hCl
  have hA : A.getD idx 0 = (vf 0).getD (idx + N) 0 := by
    have e1 : (vf 0).getD (idx + N) 0 = (vf 0).getD (idx + N) chminMon.e := getD_dflt _ _ _ _ hlt
    have e2 : A.getD idx 0 = A.getD idx chminMon.e := getD_dflt _ _ _ _ (by rw [hRf.2.2.1]; omega)
    rw [e1, e2, hleaf]
    simp
  have rr := pstmtM_ret_ok mv (gS P ([ci n, ci N, ci h, ci (idx + N)] ++ [ci (2 ^ 0)])) vf _ _ hrd
  have sRet := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have c3 := seqM_some b0 (by simp) (by rw [vvL]; exact sRet)
  have c2 := seqM_some a2 rfl c3
  have c1 := seqM_some a1 rfl c2
  refine ⟨_, vf, c1, ?_, rfl, hIf.1, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · exact congrArg some hA.symm
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nL ⊢; omega
  · simp at wL ⊢; omega

end Proofs.LazySegGet
