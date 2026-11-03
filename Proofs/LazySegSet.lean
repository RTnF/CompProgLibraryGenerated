import Proofs.LazySegGet
import Proofs.LazySegUpd

namespace Proofs.LazySegSet
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
open Proofs.LazySegUpd
open Proofs.LazySegMath (Rep LzFid Cl SInvL)
open Proofs.LazySegChmin (chminMon)
open Proofs.SegmentTreeExec (UpdBlk upd_exec mx)

/-! ### `LazySegmentTree::set` (nv = 2).  Cells: 0 = n, 1 = n_node, 2 = h_node, 3 = idx, 4 = val, 5 = pw, 6 = i -/

abbrev bodySet (nv : Nat) : Command :=
  .sequence (.primitive (.assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.variable i32 (nv + 1)))))
    (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 1))))
      (.sequence (.scope (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 2)))) (.sequence (PathLoop nv 5) Sk)))
        (.sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (nv + 3))) (.variable s64 (nv + 4))))
          (.sequence (.scope (.sequence (.primitive (.declare i32 true (.literal i32 1)))
            (.sequence (UpLoop nv 6) Sk))) Sk))))

theorem body_eqSet : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_set.body
    = bodySet 2 := rfl

set_option maxHeartbeats 64000000 in
theorem body_execSet (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (n h idx : Nat) (val : Int) (A : List Int) (hh30 : h ≤ 30) (hn : n < 2147483648) (hidx : idx < 2 ^ h)
    (hval : s64.valid val = true) (hR : Rep chminMon (2 ^ h) A (vv 0) (vv 1)) (fu : Nat) (hfu : h + 3 ≤ fu) :
    ∃ (r : PRM) (vf : Nat → List Int), pexecM mv fu (bodySet mv.nv) (gS P [ci n, ci (2 ^ h), ci h, ci idx, cs val]) vv = some r ∧
      r.ret = none ∧ r.vv = vf ∧ Rep chminMon (2 ^ h) (A.set idx val) (vf 0) (vf 1) ∧ (∃ cl : List Cell, r.ps = gS P cl) ∧
      r.cost ≤ 2500 * h + 300 ∧ r.need ≤ P.length + 800 ∧ r.wk ≤ 6 * h + 2 := by
  have hN30 : 2 ^ h ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hh30
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  have hNpos : 0 < 2 ^ h := Nat.two_pow_pos h
  set N := 2 ^ h with hNdef
  have hidxN : idx + N < 2147483648 := by omega
  -- idx += n_node
  have eI : penvN mv.nv (gS P [ci n, ci N, ci h, ci idx, cs val]) (mv.nv + 3) i32 = some (idx : Int) :=
    envs mv P [ci n, ci N, ci h, ci idx, cs val] 3 (ci idx) rfl (i32v idx (by show idx < 2147483648; omega))
  have eN : penvN mv.nv (gS P [ci n, ci N, ci h, ci idx, cs val]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci idx, cs val] 1 (ci N) rfl (i32v N (by show N < 2147483648; omega))
  have e1 : vdenM mv vv (penvN mv.nv (gS P [ci n, ci N, ci h, ci idx, cs val]))
      (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1))) = some ((idx + N : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eI, Option.bind_some, den_variable, eN, Option.bind_some]
    have : binaryValue .add (idx : Int) (N : Int) = ((idx + N : Nat) : Int) := by
      show (idx : Int) + (N : Int) = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ (by show idx + N < 2147483648; omega))
  have s1 := gSM_assign mv P [ci n, ci N, ci h, ci idx, cs val] vv 3 (by simp) i32 _ _ _ e1 (ci idx) rfl rfl
    (i32v idx (by show idx < 2147483648; omega)) (conv_signed i32 rfl rfl _ (i32v _ (by show idx + N < 2147483648; omega)))
  have eA : [ci n, ci N, ci h, ci idx, cs val].set 3 ⟨i32, ((idx + N : Nat) : Int)⟩ = [ci n, ci N, ci h, ci (idx + N), cs val] := rfl
  rw [eA] at s1
  have a1 := (pexecM_prim mv fu (.assign (mv.nv + 3) i32 (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1)))) _ _).trans s1
  -- pw = n_node
  have eN2 : penvN mv.nv (gS P [ci n, ci N, ci h, ci (idx + N), cs val]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci (idx + N), cs val] 1 (ci N) rfl (i32v N (by show N < 2147483648; omega))
  have d2 := gSM_decl mv P [ci n, ci N, ci h, ci (idx + N), cs val] vv i32 (.variable i32 (mv.nv + 1)) (N : Int) (N : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eN2) (conv_signed i32 rfl rfl _ (i32v N (by show N < 2147483648; omega)))
  have a2 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 1))) _ _).trans d2
  -- i = h_node
  have eH3 : penvN mv.nv (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci N])) (mv.nv + 2) i32 = some (h : Int) :=
    envs mv P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci N]) 2 (ci h) rfl (i32v h (by show h < 2147483648; omega))
  have d3 := gSM_decl mv P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci N]) vv i32 (.variable i32 (mv.nv + 2)) (h : Int) (h : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eH3) (conv_signed i32 rfl rfl _ (i32v h (by show h < 2147483648; omega)))
  have a3 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 2))) _ _).trans d3
  -- the path loop
  have hI0 : PInv N A (idx + N) h h vv := ⟨hR, fun s ⟨t, ht1, ht2, _⟩ => absurd ht2 (by omega)⟩
  obtain ⟨rL, vf, hL, retL, psL, vvL, hIf, cL, nL, wL⟩ := path_loop mv hnv ty0 ty1 P [ci n, ci N, ci h, ci (idx + N), cs val] 5 (by omega) rfl n h
    (idx + N) hn A rfl rfl rfl rfl hh30 (by omega) (by omega) h h vv fu rfl le_rfl hI0 (by omega)
  have hL' : pexecM mv fu (PathLoop mv.nv 5) (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci N] ++ [ci h])) vv = some rL := hL
  have sLoop := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have sIn := seqM_some a3 rfl sLoop
  have b0 := pexecM_scope mv fu _ _ _ _ sIn
  have tk : (⟨(gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0), ci 0])).mem.take
      (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci N])).mem.length,
      (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0), ci 0])).bs.take
      (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci N])).bs.length⟩ : PS) =
        gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)]) :=
    gS_takeC P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci N]) ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)]) [ci 0] rfl
  rw [psL] at b0
  simp only [tk] at b0
  -- the write of the leaf
  have hRf := hIf.1
  have hz := hIf.2
  have cV : ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)])[4]? = some (cs val) := rfl
  have cI : ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)])[3]? = some (ci (idx + N)) := rfl
  have E3 := envs mv P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)]) 3 (ci (idx + N)) cI
    (i32v _ (by show idx + N < 2147483648; omega))
  have hw := pstmtM_write_ok mv (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)])) vf 0 (by omega)
    (.cast u64 (.variable i32 (mv.nv + 3))) (.variable s64 (mv.nv + 4)) val (idx + N)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 4 val cV hval)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ _ (idx + N) E3 (by show idx + N < 2147483648; omega))
    (by rw [hRf.1]; omega) (by rw [ty0]; exact hval)
  rw [ty0] at hw
  have aw := (pexecM_prim mv fu (.write (.local 0) s64 (.cast u64 (.variable i32 (mv.nv + 3))) (.variable s64 (mv.nv + 4))) _ _).trans hw
  -- the update loop
  set vg := upd vf 0 ((vf 0).set (idx + N) val) with hvg
  have hvg0 : vg 0 = (vf 0).set (idx + N) val := by simp [hvg, upd]
  have hvg1 : vg 1 = vf 1 := by simp [hvg, upd]
  have hS0 : SInvL chminMon N (A.set idx val) (idx + N) h 0 (vg 0) (vg 1) := by
    rw [hvg0, hvg1]
    exact Proofs.LazySegMath.sInvL_init chminMon N A (idx + N) h idx val (vf 0) (vf 1) hNdef rfl hidx hval hRf hz
  have eL : ∀ (c : List Cell), c = [ci n, ci N, ci h, ci (idx + N), cs val, ci (2 ^ 0)] → True := fun _ _ => trivial
  have dI := gSM_decl mv P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)]) vg i32 (.literal i32 1) 1 1
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 1 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 1 = true from rfl))
  have aI := (pexecM_prim mv fu (.declare i32 true (.literal i32 1)) _ _).trans dI
  obtain ⟨rS, vh, hS, retS, psS, vvS, hv1S, hIS, cS, nS, wS⟩ := up_loop mv hnv ty0 P n h (idx + N) [cs val, ci 1] 6 rfl (A.set idx val) hn hh30
    (by omega) (by omega) h 0 vg fu (by omega) hS0 (by omega)
  have hS' : pexecM mv fu (UpLoop mv.nv 6)
      (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)] ++ [(⟨i32, (1 : Int)⟩ : Cell)])) vg = some rS := by
    have h0 := hS
    simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add] at h0
    exact h0
  have sLoop2 := seqM_some hS' retS (pexecM_skip mv fu rS.ps rS.vv)
  have sIn2 := seqM_some aI rfl sLoop2
  have b1 := pexecM_scope mv fu _ _ _ _ sIn2
  have tk2 : (⟨(gS P (UC n (2 ^ h) h ((idx + N) / 2 ^ h) [cs val, ci 1] (h + 1))).mem.take
      (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)])).mem.length,
      (gS P (UC n (2 ^ h) h ((idx + N) / 2 ^ h) [cs val, ci 1] (h + 1))).bs.take
      (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)])).bs.length⟩ : PS) =
        gS P [ci n, ci N, ci h, ci ((idx + N) / 2 ^ h), cs val, ci 1] :=
    gS_takeC P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci (2 ^ 0)]) [ci n, ci N, ci h, ci ((idx + N) / 2 ^ h), cs val, ci 1]
      [ci (h + 1)] rfl
  rw [psS] at b1
  simp only [tk2] at b1
  have c4 := seqM_some b1 (by simp) (pexecM_skip mv fu _ _)
  have c3 := seqM_some aw rfl (by simpa using c4)
  have c2 := seqM_some b0 (by simp) (by rw [vvL]; exact c3)
  have c1 := seqM_some a2 rfl c2
  have c0 := seqM_some a1 rfl c1
  refine ⟨_, vh, c0, ?_, ?_, ?_, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · simp
  · simp [vvS]
  · exact Proofs.LazySegMath.rep_of_sInvL chminMon N (A.set idx val) (idx + N) h (vh 0) (vh 1) hIS
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL cS ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nL nS ⊢; omega
  · simp at wL wS ⊢; omega

end Proofs.LazySegSet
