import Proofs.LazySegApplyGlue

namespace Proofs.LazySegUpdBody
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.ForLoopC (gS_takeC)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs pexecM_branch_true pexecM_branch_false)
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den)
open Proofs.LazySegBlocks
open Proofs.LazySegRange (Path2Loop)
open Proofs.LazySegProduct (condP)
open Proofs.LazySegApplyExec

abbrev bodyUpd (nv : Nat) : Command :=
  .sequence (.primitive (.assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.variable i32 (nv + 1)))))
    (.sequence (.primitive (.assign (nv + 4) i32 (.binary i32 .add (.variable i32 (nv + 4)) (.variable i32 (nv + 1)))))
      (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 1))))
        (.sequence (.scope (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 2)))) (.sequence (Path2Loop nv 6) Sk)))
          (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 3))))
            (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 4))))
              (.sequence (.whileLoop (condP nv) (LoopBodyU nv))
                (.sequence (.primitive (.assign (nv + 3) i32 (.variable i32 (nv + 7))))
                  (.sequence (.primitive (.assign (nv + 4) i32 (.variable i32 (nv + 8))))
                    (.sequence (.primitive (.assign (nv + 6) i32 (.literal i32 2)))
                      (.sequence (.scope (.sequence (.primitive (.declare i32 true (.literal i32 1))) (.sequence (FinLoop nv) Sk)))
                        Sk))))))))))

theorem body_eqUpd : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_3.body
    = bodyUpd 2 := rfl

open Proofs.LazySegMath (Rep LzFid Cl)
open Proofs.LazySegChmin (chminMon mi)
open Proofs.LazySegRange (PInv2 S2 path2_loop)
open Proofs.LazySegApplyGlue
open Proofs.LazySegApplyLoop (AI UI)
open Proofs.LazySegChmin (chminMon)

set_option maxHeartbeats 512000000 in
theorem body_execUpd (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (n h l r : Nat) (f : Int) (A : List Int) (hh29 : h ≤ 29) (hn : n < 2147483648) (hlr : l ≤ r)
    (hrN : r ≤ 2 ^ h) (vf : s64.valid f = true) (hR : Rep chminMon (2 ^ h) A (vv 0) (vv 1)) (fu : Nat)
    (hfu : h + Nat.log2 (r - l) + 8 ≤ fu) :
    ∃ (res : PRM) (vF : Nat → List Int), pexecM mv fu (bodyUpd mv.nv) (gS P [ci n, ci (2 ^ h), ci h, ci l, ci r, cs f]) vv = some res ∧
      res.ret = none ∧ res.vv = vF ∧ Rep chminMon (2 ^ h) (chminRange A l r f) (vF 0) (vF 1) ∧
      (∃ cl : List Cell, res.ps = gS P cl) ∧ res.cost ≤ 7000 * h + 3100 * (Nat.log2 (r - l) + 1) + 1000 ∧
      res.need ≤ P.length + 900 ∧ res.wk ≤ 12 * h + 4 * (Nat.log2 (r - l) + 1) := by
  have hN29 : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hh29
  have h29 : 2 ^ 29 = 536870912 := by norm_num
  have hNpos : 0 < 2 ^ h := Nat.two_pow_pos h
  set N := 2 ^ h with hNdef
  have hl31 : l < 2147483648 := by omega
  have hr31 : r < 2147483648 := by omega
  have hN31 : N < 2147483648 := by omega
  have hA : A.length = N := hR.2.2.1
  have hAV : Proofs.SegTreeMath.AllV chminMon.toMon A := hR.2.2.2.2.2.1
  -- l += n_node
  have eN : penvN mv.nv (gS P [ci n, ci N, ci h, ci l, ci r, cs f]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci l, ci r, cs f] 1 (ci N) rfl (i32v N hN31)
  have eL : penvN mv.nv (gS P [ci n, ci N, ci h, ci l, ci r, cs f]) (mv.nv + 3) i32 = some (l : Int) :=
    envs mv P [ci n, ci N, ci h, ci l, ci r, cs f] 3 (ci l) rfl (i32v l hl31)
  have vA : vdenM mv vv (penvN mv.nv (gS P [ci n, ci N, ci h, ci l, ci r, cs f]))
      (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1))) = some ((l + N : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eL, Option.bind_some, den_variable, eN, Option.bind_some]
    have : binaryValue .add (l : Int) (N : Int) = ((l + N : Nat) : Int) := by
      show (l : Int) + (N : Int) = _; push_cast; rfl
    rw [this]; exact conv_signed i32 rfl rfl _ (i32v _ (by show l + N < 2147483648; omega))
  have s5 := gSM_assign mv P [ci n, ci N, ci h, ci l, ci r, cs f] vv 3 (by simp) i32 _ _ _ vA (ci l) rfl rfl (i32v l hl31)
    (conv_signed i32 rfl rfl _ (i32v _ (by show l + N < 2147483648; omega)))
  have eS5 : [ci n, ci N, ci h, ci l, ci r, cs f].set 3 ⟨i32, ((l + N : Nat) : Int)⟩ = [ci n, ci N, ci h, ci (l + N), ci r, cs f] := rfl
  rw [eS5] at s5
  have a5 := (pexecM_prim mv fu (.assign (mv.nv + 3) i32 (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1)))) _ _).trans s5
  -- r += n_node
  have eR : penvN mv.nv (gS P [ci n, ci N, ci h, ci (l + N), ci r, cs f]) (mv.nv + 4) i32 = some (r : Int) :=
    envs mv P [ci n, ci N, ci h, ci (l + N), ci r, cs f] 4 (ci r) rfl (i32v r hr31)
  have eN2 : penvN mv.nv (gS P [ci n, ci N, ci h, ci (l + N), ci r, cs f]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci (l + N), ci r, cs f] 1 (ci N) rfl (i32v N hN31)
  have vB : vdenM mv vv (penvN mv.nv (gS P [ci n, ci N, ci h, ci (l + N), ci r, cs f]))
      (.binary i32 .add (.variable i32 (mv.nv + 4)) (.variable i32 (mv.nv + 1))) = some ((r + N : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eR, Option.bind_some, den_variable, eN2, Option.bind_some]
    have : binaryValue .add (r : Int) (N : Int) = ((r + N : Nat) : Int) := by
      show (r : Int) + (N : Int) = _; push_cast; rfl
    rw [this]; exact conv_signed i32 rfl rfl _ (i32v _ (by show r + N < 2147483648; omega))
  have s6 := gSM_assign mv P [ci n, ci N, ci h, ci (l + N), ci r, cs f] vv 4 (by simp) i32 _ _ _ vB (ci r) rfl rfl (i32v r hr31)
    (conv_signed i32 rfl rfl _ (i32v _ (by show r + N < 2147483648; omega)))
  have eS6 : [ci n, ci N, ci h, ci (l + N), ci r, cs f].set 4 ⟨i32, ((r + N : Nat) : Int)⟩ =
      [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] := rfl
  rw [eS6] at s6
  have a6 := (pexecM_prim mv fu (.assign (mv.nv + 4) i32 (.binary i32 .add (.variable i32 (mv.nv + 4)) (.variable i32 (mv.nv + 1)))) _ _).trans s6
  -- pw = n_node
  have eN3 : penvN mv.nv (gS P [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] 1 (ci N) rfl (i32v N hN31)
  have d7 := gSM_decl mv P [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] vv i32 (.variable i32 (mv.nv + 1)) (N : Int) (N : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eN3) (conv_signed i32 rfl rfl _ (i32v N hN31))
  have a7 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 1))) _ _).trans d7
  -- i = h_node
  have eH : penvN mv.nv (gS P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci N])) (mv.nv + 2) i32 = some (h : Int) :=
    envs mv P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci N]) 2 (ci h) rfl (i32v h (by show h < 2147483648; omega))
  have d8 := gSM_decl mv P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci N]) vv i32 (.variable i32 (mv.nv + 2)) (h : Int) (h : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eH) (conv_signed i32 rfl rfl _ (i32v h (by show h < 2147483648; omega)))
  have a8 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 2))) _ _).trans d8
  -- the path loop
  have hI0 : PInv2 N A (l + N) (r + N) h h vv := ⟨hR, fun s ⟨t, ht1, ht2, _⟩ => absurd ht2 (by omega)⟩
  obtain ⟨rL, vF1, hL, retL, psL, vvL, hIf, cL, nL, wL⟩ := path2_loop mv hnv ty0 ty1 P [cs f] 6 rfl A h n (l + N) (r + N) hh29 hn
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ h h vv fu rfl le_rfl hI0 (by omega)
  have hL' : pexecM mv fu (Path2Loop mv.nv 6) (gS P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci N] ++ [ci h])) vv = some rL := hL
  have sLoop := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have sIn := seqM_some a8 rfl sLoop
  have b0 := pexecM_scope mv fu _ _ _ _ sIn
  have tk : (⟨(gS P ([ci n, ci (2 ^ h), ci h, ci (l + N), ci (r + N)] ++ [cs f] ++ [ci (2 ^ 0), ci 0])).mem.take
      (gS P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci N])).mem.length,
      (gS P ([ci n, ci (2 ^ h), ci h, ci (l + N), ci (r + N)] ++ [cs f] ++ [ci (2 ^ 0), ci 0])).bs.take
      (gS P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci N])).bs.length⟩ : PS) =
        gS P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci (2 ^ 0)]) :=
    gS_takeC P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci N])
      ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci (2 ^ 0)]) [ci 0] rfl
  rw [psL] at b0
  simp only [tk] at b0
  -- l2 = l; r2 = r
  have eL2 : penvN mv.nv (gS P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci (2 ^ 0)])) (mv.nv + 3) i32 =
      some ((l + N : Nat) : Int) :=
    envs mv P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci (2 ^ 0)]) 3 (ci (l + N)) rfl
      (i32v _ (by show l + N < 2147483648; omega))
  have d9 := gSM_decl mv P ([ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci (2 ^ 0)]) vF1 i32 (.variable i32 (mv.nv + 3))
    ((l + N : Nat) : Int) ((l + N : Nat) : Int) (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eL2)
    (conv_signed i32 rfl rfl _ (i32v _ (by show l + N < 2147483648; omega)))
  have e9 : [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f] ++ [ci (2 ^ 0)] ++ [(⟨i32, ((l + N : Nat) : Int)⟩ : Cell)] =
      [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f, ci (2 ^ 0), ci (l + N)] := rfl
  rw [e9] at d9
  have a9 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 3))) _ _).trans d9
  have eR2 : penvN mv.nv (gS P [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f, ci (2 ^ 0), ci (l + N)]) (mv.nv + 4) i32 =
      some ((r + N : Nat) : Int) :=
    envs mv P [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f, ci (2 ^ 0), ci (l + N)] 4 (ci (r + N)) rfl
      (i32v _ (by show r + N < 2147483648; omega))
  have d10 := gSM_decl mv P [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f, ci (2 ^ 0), ci (l + N)] vF1 i32
    (.variable i32 (mv.nv + 4)) ((r + N : Nat) : Int) ((r + N : Nat) : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eR2)
    (conv_signed i32 rfl rfl _ (i32v _ (by show r + N < 2147483648; omega)))
  have e10 : [ci n, ci N, ci h, ci (l + N), ci (r + N), cs f, ci (2 ^ 0), ci (l + N)] ++ [(⟨i32, ((r + N : Nat) : Int)⟩ : Cell)] =
      AL n N h (l + N) (r + N) f (2 ^ 0) (l + N) (r + N) := rfl
  rw [e10] at d10
  have a10 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 4))) _ _).trans d10
  -- the loop
  have hrN2 : r + N ≤ 2 * N := by omega
  have hVok : VOK N vF1 := ⟨hIf.1.1, hIf.1.2.1, hIf.1.2.2.2.1, hIf.1.2.2.2.2.1⟩
  have hls : Proofs.LazySegProduct.lsteps (r - l) ≤ Nat.log2 (r - l) + 1 := by
    unfold Proofs.LazySegProduct.lsteps; split <;> omega
  obtain ⟨rW, lF, rF, vvF, hW, retW, psW, vvW, hVF, hQF, hex, hrF, cW, nW, wW⟩ := loopU mv hnv ty0 ty1 P n N h (2 ^ 0) (l + N) (r + N) f
    hn hN31 (by omega) (by omega) vf (QA N (l + N) (r + N) A f h)
    (fun l' r' vv' hq hlt => qa_step N h (l + N) (r + N) A f rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ vf hAV hA l' r' vv' hq hlt)
    (r - l) (l + N) (r + N) vF1 fu (by omega) (by omega) hrN2 hVok
    (qa_init N (l + N) (r + N) A f h (by omega) vF1 hIf.1 hIf.2) (by omega)
  have hQF2 := hQF
  obtain ⟨jF, _, _, hleF, _⟩ := hQF2
  have hlF31 : lF < 2147483648 := by omega
  have hrF31 : rF < 2147483648 := by omega
  -- l = l2
  have e11 : penvN mv.nv (gS P (AL n N h lF rF f (2 ^ 0) (l + N) (r + N))) (mv.nv + 7) i32 = some ((l + N : Nat) : Int) :=
    envs mv P (AL n N h lF rF f (2 ^ 0) (l + N) (r + N)) 7 (ci (l + N)) rfl (i32v _ (by show l + N < 2147483648; omega))
  have s11 := gSM_assign mv P (AL n N h lF rF f (2 ^ 0) (l + N) (r + N)) vvF 3 (by simp) i32 (.variable i32 (mv.nv + 7))
    ((l + N : Nat) : Int) ((l + N : Nat) : Int) (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e11) (ci lF) rfl rfl
    (i32v lF hlF31) (conv_signed i32 rfl rfl _ (i32v _ (by show l + N < 2147483648; omega)))
  have eS11 : (AL n N h lF rF f (2 ^ 0) (l + N) (r + N)).set 3 ⟨i32, ((l + N : Nat) : Int)⟩ =
      AL n N h (l + N) rF f (2 ^ 0) (l + N) (r + N) := rfl
  rw [eS11] at s11
  have a11 := (pexecM_prim mv fu (.assign (mv.nv + 3) i32 (.variable i32 (mv.nv + 7))) _ _).trans s11
  -- r = r2
  have e12 : penvN mv.nv (gS P (AL n N h (l + N) rF f (2 ^ 0) (l + N) (r + N))) (mv.nv + 8) i32 = some ((r + N : Nat) : Int) :=
    envs mv P (AL n N h (l + N) rF f (2 ^ 0) (l + N) (r + N)) 8 (ci (r + N)) rfl (i32v _ (by show r + N < 2147483648; omega))
  have s12 := gSM_assign mv P (AL n N h (l + N) rF f (2 ^ 0) (l + N) (r + N)) vvF 4 (by simp) i32 (.variable i32 (mv.nv + 8))
    ((r + N : Nat) : Int) ((r + N : Nat) : Int) (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e12) (ci rF) rfl rfl
    (i32v rF hrF31) (conv_signed i32 rfl rfl _ (i32v _ (by show r + N < 2147483648; omega)))
  have eS12 : (AL n N h (l + N) rF f (2 ^ 0) (l + N) (r + N)).set 4 ⟨i32, ((r + N : Nat) : Int)⟩ =
      AL n N h (l + N) (r + N) f (2 ^ 0) (l + N) (r + N) := rfl
  rw [eS12] at s12
  have a12 := (pexecM_prim mv fu (.assign (mv.nv + 4) i32 (.variable i32 (mv.nv + 8))) _ _).trans s12
  -- pw = 2
  have s13 := gSM_assign mv P (AL n N h (l + N) (r + N) f (2 ^ 0) (l + N) (r + N)) vvF 6 (by simp) i32 (.literal i32 2)
    (2 : Int) (2 : Int) (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 2 = true from rfl)]) (ci (2 ^ 0)) rfl rfl
    (i32v (2 ^ 0) (by norm_num)) (conv_signed i32 rfl rfl _ (i32v 2 (by norm_num)))
  have eS13 : (AL n N h (l + N) (r + N) f (2 ^ 0) (l + N) (r + N)).set 6 ⟨i32, (2 : Int)⟩ =
      AL n N h (l + N) (r + N) f 2 (l + N) (r + N) := rfl
  rw [eS13] at s13
  have a13 := (pexecM_prim mv fu (.assign (mv.nv + 6) i32 (.literal i32 2)) _ _).trans s13
  -- the final scope: i = 1
  have dI := gSM_decl mv P (AL n N h (l + N) (r + N) f 2 (l + N) (r + N)) vvF i32 (.literal i32 1) (1 : Int) (1 : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 1 = true from rfl)])
    (conv_signed i32 rfl rfl _ (i32v 1 (by norm_num)))
  have eDI : AL n N h (l + N) (r + N) f 2 (l + N) (r + N) ++ [(⟨i32, (1 : Int)⟩ : Cell)] =
      UL n N h (l + N) (r + N) f (2 ^ 1) (l + N) (r + N) 1 := rfl
  rw [eDI] at dI
  have aI := (pexecM_prim mv fu (.declare i32 true (.literal i32 1)) _ _).trans dI
  have hUI0 : UI N (chminRange A l r f) (S2 h (l + N) (r + N) 0) (S2 h (l + N) (r + N) (1 - 1)) (vvF 0) (vvF 1) := by
    simpa using qa_done N h (l + N) (r + N) A f lF rF vvF hQF hex l r rfl rfl hA
  have hQ' : ∀ i vv, 1 ≤ i → i ≤ h →
      UI N (chminRange A l r f) (S2 h (l + N) (r + N) 0) (S2 h (l + N) (r + N) (i - 1)) (vv 0) (vv 1) →
      UI N (chminRange A l r f) (S2 h (l + N) (r + N) 0) (S2 h (l + N) (r + N) (i + 1 - 1))
        (stepUV N (l + N) (r + N) (2 ^ i) vv 0) (stepUV N (l + N) (r + N) (2 ^ i) vv 1) := by
    intro i vv hi hih hq
    have := uf_step N h (l + N) (r + N) i (chminRange A l r f) vv rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hi hih hq
    simpa using this
  obtain ⟨rFin, vFin, hFin, retFin, psFin, vvFin, hVFin, hQFin, cFin, nFin, wFin⟩ := finLoop mv (by omega) ty0 P n h (l + N) (r + N)
    (l + N) (r + N) f hn hh29 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (fun i vv => UI N (chminRange A l r f) (S2 h (l + N) (r + N) 0) (S2 h (l + N) (r + N) (i - 1)) (vv 0) (vv 1))
    hQ' h 1 vvF fu (by omega) le_rfl (by omega) hVF hUI0 (by omega)
  have sFin := seqM_some hFin retFin (pexecM_skip mv fu rFin.ps rFin.vv)
  have sD := seqM_some aI rfl sFin
  have b0' := pexecM_scope mv fu _ _ _ _ sD
  have tk2 : (⟨(gS P (UL n (2 ^ h) h (l + N) (r + N) f (2 ^ (h + 1)) (l + N) (r + N) (h + 1))).mem.take
      (gS P (AL n N h (l + N) (r + N) f 2 (l + N) (r + N))).mem.length,
      (gS P (UL n (2 ^ h) h (l + N) (r + N) f (2 ^ (h + 1)) (l + N) (r + N) (h + 1))).bs.take
      (gS P (AL n N h (l + N) (r + N) f 2 (l + N) (r + N))).bs.length⟩ : PS) =
        gS P (AL n (2 ^ h) h (l + N) (r + N) f (2 ^ (h + 1)) (l + N) (r + N)) :=
    gS_takeC P (AL n N h (l + N) (r + N) f 2 (l + N) (r + N)) (AL n (2 ^ h) h (l + N) (r + N) f (2 ^ (h + 1)) (l + N) (r + N))
      [ci (h + 1)] rfl
  rw [psFin] at b0'
  simp only [tk2] at b0'
  have sE := seqM_some b0' (by simp) (pexecM_skip mv fu _ _)
  have t13 := seqM_some a13 rfl sE
  have t12 := seqM_some a12 rfl t13
  have t11 := seqM_some a11 rfl t12
  have t10 := seqM_some hW retW (by rw [psW, vvW]; exact t11)
  have t9 := seqM_some a10 rfl t10
  have t8 := seqM_some a9 rfl t9
  have t4 := seqM_some b0 (by simp) (by rw [vvL]; exact t8)
  have t3 := seqM_some a7 rfl t4
  have t2 := seqM_some a6 rfl t3
  have t1 := seqM_some a5 rfl t2
  have hUF : UI N (chminRange A l r f) (S2 h (l + N) (r + N) 0) (S2 h (l + N) (r + N) h) (vFin 0) (vFin 1) := by
    simpa using hQFin
  refine ⟨_, vFin, t1, ?_, ?_, rep_of_uf N h (l + N) (r + N) _ _ _ hUF (by rw [chminRange_length]; exact hA)
    (chminRange_allV A l r f hAV vf), ⟨AL n N h (l + N) (r + N) f (2 ^ (h + 1)) (l + N) (r + N), rfl⟩, ?_, ?_, ?_⟩
  · simp
  · simp [vvFin]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL cW cFin ⊢
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nL nW nFin ⊢
    omega
  · simp at wL wW wFin ⊢
    omega

end Proofs.LazySegUpdBody
