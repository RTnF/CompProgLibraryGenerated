import Proofs.TreeArcCostsExec
import Proofs.RunLengthExec
import Proofs.Generated.TreePath

namespace Proofs.TreePathExec
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
open Proofs.TopoSortExec (i32v one_den zero_den)
open Proofs.TreeArcCostsExec (VC VC_get0 VC_get1 VC_set1)
open Proofs.RunLengthExec (inc_val)

/-! ### `tree_path` (nv = 2: parent, out).  Cells: 0 = from, 1 = tg, 2 = k, 3 = v -/

abbrev cP (nv : Nat) : NExpr := .binary bT .ne (.variable i32 (nv + 3)) (.variable i32 (nv + 0))
abbrev wP (nv : Nat) : NStmt := .write (.local 1) i32 (.cast u64 (.variable i32 (nv + 2))) (.variable i32 (nv + 3))
abbrev aK (nv : Nat) : NStmt := .assign (nv + 2) i32 (.binary i32 .add (.variable i32 (nv + 2)) (.literal i32 1))
abbrev aV (nv : Nat) : NStmt := .assign (nv + 3) i32 (.read i32 (.local 0) (.cast u64 (.variable i32 (nv + 3))))
abbrev wF (nv : Nat) : NStmt := .write (.local 1) i32 (.cast u64 (.variable i32 (nv + 2))) (.variable i32 (nv + 0))
abbrev Bp (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (wP nv)) (.sequence (.primitive (aK nv)) (.sequence (.primitive (aV nv)) Sk)))) Sk
abbrev bodyTP (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.literal i32 0))) (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 1))))
    (.sequence (.whileLoop (cP nv) (Bp nv)) (.sequence (.primitive (wF nv))
      (.sequence (.primitive (.ret (.binary i32 .add (.variable i32 (nv + 2)) (.literal i32 1)))) Sk))))

theorem body_eqTP : Proofs.TreePathInstance.tree_path.body = bodyTP 2 := rfl

abbrev C4 (f tg k v : Nat) : List Cell := [ci f, ci tg, ci k, ci v]

/-- The contents of `out` after `t` iterations: the first `t` vertices of the chain. -/
def Ot (ch : Nat → Nat) (O : List Int) (t : Nat) : List Int := (List.range t).map (fun i => (ch i : Int)) ++ O.drop t

theorem Ot_len (ch : Nat → Nat) (O : List Int) (t : Nat) (h : t ≤ O.length) : (Ot ch O t).length = O.length := by
  unfold Ot; rw [List.length_append, List.length_map, List.length_range, List.length_drop]; omega

theorem Ot_succ (ch : Nat → Nat) (O : List Int) (t : Nat) (h : t < O.length) :
    (Ot ch O t).set t (ch t : Int) = Ot ch O (t + 1) := by
  unfold Ot
  have hl : ((List.range t).map (fun i => (ch i : Int))).length = t := by simp
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self, List.range_succ, List.map_append]
  have hd : O.drop t = O[t] :: O.drop (t + 1) := List.drop_eq_getElem_cons h
  rw [hd, List.set_cons_zero]
  simp [List.append_assoc]

theorem cond_val (mv : MV) (hnv : mv.nv = 2) (vv : Nat → List Int) (P : List Cell) (f tg k v : Nat)
    (hf : f < M31) (hv : v < M31) :
    vdenM mv vv (penvN mv.nv (gS P (C4 f tg k v))) (cP mv.nv) = some (if v = f then 0 else 1) := by
  have e0 := gSM_env mv.nv P (C4 f tg k v) 0 (ci f) rfl (i32v f hf)
  have e3 := gSM_env mv.nv P (C4 f tg k v) 3 (ci v) rfl (i32v v hv)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e3, Option.bind_some, den_variable, e0, Option.bind_some]
  by_cases h : v = f
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : ¬ ((v : Int) = (f : Int)) := by omega
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

set_option maxHeartbeats 16000000 in
/-- One iteration: `out[k] = v; k = k + 1; v = parent[v];`. -/
theorem b_body (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (V O : List Int) (ch : Nat → Nat)
    (P : List Cell) (f tg m t : Nat) (ht : t < m) (hm : m + 1 ≤ O.length) (hlt : ∀ i, i ≤ m → ch i < M31)
    (hch : ∀ i, i < m → ch i < V.length ∧ V.getD (ch i) 0 = ((ch (i + 1) : Nat) : Int)) (hf : f < M31) (hmM : m < M31)
    (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Bp mv.nv) (gS P (C4 f tg t (ch t))) (VC V (Ot ch O t)) = some r ∧ r.ret = none ∧
      r.ps = gS P (C4 f tg (t + 1) (ch (t + 1))) ∧ r.vv = VC V (Ot ch O (t + 1)) ∧
      r.cost ≤ 300 ∧ r.need ≤ P.length + 80 ∧ r.wk ≤ 1 := by
  have htM : t < M31 := Nat.lt_trans ht hmM
  have hct := hlt t (by omega)
  have hct1 := hlt (t + 1) (by omega)
  obtain ⟨hcl, hcv⟩ := hch t ht
  have hOl : (Ot ch O t).length = O.length := Ot_len ch O t (by omega)
  have E2 := envs mv P (C4 f tg t (ch t)) 2 (ci t) rfl (i32v t htM)
  have E3 := envs mv P (C4 f tg t (ch t)) 3 (ci (ch t)) rfl (i32v _ hct)
  have hi : ∀ W, vdenM mv W (penvN mv.nv (gS P (C4 f tg t (ch t)))) (.cast u64 (.variable i32 (mv.nv + 2))) = some ((t : Nat) : Int) := by
    intro W; rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 2) t E2 htM
  have hv : ∀ W, vdenM mv W (penvN mv.nv (gS P (C4 f tg t (ch t)))) (.variable i32 (mv.nv + 3)) = some ((ch t : Nat) : Int) := by
    intro W; rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3
  have w1 := pstmtM_write_ok mv (gS P (C4 f tg t (ch t))) (VC V (Ot ch O t)) 1 (by omega) (.cast u64 (.variable i32 (mv.nv + 2)))
    (.variable i32 (mv.nv + 3)) ((ch t : Nat) : Int) t (hv _) (hi _) (by rw [VC_get1, hOl]; omega) (by rw [ty1]; exact i32v _ hct)
  rw [ty1, VC_get1, VC_set1, Ot_succ ch O t (by omega)] at w1
  have a1 := (pexecM_prim mv fu (wP mv.nv) _ _).trans w1
  -- k = k + 1
  have lv := inc_val mv (VC V (Ot ch O (t + 1))) (penvN mv.nv (gS P (C4 f tg t (ch t)))) (mv.nv + 2) t E2 (by
    show t + 1 < 2147483648; have : m < 2147483648 := hmM; omega)
  have stK := gSM_assign mv P (C4 f tg t (ch t)) (VC V (Ot ch O (t + 1))) 2 (by simp) i32 _ _ _ lv (ci t) rfl rfl
    (i32v t htM) (conv_signed i32 rfl rfl _ (validN _ (by show t + 1 < 2147483648; have : m < 2147483648 := hmM; omega)))
  have eK : (C4 f tg t (ch t)).set 2 ⟨i32, ((t + 1 : Nat) : Int)⟩ = C4 f tg (t + 1) (ch t) := rfl
  rw [eK] at stK
  have a2 := (pexecM_prim mv fu (aK mv.nv) _ _).trans stK
  -- v = parent[v]
  have E3' := envs mv P (C4 f tg (t + 1) (ch t)) 3 (ci (ch t)) rfl (i32v _ hct)
  have rd := rdM_val mv (VC V (Ot ch O (t + 1))) (penvN mv.nv (gS P (C4 f tg (t + 1) (ch t)))) 0 (by omega) i32 ty0.symm
    (.cast u64 (.variable i32 (mv.nv + 3))) rfl rfl (ch t) (cidx_den _ (mv.nv + 3) (ch t) E3' hct) ((ch (t + 1) : Nat) : Int)
    (by rw [VC_get0, ← hcv]; exact vec_getI V (ch t) hcl) (by rw [ty0]; exact i32v _ hct1)
  have stV := gSM_assign mv P (C4 f tg (t + 1) (ch t)) (VC V (Ot ch O (t + 1))) 3 (by simp) i32 _ _ _ rd (ci (ch t)) rfl rfl
    (i32v _ hct) (conv_signed i32 rfl rfl _ (i32v _ hct1))
  have eV : (C4 f tg (t + 1) (ch t)).set 3 ⟨i32, ((ch (t + 1) : Nat) : Int)⟩ = C4 f tg (t + 1) (ch (t + 1)) := rfl
  rw [eV] at stV
  have a3 := (pexecM_prim mv fu (aV mv.nv) _ _).trans stV
  have b3 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
  have b2 := seqM_some a2 rfl b3
  have b1 := seqM_some a1 rfl b2
  have b4 := pexecM_scope mv fu _ _ _ _ b1
  have b5 := Proofs.PexecKit.scope_take (gS P (C4 f tg t (ch t))) (gS P (C4 f tg (t + 1) (ch (t + 1))))
    (by simp [gS]) (by simp [gS])
  simp only [b5] at b4
  have b6 := seqM_some b4 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, b6, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

set_option maxHeartbeats 16000000 in
/-- The loop `while (v != from) {...}` run from the state after `t` iterations. -/
theorem while_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (V O : List Int) (ch : Nat → Nat)
    (P : List Cell) (f tg m : Nat) (hm : m + 1 ≤ O.length) (hlt : ∀ i, i ≤ m → ch i < M31)
    (hch : ∀ i, i < m → ch i < V.length ∧ V.getD (ch i) 0 = ((ch (i + 1) : Nat) : Int)) (hne : ∀ i, i < m → ch i ≠ f)
    (hend : ch m = f) (hf : f < M31) (hmM : m < M31) :
    ∀ r t fu, t + r = m → r + 1 ≤ fu →
      ∃ res : PRM, pexecM mv fu (.whileLoop (cP mv.nv) (Bp mv.nv)) (gS P (C4 f tg t (ch t))) (VC V (Ot ch O t)) = some res ∧
        res.ret = none ∧ res.ps = gS P (C4 f tg m (ch m)) ∧ res.vv = VC V (Ot ch O m) ∧
        res.cost ≤ 400 * r + 20 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ r := by
  intro r
  induction r with
  | zero =>
    intro t fu ht hfu
    have htm : t = m := by omega
    subst htm
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_val mv hnv (VC V (Ot ch O t)) P f tg t (ch t) hf (hlt t (le_refl _))
    rw [if_pos hend] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ r ih =>
    intro t fu ht hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have htm : t < m := by omega
    have hc := cond_val mv hnv (VC V (Ot ch O t)) P f tg t (ch t) hf (hlt t (by omega))
    rw [if_neg (hne t htm)] at hc
    obtain ⟨r1, h1, hret1, hps1, hvv1, hc1, hn1, hw1⟩ := b_body mv hnv ty0 ty1 V O ch P f tg m t htm hm hlt hch hf hmM (fu' + 1)
    obtain ⟨r2, h2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := ih (t + 1) fu' (by omega) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, hret1, hps1, hvv1, h2]
    refine ⟨_, rfl, hret2, hps2, hvv2, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc1 hc2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hn1 hn2 ⊢; omega
    · simp at hw1 hw2 ⊢; omega

set_option maxHeartbeats 16000000 in
/-- The whole body of `tree_path`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (V O : List Int) (ch : Nat → Nat)
    (P : List Cell) (f tg m : Nat) (hm : m + 1 ≤ O.length) (hlt : ∀ i, i ≤ m → ch i < M31)
    (hch : ∀ i, i < m → ch i < V.length ∧ V.getD (ch i) 0 = ((ch (i + 1) : Nat) : Int)) (hne : ∀ i, i < m → ch i ≠ f)
    (hend : ch m = f) (h0 : ch 0 = tg) (hf : f < M31) (htg : tg < M31) (hmM : m + 1 < M31) (fu : Nat) (hfu : m + 2 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyTP mv.nv) (gS P [ci f, ci tg]) (VC V O) = some r ∧
      r.ret = some ((m + 1 : Nat) : Int) ∧ r.vv = VC V (Ot ch O (m + 1)) ∧ (∃ cs : List Cell, r.ps = gS P cs) ∧
      r.cost ≤ 400 * m + 100 ∧ r.need ≤ P.length + 80 ∧ r.wk ≤ m + 1 := by
  have hmM' : m < M31 := by have : m + 1 < M31 := hmM; omega
  have d1 := gSM_decl mv P [ci f, ci tg] (VC V O) i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact zero_den _) (conv_signed i32 rfl rfl _ (i32v 0 (by decide)))
  have q1 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d1
  have E1 := envs mv P [ci f, ci tg, ci 0] 1 (ci tg) rfl (i32v tg htg)
  have d2 := gSM_decl mv P [ci f, ci tg, ci 0] (VC V O) i32 (.variable i32 (mv.nv + 1)) (tg : Int) (tg : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1) (conv_signed i32 rfl rfl _ (i32v tg htg))
  have q2 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 1))) _ _).trans d2
  have hOl0 : Ot ch O 0 = O := by simp [Ot]
  have hc0 : ch 0 = tg := h0
  obtain ⟨res, hw, hret, hps, hvv, hc, hn, hwk⟩ := while_exec mv hnv ty0 ty1 V O ch P f tg m hm hlt hch hne hend hf hmM' m 0 fu
    (by omega) (by omega)
  rw [hc0, hOl0] at hw
  have hcell : ([ci f, ci tg] ++ [ci 0] ++ [(⟨i32, (tg : Int)⟩ : Cell)]) = C4 f tg 0 tg := rfl
  -- out[k] = from
  have E0 := envs mv P (C4 f tg m (ch m)) 0 (ci f) rfl (i32v f hf)
  have E2 := envs mv P (C4 f tg m (ch m)) 2 (ci m) rfl (i32v m hmM')
  have hi : vdenM mv (VC V (Ot ch O m)) (penvN mv.nv (gS P (C4 f tg m (ch m)))) (.cast u64 (.variable i32 (mv.nv + 2))) =
      some ((m : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 2) m E2 hmM'
  have hv : vdenM mv (VC V (Ot ch O m)) (penvN mv.nv (gS P (C4 f tg m (ch m)))) (.variable i32 (mv.nv + 0)) =
      some ((f : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E0
  have hOl : (Ot ch O m).length = O.length := Ot_len ch O m (by omega)
  have w1 := pstmtM_write_ok mv (gS P (C4 f tg m (ch m))) (VC V (Ot ch O m)) 1 (by omega) (.cast u64 (.variable i32 (mv.nv + 2)))
    (.variable i32 (mv.nv + 0)) ((f : Nat) : Int) m hv hi (by rw [VC_get1, hOl]; omega) (by rw [ty1]; exact i32v f hf)
  have hset : (Ot ch O m).set m ((f : Nat) : Int) = Ot ch O (m + 1) := by
    rw [← hend]; exact Ot_succ ch O m (by omega)
  rw [ty1, VC_get1, VC_set1, hset] at w1
  have a1 := (pexecM_prim mv fu (wF mv.nv) _ _).trans w1
  -- return k + 1
  have lv := inc_val mv (VC V (Ot ch O (m + 1))) (penvN mv.nv (gS P (C4 f tg m (ch m)))) (mv.nv + 2) m E2 hmM
  have rr := pstmtM_ret_ok mv (gS P (C4 f tg m (ch m))) (VC V (Ot ch O (m + 1))) _ _ lv
  have e5 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have c3 := seqM_some a1 rfl (by simpa using e5)
  have c2 := seqM_some hw hret (by rw [hps, hvv]; exact c3)
  have c1 := seqM_some q2 rfl (by simpa [hcell] using c2)
  have c0 := seqM_some q1 rfl c1
  refine ⟨_, c0, rfl, rfl, ⟨C4 f tg m (ch m), ?_⟩, ?_, ?_, ?_⟩
  · rfl
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hn ⊢; omega
  · simp at hwk ⊢; omega

end Proofs.TreePathExec
