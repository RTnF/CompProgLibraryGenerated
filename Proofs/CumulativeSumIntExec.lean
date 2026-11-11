import Proofs.FenwickTreeExec
import Proofs.Generated.CumulativeSum

namespace Proofs.CumulativeSumIntExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB Proofs.FenwickMath Proofs.FenwickBuildMath Proofs.FenwickTreeExec
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den envs M31 vdenM_binary vec_getM vec_getI i32_valid_nat)

/-! ### `CumulativeSum<int>::CumulativeSum(const std::vector<int> &)` (nv = 2)
Vectors: 0 = `cs` (writable), 1 = `v`. Cells: 0 = n, 1 = i. -/

abbrev rdkI (nv : Nat) : NExpr := .read i32 (.local 1) (.cast u64 (.variable i32 (nv + 1)))
abbrev declNI : NStmt := .declare i32 true (.cast i32 (.size (.integer i32) (.local 1)))

theorem size_val1I (mv : MV) (hnv : mv.nv = 2) (hty1 : mv.ty 1 = i32) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (hn : (vv 1).length < 2147483648) :
    vdenM mv vv env (.cast i32 (.size (.integer i32) (.local 1))) = some ((vv 1).length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer i32) (.local 1))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer i32) (.local 1)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer i32) (.local 1)) = some ((vv 1).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨by omega, hty1.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

abbrev rdcs (nv : Nat) : NExpr := .read i32 (.local 0) (.cast u64 (.variable i32 (nv + 1)))
abbrev wrC (nv : Nat) : NStmt := .write (.local 0) i32 (ixk nv) (.binary i32 .add (rdcs nv) (rdkI nv))
abbrev BC (nv : Nat) : Command := .sequence (.primitive (wrC nv)) Sk
abbrev w0S : NStmt := .write (.local 0) i32 (.cast u64 (.literal i32 0)) (.literal i32 0)
abbrev progC (nv : Nat) : Command :=
  .sequence (.primitive declNI) (.sequence (.primitive w0S) (.sequence (forStmtB nv 1 0 (BC nv)) Sk))

theorem body_eqC : Proofs.CumulativeSumInstance.CumulativeSum_int_new0.body = progC 2 := rfl

/-- The state of `cs` after `t` iterations: `cs[q] = pre V q` for `q ≤ t`. -/
def PC (T0 V : List Int) (t : Nat) (X : List Int) : Prop :=
  X.length = T0.length ∧ ∀ q, q < X.length → X[q]? = (if q = 0 then some 0 else if q ≤ t then some (pre V q) else T0[q]?)

theorem PC_zero (T0 V : List Int) (h : 1 ≤ T0.length) : PC T0 V 0 (T0.set 0 0) := by
  refine ⟨by simp, ?_⟩
  intro q hq
  by_cases h0 : q = 0
  · subst h0; simp [List.getElem?_set_self (show 0 < T0.length by omega)]
  · rw [List.getElem?_set_ne (Ne.symm h0)]
    simp [h0]

theorem PC_step (T0 V X : List Int) (t : Nat) (h : PC T0 V t X) (ht : t < V.length) (hX : t + 1 < X.length) :
    PC T0 V (t + 1) (X.set (t + 1) (pre V t + V.getD t 0)) := by
  refine ⟨by simp [h.1], ?_⟩
  intro q hq
  by_cases hq1 : q = t + 1
  · subst hq1
    rw [List.getElem?_set_self hX]
    rw [← pre_succ V t ht]
    simp
  · rw [List.getElem?_set_ne (Ne.symm hq1)]
    have hq' : q < X.length := by simpa using hq
    rw [h.2 q hq']
    by_cases h0 : q = 0
    · simp [h0]
    · have : (q ≤ t + 1) ↔ (q ≤ t) := by omega
      simp [h0, this]

theorem lit_zero_i32 (env : Nat → Ty → Option Int) : (NExpr.literal i32 0).denote env = some 0 := by
  have a : i32.valid 0 = true := by simp [Ty.valid]
  simp [NExpr.denote, a]

theorem cast_zero_u64 (env : Nat → Ty → Option Int) : (NExpr.cast u64 (.literal i32 0)).denote env = some 0 := by
  have a : i32.valid 0 = true := by simp [Ty.valid]
  have b : u64.valid 0 = true := by simp [Ty.valid]
  simp [NExpr.denote, a, Ty.convert_of_valid _ _ b]

set_option maxHeartbeats 4000000 in
/-- `cs[i + 1] = cs[i] + v[i];` -/
theorem bC_exec (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (fu : Nat) (P : List Cell)
    (T0 V X : List Int) (n t : Nat) (hn : n < 2147483647) (ht : t < n) (hV : V.length = n) (hX : X.length = n + 1)
    (hP : PC T0 V t X) (hVv : ∀ y ∈ V, i32.valid y = true) (hpre : ∀ q, q ≤ n → i32.valid (pre V q) = true) :
    ∃ r : PRM, pexecM mv fu (BC mv.nv) (gS P [ci n, ci t]) (VFT X V) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, ci t] ∧ r.vv = VFT (X.set (t + 1) (pre V t + V.getD t 0)) V ∧
      r.cost ≤ 200 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 1 := by
  have E1 := envs mv P [ci n, ci t] 1 (ci t) rfl (validN t (by omega))
  have hp : vdenM mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t])) (ixk mv.nv) = some ((t + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact succ_denF _ (mv.nv + 1) t E1 (by omega)
  have hmem : V.getD t 0 ∈ V := by
    have : V.getD t 0 = V[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hV, ht]
    rw [this]; exact List.getElem_mem _
  have hXt : X[t]? = some (pre V t) := by
    have := hP.2 t (by omega)
    rw [this]
    by_cases h0 : t = 0
    · subst h0; simp [pre]
    · simp [h0]
  have hXg : X.getD t 0 = pre V t := by simp [List.getD_eq_getElem?_getD, hXt]
  have hv1 := hpre t (by omega)
  have hv2 := hpre (t + 1) (by omega)
  have rv := rdM_val mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t])) 1 (by omega) i32 hty1.symm
    (.cast u64 (.variable i32 (mv.nv + 1))) rfl rfl t (cidx_den _ (mv.nv + 1) t E1 (show t < 2147483648 by omega))
    (V.getD t 0) (by rw [VFT_get1]; exact vec_getI V t (by omega)) (by rw [hty1]; exact hVv _ hmem)
  have rc := rdM_val mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t])) 0 (by omega) i32 hty0.symm
    (.cast u64 (.variable i32 (mv.nv + 1))) rfl rfl t (cidx_den _ (mv.nv + 1) t E1 (show t < 2147483648 by omega))
    (pre V t) (by rw [VFT_get0]; exact hXt) (by rw [hty0]; exact hv1)
  have hs : pre V t + V.getD t 0 = pre V (t + 1) := (pre_succ V t (by omega)).symm
  have hx : vdenM mv (VFT X V) (penvN mv.nv (gS P [ci n, ci t])) (.binary i32 .add (rdcs mv.nv) (rdkI mv.nv)) =
      some (pre V t + V.getD t 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ (by simp [NExpr.scalarOnly]), rc, rv, Option.bind_some, Option.bind_some]
    have : binaryValue .add (pre V t) (V.getD t 0) = pre V t + V.getD t 0 := rfl
    rw [this, hs]
    exact Ty.convert_of_valid _ _ hv2
  have wr := pstmtM_write_ok mv (gS P [ci n, ci t]) (VFT X V) 0 (by omega) _ _ (pre V t + V.getD t 0) (t + 1) hx hp
    (by rw [VFT_get0]; omega) (by rw [hty0, hs]; exact hv2)
  rw [hty0, VFT_write0] at wr
  have w1 := (pexecM_prim mv fu (wrC mv.nv) _ _).trans wr
  have w2 := seqM_some w1 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, w2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


set_option maxHeartbeats 8000000 in
theorem lC_loop (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (fu : Nat) (P : List Cell)
    (T0 V : List Int) (n : Nat) (hn : n < 2147483647) (hV : V.length = n) (hT : T0.length = n + 1)
    (hVv : ∀ y ∈ V, i32.valid y = true) (hpre : ∀ q, q ≤ n → i32.valid (pre V q) = true) (hfu : n + 1 ≤ fu) :
    ∃ (res : PRM) (X : List Int), pexecM mv fu (forStmtB mv.nv 1 0 (BC mv.nv)) (gS P [ci n]) (VFT (T0.set 0 0) V) = some res ∧
      res.ps = gS P [ci n] ∧ res.vv = VFT X V ∧ PC T0 V n X ∧ res.ret = none ∧ res.cost ≤ 220 * n + 30 ∧
      res.need ≤ P.length + 60 ∧ res.wk ≤ n := by
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 1 0 n (by omega) hn (BC mv.nv)
    (fun t vv C => (∃ X, vv = VFT X V ∧ PC T0 V t X) ∧ C = [ci n]) 200 60 1 0 (by omega)
    (by
      intro t vv C fu ht hCl hC0 ⟨⟨X, hvv, hP⟩, hC⟩ _
      subst hvv; subst hC
      have hX : X.length = n + 1 := by rw [hP.1]; exact hT
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := bC_exec mv hnv hty0 hty1 fu P T0 V X n t hn ht hV hX hP hVv hpre
      exact ⟨r, [], [ci n], hr, hret, hps, rfl, rfl,
        ⟨⟨X.set (t + 1) (pre V t + V.getD t 0), hvv, PC_step T0 V X t hP (by omega) (by omega)⟩, rfl⟩, hc, hnd, hwk⟩)
    (VFT (T0.set 0 0) V) [ci n] rfl rfl ⟨⟨T0.set 0 0, rfl, PC_zero T0 V (by omega)⟩, rfl⟩ fu (by omega)
  obtain ⟨⟨X, hvv, hP⟩, hC⟩ := hIn
  subst hC
  exact ⟨res, X, hr', hps, hvv, hP, hret, by omega, by omega, by omega⟩

set_option maxHeartbeats 8000000 in
/-- The whole constructor body: `cs[q] = pre V q` for every `q ≤ n`. -/
theorem body_execC (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = i32) (hty1 : mv.ty 1 = i32) (fu : Nat) (P : List Cell)
    (T0 V : List Int) (n : Nat) (hn : n < 2147483647) (hV : V.length = n) (hT : T0.length = n + 1)
    (hVv : ∀ y ∈ V, i32.valid y = true) (hpre : ∀ q, q ≤ n → i32.valid (pre V q) = true) (hfu : n + 1 ≤ fu) :
    ∃ (r : PRM) (X : List Int), pexecM mv fu (progC mv.nv) (gS P []) (VFT T0 V) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n] ∧ r.vv = VFT X V ∧ X.length = n + 1 ∧ (∀ q, q ≤ n → X.getD q 0 = pre V q) ∧
      r.cost ≤ 220 * n + 120 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ n + 1 := by
  have hsz := size_val1I mv hnv hty1 (VFT T0 V) (penvN mv.nv (gS P [])) (by rw [VFT_get1, hV]; omega)
  rw [VFT_get1, hV] at hsz
  have d0 := gSM_decl mv P [] (VFT T0 V) i32 _ _ _ hsz (conv_signed i32 rfl rfl _ (validN n (by omega)))
  have q0 := (pexecM_prim mv fu declNI _ _).trans d0
  have x0 : vdenM mv (VFT T0 V) (penvN mv.nv (gS P [ci n])) (.cast u64 (.literal i32 0)) = some ((0 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cast_zero_u64 _
  have y0 : vdenM mv (VFT T0 V) (penvN mv.nv (gS P [ci n])) (.literal i32 0) = some 0 := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact lit_zero_i32 _
  have hT1 : 0 < T0.length := by omega
  have wr := pstmtM_write_ok mv (gS P [ci n]) (VFT T0 V) 0 (by omega) _ _ 0 0 y0 x0
    (by rw [VFT_get0]; exact hT1) (by rw [hty0]; exact (by simp [Ty.valid] : i32.valid 0 = true))
  rw [hty0, VFT_write0] at wr
  have w1 := (pexecM_prim mv fu w0S _ _).trans wr
  obtain ⟨rl, X, hl, pl, vl, hPC, retl, cl, nl, wl⟩ := lC_loop mv hnv hty0 hty1 fu P T0 V n hn hV hT hVv hpre hfu
  have f1 := seqM_some hl retl (pexecM_skip mv fu rl.ps rl.vv)
  have f2 := seqM_some w1 rfl f1
  have f3 := seqM_some q0 rfl f2
  refine ⟨_, X, f3, rfl, pl, vl, by rw [hPC.1]; exact hT, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq' : q < X.length := by rw [hPC.1]; omega
    have := hPC.2 q hq'
    by_cases h0 : q = 0
    · subst h0
      simp at this
      simp [List.getD_eq_getElem?_getD, this, pre]
    · rw [if_neg h0, if_pos hq] at this
      simp [List.getD_eq_getElem?_getD, this]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cl ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at nl ⊢
    have : rl.ps.mem.length + rl.ps.bs.length = P.length + 2 := by rw [pl]; simp [gS_size]
    omega
  · simp at wl ⊢; omega

end Proofs.CumulativeSumIntExec
