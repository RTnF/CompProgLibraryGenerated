import Proofs.TreeEdgesExec
import Proofs.Generated.TreeFindRoot

namespace Proofs.TreeFindRootExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false
  getD_mem lt_conv)
open Proofs.TopoSortExec (i32v eq_conv)
open Proofs.TreeEdgesExec (cz Wr wrap_true wrap_false)

/-! ### `tree_find_root` (nv = 1: parent).  Cells: 0 = n, 1 = r, 2 = i, 3 = p -/

abbrev ixp (nv : Nat) : NExpr := .cast u64 (.variable i32 (nv + 2))
abbrev dPR (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 0) (ixp nv))
abbrev cEqR (nv : Nat) : NExpr := .binary bT .eq (.variable i32 (nv + 3)) (.variable i32 (nv + 2))
abbrev cNegR (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 3)) (.literal i32 0)
abbrev asR (nv : Nat) : NStmt := .assign (nv + 1) i32 (.variable i32 (nv + 2))
abbrev Yas (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (asR nv)) Sk)) Sk
abbrev Bfr (nv : Nat) : Command :=
  .sequence (.primitive (dPR nv)) (.sequence (.branch (cEqR nv) (Yas nv) (Wr (cNegR nv) (Yas nv))) Sk)
abbrev negOne : NExpr := .unary i32 .neg (.literal i32 1)
abbrev bodyFR (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true negOne)) (.sequence (forStmtB nv 2 0 (Bfr nv))
    (.sequence (.primitive (.ret (.variable i32 (nv + 1)))) Sk))

theorem body_eqFR : Proofs.TreeFindRootInstance.tree_find_root.body = bodyFR 1 := rfl

theorem negOne_den (env : Nat → Ty → Option Int) : negOne.denote env = some (-1) := by
  have : (NExpr.unary i32 .neg (.literal i32 1)).denote env =
      ((NExpr.literal i32 1).denote env).bind (fun v => i32.convert (unaryValue .neg v)) := by
    simp [NExpr.denote]
  rw [this, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  exact conv_signed i32 rfl rfl _ rfl

/-- The root found among the first `t` indices (`-1` if none). -/
def rootT (Pr : List Int) : Nat → Int
  | 0 => -1
  | t + 1 => if Pr.getD t 0 = (t : Int) ∨ Pr.getD t 0 < 0 then (t : Int) else rootT Pr t

def VP (Pr : List Int) : Nat → List Int := fun k => if k = 0 then Pr else []

theorem VP_get0 (Pr : List Int) : VP Pr 0 = Pr := by simp [VP]

abbrev cellsR (n : Nat) (r : Int) (t : Nat) (p : Int) : List Cell := [ci n, cz r, ci t, cz p]

set_option maxHeartbeats 8000000 in
/-- The assignment `r = i`. -/
theorem yas_exec (mv : MV) (hnv : mv.nv = 1) (Pr : List Int) (P : List Cell) (n : Nat) (r : Int) (t : Nat) (p : Int)
    (hn : n < M31) (ht : t < n) (hrv : i32.valid r = true) (fu : Nat) :
    ∃ x : PRM, pexecM mv fu (Yas mv.nv) (gS P (cellsR n r t p)) (VP Pr) = some x ∧ x.ret = none ∧
      x.ps = gS P (cellsR n (t : Int) t p) ∧ x.vv = VP Pr ∧ x.cost ≤ 40 ∧ x.need ≤ P.length + 40 ∧ x.wk = 0 := by
  have htM : t < M31 := Nat.lt_trans ht hn
  have E2 := gSM_env mv.nv P (cellsR n r t p) 2 (ci t) rfl (i32v t htM)
  have hx : vdenM mv (VP Pr) (penvN mv.nv (gS P (cellsR n r t p))) (.variable i32 (mv.nv + 2)) = some (t : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2
  have as1 := gSM_assign mv P (cellsR n r t p) (VP Pr) 1 (by simp) i32 _ _ _ hx (cz r) rfl rfl hrv
    (conv_signed i32 rfl rfl _ (i32v t htM))
  have a1 := (pexecM_prim mv fu (asR mv.nv) _ _).trans as1
  have hset : (cellsR n r t p).set 1 ⟨i32, (t : Int)⟩ = cellsR n (t : Int) t p := rfl
  rw [hset] at a1
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ (VP Pr))
  have sc := pexecM_scope mv fu _ _ _ _ a2
  have tk := gS_takeC P (cellsR n r t p) (cellsR n (t : Int) t p) [] rfl
  simp only [List.append_nil] at tk
  simp only [tk] at sc
  have a3 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, a3, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]

set_option maxHeartbeats 16000000 in
/-- One iteration of the loop. -/
theorem bfr_exec (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = i32) (Pr : List Int) (P : List Cell) (n : Nat) (r : Int) (t : Nat)
    (hn : n < M31) (ht : t < n) (hPl : t < Pr.length) (hrv : i32.valid r = true) (hPv : i32.valid (Pr.getD t 0) = true)
    (fu : Nat) :
    ∃ x : PRM, pexecM mv fu (Bfr mv.nv) (gS P [ci n, cz r, ci t]) (VP Pr) = some x ∧ x.ret = none ∧
      x.ps = gS P (cellsR n (if Pr.getD t 0 = (t : Int) ∨ Pr.getD t 0 < 0 then (t : Int) else r) t (Pr.getD t 0)) ∧
      x.vv = VP Pr ∧ x.cost ≤ 200 ∧ x.need ≤ P.length + 60 ∧ x.wk = 0 := by
  have htM : t < M31 := Nat.lt_trans ht hn
  generalize hpdef : Pr.getD t 0 = p at hPv ⊢
  have E2 := envs mv P [ci n, cz r, ci t] 2 (ci t) rfl (i32v t htM)
  have rp := rdM_val mv (VP Pr) (penvN mv.nv (gS P [ci n, cz r, ci t])) 0 (by omega) i32 ty0.symm (ixp mv.nv) rfl rfl t
    (cidx_den _ (mv.nv + 2) t E2 htM) p (by rw [VP_get0, ← hpdef]; exact vec_getI Pr t hPl) (by rw [ty0]; exact hPv)
  have d1 := gSM_decl mv P [ci n, cz r, ci t] (VP Pr) i32 _ _ _ rp (conv_signed i32 rfl rfl _ hPv)
  have q1 := (pexecM_prim mv fu (dPR mv.nv) _ _).trans d1
  have e2 := envs mv P (cellsR n r t p) 2 (ci t) rfl (i32v t htM)
  have e3 := envs mv P (cellsR n r t p) 3 (cz p) rfl hPv
  have hceq : vdenM mv (VP Pr) (penvN mv.nv (gS P (cellsR n r t p))) (cEqR mv.nv) = some (if p = (t : Int) then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e3, Option.bind_some, den_variable, e2, Option.bind_some, eq_conv]
  have hcneg : vdenM mv (VP Pr) (penvN mv.nv (gS P (cellsR n r t p))) (cNegR mv.nv) = some (if p < 0 then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e3, Option.bind_some, den_literal,
      if_pos (show i32.valid 0 = true from rfl), Option.bind_some, lt_conv]
  obtain ⟨xa, hxa, hreta, hpsa, hvva, hca, hna, hwa⟩ := yas_exec mv hnv Pr P n r t p hn ht hrv fu
  have fin : ∀ (rb : PRM) (r' : Int), pexecM mv fu (.branch (cEqR mv.nv) (Yas mv.nv) (Wr (cNegR mv.nv) (Yas mv.nv))) (gS P (cellsR n r t p))
      (VP Pr) = some rb → rb.ret = none → rb.ps = gS P (cellsR n r' t p) → rb.vv = VP Pr → rb.cost ≤ 120 →
      rb.need ≤ P.length + 50 → rb.wk = 0 →
      ∃ x : PRM, pexecM mv fu (Bfr mv.nv) (gS P [ci n, cz r, ci t]) (VP Pr) = some x ∧ x.ret = none ∧
        x.ps = gS P (cellsR n r' t p) ∧ x.vv = VP Pr ∧ x.cost ≤ 200 ∧ x.need ≤ P.length + 60 ∧ x.wk = 0 := by
    intro rb r' hrb hret hps hvv hc hn' hw
    have s1 := seqM_some hrb hret (pexecM_skip mv fu _ _)
    have s2 := seqM_some q1 rfl s1
    refine ⟨_, s2, by simpa using hret, by simp [hps], by simp [hvv], ?_, ?_, by simp [hw]⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hps]; omega
  by_cases h1 : p = (t : Int)
  · rw [if_pos h1] at hceq
    have b1 := pexecM_branch_true mv fu (cEqR mv.nv) (Yas mv.nv) (Wr (cNegR mv.nv) (Yas mv.nv)) _ _ 1 hceq (by decide) xa hxa
    obtain ⟨x, hx, hret, hps, hvv, hc, hn', hw⟩ := fin _ (t : Int) b1 (by simpa using hreta) (by simp [hpsa]) (by simp [hvva])
      (by simp [vwp, NExpr.nodes] at *; omega) (by simp [vwp, NExpr.nodes, gS_mem_len, gS_bs_len, hpsa] at *; omega) (by simp [hwa])
    refine ⟨x, hx, hret, ?_, hvv, hc, hn', hw⟩
    rw [if_pos (Or.inl h1)]; exact hps
  · rw [if_neg h1] at hceq
    by_cases h2 : p < 0
    · rw [if_pos h2] at hcneg
      obtain ⟨xw, hxw, hretw, hpsw, hvvw, hcw, hnw, hww⟩ := wrap_true mv fu (cNegR mv.nv) (Yas mv.nv) P (cellsR n r t p)
        (cellsR n (t : Int) t p) (VP Pr) xa hcneg hxa hreta hpsa rfl
      have b1 := pexecM_branch_false mv fu (cEqR mv.nv) (Yas mv.nv) (Wr (cNegR mv.nv) (Yas mv.nv)) _ _ hceq xw hxw
      obtain ⟨x, hx, hret, hps, hvv, hc, hn', hw⟩ := fin _ (t : Int) b1 (by simpa using hretw) (by simp [hpsw]) (by simp [hvvw, hvva])
        (by simp [vwp, NExpr.nodes, NExpr.scalarOnly] at *; omega)
        (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len, hpsw] at *; omega) (by simp [hww, hwa])
      refine ⟨x, hx, hret, ?_, hvv, hc, hn', hw⟩
      rw [if_pos (Or.inr h2)]; exact hps
    · rw [if_neg h2] at hcneg
      obtain ⟨xw, hxw, hretw, hpsw, hvvw, hcw, hnw, hww⟩ := wrap_false mv fu (cNegR mv.nv) (Yas mv.nv) P (cellsR n r t p) (VP Pr) hcneg
      have b1 := pexecM_branch_false mv fu (cEqR mv.nv) (Yas mv.nv) (Wr (cNegR mv.nv) (Yas mv.nv)) _ _ hceq xw hxw
      obtain ⟨x, hx, hret, hps, hvv, hc, hn', hw⟩ := fin _ r b1 (by simpa using hretw) (by simp [hpsw]) (by simp [hvvw])
        (by simp [vwp, NExpr.nodes, NExpr.scalarOnly] at *; omega)
        (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len, hpsw] at *; omega) (by simp [hww])
      refine ⟨x, hx, hret, ?_, hvv, hc, hn', hw⟩
      rw [if_neg (by tauto)]; exact hps

theorem i32_valid_of_int (x : Int) (h : -2147483648 ≤ x ∧ x < 2147483648) : i32.valid x = true := by
  show Ty.valid ⟨32, true, false⟩ x = true
  simp [Ty.valid]
  omega

theorem rootT_range (Pr : List Int) : ∀ t, rootT Pr t = -1 ∨ (0 ≤ rootT Pr t ∧ rootT Pr t < (t : Int)) := by
  intro t
  induction t with
  | zero => left; rfl
  | succ t ih =>
    unfold rootT
    by_cases h : Pr.getD t 0 = (t : Int) ∨ Pr.getD t 0 < 0
    · rw [if_pos h]; right; omega
    · rw [if_neg h]
      rcases ih with h1 | h1
      · left; exact h1
      · right; omega

set_option maxHeartbeats 16000000 in
/-- The whole body of `tree_find_root`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = i32) (Pr : List Int) (P : List Cell) (n : Nat)
    (hn : n < M31) (hn2 : n < 2147483647) (hPl : n ≤ Pr.length) (hPv : ∀ x ∈ Pr, i32.valid x = true) (fu : Nat) (hfu : n + 2 ≤ fu) :
    ∃ x : PRM, pexecM mv fu (bodyFR mv.nv) (gS P [ci n]) (VP Pr) = some x ∧ x.ret = some (rootT Pr n) ∧ x.vv = VP Pr ∧
      (∃ cs : List Cell, x.ps = gS P cs) ∧ x.cost ≤ 220 * n + 60 ∧ x.need ≤ P.length + 60 ∧ x.wk = 0 := by
  have mem : ∀ j, j < Pr.length → i32.valid (Pr.getD j 0) = true := fun j hj => hPv _ (getD_mem _ _ hj)
  have hnM : n < 2147483648 := hn
  have rvalid : ∀ t, t ≤ n → i32.valid (rootT Pr t) = true := by
    intro t ht
    rcases rootT_range Pr t with h | h
    · rw [h]; decide
    · exact i32_valid_of_int _ (by omega)
  have d0 := gSM_decl mv P [ci n] (VP Pr) i32 negOne (-1) (-1) (by rw [vdenM_scalar _ _ _ _ rfl]; exact negOne_den _)
    (conv_signed i32 rfl rfl _ (by decide))
  have q0 := (pexecM_prim mv fu (.declare i32 true negOne) _ _).trans d0
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 2 0 n (by omega) (by omega) (Bfr mv.nv)
    (fun t vv C => vv = VP Pr ∧ C = [ci n, cz (rootT Pr t)]) 200 60 0 0 (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      obtain ⟨x, hx, hret, hps, hvv, hc, hnd, hwk⟩ := bfr_exec mv hnv ty0 Pr P n (rootT Pr t) t hn ht (by omega)
        (rvalid t (by omega)) (mem t (by omega)) fu
      refine ⟨x, [cz (Pr.getD t 0)], [ci n, cz (rootT Pr (t + 1))], hx, hret, ?_, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, by omega⟩
      · rw [hps]
        have e : rootT Pr (t + 1) = if Pr.getD t 0 = (t : Int) ∨ Pr.getD t 0 < 0 then (t : Int) else rootT Pr t := rfl
        show _ = gS P ([ci n, cz (rootT Pr (t + 1))] ++ [ci t] ++ [cz (Pr.getD t 0)])
        rw [e]; rfl
      · rw [hvv])
    (VP Pr) [ci n, cz (rootT Pr 0)] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hIn
  subst hC
  have e1 := gSM_env mv.nv P [ci n, cz (rootT Pr n)] 1 (cz (rootT Pr n)) rfl (rvalid n (Nat.le_refl _))
  have rr := pstmtM_ret_ok mv (gS P [ci n, cz (rootT Pr n)]) (VP Pr) (.variable i32 (mv.nv + 1)) (rootT Pr n)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e1)
  have e4 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have hr0 : pexecM mv fu (forStmtB mv.nv 2 0 (Bfr mv.nv)) (gS P ([ci n] ++ [(⟨i32, -1⟩ : Cell)])) (VP Pr) = some res := hr'
  have c2 := seqM_some hr0 hret (by rw [hps, hvv]; exact e4)
  have c1 := seqM_some q0 rfl c2
  refine ⟨_, c1, rfl, ?_, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · simp [hvv]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hps] at hnd ⊢; omega
  · simp at hw ⊢; omega

end Proofs.TreeFindRootExec