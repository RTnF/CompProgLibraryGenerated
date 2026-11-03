import Proofs.MultiKit
import Proofs.ForLoop

namespace Proofs.ForLoopM
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN env_gen)

/-- `for (int t = ..; t < n; t++) B` where the counter is cell `p` (variable `p + 1`) and `n` is cell 0 (variable 1). -/
abbrev forCond (nv p : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + p)) (.variable i32 nv)
abbrev forInc (nv p : Nat) : NStmt := .assign (nv + p) i32 (.binary i32 .add (.variable i32 (nv + p)) (.literal i32 1))
abbrev forBody (nv p : Nat) (B : Command) : Command := .sequence (.scope B) (.sequence (.primitive (forInc nv p)) (.primitive .skip))
abbrev forLoop (nv p : Nat) (B : Command) : Command := .whileLoop (forCond nv p) (forBody nv p B)

theorem forCond_val (mv : MV) (vv : Nat → List Int) (P Cpre : List Cell) (p n t : Nat) (hp : Cpre.length = p) (h0 : Cpre[0]? = some (ci n))
    (hp1 : 1 ≤ p) (hn : n < 2147483648) (ht : t < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (Cpre ++ [ci t]))) (forCond mv.nv p) = some (if t < n then 1 else 0) := by
  have hs : (forCond mv.nv p).scalarOnly = true := rfl
  have e1 : penvN mv.nv (gS P (Cpre ++ [ci t])) mv.nv i32 = some (n : Int) := by
    have := gSM_env mv.nv P (Cpre ++ [ci t]) 0 (ci n) (by rw [List.getElem?_append_left (by omega)]; exact h0) (validN n hn)
    exact this
  have e2 : penvN mv.nv (gS P (Cpre ++ [ci t])) (mv.nv + p) i32 = some (t : Int) := by
    have := gSM_env mv.nv P (Cpre ++ [ci t]) p (ci t) (by rw [List.getElem?_append_right (by omega)]; simp [hp]) (validN t ht)
    exact this
  rw [vdenM_scalar _ _ _ _ hs, den_binary, den_variable, e2, Option.bind_some, den_variable, e1, Option.bind_some]
  have : binaryValue .lt (t : Int) (n : Int) = if t < n then 1 else 0 := by
    show (if (t : Int) < (n : Int) then 1 else 0) = _
    by_cases h : t < n
    · have : (t : Int) < (n : Int) := by omega
      simp [h]
    · have : ¬ ((t : Int) < (n : Int)) := by omega
      simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : t < n <;> simp [h]

theorem forInc_val (mv : MV) (vv : Nat → List Int) (P Cpre : List Cell) (p t : Nat) (hp : Cpre.length = p)
    (ht : t + 1 < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (Cpre ++ [ci t]))) (.binary i32 .add (.variable i32 (mv.nv + p)) (.literal i32 1)) =
      some ((t + 1 : Nat) : Int) := by
  have hs : (NExpr.binary i32 .add (.variable i32 (mv.nv + p)) (.literal i32 1)).scalarOnly = true := rfl
  have e2 : penvN mv.nv (gS P (Cpre ++ [ci t])) (mv.nv + p) i32 = some (t : Int) := by
    have := gSM_env mv.nv P (Cpre ++ [ci t]) p (ci t) (by rw [List.getElem?_append_right (by omega)]; simp [hp]) (validN t (by omega))
    exact this
  rw [vdenM_scalar _ _ _ _ hs, den_binary, den_variable, e2, Option.bind_some,
    den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .add (t : Int) 1 = ((t + 1 : Nat) : Int) := by
    show (t : Int) + 1 = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ ht)

theorem forInc_step (mv : MV) (vv : Nat → List Int) (P Cpre : List Cell) (p t : Nat) (hp : Cpre.length = p) (hp1 : 1 ≤ p)
    (ht : t + 1 < 2147483648) :
    pstmtM mv (forInc mv.nv p) (gS P (Cpre ++ [ci t])) vv =
      some ⟨gS P (Cpre ++ [ci (t + 1)]), vv, none, (vwp (.binary i32 .add (.variable i32 (mv.nv + p)) (.literal i32 1))).1 + 1,
        P.length + 2 * (Cpre ++ [ci t]).length + (vwp (.binary i32 .add (.variable i32 (mv.nv + p)) (.literal i32 1))).2 + 2, 0⟩ := by
  have hlt : p < (Cpre ++ [ci t]).length := by simp [hp]
  have := gSM_assign mv P (Cpre ++ [ci t]) vv p hlt i32 _ ((t + 1 : Nat) : Int) ((t + 1 : Nat) : Int)
    (forInc_val mv vv P Cpre p t hp ht) (ci t) (by rw [List.getElem?_append_right (by omega)]; simp [hp]) rfl
    (validN t (by omega)) (conv_signed i32 rfl rfl _ (validN _ ht))
  rw [this]
  have hset : (Cpre ++ [ci t]).set p ⟨i32, ((t + 1 : Nat) : Int)⟩ = Cpre ++ [ci (t + 1)] := by
    rw [List.set_append_right _ _ (by omega)]
    simp [hp]
  rw [hset]

theorem vwp_forCond (nv p : Nat) : vwp (forCond nv p) = (3, 3) := by simp [vwp, NExpr.nodes]
theorem vwp_forIncE (nv p : Nat) : vwp (.binary i32 .add (.variable i32 (nv + p)) (.literal i32 1)) = (3, 3) := by
  simp [vwp, NExpr.nodes]

theorem for_loop_run (mv : MV) (P Cpre : List Cell) (p n : Nat) (hp : Cpre.length = p) (h0 : Cpre[0]? = some (ci n))
    (hp1 : 1 ≤ p) (hn : n < 2147483647) (B : Command) (Inv : Nat → (Nat → List Int) → Prop) (cB nB wB fB : Nat)
    (hnB : 2 * p + 12 ≤ nB)
    (hbody : ∀ (t : Nat) (vv : Nat → List Int) (fu : Nat), t < n → Inv t vv → fB ≤ fu →
      ∃ (r : PRM) (cs' : List Cell), pexecM mv fu B (gS P (Cpre ++ [ci t])) vv = some r ∧ r.ret = none ∧
        r.ps = gS P (Cpre ++ [ci t] ++ cs') ∧ Inv (t + 1) r.vv ∧ r.cost ≤ cB ∧ r.need ≤ P.length + nB ∧ r.wk ≤ wB) :
    ∀ (m t0 : Nat), n - t0 = m → t0 ≤ n → ∀ vv, Inv t0 vv → ∀ fu, fB + m + 1 ≤ fu →
      ∃ res : PRM, pexecM mv fu (forLoop mv.nv p B) (gS P (Cpre ++ [ci t0])) vv = some res ∧
        res.ps = gS P (Cpre ++ [ci n]) ∧ Inv n res.vv ∧ res.ret = none ∧ res.cost ≤ (cB + 20) * m + 10 ∧
        res.need ≤ P.length + nB ∧ res.wk ≤ wB * m := by
  intro m
  induction m with
  | zero =>
    intro t0 hm hle vv hI fu hfu
    have ht : t0 = n := by omega
    subst ht
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := forCond_val mv vv P Cpre p t0 t0 hp h0 hp1 (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_forCond]
    refine ⟨_, rfl, rfl, hI, rfl, ?_, ?_, ?_⟩
    · simp
    · simp [gS_size, hp]; omega
    · simp
  | succ m ih =>
    intro t0 hm hle vv hI fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hlt : t0 < n := by omega
    have hc := forCond_val mv vv P Cpre p n t0 hp h0 hp1 (by omega) (by omega)
    rw [if_pos hlt] at hc
    obtain ⟨r1, cs', hB, hret, hps, hI', hcost, hneed, hwk⟩ := hbody t0 vv (fu' + 1) hlt hI (by omega)
    have sc := pexecM_scope mv (fu' + 1) B _ vv r1 hB
    rw [hps] at sc
    simp only [gS_take] at sc
    have inc := forInc_step mv r1.vv P Cpre p t0 hp hp1 (by omega)
    have q := (pexecM_prim mv (fu' + 1) (forInc mv.nv p) _ _).trans inc
    have t2 := seqM_some q rfl (pexecM_skip mv (fu' + 1) (gS P (Cpre ++ [ci (t0 + 1)])) r1.vv)
    have body := seqM_some sc hret t2
    obtain ⟨r2, h2, p2, I2, ret2, c2, n2, w2⟩ := ih (t0 + 1) (by omega) (by omega) r1.vv hI' fu' (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, body, hret, h2, vwp_forCond]
    refine ⟨_, rfl, p2, I2, ret2, ?_, ?_, ?_⟩
    · rw [Nat.mul_succ]
      simp [vwp_forIncE, vwp_forCond] at *
      omega
    · simp [gS_size, hp, vwp_forIncE, vwp_forCond] at *
      omega
    · rw [Nat.mul_succ]
      simp [vwp_forIncE] at *
      omega

/-- The whole `for (int t = 0; t < n; t++) B` statement: the counter lives in its own scope. -/
abbrev forStmt (nv p : Nat) (B : Command) : Command :=
  .scope (.sequence (.primitive (.declare i32 true (.literal i32 0))) (.sequence (forLoop nv p B) (.primitive .skip)))

theorem zero_lit_val (mv : MV) (vv : Nat → List Int) (ps : PS) :
    vdenM mv vv (penvN mv.nv ps) (.literal i32 0) = some 0 := by
  rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]

theorem for_stmt_run (mv : MV) (P Cpre : List Cell) (p n : Nat) (hp : Cpre.length = p) (h0 : Cpre[0]? = some (ci n))
    (hp1 : 1 ≤ p) (hn : n < 2147483647) (B : Command) (Inv : Nat → (Nat → List Int) → Prop) (cB nB wB fB : Nat)
    (hnB : 2 * p + 12 ≤ nB)
    (hbody : ∀ (t : Nat) (vv : Nat → List Int) (fu : Nat), t < n → Inv t vv → fB ≤ fu →
      ∃ (r : PRM) (cs' : List Cell), pexecM mv fu B (gS P (Cpre ++ [ci t])) vv = some r ∧ r.ret = none ∧
        r.ps = gS P (Cpre ++ [ci t] ++ cs') ∧ Inv (t + 1) r.vv ∧ r.cost ≤ cB ∧ r.need ≤ P.length + nB ∧ r.wk ≤ wB)
    (vv : Nat → List Int) (hI : Inv 0 vv) (fu : Nat) (hfu : fB + n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmt mv.nv p B) (gS P Cpre) vv = some res ∧ res.ps = gS P Cpre ∧ Inv n res.vv ∧
      res.ret = none ∧ res.cost ≤ (cB + 20) * n + 30 ∧ res.need ≤ P.length + nB ∧ res.wk ≤ wB * n := by
  have d := gSM_decl mv P Cpre vv i32 _ 0 0 (zero_lit_val mv vv _) (conv_signed i32 rfl rfl _ rfl)
  have q := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d
  obtain ⟨r, hr, hps, hIn, hret, hc, hnd, hw⟩ :=
    for_loop_run mv P Cpre p n hp h0 hp1 hn B Inv cB nB wB fB hnB hbody n 0 (by omega) (by omega) vv hI fu (by omega)
  have hps0 : gS P (Cpre ++ [(⟨i32, 0⟩ : Cell)]) = gS P (Cpre ++ [ci 0]) := rfl
  rw [hps0] at q
  have t1 := seqM_some hr hret (pexecM_skip mv fu _ _)
  have t0 := seqM_some q rfl (by simpa using t1)
  have sc := pexecM_scope mv fu _ _ vv _ t0
  rw [hps] at sc
  simp only [gS_take] at sc
  refine ⟨_, sc, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact hIn
  · rfl
  · show (vwp (NExpr.literal i32 0)).1 + 1 + r.cost + 1 ≤ _
    simp [vwp, NExpr.nodes] at *
    rw [Nat.mul_comm] at *
    omega
  · show max (P.length + 2 * Cpre.length + (vwp (NExpr.literal i32 0)).2 + 4)
      (max r.need ((gS P (Cpre ++ [ci n])).mem.length + (gS P (Cpre ++ [ci n])).bs.length)) ≤ _
    simp [vwp, NExpr.nodes, gS_size, hp] at *
    omega
  · show 0 + r.wk ≤ _
    omega

end Proofs.ForLoopM
