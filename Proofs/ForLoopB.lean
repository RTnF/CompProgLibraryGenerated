import Proofs.ForLoopC

namespace Proofs.ForLoopB
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.PrefixSumsCall (bT)

/-- Like `forCond`, but the bound `n` is cell `b` (variable `nv + b`) instead of cell 0. -/
abbrev forCondB (nv p b : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + p)) (.variable i32 (nv + b))
abbrev forLoopB (nv p b : Nat) (B : Command) : Command := .whileLoop (forCondB nv p b) (forBody nv p B)
abbrev forStmtB (nv p b : Nat) (B : Command) : Command :=
  .scope (.sequence (.primitive (.declare i32 true (.literal i32 0))) (.sequence (forLoopB nv p b B) (.primitive .skip)))

theorem forCondB_val (mv : MV) (vv : Nat → List Int) (P Cpre : List Cell) (p b n t : Nat) (hp : Cpre.length = p)
    (h0 : Cpre[b]? = some (ci n)) (hb : b < p) (hn : n < 2147483648) (ht : t < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (Cpre ++ [ci t]))) (forCondB mv.nv p b) = some (if t < n then 1 else 0) := by
  have hs : (forCondB mv.nv p b).scalarOnly = true := rfl
  have e1 : penvN mv.nv (gS P (Cpre ++ [ci t])) (mv.nv + b) i32 = some (n : Int) := by
    have := gSM_env mv.nv P (Cpre ++ [ci t]) b (ci n) (by rw [List.getElem?_append_left (by omega)]; exact h0) (validN n hn)
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

theorem vwp_forCondB (nv p b : Nat) : vwp (forCondB nv p b) = (3, 3) := by simp [vwp, NExpr.nodes]

/-- Like `for_loop_run`, but the cells below the counter (`C`, e.g. an accumulator) may change in every iteration. -/
theorem for_loop_runB (mv : MV) (P : List Cell) (p b n : Nat) (hb : b < p) (hn : n < 2147483647) (B : Command)
    (Inv : Nat → (Nat → List Int) → List Cell → Prop) (cB nB wB fB : Nat) (hnB : 2 * p + 12 ≤ nB)
    (hbody : ∀ (t : Nat) (vv : Nat → List Int) (C : List Cell) (fu : Nat), t < n → C.length = p → C[b]? = some (ci n) →
      Inv t vv C → fB ≤ fu →
      ∃ (r : PRM) (cs' C' : List Cell), pexecM mv fu B (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧
        r.ps = gS P (C' ++ [ci t] ++ cs') ∧ C'.length = p ∧ C'[b]? = some (ci n) ∧ Inv (t + 1) r.vv C' ∧
        r.cost ≤ cB ∧ r.need ≤ P.length + nB ∧ r.wk ≤ wB) :
    ∀ (m t0 : Nat), n - t0 = m → t0 ≤ n → ∀ vv C, C.length = p → C[b]? = some (ci n) → Inv t0 vv C → ∀ fu, fB + m + 1 ≤ fu →
      ∃ (res : PRM) (C2 : List Cell), pexecM mv fu (forLoopB mv.nv p b B) (gS P (C ++ [ci t0])) vv = some res ∧
        res.ps = gS P (C2 ++ [ci n]) ∧ C2.length = p ∧ Inv n res.vv C2 ∧ res.ret = none ∧ res.cost ≤ (cB + 20) * m + 10 ∧
        res.need ≤ P.length + nB ∧ res.wk ≤ wB * m := by
  intro m
  induction m with
  | zero =>
    intro t0 hm hle vv C hCp h0 hI fu hfu
    have ht : t0 = n := by omega
    subst ht
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := forCondB_val mv vv P C p b t0 t0 hCp h0 hb (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_forCondB]
    refine ⟨_, C, rfl, rfl, hCp, hI, rfl, ?_, ?_, ?_⟩
    · simp
    · simp [gS_size, hCp]; omega
    · simp
  | succ m ih =>
    intro t0 hm hle vv C hCp h0 hI fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hlt : t0 < n := by omega
    have hc := forCondB_val mv vv P C p b n t0 hCp h0 hb (by omega) (by omega)
    rw [if_pos hlt] at hc
    obtain ⟨r1, cs', C', hB, hret, hps, hC'p, hC'0, hI', hcost, hneed, hwk⟩ :=
      hbody t0 vv C (fu' + 1) hlt hCp h0 hI (by omega)
    have sc := pexecM_scope mv (fu' + 1) B _ vv r1 hB
    rw [hps] at sc
    have tk := gS_takeC P (C ++ [ci t0]) (C' ++ [ci t0]) cs' (by simp [hCp, hC'p])
    simp only [List.append_assoc] at sc tk ⊢
    simp only [tk] at sc
    have inc := forInc_step mv r1.vv P C' p t0 hC'p (by omega) (by omega)
    have q := (pexecM_prim mv (fu' + 1) (forInc mv.nv p) _ _).trans inc
    have t2 := seqM_some q rfl (pexecM_skip mv (fu' + 1) (gS P (C' ++ [ci (t0 + 1)])) r1.vv)
    have body := seqM_some sc hret t2
    obtain ⟨r2, C2, h2, p2, C2p, I2, ret2, c2, n2, w2⟩ :=
      ih (t0 + 1) (by omega) (by omega) r1.vv C' hC'p hC'0 hI' fu' (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, body, hret, h2, vwp_forCondB]
    refine ⟨_, C2, rfl, p2, C2p, I2, ret2, ?_, ?_, ?_⟩
    · rw [Nat.mul_succ]
      simp [vwp_forIncE, vwp_forCondB] at *
      omega
    · simp [gS_size, hCp, vwp_forIncE, vwp_forCondB] at *
      omega
    · rw [Nat.mul_succ]
      simp [vwp_forIncE] at *
      omega

theorem for_stmt_runB (mv : MV) (P : List Cell) (p b n : Nat) (hb : b < p) (hn : n < 2147483647) (B : Command)
    (Inv : Nat → (Nat → List Int) → List Cell → Prop) (cB nB wB fB : Nat) (hnB : 2 * p + 12 ≤ nB)
    (hbody : ∀ (t : Nat) (vv : Nat → List Int) (C : List Cell) (fu : Nat), t < n → C.length = p → C[b]? = some (ci n) →
      Inv t vv C → fB ≤ fu →
      ∃ (r : PRM) (cs' C' : List Cell), pexecM mv fu B (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧
        r.ps = gS P (C' ++ [ci t] ++ cs') ∧ C'.length = p ∧ C'[b]? = some (ci n) ∧ Inv (t + 1) r.vv C' ∧
        r.cost ≤ cB ∧ r.need ≤ P.length + nB ∧ r.wk ≤ wB)
    (vv : Nat → List Int) (C : List Cell) (hCp : C.length = p) (h0 : C[b]? = some (ci n)) (hI : Inv 0 vv C) (fu : Nat)
    (hfu : fB + n + 1 ≤ fu) :
    ∃ (res : PRM) (C2 : List Cell), pexecM mv fu (forStmtB mv.nv p b B) (gS P C) vv = some res ∧ res.ps = gS P C2 ∧
      C2.length = p ∧ Inv n res.vv C2 ∧ res.ret = none ∧ res.cost ≤ (cB + 20) * n + 30 ∧ res.need ≤ P.length + nB ∧
      res.wk ≤ wB * n := by
  have d := gSM_decl mv P C vv i32 _ 0 0 (zero_lit_val mv vv _) (conv_signed i32 rfl rfl _ rfl)
  have q := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d
  obtain ⟨r, C2, hr, hps, hC2, hIn, hret, hc, hnd, hw⟩ :=
    for_loop_runB mv P p b n hb hn B Inv cB nB wB fB hnB hbody n 0 (by omega) (by omega) vv C hCp h0 hI fu (by omega)
  have hps0 : gS P (C ++ [(⟨i32, 0⟩ : Cell)]) = gS P (C ++ [ci 0]) := rfl
  rw [hps0] at q
  have t1 := seqM_some hr hret (pexecM_skip mv fu _ _)
  have t0 := seqM_some q rfl (by simpa using t1)
  have sc := pexecM_scope mv fu _ _ vv _ t0
  rw [hps] at sc
  have tk := gS_takeC P C C2 [ci n] (by simp [hCp, hC2])
  simp only [tk] at sc
  refine ⟨_, C2, sc, rfl, hC2, ?_, ?_, ?_, ?_, ?_⟩
  · exact hIn
  · rfl
  · show (vwp (NExpr.literal i32 0)).1 + 1 + r.cost + 1 ≤ _
    simp [vwp, NExpr.nodes] at *
    rw [Nat.mul_comm] at *
    omega
  · show max (P.length + 2 * C.length + (vwp (NExpr.literal i32 0)).2 + 4)
      (max r.need ((gS P (C2 ++ [ci n])).mem.length + (gS P (C2 ++ [ci n])).bs.length)) ≤ _
    simp [vwp, NExpr.nodes, gS_size, hCp, hC2] at *
    omega
  · show 0 + r.wk ≤ _
    omega

end Proofs.ForLoopB
