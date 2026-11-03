import Proofs.ForLoopB

namespace Proofs.ForLoopG
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.PrefixSumsCall (bT)
open Proofs.ForLoopB (forCondB forLoopB forStmtB forCondB_val vwp_forCondB)

/-- Like `for_loop_run`, but the cells below the counter (`C`, e.g. an accumulator) may change in every iteration. -/
theorem for_loop_runG {γ : Type} (mv : MV) (P : List Cell) (p b n : Nat) (hb : b < p) (hn : n < 2147483647) (B : Command)
    (Inv : Nat → (Nat → List Int) → List Cell → γ → Prop) (Φc Φw : γ → Nat)
    (cB nB wB fB : Nat) (hnB : 2 * p + 12 ≤ nB)
    (hbody : ∀ (t : Nat) (vv : Nat → List Int) (C : List Cell) (g : γ) (fu : Nat), t < n → C.length = p → C[b]? = some (ci n) →
      Inv t vv C g → fB ≤ fu →
      ∃ (r : PRM) (cs' C' : List Cell) (g' : γ), pexecM mv fu B (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧
        r.ps = gS P (C' ++ [ci t] ++ cs') ∧ C'.length = p ∧ C'[b]? = some (ci n) ∧ Inv (t + 1) r.vv C' g' ∧
        r.cost + Φc g' ≤ cB + Φc g ∧ r.need ≤ P.length + nB ∧
        r.wk + Φw g' ≤ wB + Φw g) :
    ∀ (m t0 : Nat), n - t0 = m → t0 ≤ n → ∀ vv C (g : γ), C.length = p → C[b]? = some (ci n) → Inv t0 vv C g → ∀ fu, fB + m + 1 ≤ fu →
      ∃ (res : PRM) (C2 : List Cell) (g2 : γ), pexecM mv fu (forLoopB mv.nv p b B) (gS P (C ++ [ci t0])) vv = some res ∧
        res.ps = gS P (C2 ++ [ci n]) ∧ C2.length = p ∧ Inv n res.vv C2 g2 ∧ res.ret = none ∧ res.cost + Φc g2 ≤ (cB + 20) * m + 10 + Φc g ∧
        res.need ≤ P.length + nB ∧ res.wk + Φw g2 ≤ wB * m + Φw g := by
  intro m
  induction m with
  | zero =>
    intro t0 hm hle vv C g hCp h0 hI fu hfu
    have ht : t0 = n := by omega
    subst ht
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := forCondB_val mv vv P C p b t0 t0 hCp h0 hb (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_forCondB]
    refine ⟨_, C, g, rfl, rfl, hCp, hI, rfl, ?_, ?_, ?_⟩
    · simp
    · simp [gS_size, hCp]; omega
    · simp
  | succ m ih =>
    intro t0 hm hle vv C g hCp h0 hI fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hlt : t0 < n := by omega
    have hc := forCondB_val mv vv P C p b n t0 hCp h0 hb (by omega) (by omega)
    rw [if_pos hlt] at hc
    obtain ⟨r1, cs', C', g', hB, hret, hps, hC'p, hC'0, hI', hcost, hneed, hwk⟩ :=
      hbody t0 vv C g (fu' + 1) hlt hCp h0 hI (by omega)
    have sc := pexecM_scope mv (fu' + 1) B _ vv r1 hB
    rw [hps] at sc
    have tk := gS_takeC P (C ++ [ci t0]) (C' ++ [ci t0]) cs' (by simp [hCp, hC'p])
    simp only [List.append_assoc] at sc tk ⊢
    simp only [tk] at sc
    have inc := forInc_step mv r1.vv P C' p t0 hC'p (by omega) (by omega)
    have q := (pexecM_prim mv (fu' + 1) (forInc mv.nv p) _ _).trans inc
    have t2 := seqM_some q rfl (pexecM_skip mv (fu' + 1) (gS P (C' ++ [ci (t0 + 1)])) r1.vv)
    have body := seqM_some sc hret t2
    obtain ⟨r2, C2, g2, h2, p2, C2p, I2, ret2, c2, n2, w2⟩ :=
      ih (t0 + 1) (by omega) (by omega) r1.vv C' g' hC'p hC'0 hI' fu' (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, body, hret, h2, vwp_forCondB]
    refine ⟨_, C2, g2, rfl, p2, C2p, I2, ret2, ?_, ?_, ?_⟩
    · rw [Nat.mul_succ]
      simp [vwp_forIncE, vwp_forCondB] at *
      omega
    · simp [gS_size, hCp, vwp_forIncE, vwp_forCondB] at *
      omega
    · rw [Nat.mul_succ]
      simp [vwp_forIncE] at *
      omega

theorem for_stmt_runG {γ : Type} (mv : MV) (P : List Cell) (p b n : Nat) (hb : b < p) (hn : n < 2147483647) (B : Command)
    (Inv : Nat → (Nat → List Int) → List Cell → γ → Prop) (Φc Φw : γ → Nat)
    (cB nB wB fB : Nat) (hnB : 2 * p + 12 ≤ nB)
    (hbody : ∀ (t : Nat) (vv : Nat → List Int) (C : List Cell) (g : γ) (fu : Nat), t < n → C.length = p → C[b]? = some (ci n) →
      Inv t vv C g → fB ≤ fu →
      ∃ (r : PRM) (cs' C' : List Cell) (g' : γ), pexecM mv fu B (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧
        r.ps = gS P (C' ++ [ci t] ++ cs') ∧ C'.length = p ∧ C'[b]? = some (ci n) ∧ Inv (t + 1) r.vv C' g' ∧
        r.cost + Φc g' ≤ cB + Φc g ∧ r.need ≤ P.length + nB ∧
        r.wk + Φw g' ≤ wB + Φw g)
    (vv : Nat → List Int) (C : List Cell) (g : γ) (hCp : C.length = p) (h0 : C[b]? = some (ci n)) (hI : Inv 0 vv C g) (fu : Nat)
    (hfu : fB + n + 1 ≤ fu) :
    ∃ (res : PRM) (C2 : List Cell) (g2 : γ), pexecM mv fu (forStmtB mv.nv p b B) (gS P C) vv = some res ∧ res.ps = gS P C2 ∧
      C2.length = p ∧ Inv n res.vv C2 g2 ∧ res.ret = none ∧ res.cost + Φc g2 ≤ (cB + 20) * n + 30 + Φc g ∧ res.need ≤ P.length + nB ∧
      res.wk + Φw g2 ≤ wB * n + Φw g := by
  have d := gSM_decl mv P C vv i32 _ 0 0 (zero_lit_val mv vv _) (conv_signed i32 rfl rfl _ rfl)
  have q := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d
  obtain ⟨r, C2, g2, hr, hps, hC2, hIn, hret, hc, hnd, hw⟩ :=
    for_loop_runG mv P p b n hb hn B Inv Φc Φw cB nB wB fB hnB hbody n 0 (by omega) (by omega) vv C g hCp h0 hI fu (by omega)
  have hps0 : gS P (C ++ [(⟨i32, 0⟩ : Cell)]) = gS P (C ++ [ci 0]) := rfl
  rw [hps0] at q
  have t1 := seqM_some hr hret (pexecM_skip mv fu _ _)
  have t0 := seqM_some q rfl (by simpa using t1)
  have sc := pexecM_scope mv fu _ _ vv _ t0
  rw [hps] at sc
  have tk := gS_takeC P C C2 [ci n] (by simp [hCp, hC2])
  simp only [tk] at sc
  refine ⟨_, C2, g2, sc, rfl, hC2, ?_, ?_, ?_, ?_, ?_⟩
  · exact hIn
  · rfl
  · show (vwp (NExpr.literal i32 0)).1 + 1 + r.cost + 1 + Φc g2 ≤ _
    simp [vwp, NExpr.nodes] at *
    rw [Nat.mul_comm] at *
    omega
  · show max (P.length + 2 * C.length + (vwp (NExpr.literal i32 0)).2 + 4)
      (max r.need ((gS P (C2 ++ [ci n])).mem.length + (gS P (C2 ++ [ci n])).bs.length)) ≤ _
    simp [vwp, NExpr.nodes, gS_size, hCp, hC2] at *
    omega
  · show 0 + r.wk + Φw g2 ≤ _
    omega

end Proofs.ForLoopG
