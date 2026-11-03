import Proofs.BeatsApply0
import Proofs.BeatsCalcApply
import Proofs.Generated.SegmentTreeBeats
import Proofs.BeatsNeed
import Proofs.BeatsAlias
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
set_option maxRecDepth 100000

theorem venv (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (k s : Nat) (c : Cell) (hk : cl[k]? = some c)
    (hv : c.type.valid c.value = true) (hs : s = mv.nv + k) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.variable c.type s) = some c.value := by
  rw [vdenM_scalar _ _ _ _ rfl, den_variable, hs]; exact envs mv P cl k c hk hv

theorem lenv (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (t : Ty) (v : Int) (hv : t.valid v = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.literal t v) = some v := by
  rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos hv]

/-- The six leading copies `inf, n, op, a, b, x` of an `apply_op` wrapper. -/
abbrev W6 (op : Nat) (REST : Command) : Command :=
  .sequence (.primitive (.declare s64 true (.variable s64 15)))
  (.sequence (.primitive (.declare i32 true (.variable i32 16)))
  (.sequence (.primitive (.declare i32 true (.literal i32 (op : Int))))
  (.sequence (.primitive (.declare i32 true (.variable i32 17)))
  (.sequence (.primitive (.declare i32 true (.variable i32 18)))
  (.sequence (.primitive (.declare s64 true (.variable s64 19))) REST)))))

theorem w6_exec (mv : MV) (hnv : mv.nv = 15) (P : List Cell) (vv : Nat → List Int) (fu : Nat)
    (inf x : Int) (n a b : Nat) (op : Nat) (hinf : s64.valid inf = true) (hx : s64.valid x = true)
    (hn : n < M31) (ha : a < M31) (hb : b < M31) (hop : i32.valid (op : Int) = true)
    (REST : Command) (r2 : PRM)
    (h2 : pexecM mv fu REST (gS P [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n, ci op, ci a, ci b, cs x]) vv = some r2) :
    ∃ r : PRM, pexecM mv fu (W6 op REST) (gS P [cs inf, ci n, ci a, ci b, cs x]) vv = some r ∧
      r.ps = r2.ps ∧ r.vv = r2.vv ∧ r.ret = r2.ret ∧ r.cost ≤ 12 + r2.cost ∧ r.need ≤ max (P.length + 40) r2.need ∧ r.wk = r2.wk := by
  have K : ∀ (cl : List Cell) (e : NExpr) (v v' : Int) (ty : Ty),
      vdenM mv vv (penvN mv.nv (gS P cl)) e = some v → ty.convert v = some v' →
      pexecM mv fu (.primitive (.declare ty true e)) (gS P cl) vv =
        some ⟨gS P (cl ++ [⟨ty, v'⟩]), vv, none, (vwp e).1 + 1, P.length + 2 * cl.length + (vwp e).2 + 4, 0⟩ :=
    fun cl e v v' ty hv hc => (pexecM_prim mv fu _ _ _).trans (gSM_decl mv P cl vv ty e v v' hv hc)
  have q6 := K [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n, ci op, ci a, ci b] (.variable s64 19) x x s64
    (by have := venv mv vv P [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n, ci op, ci a, ci b] 4 19 (cs x) rfl hx (by omega); exact this)
    (conv_signed s64 rfl rfl _ hx)
  have q5 := K [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n, ci op, ci a] (.variable i32 18) b b i32
    (by have := venv mv vv P [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n, ci op, ci a] 3 18 (ci b) rfl (validN b hb) (by omega); exact this)
    (conv_signed i32 rfl rfl _ (validN b hb))
  have q4 := K [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n, ci op] (.variable i32 17) a a i32
    (by have := venv mv vv P [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n, ci op] 2 17 (ci a) rfl (validN a ha) (by omega); exact this)
    (conv_signed i32 rfl rfl _ (validN a ha))
  have q3 := K [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n] (.literal i32 (op : Int)) op op i32
    (lenv mv vv P _ i32 op hop) (conv_signed i32 rfl rfl _ hop)
  have q2 := K [cs inf, ci n, ci a, ci b, cs x, cs inf] (.variable i32 16) n n i32
    (by have := venv mv vv P [cs inf, ci n, ci a, ci b, cs x, cs inf] 1 16 (ci n) rfl (validN n hn) (by omega); exact this)
    (conv_signed i32 rfl rfl _ (validN n hn))
  have q1 := K [cs inf, ci n, ci a, ci b, cs x] (.variable s64 15) inf inf s64
    (by have := venv mv vv P [cs inf, ci n, ci a, ci b, cs x] 0 15 (cs inf) rfl hinf (by omega); exact this)
    (conv_signed s64 rfl rfl _ hinf)
  have c6 := seqM_some q6 rfl h2
  have c5 := seqM_some q5 rfl c6
  have c4 := seqM_some q4 rfl c5
  have c3 := seqM_some q3 rfl c4
  have c2 := seqM_some q2 rfl c3
  have c1 := seqM_some q1 rfl c2
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
  · simp


theorem wrap_gen (mv : MV) (hnv : mv.nv = 15) (P : List Cell) (vv : Nat → List Int)
    (inf x : Int) (n a b : Nat) (op : Nat) (hinf : s64.valid inf = true) (hx : s64.valid x = true)
    (hn : n < M31) (ha : a < M31) (hb : b < M31) (hop : op < M31)
    (T : Command) (hsim : Sim 5 (ApplyOpCmd 20) T) (hna : noAsg 5 (ApplyOpCmd 20) = true)
    (hWf : Wf (W6 op T) = true) (hNb : Nb (W6 op T) ≤ 335)
    (C W : Nat) (Q : (Nat → List Int) → Prop) (LC : List Cell)
    (hA : ∃ F r, pexecM mv F (ApplyOpCmd 20) (gS P [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n, ci op, ci a, ci b, cs x]) vv = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci a, ci b, cs x] ++ LC) ∧ Q r.vv ∧ r.cost ≤ C ∧ r.wk ≤ W) :
    ∃ F r, pexecM mv F (W6 op T) (gS P [cs inf, ci n, ci a, ci b, cs x]) vv = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci a, ci b, cs x] ++ LC) ∧ Q r.vv ∧ r.cost ≤ C + 12 ∧
      r.need ≤ P.length + 345 ∧ r.wk ≤ W := by
  obtain ⟨F, r2, h2, hret, hps, hQ, hc, hw⟩ := hA
  have hAl : Al 5 [cs inf, ci n, ci a, ci b, cs x, cs inf, ci n, ci op, ci a, ci b, cs x] := ⟨by simp, rfl, rfl⟩
  obtain ⟨h2', _⟩ := sim_exec 5 mv hnv hsim hna F P _ vv r2 hAl h2
  obtain ⟨r, h, e1, e2, e3, e4, e5, e6⟩ := w6_exec mv hnv P vv F inf x n a b op hinf hx hn ha hb (validN op hop) _ r2 h2'
  refine ⟨F, r, h, by rw [e3]; exact hret, by rw [e1]; exact hps, by rw [e2]; exact hQ, by omega, ?_, by omega⟩
  have := (cmd_need mv _ hWf F _ vv r h).1
  simp [szP, gS] at this
  omega

end Proofs.BeatsRep
