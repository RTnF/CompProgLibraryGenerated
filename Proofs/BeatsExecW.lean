import Proofs.BeatsExecBase
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk int_one_ne)

/-- A single write as a command. -/
theorem prim_write (mv : MV) (fu : Nat) (ps : PS) (vv : Nat → List Int) (v : Nat) (hv : v < mv.nv) (ty : Ty) (hty : mv.ty v = ty)
    (iE vE : NExpr) (x : Int) (p : Nat) (hx : vdenM mv vv (penvN mv.nv ps) vE = some x)
    (hp : vdenM mv vv (penvN mv.nv ps) iE = some (p : Int)) (hlt : p < (vv v).length) (hval : ty.valid x = true) :
    pexecM mv fu (.primitive (.write (.local v) ty iE vE)) ps vv =
      some ⟨ps, upd vv v ((vv v).set p x), none, (vwp vE).1 + (vwp iE).1 + 3,
        ps.mem.length + ps.bs.length + iE.nodes + vE.nodes + (vwp vE).2 + (vwp iE).2 + 5, 1⟩ := by
  subst hty
  exact (pexecM_prim mv fu _ ps vv).trans (pstmtM_write_ok mv ps vv v hv iE vE x p hx hp hlt hval)

/-- One write followed by the rest of a straight-line sequence. -/
theorem seq_write (mv : MV) (fu : Nat) (ps : PS) (vv : Nat → List Int) (v : Nat) (hv : v < mv.nv) (ty : Ty) (hty : mv.ty v = ty) (iE vE : NExpr)
    (x : Int) (p : Nat) (hx : vdenM mv vv (penvN mv.nv ps) vE = some x) (hp : vdenM mv vv (penvN mv.nv ps) iE = some (p : Int))
    (hlt : p < (vv v).length) (hval : ty.valid x = true) (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST ps (upd vv v ((vv v).set p x)) = some r) (hret : r.ret = none)
    (c0 : Nat) (hc0 : (vwp vE).1 + (vwp iE).1 + 3 ≤ c0) (n0 : Nat)
    (hn0 : ps.mem.length + ps.bs.length + iE.nodes + vE.nodes + (vwp vE).2 + (vwp iE).2 + 5 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (.write (.local v) ty iE vE)) REST) ps vv = some r2 ∧
      r2.ret = none ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧ r2.need ≤ max n0 r.need ∧ r2.wk ≤ 1 + r.wk := by
  subst hty
  have w := pstmtM_write_ok mv ps vv v hv iE vE x p hx hp hlt hval
  have a1 := (pexecM_prim mv fu (.write (.local v) (mv.ty v) iE vE) ps vv).trans w
  have a2 := seqM_some a1 rfl (by simpa using hrest)
  refine ⟨_, a2, hret, rfl, rfl, ?_, ?_, ?_⟩
  · simp; omega
  · simp; omega
  · simp


open Proofs.BellmanFordExec (pexecM_branch_true pexecM_branch_false)

/-- `if (C) { v[i] = e; }` followed by the rest. -/
theorem seq_cw (mv : MV) (fu : Nat) (ps : PS) (vv : Nat → List Int) (v : Nat) (hv : v < mv.nv) (ty : Ty) (hty : mv.ty v = ty)
    (iE vE cE : NExpr) (C : Prop) [Decidable C] (x : Int) (p : Nat)
    (hc : vdenM mv vv (penvN mv.nv ps) cE = some (if C then 1 else 0))
    (hx : C → vdenM mv vv (penvN mv.nv ps) vE = some x) (hp : C → vdenM mv vv (penvN mv.nv ps) iE = some (p : Int))
    (hlt : C → p < (vv v).length) (hval : C → ty.valid x = true) (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST ps (if C then upd vv v ((vv v).set p x) else vv) = some r) (hret : r.ret = none) (hps : r.ps = ps)
    (c0 : Nat) (hc0 : (vwp vE).1 + (vwp iE).1 + (vwp cE).1 + 6 ≤ c0) (n0 : Nat)
    (hn0 : ps.mem.length + ps.bs.length + iE.nodes + vE.nodes + (vwp vE).2 + (vwp iE).2 + (vwp cE).2 + 8 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch cE (.sequence (.scope (.sequence (.primitive (.write (.local v) ty iE vE)) Sk)) Sk) Sk) REST)
        ps vv = some r2 ∧ r2.ret = none ∧ r2.ps = ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧ r2.need ≤ max n0 r.need ∧ r2.wk ≤ 1 + r.wk := by
  subst hty
  by_cases hC : C
  · rw [if_pos hC] at hc hrest
    have w := pstmtM_write_ok mv ps vv v hv iE vE x p (hx hC) (hp hC) (hlt hC) (hval hC)
    have a1 := (pexecM_prim mv fu (.write (.local v) (mv.ty v) iE vE) ps vv).trans w
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu ps (upd vv v ((vv v).set p x)))
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    have tk : (⟨ps.mem.take ps.mem.length, ps.bs.take ps.bs.length⟩ : PS) = ps := by simp
    simp only [tk] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu ps (upd vv v ((vv v).set p x)))
    have b1 := pexecM_branch_true mv fu cE _ Sk ps vv 1 hc (by decide) _ a4
    have b2 := seqM_some b1 rfl (by simpa [hps] using hrest)
    refine ⟨_, b2, hret, hps, rfl, ?_, ?_, ?_⟩
    · simp; omega
    · simp; omega
    · simp
  · rw [if_neg hC] at hc hrest
    have b1 := pexecM_branch_false mv fu cE (.sequence (.scope (.sequence (.primitive (.write (.local v) (mv.ty v) iE vE)) Sk)) Sk) Sk ps vv hc _
      (pexecM_skip mv fu ps vv)
    have b2 := seqM_some b1 rfl (by simpa using hrest)
    refine ⟨_, b2, hret, hps, rfl, ?_, ?_, ?_⟩
    · simp; omega
    · simp; omega
    · simp


/-- `if (C) { v1[i] = e1; } else { v2[i] = e2; }` followed by the rest. -/
theorem seq_ite (mv : MV) (fu : Nat) (ps : PS) (vv : Nat → List Int) (v1 v2 : Nat) (hv1 : v1 < mv.nv) (hv2 : v2 < mv.nv)
    (ty : Ty) (ht1 : mv.ty v1 = ty) (ht2 : mv.ty v2 = ty) (iE vE1 vE2 cE : NExpr) (C : Prop) [Decidable C]
    (x1 x2 : Int) (p : Nat)
    (hc : vdenM mv vv (penvN mv.nv ps) cE = some (if C then 1 else 0))
    (hx1 : C → vdenM mv vv (penvN mv.nv ps) vE1 = some x1) (hx2 : ¬ C → vdenM mv vv (penvN mv.nv ps) vE2 = some x2)
    (hp : vdenM mv vv (penvN mv.nv ps) iE = some (p : Int))
    (hlt1 : C → p < (vv v1).length) (hlt2 : ¬ C → p < (vv v2).length)
    (hval1 : C → ty.valid x1 = true) (hval2 : ¬ C → ty.valid x2 = true) (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST ps (if C then upd vv v1 ((vv v1).set p x1) else upd vv v2 ((vv v2).set p x2)) = some r)
    (hret : r.ret = none) (hps : r.ps = ps)
    (c0 : Nat) (hc0 : (vwp vE1).1 + (vwp vE2).1 + (vwp iE).1 + (vwp cE).1 + 8 ≤ c0) (n0 : Nat)
    (hn0 : ps.mem.length + ps.bs.length + iE.nodes + vE1.nodes + vE2.nodes + (vwp vE1).2 + (vwp vE2).2 + (vwp iE).2 + (vwp cE).2 + 10 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch cE (.sequence (.scope (.sequence (.primitive (.write (.local v1) ty iE vE1)) Sk)) Sk)
        (.sequence (.scope (.sequence (.primitive (.write (.local v2) ty iE vE2)) Sk)) Sk)) REST) ps vv = some r2 ∧
      r2.ret = none ∧ r2.ps = ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧ r2.need ≤ max n0 r.need ∧ r2.wk ≤ 1 + r.wk := by
  have tk : (⟨ps.mem.take ps.mem.length, ps.bs.take ps.bs.length⟩ : PS) = ps := by simp
  by_cases hC : C
  · rw [if_pos hC] at hc hrest
    have a1 := prim_write mv fu ps vv v1 hv1 ty ht1 iE vE1 x1 p (hx1 hC) hp (hlt1 hC) (hval1 hC)
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu ps (upd vv v1 ((vv v1).set p x1)))
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    simp only [tk] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu ps (upd vv v1 ((vv v1).set p x1)))
    have b1 := pexecM_branch_true mv fu cE _ (.sequence (.scope (.sequence (.primitive (.write (.local v2) ty iE vE2)) Sk)) Sk)
      ps vv 1 hc (by decide) _ a4
    have b2 := seqM_some b1 rfl (by simpa [hps] using hrest)
    refine ⟨_, b2, hret, hps, rfl, ?_, ?_, ?_⟩
    · simp; omega
    · simp; omega
    · simp
  · rw [if_neg hC] at hc hrest
    have a1 := prim_write mv fu ps vv v2 hv2 ty ht2 iE vE2 x2 p (hx2 hC) hp (hlt2 hC) (hval2 hC)
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu ps (upd vv v2 ((vv v2).set p x2)))
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    simp only [tk] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu ps (upd vv v2 ((vv v2).set p x2)))
    have b1 := pexecM_branch_false mv fu cE (.sequence (.scope (.sequence (.primitive (.write (.local v1) ty iE vE1)) Sk)) Sk)
      _ ps vv hc _ a4
    have b2 := seqM_some b1 rfl (by simpa [hps] using hrest)
    refine ⟨_, b2, hret, hps, rfl, ?_, ?_, ?_⟩
    · simp; omega
    · simp; omega
    · simp

end Proofs.BeatsExec
