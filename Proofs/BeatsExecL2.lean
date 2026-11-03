import Proofs.BeatsExecL0
import Proofs.BeatsExecU0
import Proofs.BeatsExecS
import Proofs.BeatsExecW
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.BellmanFordExec


theorem seq_sbranch_r {rv : Option Int} (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (slot : Nat) (hslot : slot < cl.length)
    (ty : Ty) (cE eA : NExpr) (C : Prop) [Decidable C] (v v' : Int) (c : Cell)
    (hc : vdenM mv vv (penvN mv.nv (gS P cl)) cE = some (if C then 1 else 0))
    (hv : C → vdenM mv vv (penvN mv.nv (gS P cl)) eA = some v) (hcc : cl[slot]? = some c) (hct : c.type = ty)
    (hcv : ty.valid c.value = true) (hconv : C → ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (if C then cl.set slot ⟨ty, v'⟩ else cl)) vv = some r) (hret : r.ret = rv)
    (c0 : Nat) (hc0 : (vwp eA).1 + (vwp cE).1 + 4 ≤ c0) (n0 : Nat)
    (hn0 : P.length + 2 * cl.length + (vwp eA).2 + (vwp cE).2 + 6 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch cE (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + slot) ty eA)) Sk)) Sk) Sk) REST)
        (gS P cl) vv = some r2 ∧ r2.ret = rv ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧
        r2.need ≤ max n0 r.need ∧ r2.wk ≤ r.wk := by
  by_cases hC : C
  · rw [if_pos hC] at hc hrest
    have as1 := gSM_assign mv P cl vv slot hslot ty eA v v' (hv hC) c hcc hct hcv (hconv hC)
    have a1 := (pexecM_prim mv fu (.assign (mv.nv + slot) ty eA) (gS P cl) vv).trans as1
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (cl.set slot ⟨ty, v'⟩)) vv)
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    simp only [gS_take_len P cl (cl.set slot ⟨ty, v'⟩) (by simp)] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (cl.set slot ⟨ty, v'⟩)) vv)
    have b1 := pexecM_branch_true mv fu cE _ Sk (gS P cl) vv 1 hc (by decide) _ a4
    have b2 := seqM_some b1 rfl hrest
    refine ⟨_, b2, hret, rfl, rfl, ?_, ?_, ?_⟩
    · simp; omega
    · simp [gS_size]; omega
    · simp
  · rw [if_neg hC] at hc hrest
    have b1 := pexecM_branch_false mv fu cE (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + slot) ty eA)) Sk)) Sk) Sk
      (gS P cl) vv hc _ (pexecM_skip mv fu (gS P cl) vv)
    have b2 := seqM_some b1 rfl hrest
    refine ⟨_, b2, hret, rfl, rfl, ?_, ?_, ?_⟩
    · simp; omega
    · simp [gS_size]; omega
    · simp

theorem seq_sbranch2_r {rv : Option Int} (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (slot : Nat) (hslot : slot < cl.length)
    (ty : Ty) (cE eA : NExpr) (C : Prop) [Decidable C] (v v' : Int) (c : Cell)
    (hc : vdenM mv vv (penvN mv.nv (gS P cl)) cE = some (if C then 1 else 0))
    (hv : C → vdenM mv vv (penvN mv.nv (gS P cl)) eA = some v) (hcc : cl[slot]? = some c) (hct : c.type = ty)
    (hcv : ty.valid c.value = true) (hconv : C → ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (cl.set slot ⟨ty, if C then v' else c.value⟩)) vv = some r) (hret : r.ret = rv)
    (c0 : Nat) (hc0 : (vwp eA).1 + (vwp cE).1 + 4 ≤ c0) (n0 : Nat)
    (hn0 : P.length + 2 * cl.length + (vwp eA).2 + (vwp cE).2 + 6 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch cE (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + slot) ty eA)) Sk)) Sk) Sk) REST)
        (gS P cl) vv = some r2 ∧ r2.ret = rv ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧
        r2.need ≤ max n0 r.need ∧ r2.wk ≤ r.wk := by
  apply seq_sbranch_r (rv := rv) mv fu P cl vv slot hslot ty cE eA C v v' c hc hv hcc hct hcv hconv REST r _ hret c0 hc0 n0 hn0
  by_cases hC : C
  · rw [if_pos hC]; rw [if_pos hC] at hrest; exact hrest
  · rw [if_neg hC]; rw [if_neg hC] at hrest
    have : (⟨ty, c.value⟩ : Cell) = c := by cases c; simp at hct ⊢; exact hct.symm
    rw [this, set_self_cell cl slot c hcc] at hrest
    exact hrest

theorem seq_sbranch3_r {rv : Option Int} (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (slot : Nat) (hslot : slot < cl.length)
    (ty : Ty) (cE eA : NExpr) (C : Prop) [Decidable C] (v v' x0 : Int) (c : Cell)
    (hc : vdenM mv vv (penvN mv.nv (gS P cl)) cE = some (if C then 1 else 0))
    (hv : C → vdenM mv vv (penvN mv.nv (gS P cl)) eA = some v) (hcc : cl[slot]? = some c) (hct : c.type = ty)
    (hcv : ty.valid c.value = true) (hx0 : c.value = x0) (hconv : C → ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (cl.set slot ⟨ty, if C then v' else x0⟩)) vv = some r) (hret : r.ret = rv)
    (c0 : Nat) (hc0 : (vwp eA).1 + (vwp cE).1 + 4 ≤ c0) (n0 : Nat)
    (hn0 : P.length + 2 * cl.length + (vwp eA).2 + (vwp cE).2 + 6 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch cE (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + slot) ty eA)) Sk)) Sk) Sk) REST)
        (gS P cl) vv = some r2 ∧ r2.ret = rv ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧
        r2.need ≤ max n0 r.need ∧ r2.wk ≤ r.wk := by
  subst hx0
  exact seq_sbranch2_r (rv := rv) mv fu P cl vv slot hslot ty cE eA C v v' c hc hv hcc hct hcv hconv REST r hrest hret c0 hc0 n0 hn0

theorem seq_assign_r {rv : Option Int} (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (slot : Nat) (hslot : slot < cl.length)
    (ty : Ty) (eA : NExpr) (v v' : Int) (c : Cell)
    (hv : vdenM mv vv (penvN mv.nv (gS P cl)) eA = some v) (hcc : cl[slot]? = some c) (hct : c.type = ty)
    (hcv : ty.valid c.value = true) (hconv : ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (cl.set slot ⟨ty, v'⟩)) vv = some r) (hret : r.ret = rv) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (.assign (mv.nv + slot) ty eA)) REST) (gS P cl) vv = some r2 ∧
      r2.ret = rv ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ (vwp eA).1 + 1 + r.cost ∧
      r2.need ≤ max (P.length + 2 * cl.length + (vwp eA).2 + 4) r.need ∧ r2.wk ≤ r.wk := by
  have as1 := gSM_assign mv P cl vv slot hslot ty eA v v' hv c hcc hct hcv hconv
  have a1 := (pexecM_prim mv fu (.assign (mv.nv + slot) ty eA) (gS P cl) vv).trans as1
  have a2 := seqM_some a1 rfl hrest
  refine ⟨_, a2, hret, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp [gS_size]; omega
  · simp

theorem seq_decl_r {rv : Option Int} (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (ty : Ty) (e : NExpr) (v v' : Int)
    (hv : vdenM mv vv (penvN mv.nv (gS P cl)) e = some v) (hc : ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (cl ++ [⟨ty, v'⟩])) vv = some r) (hret : r.ret = rv) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (.declare ty true e)) REST) (gS P cl) vv = some r2 ∧ r2.ret = rv ∧
      r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ (vwp e).1 + 1 + r.cost ∧
      r2.need ≤ max (P.length + 2 * cl.length + (vwp e).2 + 4) r.need ∧ r2.wk ≤ r.wk := by
  have a1 := (pexecM_prim mv fu (.declare ty true e) (gS P cl) vv).trans (gSM_decl mv P cl vv ty e v v' hv hc)
  have a2 := seqM_some a1 rfl hrest
  refine ⟨_, a2, hret, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp

theorem seq_write_r {rv : Option Int} (mv : MV) (fu : Nat) (ps : PS) (vv : Nat → List Int) (v : Nat) (hv : v < mv.nv) (ty : Ty) (hty : mv.ty v = ty) (iE vE : NExpr)
    (x : Int) (p : Nat) (hx : vdenM mv vv (penvN mv.nv ps) vE = some x) (hp : vdenM mv vv (penvN mv.nv ps) iE = some (p : Int))
    (hlt : p < (vv v).length) (hval : ty.valid x = true) (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST ps (upd vv v ((vv v).set p x)) = some r) (hret : r.ret = rv)
    (c0 : Nat) (hc0 : (vwp vE).1 + (vwp iE).1 + 3 ≤ c0) (n0 : Nat)
    (hn0 : ps.mem.length + ps.bs.length + iE.nodes + vE.nodes + (vwp vE).2 + (vwp iE).2 + 5 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (.write (.local v) ty iE vE)) REST) ps vv = some r2 ∧
      r2.ret = rv ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧ r2.need ≤ max n0 r.need ∧ r2.wk ≤ 1 + r.wk := by
  subst hty
  have w := pstmtM_write_ok mv ps vv v hv iE vE x p hx hp hlt hval
  have a1 := (pexecM_prim mv fu (.write (.local v) (mv.ty v) iE vE) ps vv).trans w
  have a2 := seqM_some a1 rfl (by simpa using hrest)
  refine ⟨_, a2, hret, rfl, rfl, ?_, ?_, ?_⟩
  · simp; omega
  · simp; omega
  · simp


open Proofs.BellmanFordExec (pexecM_branch_true pexecM_branch_false)

end Proofs.BeatsExec
