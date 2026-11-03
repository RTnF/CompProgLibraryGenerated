import Proofs.BeatsExecAdd
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec (pexecM_branch_true pexecM_branch_false)

/-- `T x = e;` followed by the rest. -/
theorem seq_decl (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (ty : Ty) (e : NExpr) (v v' : Int)
    (hv : vdenM mv vv (penvN mv.nv (gS P cl)) e = some v) (hc : ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (cl ++ [⟨ty, v'⟩])) vv = some r) (hret : r.ret = none) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (.declare ty true e)) REST) (gS P cl) vv = some r2 ∧ r2.ret = none ∧
      r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ (vwp e).1 + 1 + r.cost ∧
      r2.need ≤ max (P.length + 2 * cl.length + (vwp e).2 + 4) r.need ∧ r2.wk ≤ r.wk := by
  have a1 := (pexecM_prim mv fu (.declare ty true e) (gS P cl) vv).trans (gSM_decl mv P cl vv ty e v v' hv hc)
  have a2 := seqM_some a1 rfl hrest
  refine ⟨_, a2, hret, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp

theorem gS_take_len (P cl cl' : List Cell) (h : cl'.length = cl.length) :
    (⟨(gS P cl').mem.take (gS P cl).mem.length, (gS P cl').bs.take (gS P cl).bs.length⟩ : PS) = gS P cl' := by
  have h1 : (gS P cl).mem.length = (gS P cl').mem.length := by simp [gS_mem_len, h]
  have h2 : (gS P cl).bs.length = (gS P cl').bs.length := by simp [gS_bs_len, h]
  rw [h1, h2]; simp

/-- `if (C) { local = e; }` followed by the rest (the condition is a scalar expression). -/
theorem seq_sbranch (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (slot : Nat) (hslot : slot < cl.length)
    (ty : Ty) (cE eA : NExpr) (C : Prop) [Decidable C] (v v' : Int) (c : Cell)
    (hc : vdenM mv vv (penvN mv.nv (gS P cl)) cE = some (if C then 1 else 0))
    (hv : C → vdenM mv vv (penvN mv.nv (gS P cl)) eA = some v) (hcc : cl[slot]? = some c) (hct : c.type = ty)
    (hcv : ty.valid c.value = true) (hconv : C → ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (if C then cl.set slot ⟨ty, v'⟩ else cl)) vv = some r) (hret : r.ret = none)
    (c0 : Nat) (hc0 : (vwp eA).1 + (vwp cE).1 + 4 ≤ c0) (n0 : Nat)
    (hn0 : P.length + 2 * cl.length + (vwp eA).2 + (vwp cE).2 + 6 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch cE (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + slot) ty eA)) Sk)) Sk) Sk) REST)
        (gS P cl) vv = some r2 ∧ r2.ret = none ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧
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


theorem set_self_cell (cl : List Cell) (slot : Nat) (c : Cell) (h : cl[slot]? = some c) : cl.set slot c = cl := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    by_cases hi : i = slot
    · subst hi
      rw [List.getElem_set_self]
      have := List.getElem?_eq_getElem h2
      rw [h] at this
      exact (Option.some.inj this)
    · rw [List.getElem_set_ne (Ne.symm hi)]

/-- Like `seq_sbranch` but the new state is expressed uniformly: the cell becomes `if C then v' else old`. -/
theorem seq_sbranch2 (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (slot : Nat) (hslot : slot < cl.length)
    (ty : Ty) (cE eA : NExpr) (C : Prop) [Decidable C] (v v' : Int) (c : Cell)
    (hc : vdenM mv vv (penvN mv.nv (gS P cl)) cE = some (if C then 1 else 0))
    (hv : C → vdenM mv vv (penvN mv.nv (gS P cl)) eA = some v) (hcc : cl[slot]? = some c) (hct : c.type = ty)
    (hcv : ty.valid c.value = true) (hconv : C → ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (cl.set slot ⟨ty, if C then v' else c.value⟩)) vv = some r) (hret : r.ret = none)
    (c0 : Nat) (hc0 : (vwp eA).1 + (vwp cE).1 + 4 ≤ c0) (n0 : Nat)
    (hn0 : P.length + 2 * cl.length + (vwp eA).2 + (vwp cE).2 + 6 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch cE (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + slot) ty eA)) Sk)) Sk) Sk) REST)
        (gS P cl) vv = some r2 ∧ r2.ret = none ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧
        r2.need ≤ max n0 r.need ∧ r2.wk ≤ r.wk := by
  apply seq_sbranch mv fu P cl vv slot hslot ty cE eA C v v' c hc hv hcc hct hcv hconv REST r _ hret c0 hc0 n0 hn0
  by_cases hC : C
  · rw [if_pos hC]; rw [if_pos hC] at hrest; exact hrest
  · rw [if_neg hC]; rw [if_neg hC] at hrest
    have : (⟨ty, c.value⟩ : Cell) = c := by cases c; simp at hct ⊢; exact hct.symm
    rw [this, set_self_cell cl slot c hcc] at hrest
    exact hrest


/-- `if (C) { a = eA; } else { b = eB; }` followed by the rest, with the two cells updated uniformly. -/
theorem seq_sbranch_ite (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (sa sb : Nat) (hab : sa ≠ sb)
    (hsa : sa < cl.length) (hsb : sb < cl.length) (ty : Ty) (cE eA eB : NExpr) (C : Prop) [Decidable C]
    (va va' vb vb' : Int) (ca cb : Cell)
    (hc : vdenM mv vv (penvN mv.nv (gS P cl)) cE = some (if C then 1 else 0))
    (hva : C → vdenM mv vv (penvN mv.nv (gS P cl)) eA = some va) (hvb : ¬ C → vdenM mv vv (penvN mv.nv (gS P cl)) eB = some vb)
    (hca : cl[sa]? = some ca) (hcb : cl[sb]? = some cb) (hta : ca.type = ty) (htb : cb.type = ty)
    (hva_ : ty.valid ca.value = true) (hvb_ : ty.valid cb.value = true)
    (hconva : C → ty.convert va = some va') (hconvb : ¬ C → ty.convert vb = some vb') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P ((cl.set sa ⟨ty, if C then va' else ca.value⟩).set sb ⟨ty, if C then cb.value else vb'⟩)) vv = some r)
    (hret : r.ret = none) (c0 : Nat) (hc0 : (vwp eA).1 + (vwp eB).1 + (vwp cE).1 + 6 ≤ c0) (n0 : Nat)
    (hn0 : P.length + 2 * cl.length + (vwp eA).2 + (vwp eB).2 + (vwp cE).2 + 8 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch cE (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sa) ty eA)) Sk)) Sk)
        (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sb) ty eB)) Sk)) Sk)) REST)
        (gS P cl) vv = some r2 ∧ r2.ret = none ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧
        r2.need ≤ max n0 r.need ∧ r2.wk ≤ r.wk := by
  have cat : (⟨ty, ca.value⟩ : Cell) = ca := by cases ca; simp at hta ⊢; exact hta.symm
  have cbt : (⟨ty, cb.value⟩ : Cell) = cb := by cases cb; simp at htb ⊢; exact htb.symm
  by_cases hC : C
  · rw [if_pos hC] at hc
    rw [if_pos hC, if_pos hC] at hrest
    have e : (cl.set sa ⟨ty, va'⟩).set sb ⟨ty, cb.value⟩ = cl.set sa ⟨ty, va'⟩ := by
      apply set_self_cell
      rw [List.getElem?_set_ne hab, hcb, cbt]
    rw [e] at hrest
    have as1 := gSM_assign mv P cl vv sa hsa ty eA va va' (hva hC) ca hca hta hva_ (hconva hC)
    have a1 := (pexecM_prim mv fu (.assign (mv.nv + sa) ty eA) (gS P cl) vv).trans as1
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (cl.set sa ⟨ty, va'⟩)) vv)
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    simp only [gS_take_len P cl (cl.set sa ⟨ty, va'⟩) (by simp)] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (cl.set sa ⟨ty, va'⟩)) vv)
    have b1 := pexecM_branch_true mv fu cE _ (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sb) ty eB)) Sk)) Sk)
      (gS P cl) vv 1 hc (by decide) _ a4
    have b2 := seqM_some b1 rfl hrest
    refine ⟨_, b2, hret, rfl, rfl, ?_, ?_, ?_⟩
    · simp; omega
    · simp [gS_size]; omega
    · simp
  · rw [if_neg hC] at hc
    rw [if_neg hC, if_neg hC] at hrest
    have e : (cl.set sa ⟨ty, ca.value⟩).set sb ⟨ty, vb'⟩ = cl.set sb ⟨ty, vb'⟩ := by
      rw [cat, set_self_cell cl sa ca hca]
    rw [e] at hrest
    have as1 := gSM_assign mv P cl vv sb hsb ty eB vb vb' (hvb hC) cb hcb htb hvb_ (hconvb hC)
    have a1 := (pexecM_prim mv fu (.assign (mv.nv + sb) ty eB) (gS P cl) vv).trans as1
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (cl.set sb ⟨ty, vb'⟩)) vv)
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    simp only [gS_take_len P cl (cl.set sb ⟨ty, vb'⟩) (by simp)] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (cl.set sb ⟨ty, vb'⟩)) vv)
    have b1 := pexecM_branch_false mv fu cE (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sa) ty eA)) Sk)) Sk) _
      (gS P cl) vv hc _ a4
    have b2 := seqM_some b1 rfl hrest
    refine ⟨_, b2, hret, rfl, rfl, ?_, ?_, ?_⟩
    · simp; omega
    · simp [gS_size]; omega
    · simp


/-- `if (C1) { a = e1; } else { if (C2) { b = e2; } }` followed by the rest, with the cells updated uniformly. -/
theorem seq_sbranch_elif (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (sa sb : Nat) (hab : sa ≠ sb)
    (hsa : sa < cl.length) (hsb : sb < cl.length) (ty : Ty) (c1E c2E eA eB : NExpr) (C1 C2 : Prop) [Decidable C1] [Decidable C2]
    (va vb : Int) (ca cb : Cell)
    (hc1 : vdenM mv vv (penvN mv.nv (gS P cl)) c1E = some (if C1 then 1 else 0))
    (hc2 : ¬ C1 → vdenM mv vv (penvN mv.nv (gS P cl)) c2E = some (if C2 then 1 else 0))
    (hva : C1 → vdenM mv vv (penvN mv.nv (gS P cl)) eA = some va)
    (hvb : ¬ C1 → C2 → vdenM mv vv (penvN mv.nv (gS P cl)) eB = some vb)
    (hca : cl[sa]? = some ca) (hcb : cl[sb]? = some cb) (hta : ca.type = ty) (htb : cb.type = ty)
    (hva_ : ty.valid ca.value = true) (hvb_ : ty.valid cb.value = true)
    (hconva : C1 → ty.convert va = some va) (hconvb : ¬ C1 → C2 → ty.convert vb = some vb) (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P ((cl.set sa ⟨ty, if C1 then va else ca.value⟩).set sb
      ⟨ty, if ¬ C1 ∧ C2 then vb else cb.value⟩)) vv = some r)
    (hret : r.ret = none) (c0 : Nat) (hc0 : (vwp eA).1 + (vwp eB).1 + (vwp c1E).1 + (vwp c2E).1 + 10 ≤ c0) (n0 : Nat)
    (hn0 : P.length + 2 * cl.length + (vwp eA).2 + (vwp eB).2 + (vwp c1E).2 + (vwp c2E).2 + 12 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch c1E (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sa) ty eA)) Sk)) Sk)
        (.sequence (.scope (.sequence (.branch c2E (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sb) ty eB)) Sk)) Sk) Sk) Sk)) Sk))
        REST) (gS P cl) vv = some r2 ∧ r2.ret = none ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧
        r2.need ≤ max n0 r.need ∧ r2.wk ≤ r.wk := by
  have cat : (⟨ty, ca.value⟩ : Cell) = ca := by cases ca; simp at hta ⊢; exact hta.symm
  have cbt : (⟨ty, cb.value⟩ : Cell) = cb := by cases cb; simp at htb ⊢; exact htb.symm
  by_cases h1 : C1
  · rw [if_pos h1] at hc1
    have e : (cl.set sa ⟨ty, va⟩).set sb ⟨ty, cb.value⟩ = cl.set sa ⟨ty, va⟩ := by
      apply set_self_cell
      rw [List.getElem?_set_ne hab, hcb, cbt]
    rw [if_pos h1] at hrest
    have hn : ¬ (¬ C1 ∧ C2) := fun h => h.1 h1
    rw [if_neg hn, e] at hrest
    have as1 := gSM_assign mv P cl vv sa hsa ty eA va va (hva h1) ca hca hta hva_ (hconva h1)
    have a1 := (pexecM_prim mv fu (.assign (mv.nv + sa) ty eA) (gS P cl) vv).trans as1
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (cl.set sa ⟨ty, va⟩)) vv)
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    simp only [gS_take_len P cl (cl.set sa ⟨ty, va⟩) (by simp)] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (cl.set sa ⟨ty, va⟩)) vv)
    have b1 := pexecM_branch_true mv fu c1E _ (.sequence (.scope (.sequence (.branch c2E (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sb) ty eB)) Sk)) Sk) Sk) Sk)) Sk)
      (gS P cl) vv 1 hc1 (by decide) _ a4
    have b2 := seqM_some b1 rfl hrest
    refine ⟨_, b2, hret, rfl, rfl, ?_, ?_, ?_⟩
    · simp; omega
    · simp [gS_size]; omega
    · simp
  · rw [if_neg h1] at hc1
    have hc2' := hc2 h1
    rw [if_neg h1] at hrest
    by_cases h2 : C2
    · rw [if_pos h2] at hc2'
      have hp : ¬ C1 ∧ C2 := ⟨h1, h2⟩
      rw [if_pos hp] at hrest
      have e : (cl.set sa ⟨ty, ca.value⟩).set sb ⟨ty, vb⟩ = cl.set sb ⟨ty, vb⟩ := by
        rw [cat, set_self_cell cl sa ca hca]
      rw [e] at hrest
      have as1 := gSM_assign mv P cl vv sb hsb ty eB vb vb (hvb h1 h2) cb hcb htb hvb_ (hconvb h1 h2)
      have a1 := (pexecM_prim mv fu (.assign (mv.nv + sb) ty eB) (gS P cl) vv).trans as1
      have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (cl.set sb ⟨ty, vb⟩)) vv)
      have a3 := pexecM_scope mv fu _ _ _ _ a2
      simp only [gS_take_len P cl (cl.set sb ⟨ty, vb⟩) (by simp)] at a3
      have a4 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (cl.set sb ⟨ty, vb⟩)) vv)
      have i1 := pexecM_branch_true mv fu c2E _ Sk (gS P cl) vv 1 hc2' (by decide) _ a4
      have i2 := seqM_some i1 rfl (pexecM_skip mv fu (gS P (cl.set sb ⟨ty, vb⟩)) vv)
      have i3 := pexecM_scope mv fu _ _ _ _ i2
      simp only [gS_take_len P cl (cl.set sb ⟨ty, vb⟩) (by simp)] at i3
      have i4 := seqM_some i3 rfl (pexecM_skip mv fu (gS P (cl.set sb ⟨ty, vb⟩)) vv)
      have b1 := pexecM_branch_false mv fu c1E (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sa) ty eA)) Sk)) Sk) _
        (gS P cl) vv hc1 _ i4
      have b2 := seqM_some b1 rfl hrest
      refine ⟨_, b2, hret, rfl, rfl, ?_, ?_, ?_⟩
      · simp; omega
      · simp [gS_size]; omega
      · simp
    · rw [if_neg h2] at hc2'
      have hn : ¬ (¬ C1 ∧ C2) := fun h => h2 h.2
      rw [if_neg hn] at hrest
      have e : (cl.set sa ⟨ty, ca.value⟩).set sb ⟨ty, cb.value⟩ = cl := by
        rw [cat, cbt, set_self_cell cl sa ca hca, set_self_cell cl sb cb hcb]
      rw [e] at hrest
      have i1 := pexecM_branch_false mv fu c2E (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sb) ty eB)) Sk)) Sk) Sk
        (gS P cl) vv hc2' _ (pexecM_skip mv fu (gS P cl) vv)
      have i2 := seqM_some i1 rfl (pexecM_skip mv fu (gS P cl) vv)
      have i3 := pexecM_scope mv fu _ _ _ _ i2
      simp only [gS_take_len P cl cl rfl] at i3
      have i4 := seqM_some i3 rfl (pexecM_skip mv fu (gS P cl) vv)
      have b1 := pexecM_branch_false mv fu c1E (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + sa) ty eA)) Sk)) Sk) _
        (gS P cl) vv hc1 _ i4
      have b2 := seqM_some b1 rfl hrest
      refine ⟨_, b2, hret, rfl, rfl, ?_, ?_, ?_⟩
      · simp; omega
      · simp [gS_size]; omega
      · simp

end Proofs.BeatsExec
