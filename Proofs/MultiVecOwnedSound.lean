import Proofs.MultiVec

namespace Proofs.MultiVec
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedFacts
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.FillWriteStmt Proofs.InvPermFrame
open Proofs.VecStraight Proofs.VecStmt Proofs.VecWrite Proofs.VecKitW
open Proofs.CppState (Cell)


-- A root owned by the current scope survives leaving a nested scope.
theorem FWM.fresh_owned {mv : MV} {vv : Nat → List Int} {bb : Nat → Buffer Value}
    {wk : Nat} {fr : Frame} (fw : FWM mv vv bb wk fr) {scope : Nat} (bound : mv.sc ≤ scope+1) :
    ∀ owner, fr.state.forest.context owner ≠ some (scope+1) := by
  intro owner found
  have := fw.strict owner _ found
  omega

theorem soundM_owned (mv : MV) (w : Nat → Bool) (hw : ∀ k, w k = true → mv.wV k = true ∧ mv.flag k = true) : ∀ (c : Command), WrM w c = true → ∀ (fu : Nat) (ps : PS) (vv : Nat → List Int) (r : PRM), pexecM mv fu c ps vv = some r →
    ∀ {B sc SPB TPB W wk : Nat} {bb : Nat → Buffer Value} (S : NState), QS S [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length) →
      FWM mv vv bb wk S.frame → Cq SPB TPB W S → B ≤ ps.mem.length → ps.mem.length+ps.bs.length ≤ SPB+B →
      r.need ≤ SPB+B → mv.sc ≤ sc+1 → mv.L0+1 ≤ TPB →
      RunsTo c S (QpostM mv r B sc SPB TPB W wk) := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    exact soundM_prim mv w hw st hs ps vv r (by simpa [pexecM] using hr) S qs fw cq hB hneed hL
  | sequence a b iha ihb =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : pexecM mv fu a ps vv with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v =>
        simp only [hret] at hr
        have e := Option.some.inj hr
        rw [← e] at hneed ⊢
        apply RunsTo.sequence
        refine (iha hs.1 fu ps vv r1 h1 S qs fw cq hB hlive hneed hsc hL).mono ?_
        intro step post
        left
        exact ⟨Or.inl (by rw [post.1,hret]; rfl),post⟩
      | none =>
        simp only [hret] at hr
        cases h2 : pexecM mv fu b r1.ps r1.vv with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          have ext := pexecM_ext mv w a hs.1 fu ps vv r1 h1
          have nd := pexecM_need mv w a hs.1 fu ps vv r1 h1
          apply RunsTo.sequence
          refine (iha hs.1 fu ps vv r1 h1 S qs fw cq hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro step ⟨ret,brk,qs1,⟨bb1,fw1⟩,cq1⟩
          right
          refine ⟨by simpa [hret] using ret,brk,?_⟩
          have := ihb hs.2 fu r1.ps r1.vv r2 h2 step.state qs1 fw1 cq1 (Nat.le_trans hB ext.2.2.1)
            (by simp at hneed; omega) (by simp at hneed; omega) hsc hL
          refine this.mono ?_
          intro st2 ⟨a1,a2,a3,⟨bf,a4⟩,a5⟩
          exact ⟨a1,a2,a3,⟨bf,a4.wk_eq (by simp; omega)⟩,a5.mono (by simp; omega)⟩
  | scope body ih =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    simp only [WrM] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    cases h1 : pexecM mv fu body ps vv with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      have ext := pexecM_ext mv w body hs fu ps vv r1 h1
      obtain ⟨l1,t1,m1,y1⟩ := ext
      have eS : (fx SPB TPB).SPB = SPB := rfl
      have eT : (fx SPB TPB).TPB = TPB := rfl
      apply RunsTo.scope
      have qs' : QS (scopeUp S) [] B (sc+1) ps.mem ps.bs (slN mv.nv ps.bs.length) := qs.enter
      refine (ih hs fu ps vv r1 h1 (scopeUp S) qs' fw cq.enter hB hlive (by simp at hneed; omega) (by omega) hL).mono ?_
      intro inner ⟨ret,brk,qsI,⟨bbI,fwI⟩,cqI⟩
      have hscope : S.scope = sc := qs.scope
      have fits : S.scalars.memory.length ≤ inner.state.scalars.memory.length := by
        rw [qsI.memory,qs.memory]; simpa using m1
      have takeEq : inner.state.scalars.memory.take S.scalars.memory.length = r1.ps.mem.take ps.mem.length := by
        rw [qsI.memory,qs.memory]; simp
      have types : (inner.state.scalars.memory.take S.scalars.memory.length).map Cell.type =
          S.scalars.memory.map Cell.type := by
        rw [takeEq,qs.memory]; simpa using y1
      have notVec : ∀ owner element, inner.returned ≠ some (.vector owner element) := by
        intro owner element h
        rw [ret] at h
        cases hv : r1.ret <;> simp [hv] at h
      have leaveEq := leave_scalar S inner.state inner.returned notVec fits types fwI.valid
        (by rw [hscope]; exact fwI.fresh_owned (by omega))
      refine ⟨S.left inner.state,leaveEq,ret,brk,?_,?_,?_⟩
      · refine ⟨?_,?_,?_,?_,?_⟩
        · rw [left_slots,qs.slots]
          have : (r1.ps.bs.take ps.bs.length) = ps.bs := t1
          simp only [this]
        · rw [left_memory,takeEq]; simp
        · rw [left_bindings,qs.bindings]
          have : (r1.ps.bs.take ps.bs.length) = ps.bs := t1
          simp only [this]
        · rw [left_baseMemory]; exact qs.base
        · rw [left_scope]; exact qs.scope
      · refine ⟨bbI, fwI.noop (by rw [left_state]; exact noopRetired_same _) (by rw [left_rootWritable]) ?_ ?_⟩
        · rw [left_state]; rfl
        · rw [left_frameBindings,fwI.bindings,fw.bindings]; exact List.take_length
      · have lengthTake : (inner.state.scalars.memory.take S.scalars.memory.length).length =
            S.scalars.memory.length := by
          rw [takeEq,qs.memory]; simp; omega
        have hl : inner.state.frame.state.liveSpace-inner.state.frame.state.storage.baseSpace ≤ TPB := by
          rw [fwI.live]; omega
        have := Cb.left cq cqI lengthTake (by rw [live_psN qs]; omega) hl
        exact this
  | branch cnd y n ihy ihn =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    simp only [WrM,Bool.and_eq_true] at hs
    simp only [pexecM,Bind.bind,Option.bind] at hr
    have eS : (fx SPB TPB).SPB = SPB := rfl
    cases h1 : vdenM mv vv (penvN mv.nv ps) cnd with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      obtain ⟨u,ev⟩ := ev_vdenM mv cnd S ps v qs rfl fw h1
      have good := Ev.good ev
      have hu := ev.1
      have self := release_self good.1.1
      have qsU : QS (u.charge 1 0) [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length) :=
        qs.core (good.1.trans (core_charge u 1 0))
      have fwU : FWM mv vv bb wk (u.charge 1 0).frame := fw.of_eq (by simpa using good.1.1)
      have live := live_psN qs
      by_cases z : v = 0
      · simp only [z,ite_true] at hr
        cases h2 : pexecM mv fu n ps vv with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [z,ite_eq_left rfl,self]
          refine (ihn hs.2 fu ps vv r1 h2 (u.charge 1 0) qsU fwU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
      · simp only [z,ite_false] at hr
        cases h2 : pexecM mv fu y ps vv with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [ite_eq_right z,self]
          refine (ihy hs.1 fu ps vv r1 h2 (u.charge 1 0) qsU fwU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
  | whileLoop cnd b ih =>
    intro hs fu ps vv r hr B sc SPB TPB W wk bb S qs fw cq hB hlive hneed hsc hL
    simp only [WrM] at hs
    have eS : (fx SPB TPB).SPB = SPB := rfl
    refine RunsTo.whileGhost (fun g t => ∃ (ps1 : PS) (vv1 : Nat → List Int) (r1 : PRM) (k j : Nat) (bb1 : Nat → Buffer Value),
        pexecM mv g (.whileLoop cnd b) ps1 vv1 = some r1 ∧
        r.ps = r1.ps ∧ r.vv = r1.vv ∧ r.ret = r1.ret ∧ r.cost = k + r1.cost ∧ r.wk = j + r1.wk ∧ r1.need ≤ r.need ∧
        QS t [] B sc ps1.mem ps1.bs (slN mv.nv ps1.bs.length) ∧ FWM mv vv1 bb1 (wk+j) t.frame ∧ Cq SPB TPB (W+k) t ∧
        B ≤ ps1.mem.length ∧ ps1.mem.length+ps1.bs.length ≤ SPB+B) _ ?_ fu fu S (Nat.le_refl _)
      ⟨ps,vv,r,0,0,bb,hr,rfl,rfl,rfl,by omega,by omega,Nat.le_refl _,qs,fw,cq,hB,hlive⟩
    intro g t ⟨ps1,vv1,r1,k,j,bb1,hr1,hrps,hrvec,hrret,hrcost,hrwk,hrneed,qs1,fw1,cq1,hB1,hsz⟩
    cases g with
    | zero => simp [pexecM] at hr1
    | succ g' =>
      simp only [pexecM,Bind.bind,Option.bind] at hr1
      cases h1 : vdenM mv vv1 (penvN mv.nv ps1) cnd with
      | none => simp [h1] at hr1
      | some v =>
        simp only [h1] at hr1
        obtain ⟨u,ev⟩ := ev_vdenM mv cnd t ps1 v qs1 rfl fw1 h1
        have good := Ev.good ev
        have hu := ev.1
        have self := release_self good.1.1
        have qsU : QS (u.charge 1 0) [] B sc ps1.mem ps1.bs (slN mv.nv ps1.bs.length) :=
          qs1.core (good.1.trans (core_charge u 1 0))
        have fwU : FWM mv vv1 bb1 (wk+j) (u.charge 1 0).frame := fw1.of_eq (by simpa using good.1.1)
        have live := live_psN qs1
        refine ⟨u,v,hu,?_,?_⟩
        · intro z
          simp only [z,ite_true] at hr1
          cases hr1
          rw [self]
          simp at hrneed hrps hrvec hrret hrcost hrwk
          have cqC : Cq SPB TPB (W+k+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq1.good good (by omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
          refine ⟨by rw [hrret]; rfl,rfl,?_,⟨bb1,?_⟩,?_⟩
          · rw [hrps]; exact qsU
          · rw [hrvec]
            exact fwU.wk_eq (by omega)
          · rw [hrcost]; exact cqC.mono (by omega)
        · intro z
          simp only [z,ite_false] at hr1
          cases h2 : pexecM mv (g'+1) b ps1 vv1 with
          | none => simp [h2] at hr1
          | some rb =>
            simp only [h2] at hr1
            cases hret : rb.ret with
            | some _ => simp [hret] at hr1
            | none =>
              simp only [hret] at hr1
              cases h3 : pexecM mv g' (.whileLoop cnd b) rb.ps rb.vv with
              | none => simp [h3] at hr1
              | some r2 =>
                simp only [h3] at hr1
                cases hr1
                have ext := pexecM_ext mv w b hs (g'+1) ps1 vv1 rb h2
                have nd := pexecM_need mv w b hs (g'+1) ps1 vv1 rb h2
                simp at hrneed hrps hrvec hrret hrcost hrwk
                have cqC : Cq SPB TPB (W+k+(vwp cnd).1+1) (u.charge 1 0) := by
                  have c1 := cq1.good good (by omega)
                  exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
                rw [self]
                refine (ih hs (g'+1) ps1 vv1 rb h2 (u.charge 1 0) qsU fwU cqC hB1 hsz (by omega) hsc hL).mono ?_
                intro inner ⟨ret,brk,qsI,⟨bbI,fwI⟩,cqI⟩
                refine ⟨by rw [ret,hret]; rfl,brk,g',Nat.lt_succ_self _,rb.ps,rb.vv,r2,k+(vwp cnd).1+1+rb.cost,j+rb.wk,bbI,h3,?_,?_,?_,?_,?_,?_,qsI,?_,?_,?_,?_⟩
                · exact hrps
                · exact hrvec
                · exact hrret
                · omega
                · omega
                · omega
                · exact fwI.wk_eq (by omega)
                · have : W+k+(vwp cnd).1+1+rb.cost = W+(k+(vwp cnd).1+1+rb.cost) := by omega
                  rw [this] at cqI; exact cqI
                · exact Nat.le_trans hB1 ext.2.2.1
                · omega
  | _ => intro hs; simp [WrM] at hs

end Proofs.MultiVec
