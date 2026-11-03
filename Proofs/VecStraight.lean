import Proofs.VecStmt

namespace Proofs.VecStraight
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.StraightLine Proofs.VecExpr Proofs.VecStmt Proofs.Mod61Body
open Proofs.CppState (Cell)

def ScalarV : Command → Bool
  | .primitive (.declare _ _ e) => true
  | .primitive (.assign _ _ e) => true
  | .primitive (.ret e) => true
  | .primitive (.check e) => true
  | .primitive .skip => true
  | .sequence a b => ScalarV a && ScalarV b
  | .scope body => ScalarV body
  | .branch c y n => ScalarV y && ScalarV n
  | .whileLoop c b => ScalarV b
  | _ => false

def pstmtV (vc : VCtx) : NStmt → PS → Option PR
  | .declare ty w e, ps => do
      let v ← vden vc (penv1 ps) e
      let v' ← ty.convert v
      some ⟨⟨ps.mem ++ [⟨ty,v'⟩],ps.bs ++ [⟨ps.mem.length,w⟩]⟩,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+4⟩
  | .assign (slot+1) ty e, ps => do
      let v ← vden vc (penv1 ps) e
      let b ← ps.bs[slot]?
      let c ← ps.mem[b.address]?
      if c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true then do
        let v' ← ty.convert v
        some ⟨⟨ps.mem.set b.address ⟨ty,v'⟩,ps.bs⟩,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2⟩
      else none
  | .ret e, ps => do
      let v ← vden vc (penv1 ps) e
      some ⟨ps,some v,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2⟩
  | .check e, ps => do
      let v ← vden vc (penv1 ps) e
      if v ≠ 0 then some ⟨ps,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2⟩ else none
  | .skip, ps => some ⟨ps,none,0,ps.mem.length+ps.bs.length⟩
  | _, _ => none

def pexecV (vc : VCtx) : Nat → Command → PS → Option PR
  | _, .primitive st, ps => pstmtV vc st ps
  | fu, .sequence a b, ps => do
      let r ← pexecV vc fu a ps
      match r.ret with
      | some _ => some r
      | none => do
          let r2 ← pexecV vc fu b r.ps
          some ⟨r2.ps,r2.ret,r.cost+r2.cost,max r.need r2.need⟩
  | fu, .scope body, ps => do
      let r ← pexecV vc fu body ps
      some ⟨⟨r.ps.mem.take ps.mem.length,r.ps.bs.take ps.bs.length⟩,r.ret,r.cost+1,r.need⟩
  | fu, .branch c y n, ps => do
      let v ← vden vc (penv1 ps) c
      if v = 0 then do
        let r ← pexecV vc fu n ps
        some ⟨r.ps,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need⟩
      else do
        let r ← pexecV vc fu y ps
        some ⟨r.ps,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need⟩
  | 0, .whileLoop _ _, _ => none
  | fu+1, .whileLoop c b, ps => do
      let v ← vden vc (penv1 ps) c
      if v = 0 then some ⟨ps,none,(vwp c).1+1,ps.mem.length+ps.bs.length+(vwp c).2+2⟩
      else do
        let r ← pexecV vc (fu+1) b ps
        match r.ret with
        | some _ => none
        | none => do
            let r2 ← pexecV vc fu (.whileLoop c b) r.ps
            some ⟨r2.ps,r2.ret,(vwp c).1+1+r.cost+r2.cost,
              max (ps.mem.length+ps.bs.length+(vwp c).2+2) (max r.need r2.need)⟩
  | _, _, _ => none
termination_by fu c => (fu, c)



theorem pexecV_ext (vc : VCtx) : ∀ (c : Command), ScalarV c = true → ∀ (fu : Nat) (ps : PS) (r : PR), pexecV vc fu c ps = some r → Ext ps r.ps := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps r hr
    cases st with
    | declare ty w e =>
      simp only [pexecV,pstmtV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ty.convert v with
        | none => simp [h2] at hr
        | some v' =>
          simp only [h2] at hr
          cases hr
          refine ⟨by simp,?_,by simp,?_⟩
          · simp [List.take_left']
          · simp [List.take_left']
    | assign slot0 ty e =>
      rcases slot0 with _ | slot
      · simp [pexecV,pstmtV] at hr
      simp only [pexecV,pstmtV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ps.bs[slot]? with
        | none => simp [h2] at hr
        | some b =>
          simp only [h2] at hr
          cases h3 : ps.mem[b.address]? with
          | none => simp [h3] at hr
          | some c =>
            simp only [h3] at hr
            by_cases ok : c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
            · simp only [ok,and_self,if_true] at hr
              cases h4 : ty.convert v with
              | none => simp [h4] at hr
              | some v' =>
                simp only [h4] at hr
                cases hr
                refine ⟨Nat.le_refl _,List.take_length,by simp,?_⟩
                have hl : (ps.mem.set b.address ⟨ty,v'⟩).take ps.mem.length = ps.mem.set b.address ⟨ty,v'⟩ :=
                  List.take_of_length_le (by simp)
                show ((ps.mem.set b.address ⟨ty,v'⟩).take ps.mem.length).map Cell.type = ps.mem.map Cell.type
                rw [hl]
                exact map_type_set_gen ps.mem b.address c ty v' h3 ok.1
            · simp [ok] at hr
    | ret e =>
      simp only [pexecV,pstmtV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) e with
      | none => simp [h1] at hr
      | some v => simp only [h1] at hr; cases hr; exact Ext.refl _
    | check e =>
      simp only [pexecV,pstmtV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases nz : v ≠ 0
        · simp [nz] at hr; cases hr; exact Ext.refl _
        · simp [nz] at hr
    | skip => simp only [pexecV,pstmtV] at hr; cases hr; exact Ext.refl _
    | _ => simp [pexecV,pstmtV] at hr
  | sequence a b iha ihb =>
    intro hs fu ps r hr
    simp only [ScalarV,Bool.and_eq_true] at hs
    simp only [pexecV,Bind.bind,Option.bind] at hr
    cases h1 : pexecV vc fu a ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v => simp only [hret] at hr; rw [← Option.some.inj hr]; exact iha hs.1 fu ps r1 h1
      | none =>
        simp only [hret] at hr
        cases h2 : pexecV vc fu b r1.ps with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          exact (iha hs.1 fu ps r1 h1).trans (ihb hs.2 fu r1.ps r2 h2)
  | scope body ih =>
    intro hs fu ps r hr
    simp only [ScalarV,Bool.and_eq_true] at hs
    simp only [pexecV,Bind.bind,Option.bind] at hr
    cases h1 : pexecV vc fu body ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      obtain ⟨l1,t1,m1,y1⟩ := ih hs fu ps r1 h1
      refine ⟨by simp; omega,?_,by simp; omega,?_⟩
      · simp [List.take_take,t1]
      · simp [List.take_take,y1]
  | branch c y n ihy ihn =>
    intro hs fu ps r hr
    simp only [ScalarV,Bool.and_eq_true] at hs
    simp only [pexecV,Bind.bind,Option.bind] at hr
    cases h1 : vden vc (penv1 ps) c with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexecV vc fu n ps with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; exact ihn hs.2 fu ps r1 h2
      · simp only [z,if_false] at hr
        cases h2 : pexecV vc fu y ps with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; exact ihy hs.1 fu ps r1 h2
  | whileLoop cnd b ih =>
    intro hs fu
    simp only [ScalarV,Bool.and_eq_true] at hs
    induction fu with
    | zero => intro ps r hr; simp [pexecV] at hr
    | succ fu ihf =>
      intro ps r hr
      simp only [pexecV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) cnd with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases z : v = 0
        · simp only [z,if_true] at hr; cases hr; exact Ext.refl _
        · simp only [z,if_false] at hr
          cases h2 : pexecV vc (fu+1) b ps with
          | none => simp [h2] at hr
          | some r1 =>
            simp only [h2] at hr
            cases hret : r1.ret with
            | some _ => simp [hret] at hr
            | none =>
              simp only [hret] at hr
              cases h3 : pexecV vc fu (.whileLoop cnd b) r1.ps with
              | none => simp [h3] at hr
              | some r2 =>
                simp only [h3] at hr
                cases hr
                exact (ih hs (fu+1) ps r1 h2).trans (ihf r1.ps r2 h3)
  | _ => intro hs; simp [ScalarV] at hs




theorem sl1_succ (n : Nat) : sl1 (n+1) = sl1 n ++ [.scalar n] := by simp [sl1, ssl_succ]

theorem sl1_get (n k : Nat) (h : k < n) : (sl1 n)[k+1]? = some (.scalar k) := by simp [sl1, ssl, h]

theorem vwp_pos (e : NExpr) : 1 ≤ (vwp e).2 := by
  cases e with
  | size el ct => cases ct <;> simp [vwp, NExpr.nodes]
  | read ty ct index => cases ct <;> simp [vwp, NExpr.nodes] <;> omega
  | _ =>
    simp [vwp, NExpr.nodes] <;> try omega
    all_goals split <;> simp [NExpr.nodes] <;> omega

theorem _root_.Proofs.VecExpr.FV.of_eq {c : VCtx} {fr fr' : Frame} (fv : FV c fr) (h : fr' = fr) : FV c fr' := by rw [h]; exact fv

theorem _root_.Proofs.VecExpr.FV.fresh {c : VCtx} {fr : Frame} {scope : Nat} (fv : FV c fr) (hsc : c.sc ≤ scope) :
    ∀ owner, fr.state.forest.context owner ≠ some (scope+1) := by
  intro owner h
  have := fv.strict owner _ h
  omega

theorem _root_.Proofs.VecExpr.FV.noop {c : VCtx} {fr fr' : Frame} (fv : FV c fr) (same : SameObjects fr.state fr'.state)
    (rw : fr'.rootWritable = fr.rootWritable) (work : fr'.state.storage.work = fr.state.storage.work)
    (hb : fr'.bindings = fr.bindings) : FV c fr' := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [same.wellFormed]; exact fv.valid
  · rw [rw,same.1]; exact fv.lengths
  · rw [same.liveSpace]; exact fv.live
  · rw [work]; exact fv.work
  · intro owner k h
    rw [same.1] at h
    exact fv.strict owner k h
  · rw [same.2.1]; exact fv.count
  · rw [hb]; exact fv.bindings
  · rw [same.1]; exact fv.vtag
  · rw [same.lookup]; exact fv.vfound
  · rw [rw]; exact fv.flagR

abbrev QpostV (vc : VCtx) (r : PR) (B sc : Nat) (SPB TPB W : Nat) (step : NStep) : Prop :=
  step.returned = r.ret.map Ret.scalar ∧ step.breaking = false ∧
  QS step.state [] B sc r.ps.mem r.ps.bs (sl1 r.ps.bs.length) ∧ FV vc step.state.frame ∧
  Cq SPB TPB (W+r.cost) step.state

theorem live_psV {S : NState} {B sc : Nat} {ps : PS} (qs : QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length)) :
    liveS S = ps.mem.length-B+ps.bs.length := by
  rw [qs.live_eq]; simp


theorem soundV_prim (vc : VCtx) (st : NStmt) (hs : ScalarV (.primitive st) = true) (ps : PS) (r : PR)
    (hr : pstmtV vc st ps = some r) {B sc SPB TPB W : Nat} (S : NState)
    (qs : QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length)) (fv : FV vc S.frame) (cq : Cq SPB TPB W S)
    (hB : B ≤ ps.mem.length) (hneed : r.need ≤ SPB+B) :
    RunsTo (.primitive st) S (QpostV vc r B sc SPB TPB W) := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have live := live_psV qs
  cases st with
  | declare ty w e =>
    simp only [pstmtV,Bind.bind,Option.bind] at hr
    cases h1 : vden vc (penv1 ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases h2 : ty.convert v with
      | none => simp [h2] at hr
      | some v' =>
        simp only [h2] at hr
        cases hr
        obtain ⟨t0,ev⟩ := ev_vden vc e S ps v qs fv h1
        have good := Ev.good ev
        obtain ⟨t,run,fr,qs',cq'⟩ := decl_stepG S t0 e ty w v v' _ _ qs cq (by simp at hneed; omega) ev.1 good
          (vwp_pos e) h2
        apply RunsTo.primitive run
        refine ⟨rfl,rfl,qs'.of_eq (by simp) (by simp) ?_,fv.of_eq fr,cq'⟩
        simp [sl1_succ]
  | assign slot0 ty e =>
    rcases slot0 with _ | slot
    · simp [pstmtV] at hr
    simp only [pstmtV,Bind.bind,Option.bind] at hr
    cases h1 : vden vc (penv1 ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases h2 : ps.bs[slot]? with
      | none => simp [h2] at hr
      | some b =>
        simp only [h2] at hr
        cases h3 : ps.mem[b.address]? with
        | none => simp [h3] at hr
        | some c =>
          simp only [h3] at hr
          by_cases ok : c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
          · simp only [ok,and_self,if_true] at hr
            cases h4 : ty.convert v with
            | none => simp [h4] at hr
            | some v' =>
              simp only [h4] at hr
              cases hr
              have lt : slot < ps.bs.length := (List.getElem?_eq_some_iff.mp h2).1
              obtain ⟨t0,ev⟩ := ev_vden vc e S ps v qs fv h1
              have good := Ev.good ev
              obtain ⟨t,run,fr,qs',cq'⟩ := assign_stepG S t0 e (slot+1) slot ty v v' _ _ b c qs cq (by simp at hneed; omega)
                ev.1 good h4 (by simp [qs.slots,sl1_get _ _ lt]) h2 (by simpa using h3) ok.1 ok.2.1 ok.2.2
                (cells' := ps.mem.set b.address ⟨ty,v'⟩) (by simp)
              apply RunsTo.primitive run
              exact ⟨rfl,rfl,qs',fv.of_eq fr,cq'⟩
          · simp [ok] at hr
  | ret e =>
    simp only [pstmtV,Bind.bind,Option.bind] at hr
    cases h1 : vden vc (penv1 ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases hr
      obtain ⟨u,ev⟩ := ev_vden vc e S ps v qs fv h1
      have good := Ev.good ev
      have self := release_self good.1.1
      have run : (NStmt.ret e).run S = some ⟨u.charge 1 0,some (.scalar v),false⟩ := by
        simp [NStmt.run,ev.1,self]
      have cqU : Cq SPB TPB (W+(vwp e).1) u := cq.good good (by simp at hneed; omega)
      have cqC : Cq SPB TPB (W+(vwp e).1+1) (u.charge 1 0) :=
        cqU.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
      apply RunsTo.primitive run
      exact ⟨rfl,rfl,qs.core (good.1.trans (core_charge u 1 0)),fv.of_eq (by simpa using good.1.1),cqC⟩
  | check e =>
    simp only [pstmtV,Bind.bind,Option.bind] at hr
    cases h1 : vden vc (penv1 ps) e with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases nz : v ≠ 0
      · simp only [nz,ne_eq,not_false_eq_true,if_true] at hr
        cases hr
        obtain ⟨t0,ev⟩ := ev_vden vc e S ps v qs fv h1
        obtain ⟨t,run,good⟩ := check_good_g e S t0 v _ _ ev.1 (Ev.good ev) nz
        apply RunsTo.primitive run
        refine ⟨rfl,rfl,qs.core good.1,fv.of_eq good.1.1,?_⟩
        exact cq.good good (by simp at hneed; omega)
      · simp [nz] at hr
  | skip =>
    simp only [pstmtV] at hr
    cases hr
    apply RunsTo.skip
    exact ⟨rfl,rfl,qs,fv,cq.mono (by omega)⟩
  | _ => simp [ScalarV] at hs


theorem pexecV_need (vc : VCtx) : ∀ (c : Command), ScalarV c = true → ∀ (fu : Nat) (ps : PS) (r : PR), pexecV vc fu c ps = some r →
    r.ps.mem.length+r.ps.bs.length ≤ r.need := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps r hr
    cases st with
    | declare ty w e =>
      simp only [pexecV,pstmtV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ty.convert v with
        | none => simp [h2] at hr
        | some v' => simp only [h2] at hr; cases hr; simp; omega
    | assign slot0 ty e =>
      rcases slot0 with _ | slot
      · simp [pexecV,pstmtV] at hr
      simp only [pexecV,pstmtV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ps.bs[slot]? with
        | none => simp [h2] at hr
        | some b =>
          simp only [h2] at hr
          cases h3 : ps.mem[b.address]? with
          | none => simp [h3] at hr
          | some c =>
            simp only [h3] at hr
            by_cases ok : c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
            · simp only [ok,and_self,if_true] at hr
              cases h4 : ty.convert v with
              | none => simp [h4] at hr
              | some v' => simp only [h4] at hr; cases hr; simp; omega
            · simp [ok] at hr
    | ret e =>
      simp only [pexecV,pstmtV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) e with
      | none => simp [h1] at hr
      | some v => simp only [h1] at hr; cases hr; simp; omega
    | check e =>
      simp only [pexecV,pstmtV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) e with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases nz : v ≠ 0
        · simp [nz] at hr; cases hr; simp; omega
        · simp [nz] at hr
    | skip => simp only [pexecV,pstmtV] at hr; cases hr; simp
    | _ => simp [pexecV,pstmtV] at hr
  | sequence a b iha ihb =>
    intro hs fu ps r hr
    simp only [ScalarV,Bool.and_eq_true] at hs
    simp only [pexecV,Bind.bind,Option.bind] at hr
    cases h1 : pexecV vc fu a ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v => simp only [hret] at hr; rw [← Option.some.inj hr]; exact iha hs.1 fu ps r1 h1
      | none =>
        simp only [hret] at hr
        cases h2 : pexecV vc fu b r1.ps with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          have := ihb hs.2 fu r1.ps r2 h2
          simp; omega
  | scope body ih =>
    intro hs fu ps r hr
    simp only [ScalarV,Bool.and_eq_true] at hs
    simp only [pexecV,Bind.bind,Option.bind] at hr
    cases h1 : pexecV vc fu body ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      have := ih hs fu ps r1 h1
      simp; omega
  | branch c y n ihy ihn =>
    intro hs fu ps r hr
    simp only [ScalarV,Bool.and_eq_true] at hs
    simp only [pexecV,Bind.bind,Option.bind] at hr
    cases h1 : vden vc (penv1 ps) c with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexecV vc fu n ps with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; have := ihn hs.2 fu ps r1 h2; simp; omega
      · simp only [z,if_false] at hr
        cases h2 : pexecV vc fu y ps with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; have := ihy hs.1 fu ps r1 h2; simp; omega
  | whileLoop cnd b ih =>
    intro hs fu
    simp only [ScalarV,Bool.and_eq_true] at hs
    induction fu with
    | zero => intro ps r hr; simp [pexecV] at hr
    | succ fu ihf =>
      intro ps r hr
      simp only [pexecV,Bind.bind,Option.bind] at hr
      cases h1 : vden vc (penv1 ps) cnd with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases z : v = 0
        · simp only [z,if_true] at hr; cases hr; simp; omega
        · simp only [z,if_false] at hr
          cases h2 : pexecV vc (fu+1) b ps with
          | none => simp [h2] at hr
          | some r1 =>
            simp only [h2] at hr
            cases hret : r1.ret with
            | some _ => simp [hret] at hr
            | none =>
              simp only [hret] at hr
              cases h3 : pexecV vc fu (.whileLoop cnd b) r1.ps with
              | none => simp [h3] at hr
              | some r2 =>
                simp only [h3] at hr
                cases hr
                have := ihf r1.ps r2 h3
                simp; omega
  | _ => intro hs; simp [ScalarV] at hs



theorem soundV (vc : VCtx) : ∀ (c : Command), ScalarV c = true → ∀ (fu : Nat) (ps : PS) (r : PR), pexecV vc fu c ps = some r →
    ∀ {B sc SPB TPB W : Nat} (S : NState), QS S [] B sc ps.mem ps.bs (sl1 ps.bs.length) →
      FV vc S.frame → Cq SPB TPB W S → B ≤ ps.mem.length → ps.mem.length+ps.bs.length ≤ SPB+B →
      r.need ≤ SPB+B → vc.sc ≤ sc → vc.L0 ≤ TPB →
      RunsTo c S (QpostV vc r B sc SPB TPB W) := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps r hr B sc SPB TPB W S qs fv cq hB hlive hneed hsc hL
    exact soundV_prim vc st hs ps r (by simpa [pexecV] using hr) S qs fv cq hB hneed
  | sequence a b iha ihb =>
    intro hs fu ps r hr B sc SPB TPB W S qs fv cq hB hlive hneed hsc hL
    simp only [ScalarV,Bool.and_eq_true] at hs
    simp only [pexecV,Bind.bind,Option.bind] at hr
    cases h1 : pexecV vc fu a ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v =>
        simp only [hret] at hr
        have e := Option.some.inj hr
        rw [← e] at hneed ⊢
        apply RunsTo.sequence
        refine (iha hs.1 fu ps r1 h1 S qs fv cq hB hlive hneed hsc hL).mono ?_
        intro step post
        left
        exact ⟨Or.inl (by rw [post.1,hret]; rfl),post⟩
      | none =>
        simp only [hret] at hr
        cases h2 : pexecV vc fu b r1.ps with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          have ext := pexecV_ext vc a hs.1 fu ps r1 h1
          have nd := pexecV_need vc a hs.1 fu ps r1 h1
          apply RunsTo.sequence
          refine (iha hs.1 fu ps r1 h1 S qs fv cq hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro step ⟨ret,brk,qs1,fv1,cq1⟩
          right
          refine ⟨by simpa [hret] using ret,brk,?_⟩
          have := ihb hs.2 fu r1.ps r2 h2 step.state qs1 fv1 cq1 (Nat.le_trans hB ext.2.2.1)
            (by simp at hneed; omega) (by simp at hneed; omega) hsc hL
          refine this.mono ?_
          intro st2 ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
  | scope body ih =>
    intro hs fu ps r hr B sc SPB TPB W S qs fv cq hB hlive hneed hsc hL
    simp only [ScalarV,Bool.and_eq_true] at hs
    simp only [pexecV,Bind.bind,Option.bind] at hr
    cases h1 : pexecV vc fu body ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      have ext := pexecV_ext vc body hs fu ps r1 h1
      obtain ⟨l1,t1,m1,y1⟩ := ext
      have eS : (fx SPB TPB).SPB = SPB := rfl
      have eT : (fx SPB TPB).TPB = TPB := rfl
      apply RunsTo.scope
      have qs' : QS (scopeUp S) [] B (sc+1) ps.mem ps.bs (sl1 ps.bs.length) := qs.enter
      refine (ih hs fu ps r1 h1 (scopeUp S) qs' fv cq.enter hB hlive (by simp at hneed; omega) (by omega) hL).mono ?_
      intro inner ⟨ret,brk,qsI,fvI,cqI⟩
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
      have leaveEq := leave_scalar S inner.state inner.returned notVec fits types fvI.valid
        (by rw [hscope]; exact fvI.fresh (by omega))
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
      · refine fvI.noop (by rw [left_state]; exact noopRetired_same _) (by rw [left_rootWritable]) ?_ ?_
        · rw [left_state]; rfl
        · rw [left_frameBindings,fvI.bindings,fv.bindings]; rfl
      · have lengthTake : (inner.state.scalars.memory.take S.scalars.memory.length).length =
            S.scalars.memory.length := by
          rw [takeEq,qs.memory]; simp; omega
        have hl : inner.state.frame.state.liveSpace-inner.state.frame.state.storage.baseSpace ≤ TPB := by
          rw [fvI.live]; omega
        have := Cb.left cq cqI lengthTake (by rw [live_psV qs]; omega) hl
        exact this
  | branch cnd y n ihy ihn =>
    intro hs fu ps r hr B sc SPB TPB W S qs fv cq hB hlive hneed hsc hL
    simp only [ScalarV,Bool.and_eq_true] at hs
    simp only [pexecV,Bind.bind,Option.bind] at hr
    have eS : (fx SPB TPB).SPB = SPB := rfl
    cases h1 : vden vc (penv1 ps) cnd with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      obtain ⟨u,ev⟩ := ev_vden vc cnd S ps v qs fv h1
      have good := Ev.good ev
      have hu := ev.1
      have self := release_self good.1.1
      have qsU : QS (u.charge 1 0) [] B sc ps.mem ps.bs (sl1 ps.bs.length) :=
        qs.core (good.1.trans (core_charge u 1 0))
      have fvU : FV vc (u.charge 1 0).frame := fv.of_eq (by simpa using good.1.1)
      have live := live_psV qs
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexecV vc fu n ps with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [z,if_pos rfl,self]
          refine (ihn hs.2 fu ps r1 h2 (u.charge 1 0) qsU fvU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
      · simp only [z,if_false] at hr
        cases h2 : pexecV vc fu y ps with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [if_neg z,self]
          refine (ihy hs.1 fu ps r1 h2 (u.charge 1 0) qsU fvU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
  | whileLoop cnd b ih =>
    intro hs fu ps r hr B sc SPB TPB W S qs fv cq hB hlive hneed hsc hL
    simp only [ScalarV] at hs
    have eS : (fx SPB TPB).SPB = SPB := rfl
    refine RunsTo.whileGhost (fun g t => ∃ (ps1 : PS) (r1 : PR) (k : Nat), pexecV vc g (.whileLoop cnd b) ps1 = some r1 ∧
        r.ps = r1.ps ∧ r.ret = r1.ret ∧ r.cost = k + r1.cost ∧ r1.need ≤ r.need ∧
        QS t [] B sc ps1.mem ps1.bs (sl1 ps1.bs.length) ∧ FV vc t.frame ∧ Cq SPB TPB (W+k) t ∧
        B ≤ ps1.mem.length ∧ ps1.mem.length+ps1.bs.length ≤ SPB+B) _ ?_ fu fu S (Nat.le_refl _)
      ⟨ps,r,0,hr,rfl,rfl,by omega,Nat.le_refl _,qs,fv,cq,hB,hlive⟩
    intro g t ⟨ps1,r1,k,hr1,hrps,hrret,hrcost,hrneed,qs1,fv1,cq1,hB1,hsz⟩
    cases g with
    | zero => simp [pexecV] at hr1
    | succ g' =>
      simp only [pexecV,Bind.bind,Option.bind] at hr1
      cases h1 : vden vc (penv1 ps1) cnd with
      | none => simp [h1] at hr1
      | some v =>
        simp only [h1] at hr1
        obtain ⟨u,ev⟩ := ev_vden vc cnd t ps1 v qs1 fv1 h1
        have good := Ev.good ev
        have hu := ev.1
        have self := release_self good.1.1
        have qsU : QS (u.charge 1 0) [] B sc ps1.mem ps1.bs (sl1 ps1.bs.length) :=
          qs1.core (good.1.trans (core_charge u 1 0))
        have fvU : FV vc (u.charge 1 0).frame := fv1.of_eq (by simpa using good.1.1)
        have live := live_psV qs1
        refine ⟨u,v,hu,?_,?_⟩
        · intro z
          simp only [z,if_true] at hr1
          cases hr1
          rw [self]
          have cqC : Cq SPB TPB (W+k+(vwp cnd).1+1) (u.charge 1 0) := by
            have c1 := cq1.good good (by simp at hrneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hrneed; omega)
          refine ⟨by rw [hrret]; rfl,rfl,?_,fvU,?_⟩
          · rw [hrps]; exact qsU
          · rw [hrcost]; exact cqC.mono (by simp; omega)
        · intro z
          simp only [z,if_false] at hr1
          cases h2 : pexecV vc (g'+1) b ps1 with
          | none => simp [h2] at hr1
          | some rb =>
            simp only [h2] at hr1
            cases hret : rb.ret with
            | some _ => simp [hret] at hr1
            | none =>
              simp only [hret] at hr1
              cases h3 : pexecV vc g' (.whileLoop cnd b) rb.ps with
              | none => simp [h3] at hr1
              | some r2 =>
                simp only [h3] at hr1
                cases hr1
                have ext := pexecV_ext vc b hs (g'+1) ps1 rb h2
                have nd := pexecV_need vc b hs (g'+1) ps1 rb h2
                simp at hrneed hrps hrret hrcost
                have cqC : Cq SPB TPB (W+k+(vwp cnd).1+1) (u.charge 1 0) := by
                  have c1 := cq1.good good (by omega)
                  exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
                rw [self]
                refine (ih hs (g'+1) ps1 rb h2 (u.charge 1 0) qsU fvU cqC hB1 hsz (by omega) hsc hL).mono ?_
                intro inner ⟨ret,brk,qsI,fvI,cqI⟩
                refine ⟨by rw [ret,hret]; rfl,brk,g',Nat.lt_succ_self _,rb.ps,r2,k+(vwp cnd).1+1+rb.cost,h3,?_,?_,?_,?_,qsI,fvI,?_,?_,?_⟩
                · exact hrps
                · exact hrret
                · omega
                · omega
                · have : W+k+(vwp cnd).1+1+rb.cost = W+(k+(vwp cnd).1+1+rb.cost) := by omega
                  rw [this] at cqI; exact cqI
                · exact Nat.le_trans hB1 ext.2.2.1
                · omega
  | _ => intro hs; simp [ScalarV] at hs


end Proofs.VecStraight
