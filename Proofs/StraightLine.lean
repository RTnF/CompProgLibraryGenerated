import Proofs.QuotientSearch
import Proofs.Mod61Body

namespace Proofs.StraightLine
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.QuotientSearch Proofs.Mod61Body
open Proofs.CppState (Cell)

-- The scalar memory and its bindings, without frames, counters or ghost slots.
structure PS where
  mem : List Cell
  bs : List CppState.Binding

def penv (ps : PS) (slot : Nat) (ty : Ty) : Option Int := do
  let b ← ps.bs[slot]?
  let c ← ps.mem[b.address]?
  if c.type = ty ∧ ty.valid c.value = true then some c.value else none

structure PR where
  ps : PS
  ret : Option Int
  cost : Nat
  need : Nat

def Scalar : Command → Bool
  | .primitive (.declare _ _ e) => e.scalarOnly
  | .primitive (.assign _ _ e) => e.scalarOnly
  | .primitive (.ret e) => e.scalarOnly
  | .primitive (.check e) => e.scalarOnly
  | .primitive .skip => true
  | .sequence a b => Scalar a && Scalar b
  | .scope body => Scalar body
  | .branch c y n => c.scalarOnly && Scalar y && Scalar n
  | .whileLoop c b => c.scalarOnly && Scalar b
  | _ => false

def pstmt : NStmt → PS → Option PR
  | .declare ty w e, ps => do
      let v ← e.denote (penv ps)
      let v' ← ty.convert v
      some ⟨⟨ps.mem ++ [⟨ty,v'⟩],ps.bs ++ [⟨ps.mem.length,w⟩]⟩,none,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+4⟩
  | .assign slot ty e, ps => do
      let v ← e.denote (penv ps)
      let b ← ps.bs[slot]?
      let c ← ps.mem[b.address]?
      if c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true then do
        let v' ← ty.convert v
        some ⟨⟨ps.mem.set b.address ⟨ty,v'⟩,ps.bs⟩,none,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+2⟩
      else none
  | .ret e, ps => do
      let v ← e.denote (penv ps)
      some ⟨ps,some v,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+2⟩
  | .check e, ps => do
      let v ← e.denote (penv ps)
      if v ≠ 0 then some ⟨ps,none,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+2⟩ else none
  | .skip, ps => some ⟨ps,none,0,ps.mem.length+ps.bs.length⟩
  | _, _ => none

def pexec : Nat → Command → PS → Option PR
  | _, .primitive st, ps => pstmt st ps
  | fu, .sequence a b, ps => do
      let r ← pexec fu a ps
      match r.ret with
      | some _ => some r
      | none => do
          let r2 ← pexec fu b r.ps
          some ⟨r2.ps,r2.ret,r.cost+r2.cost,max r.need r2.need⟩
  | fu, .scope body, ps => do
      let r ← pexec fu body ps
      some ⟨⟨r.ps.mem.take ps.mem.length,r.ps.bs.take ps.bs.length⟩,r.ret,r.cost+1,r.need⟩
  | fu, .branch c y n, ps => do
      let v ← c.denote (penv ps)
      if v = 0 then do
        let r ← pexec fu n ps
        some ⟨r.ps,r.ret,r.cost+c.nodes+1,max (ps.mem.length+ps.bs.length+c.nodes+2) r.need⟩
      else do
        let r ← pexec fu y ps
        some ⟨r.ps,r.ret,r.cost+c.nodes+1,max (ps.mem.length+ps.bs.length+c.nodes+2) r.need⟩
  | 0, .whileLoop _ _, _ => none
  | fu+1, .whileLoop c b, ps => do
      let v ← c.denote (penv ps)
      if v = 0 then some ⟨ps,none,c.nodes+1,ps.mem.length+ps.bs.length+c.nodes+2⟩
      else do
        let r ← pexec (fu+1) b ps
        match r.ret with
        | some _ => none
        | none => do
            let r2 ← pexec fu (.whileLoop c b) r.ps
            some ⟨r2.ps,r2.ret,c.nodes+1+r.cost+r2.cost,
              max (ps.mem.length+ps.bs.length+c.nodes+2) (max r.need r2.need)⟩
  | _, _, _ => none
termination_by fu c => (fu, c)



-- Later states keep every earlier binding and the types of every earlier cell.
def Ext (ps ps' : PS) : Prop :=
  ps.bs.length ≤ ps'.bs.length ∧ ps'.bs.take ps.bs.length = ps.bs ∧ ps.mem.length ≤ ps'.mem.length ∧
    (ps'.mem.take ps.mem.length).map Cell.type = ps.mem.map Cell.type

theorem Ext.refl (ps : PS) : Ext ps ps := by
  refine ⟨Nat.le_refl _,List.take_length,Nat.le_refl _,?_⟩
  rw [List.take_length]

theorem Ext.trans {a b c : PS} (h1 : Ext a b) (h2 : Ext b c) : Ext a c := by
  obtain ⟨l1,t1,m1,y1⟩ := h1
  obtain ⟨l2,t2,m2,y2⟩ := h2
  refine ⟨Nat.le_trans l1 l2,?_,Nat.le_trans m1 m2,?_⟩
  · rw [← t1,← t2,List.take_take]
    simp [Nat.min_eq_left l1]
  · have : (c.mem.take a.mem.length) = (c.mem.take b.mem.length).take a.mem.length := by
      rw [List.take_take]; simp [Nat.min_eq_left m1]
    have e1 : (c.mem.take a.mem.length).map Cell.type =
        ((c.mem.take b.mem.length).map Cell.type).take a.mem.length := by rw [this,List.map_take]
    rw [e1,y2,← List.map_take,y1]


theorem map_type_set_gen (mem : List Cell) (a : Nat) (c : Cell) (ty : Ty) (v : Int) (h : mem[a]? = some c)
    (ht : c.type = ty) : (mem.set a ⟨ty,v⟩).map Cell.type = mem.map Cell.type := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k = a
  · subst hk
    have lt : k < mem.length := (List.getElem?_eq_some_iff.mp h).1
    have lt' : k < (mem.map Cell.type).length := by simpa using lt
    simp [List.getElem?_set_self lt',h,ht]
  · simp [List.getElem?_set_ne (Ne.symm hk)]

theorem pexec_ext : ∀ (c : Command), Scalar c = true → ∀ (fu : Nat) (ps : PS) (r : PR), pexec fu c ps = some r → Ext ps r.ps := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps r hr
    cases st with
    | declare ty w e =>
      simp only [pexec,pstmt,Bind.bind,Option.bind] at hr
      cases h1 : e.denote (penv ps) with
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
    | assign slot ty e =>
      simp only [pexec,pstmt,Bind.bind,Option.bind] at hr
      cases h1 : e.denote (penv ps) with
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
      simp only [pexec,pstmt,Bind.bind,Option.bind] at hr
      cases h1 : e.denote (penv ps) with
      | none => simp [h1] at hr
      | some v => simp only [h1] at hr; cases hr; exact Ext.refl _
    | check e =>
      simp only [pexec,pstmt,Bind.bind,Option.bind] at hr
      cases h1 : e.denote (penv ps) with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases nz : v ≠ 0
        · simp [nz] at hr; cases hr; exact Ext.refl _
        · simp [nz] at hr
    | skip => simp only [pexec,pstmt] at hr; cases hr; exact Ext.refl _
    | _ => simp [pexec,pstmt] at hr
  | sequence a b iha ihb =>
    intro hs fu ps r hr
    simp only [Scalar,Bool.and_eq_true] at hs
    simp only [pexec,Bind.bind,Option.bind] at hr
    cases h1 : pexec fu a ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v => simp only [hret] at hr; rw [← Option.some.inj hr]; exact iha hs.1 fu ps r1 h1
      | none =>
        simp only [hret] at hr
        cases h2 : pexec fu b r1.ps with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          exact (iha hs.1 fu ps r1 h1).trans (ihb hs.2 fu r1.ps r2 h2)
  | scope body ih =>
    intro hs fu ps r hr
    simp only [Scalar] at hs
    simp only [pexec,Bind.bind,Option.bind] at hr
    cases h1 : pexec fu body ps with
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
    simp only [Scalar,Bool.and_eq_true] at hs
    simp only [pexec,Bind.bind,Option.bind] at hr
    cases h1 : c.denote (penv ps) with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexec fu n ps with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; exact ihn hs.2 fu ps r1 h2
      · simp only [z,if_false] at hr
        cases h2 : pexec fu y ps with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; exact ihy hs.1.2 fu ps r1 h2
  | whileLoop cnd b ih =>
    intro hs fu
    simp only [Scalar,Bool.and_eq_true] at hs
    induction fu with
    | zero => intro ps r hr; simp [pexec] at hr
    | succ fu ihf =>
      intro ps r hr
      simp only [pexec,Bind.bind,Option.bind] at hr
      cases h1 : cnd.denote (penv ps) with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases z : v = 0
        · simp only [z,if_true] at hr; cases hr; exact Ext.refl _
        · simp only [z,if_false] at hr
          cases h2 : pexec (fu+1) b ps with
          | none => simp [h2] at hr
          | some r1 =>
            simp only [h2] at hr
            cases hret : r1.ret with
            | some _ => simp [hret] at hr
            | none =>
              simp only [hret] at hr
              cases h3 : pexec fu (.whileLoop cnd b) r1.ps with
              | none => simp [h3] at hr
              | some r2 =>
                simp only [h3] at hr
                cases hr
                exact (ih hs.2 (fu+1) ps r1 h2).trans (ihf r1.ps r2 h3)
  | _ => intro hs; simp [Scalar] at hs


theorem env_of_qs {S : NState} {B sc : Nat} {ps : PS} (qs : QS S [] B sc ps.mem ps.bs (ssl ps.bs.length)) :
    envOf S = penv ps := by
  funext slot ty
  unfold envOf NState.scalarCell NState.scalarSlot penv
  rw [qs.slots,qs.bindings,qs.memory]
  by_cases h : slot < ps.bs.length
  · have e : (ssl ps.bs.length)[slot]? = some (.scalar slot) := by simp [ssl,h]
    rw [e]
    cases hb : ps.bs[slot]? with
    | none => simp at hb; omega
    | some b =>
      cases hm : ps.mem[b.address]? with
      | none => simp [hb,hm]
      | some c =>
        by_cases ok : c.type = ty ∧ ty.valid c.value = true
        · simp [hb,hm,ok]
        · simp [hb,hm,ok]
  · have e : (ssl ps.bs.length)[slot]? = none := by simp [ssl]; omega
    have e2 : ps.bs[slot]? = none := by simp; omega
    simp [e,e2]

abbrev Qpost (r : PR) (B sc L0 T0 N scq SPB TPB W : Nat) (step : NStep) : Prop :=
  step.returned = r.ret.map Ret.scalar ∧ step.breaking = false ∧
  QS step.state [] B sc r.ps.mem r.ps.bs (ssl r.ps.bs.length) ∧ FA step.state.frame L0 T0 scq N ∧
  Cq SPB TPB (W+r.cost) step.state

theorem live_ps {S : NState} {B sc : Nat} {ps : PS} (qs : QS S [] B sc ps.mem ps.bs (ssl ps.bs.length)) :
    liveS S = ps.mem.length-B+ps.bs.length := by
  rw [qs.live_eq]; simp


theorem qs_extend {S : NState} {B sc : Nat} {ps ps' : PS} (qs : QS S [] B sc ps'.mem ps'.bs (ssl ps'.bs.length)) :
    QS S [] B sc ps'.mem ps'.bs (ssl ps'.bs.length) := qs

theorem sound_prim (st : NStmt) (hs : Scalar (.primitive st) = true) (ps : PS) (r : PR)
    (hr : pstmt st ps = some r) {B sc L0 T0 N scq SPB TPB W : Nat} (S : NState)
    (qs : QS S [] B sc ps.mem ps.bs (ssl ps.bs.length)) (fa : FA S.frame L0 T0 scq N) (cq : Cq SPB TPB W S)
    (hB : B ≤ ps.mem.length) (hneed : r.need ≤ SPB+B) :
    RunsTo (.primitive st) S (Qpost r B sc L0 T0 N scq SPB TPB W) := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have env := env_of_qs qs
  have live := live_ps qs
  cases st with
  | declare ty w e =>
    simp only [Scalar] at hs
    simp only [pstmt,Bind.bind,Option.bind] at hr
    cases h1 : e.denote (penv ps) with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases h2 : ty.convert v with
      | none => simp [h2] at hr
      | some v' =>
        simp only [h2] at hr
        cases hr
        obtain ⟨t,run,fr,qs',cq'⟩ := decl_step S e ty w v v' qs cq (by simp at hneed; omega) hs
          (by rw [env]; exact h1) h2
        apply RunsTo.primitive run
        refine ⟨rfl,rfl,qs'.of_eq (by simp) (by simp) ?_,fa.of_eq fr,cq'⟩
        simp [ssl_succ]
  | assign slot ty e =>
    simp only [Scalar] at hs
    simp only [pstmt,Bind.bind,Option.bind] at hr
    cases h1 : e.denote (penv ps) with
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
              obtain ⟨t,run,fr,qs',cq'⟩ := assign_step S e slot slot ty v v' b c qs cq (by simp at hneed; omega) hs
                (by rw [env]; exact h1) h4 (by simp [qs.slots,ssl,lt]) h2 (by simpa using h3) ok.1 ok.2.1 ok.2.2
                (cells' := ps.mem.set b.address ⟨ty,v'⟩) (by simp)
              apply RunsTo.primitive run
              exact ⟨rfl,rfl,qs',fa.of_eq fr,cq'⟩
          · simp [ok] at hr
  | ret e =>
    simp only [Scalar] at hs
    simp only [pstmt,Bind.bind,Option.bind] at hr
    cases h1 : e.denote (penv ps) with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      cases hr
      obtain ⟨u,hu,good⟩ := scalar_eval e S v hs (by rw [env]; exact h1)
      have self := release_self good.1.1
      have run : (NStmt.ret e).run S = some ⟨u.charge 1 0,some (.scalar v),false⟩ := by
        simp [NStmt.run,hu,self]
      have cqU : Cq SPB TPB (W+e.nodes) u := cq.good good (by simp at hneed; omega)
      have cqC : Cq SPB TPB (W+e.nodes+1) (u.charge 1 0) :=
        cqU.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
      apply RunsTo.primitive run
      exact ⟨rfl,rfl,qs.core (good.1.trans (core_charge u 1 0)),fa.of_eq (by simpa using good.1.1),cqC⟩
  | check e =>
    simp only [Scalar] at hs
    simp only [pstmt,Bind.bind,Option.bind] at hr
    cases h1 : e.denote (penv ps) with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases nz : v ≠ 0
      · simp only [nz,ne_eq,not_false_eq_true,if_true] at hr
        cases hr
        obtain ⟨t,run,good⟩ := check_good e S v hs (by rw [env]; exact h1) nz
        apply RunsTo.primitive run
        refine ⟨rfl,rfl,qs.core good.1,fa.of_eq good.1.1,?_⟩
        exact cq.good good (by simp at hneed; omega)
      · simp [nz] at hr
  | skip =>
    simp only [pstmt] at hr
    cases hr
    apply RunsTo.skip
    exact ⟨rfl,rfl,qs,fa,cq.mono (by omega)⟩
  | _ => simp [Scalar] at hs


theorem pexec_need : ∀ (c : Command), Scalar c = true → ∀ (fu : Nat) (ps : PS) (r : PR), pexec fu c ps = some r →
    r.ps.mem.length+r.ps.bs.length ≤ r.need := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps r hr
    cases st with
    | declare ty w e =>
      simp only [pexec,pstmt,Bind.bind,Option.bind] at hr
      cases h1 : e.denote (penv ps) with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        cases h2 : ty.convert v with
        | none => simp [h2] at hr
        | some v' => simp only [h2] at hr; cases hr; simp; omega
    | assign slot ty e =>
      simp only [pexec,pstmt,Bind.bind,Option.bind] at hr
      cases h1 : e.denote (penv ps) with
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
      simp only [pexec,pstmt,Bind.bind,Option.bind] at hr
      cases h1 : e.denote (penv ps) with
      | none => simp [h1] at hr
      | some v => simp only [h1] at hr; cases hr; simp; omega
    | check e =>
      simp only [pexec,pstmt,Bind.bind,Option.bind] at hr
      cases h1 : e.denote (penv ps) with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases nz : v ≠ 0
        · simp [nz] at hr; cases hr; simp; omega
        · simp [nz] at hr
    | skip => simp only [pexec,pstmt] at hr; cases hr; simp
    | _ => simp [pexec,pstmt] at hr
  | sequence a b iha ihb =>
    intro hs fu ps r hr
    simp only [Scalar,Bool.and_eq_true] at hs
    simp only [pexec,Bind.bind,Option.bind] at hr
    cases h1 : pexec fu a ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v => simp only [hret] at hr; rw [← Option.some.inj hr]; exact iha hs.1 fu ps r1 h1
      | none =>
        simp only [hret] at hr
        cases h2 : pexec fu b r1.ps with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          have := ihb hs.2 fu r1.ps r2 h2
          simp; omega
  | scope body ih =>
    intro hs fu ps r hr
    simp only [Scalar] at hs
    simp only [pexec,Bind.bind,Option.bind] at hr
    cases h1 : pexec fu body ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      have := ih hs fu ps r1 h1
      simp; omega
  | branch c y n ihy ihn =>
    intro hs fu ps r hr
    simp only [Scalar,Bool.and_eq_true] at hs
    simp only [pexec,Bind.bind,Option.bind] at hr
    cases h1 : c.denote (penv ps) with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexec fu n ps with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; have := ihn hs.2 fu ps r1 h2; simp; omega
      · simp only [z,if_false] at hr
        cases h2 : pexec fu y ps with
        | none => simp [h2] at hr
        | some r1 => simp only [h2] at hr; cases hr; have := ihy hs.1.2 fu ps r1 h2; simp; omega
  | whileLoop cnd b ih =>
    intro hs fu
    simp only [Scalar,Bool.and_eq_true] at hs
    induction fu with
    | zero => intro ps r hr; simp [pexec] at hr
    | succ fu ihf =>
      intro ps r hr
      simp only [pexec,Bind.bind,Option.bind] at hr
      cases h1 : cnd.denote (penv ps) with
      | none => simp [h1] at hr
      | some v =>
        simp only [h1] at hr
        by_cases z : v = 0
        · simp only [z,if_true] at hr; cases hr; simp; omega
        · simp only [z,if_false] at hr
          cases h2 : pexec (fu+1) b ps with
          | none => simp [h2] at hr
          | some r1 =>
            simp only [h2] at hr
            cases hret : r1.ret with
            | some _ => simp [hret] at hr
            | none =>
              simp only [hret] at hr
              cases h3 : pexec fu (.whileLoop cnd b) r1.ps with
              | none => simp [h3] at hr
              | some r2 =>
                simp only [h3] at hr
                cases hr
                have := ihf r1.ps r2 h3
                simp; omega
  | _ => intro hs; simp [Scalar] at hs


theorem sound : ∀ (c : Command), Scalar c = true → ∀ (fu : Nat) (ps : PS) (r : PR), pexec fu c ps = some r →
    ∀ {B sc L0 T0 N scq SPB TPB W : Nat} (S : NState), QS S [] B sc ps.mem ps.bs (ssl ps.bs.length) →
      FA S.frame L0 T0 scq N → Cq SPB TPB W S → B ≤ ps.mem.length → ps.mem.length+ps.bs.length ≤ SPB+B →
      r.need ≤ SPB+B → scq ≤ sc → L0 ≤ TPB →
      RunsTo c S (Qpost r B sc L0 T0 N scq SPB TPB W) := by
  intro c
  induction c with
  | primitive st =>
    intro hs fu ps r hr B sc L0 T0 N scq SPB TPB W S qs fa cq hB hlive hneed hsc hL
    exact sound_prim st hs ps r (by simpa [pexec] using hr) S qs fa cq hB hneed
  | sequence a b iha ihb =>
    intro hs fu ps r hr B sc L0 T0 N scq SPB TPB W S qs fa cq hB hlive hneed hsc hL
    simp only [Scalar,Bool.and_eq_true] at hs
    simp only [pexec,Bind.bind,Option.bind] at hr
    cases h1 : pexec fu a ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hret : r1.ret with
      | some v =>
        simp only [hret] at hr
        have e := Option.some.inj hr
        rw [← e] at hneed ⊢
        apply RunsTo.sequence
        refine (iha hs.1 fu ps r1 h1 S qs fa cq hB hlive hneed hsc hL).mono ?_
        intro step post
        left
        exact ⟨Or.inl (by rw [post.1,hret]; rfl),post⟩
      | none =>
        simp only [hret] at hr
        cases h2 : pexec fu b r1.ps with
        | none => simp [h2] at hr
        | some r2 =>
          simp only [h2] at hr
          cases hr
          have ext := pexec_ext a hs.1 fu ps r1 h1
          have nd := pexec_need a hs.1 fu ps r1 h1
          apply RunsTo.sequence
          refine (iha hs.1 fu ps r1 h1 S qs fa cq hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro step ⟨ret,brk,qs1,fa1,cq1⟩
          right
          refine ⟨by simpa [hret] using ret,brk,?_⟩
          have := ihb hs.2 fu r1.ps r2 h2 step.state qs1 fa1 cq1 (Nat.le_trans hB ext.2.2.1)
            (by simp at hneed; omega) (by simp at hneed; omega) hsc hL
          refine this.mono ?_
          intro st2 ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
  | scope body ih =>
    intro hs fu ps r hr B sc L0 T0 N scq SPB TPB W S qs fa cq hB hlive hneed hsc hL
    simp only [Scalar] at hs
    simp only [pexec,Bind.bind,Option.bind] at hr
    cases h1 : pexec fu body ps with
    | none => simp [h1] at hr
    | some r1 =>
      simp only [h1] at hr
      cases hr
      have ext := pexec_ext body hs fu ps r1 h1
      obtain ⟨l1,t1,m1,y1⟩ := ext
      have eS : (fx SPB TPB).SPB = SPB := rfl
      have eT : (fx SPB TPB).TPB = TPB := rfl
      apply RunsTo.scope
      have qs' : QS (scopeUp S) [] B (sc+1) ps.mem ps.bs (ssl ps.bs.length) := qs.enter
      refine (ih hs fu ps r1 h1 (scopeUp S) qs' fa cq.enter hB hlive (by simp at hneed; omega) (by omega) hL).mono ?_
      intro inner ⟨ret,brk,qsI,faI,cqI⟩
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
      have leaveEq := leave_scalar S inner.state inner.returned notVec fits types faI.valid
        (by rw [hscope]; exact faI.fresh (by omega))
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
      · refine faI.noop (by rw [left_state]; exact noopRetired_same _) (by rw [left_rootWritable]) ?_ ?_
        · rw [left_state]; rfl
        · rw [left_frameBindings,faI.bindings]; exact List.take_nil
      · have lengthTake : (inner.state.scalars.memory.take S.scalars.memory.length).length =
            S.scalars.memory.length := by
          rw [takeEq,qs.memory]; simp; omega
        have hl : inner.state.frame.state.liveSpace-inner.state.frame.state.storage.baseSpace ≤ TPB := by
          rw [faI.live]; omega
        have := Cb.left cq cqI lengthTake (by rw [live_ps qs]; omega) hl
        exact this
  | branch cnd y n ihy ihn =>
    intro hs fu ps r hr B sc L0 T0 N scq SPB TPB W S qs fa cq hB hlive hneed hsc hL
    simp only [Scalar,Bool.and_eq_true] at hs
    simp only [pexec,Bind.bind,Option.bind] at hr
    have eS : (fx SPB TPB).SPB = SPB := rfl
    have env := env_of_qs qs
    cases h1 : cnd.denote (penv ps) with
    | none => simp [h1] at hr
    | some v =>
      simp only [h1] at hr
      obtain ⟨u,hu,good⟩ := scalar_eval cnd S v hs.1.1 (by rw [env]; exact h1)
      have self := release_self good.1.1
      have qsU : QS (u.charge 1 0) [] B sc ps.mem ps.bs (ssl ps.bs.length) :=
        qs.core (good.1.trans (core_charge u 1 0))
      have faU : FA (u.charge 1 0).frame L0 T0 scq N := fa.of_eq (by simpa using good.1.1)
      have live := live_ps qs
      by_cases z : v = 0
      · simp only [z,if_true] at hr
        cases h2 : pexec fu n ps with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+cnd.nodes+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [z,if_pos rfl,self]
          refine (ihn hs.2 fu ps r1 h2 (u.charge 1 0) qsU faU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
      · simp only [z,if_false] at hr
        cases h2 : pexec fu y ps with
        | none => simp [h2] at hr
        | some r1 =>
          simp only [h2] at hr
          cases hr
          have cqC : Cq SPB TPB (W+cnd.nodes+1) (u.charge 1 0) := by
            have c1 := cq.good good (by simp at hneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hneed; omega)
          apply RunsTo.branch (next := u) (value := v) hu
          rw [if_neg z,self]
          refine (ihy hs.1.2 fu ps r1 h2 (u.charge 1 0) qsU faU cqC hB hlive (by simp at hneed; omega) hsc hL).mono ?_
          intro st ⟨a1,a2,a3,a4,a5⟩
          exact ⟨a1,a2,a3,a4,a5.mono (by simp; omega)⟩
  | whileLoop cnd b ih =>
    intro hs fu ps r hr B sc L0 T0 N scq SPB TPB W S qs fa cq hB hlive hneed hsc hL
    simp only [Scalar,Bool.and_eq_true] at hs
    have eS : (fx SPB TPB).SPB = SPB := rfl
    refine RunsTo.whileGhost (fun g t => ∃ (ps1 : PS) (r1 : PR) (k : Nat), pexec g (.whileLoop cnd b) ps1 = some r1 ∧
        r.ps = r1.ps ∧ r.ret = r1.ret ∧ r.cost = k + r1.cost ∧ r1.need ≤ r.need ∧
        QS t [] B sc ps1.mem ps1.bs (ssl ps1.bs.length) ∧ FA t.frame L0 T0 scq N ∧ Cq SPB TPB (W+k) t ∧
        B ≤ ps1.mem.length ∧ ps1.mem.length+ps1.bs.length ≤ SPB+B) _ ?_ fu fu S (Nat.le_refl _)
      ⟨ps,r,0,hr,rfl,rfl,by omega,Nat.le_refl _,qs,fa,cq,hB,hlive⟩
    intro g t ⟨ps1,r1,k,hr1,hrps,hrret,hrcost,hrneed,qs1,fa1,cq1,hB1,hsz⟩
    cases g with
    | zero => simp [pexec] at hr1
    | succ g' =>
      simp only [pexec,Bind.bind,Option.bind] at hr1
      cases h1 : cnd.denote (penv ps1) with
      | none => simp [h1] at hr1
      | some v =>
        simp only [h1] at hr1
        have env := env_of_qs qs1
        obtain ⟨u,hu,good⟩ := scalar_eval cnd t v hs.1 (by rw [env]; exact h1)
        have self := release_self good.1.1
        have qsU : QS (u.charge 1 0) [] B sc ps1.mem ps1.bs (ssl ps1.bs.length) :=
          qs1.core (good.1.trans (core_charge u 1 0))
        have faU : FA (u.charge 1 0).frame L0 T0 scq N := fa1.of_eq (by simpa using good.1.1)
        have live := live_ps qs1
        refine ⟨u,v,hu,?_,?_⟩
        · intro z
          simp only [z,if_true] at hr1
          cases hr1
          rw [self]
          have cqC : Cq SPB TPB (W+k+cnd.nodes+1) (u.charge 1 0) := by
            have c1 := cq1.good good (by simp at hrneed; omega)
            exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; simp at hrneed; omega)
          refine ⟨by rw [hrret]; rfl,rfl,?_,faU,?_⟩
          · rw [hrps]; exact qsU
          · rw [hrcost]; exact cqC.mono (by simp; omega)
        · intro z
          simp only [z,if_false] at hr1
          cases h2 : pexec (g'+1) b ps1 with
          | none => simp [h2] at hr1
          | some rb =>
            simp only [h2] at hr1
            cases hret : rb.ret with
            | some _ => simp [hret] at hr1
            | none =>
              simp only [hret] at hr1
              cases h3 : pexec g' (.whileLoop cnd b) rb.ps with
              | none => simp [h3] at hr1
              | some r2 =>
                simp only [h3] at hr1
                cases hr1
                have ext := pexec_ext b hs.2 (g'+1) ps1 rb h2
                have nd := pexec_need b hs.2 (g'+1) ps1 rb h2
                simp at hrneed hrps hrret hrcost
                have cqC : Cq SPB TPB (W+k+cnd.nodes+1) (u.charge 1 0) := by
                  have c1 := cq1.good good (by omega)
                  exact c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
                rw [self]
                refine (ih hs.2 (g'+1) ps1 rb h2 (u.charge 1 0) qsU faU cqC hB1 hsz (by omega) hsc hL).mono ?_
                intro inner ⟨ret,brk,qsI,faI,cqI⟩
                refine ⟨by rw [ret,hret]; rfl,brk,g',Nat.lt_succ_self _,rb.ps,r2,k+cnd.nodes+1+rb.cost,h3,?_,?_,?_,?_,qsI,faI,?_,?_,?_⟩
                · exact hrps
                · exact hrret
                · omega
                · omega
                · have : W+k+cnd.nodes+1+rb.cost = W+(k+cnd.nodes+1+rb.cost) := by omega
                  rw [this] at cqI; exact cqI
                · exact Nat.le_trans hB1 ext.2.2.1
                · omega
  | _ => intro hs; simp [Scalar] at hs

end Proofs.StraightLine
