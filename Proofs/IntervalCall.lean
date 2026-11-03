import Proofs.GroupCall
import Proofs.Generated.Interval

namespace Proofs.IntervalCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCall
open Proofs.GroupCall
open Proofs.CppState (Cell)

theorem prep_refs3 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (t2 : Ty) (t3 : Ty) (s1 : Nat) (s2 : Nat) (s3 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (b3 : CppState.Binding) (v1 : Int) (v2 : Int) (v3 : Int)
    (hp : params = [.scalar t1 true false,.scalar t2 true false,.scalar t3 true false])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (c3 : caller.scalarCell s3 t3 = some (b3,⟨t3,v3⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+7 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  obtain ⟨i3,_,_,m3,_,w3⟩ := scalarCell_facts c3
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have l3 : b3.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m3).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have c3' : ((caller.charge 1 1).charge 1 1).scalarCell s3 t3 = some (b3,⟨t3,v3⟩) := c3
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have h2 := pad t2 b2 v2 l2 m2
  have h3 := pad t3 b3 v3 l3 m3
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,c1,c2',c3']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,h3,w1,w2,w3]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  repeat first
    | exact Nat.le_max_left _ _
    | (apply Nat.le_trans (Nat.le_max_left _ _); skip)

set_option maxHeartbeats 8000000 in
theorem prep_refs6 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (t2 : Ty) (t3 : Ty) (t4 : Ty) (t5 : Ty) (t6 : Ty) (s1 : Nat) (s2 : Nat) (s3 : Nat) (s4 : Nat) (s5 : Nat) (s6 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (b3 : CppState.Binding) (b4 : CppState.Binding) (b5 : CppState.Binding) (b6 : CppState.Binding) (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) (v5 : Int) (v6 : Int)
    (hp : params = [.scalar t1 true false,.scalar t2 true false,.scalar t3 true false,.scalar t4 true false,.scalar t5 true false,.scalar t6 true false])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (c3 : caller.scalarCell s3 t3 = some (b3,⟨t3,v3⟩))
    (c4 : caller.scalarCell s4 t4 = some (b4,⟨t4,v4⟩))
    (c5 : caller.scalarCell s5 t5 = some (b5,⟨t5,v5⟩))
    (c6 : caller.scalarCell s6 t6 = some (b6,⟨t6,v6⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,.scalarReference s6] = some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3,.scalar 4,.scalar 5] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩,⟨b5.address,false⟩,⟨b6.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+13 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  obtain ⟨i3,_,_,m3,_,w3⟩ := scalarCell_facts c3
  obtain ⟨i4,_,_,m4,_,w4⟩ := scalarCell_facts c4
  obtain ⟨i5,_,_,m5,_,w5⟩ := scalarCell_facts c5
  obtain ⟨i6,_,_,m6,_,w6⟩ := scalarCell_facts c6
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have l3 : b3.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m3).1
  have l4 : b4.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m4).1
  have l5 : b5.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m5).1
  have l6 : b6.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m6).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have c3' : ((caller.charge 1 1).charge 1 1).scalarCell s3 t3 = some (b3,⟨t3,v3⟩) := c3
  have c4' : (((caller.charge 1 1).charge 1 1).charge 1 1).scalarCell s4 t4 = some (b4,⟨t4,v4⟩) := c4
  have c5' : ((((caller.charge 1 1).charge 1 1).charge 1 1).charge 1 1).scalarCell s5 t5 = some (b5,⟨t5,v5⟩) := c5
  have c6' : (((((caller.charge 1 1).charge 1 1).charge 1 1).charge 1 1).charge 1 1).scalarCell s6 t6 = some (b6,⟨t6,v6⟩) := c6
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have h2 := pad t2 b2 v2 l2 m2
  have h3 := pad t3 b3 v3 l3 m3
  have h4 := pad t4 b4 v4 l4 m4
  have h5 := pad t5 b5 v5 l5 m5
  have h6 := pad t6 b6 v6 l6 m6
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,c1,c2',c3',c4',c5',c6']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,h3,h4,h5,h6,w1,w2,w3,w4,w5,w6]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  repeat first
    | exact Nat.le_max_left _ _
    | (apply Nat.le_trans (Nat.le_max_left _ _); skip)


theorem penv_old (ps : PS) (k : Nat) (ty : Ty) (b : CppState.Binding) (v : Int) (hb : ps.bs[k]? = some b)
    (hm : ps.mem[b.address]? = some ⟨ty,v⟩) (hv : ty.valid v = true) : penv ps k ty = some v :=
  penv_ok ps k ty b ⟨ty,v⟩ hb hm rfl hv

theorem pstmt_check_ok (ps : PS) (e : NExpr) (v : Int) (hv : e.denote (penv ps) = some v) (hne : v ≠ 0) :
    pstmt (.check e) ps = some ⟨ps,none,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+2⟩ := by
  simp [pstmt, hv, hne]

theorem cmp_den (op : Binary) (i j : Nat) (env : Nat → Ty → Option Int) (x y : Int)
    (hi : env i s64 = some x) (hj : env j s64 = some y) (hx : s64.valid x = true) (hy : s64.valid y = true)
    (hop : op = .gt ∨ op = .lt ∨ op = .le ∨ op = .ge) :
    (NExpr.binary bl op (.variable s64 i) (.variable s64 j)).denote env = some (binaryValue op x y) := by
  rw [den_binary, den_variable, den_variable, hi, hj]
  simp only [Option.bind_some]
  have h01 : binaryValue op x y = 0 ∨ binaryValue op x y = 1 := by
    rcases hop with h | h | h | h <;> subst h <;> simp [binaryValue] <;> omega
  unfold Ty.convert
  rcases h01 with h | h <;> simp [h, bl, Ty.valid]


abbrev brA (op : Binary) (i j slot src : Nat) : Command :=
  .branch (.binary bl op (.variable s64 i) (.variable s64 j))
    (.sequence (.scope (.sequence (.primitive (.assign slot s64 (.variable s64 src))) Sk)) Sk) Sk

theorem stage_assign (op : Binary) (hop : op = .gt ∨ op = .lt ∨ op = .le ∨ op = .ge) (i j slot src : Nat) (Q : PS)
    (x y z old : Int) (n : Nat) (fu : Nat)
    (hi : penv Q i s64 = some x) (hj : penv Q j s64 = some y) (hz : penv Q src s64 = some z)
    (hbs : Q.bs[slot]? = some ⟨n,true⟩) (hm : Q.mem[n]? = some ⟨s64,old⟩) (hvold : s64.valid old = true)
    (hvz : s64.valid z = true) (hx : s64.valid x = true) (hy : s64.valid y = true) :
    ∃ r, pexec fu (brA op i j slot src) Q = some r ∧ r.ret = none ∧
      r.ps = (if binaryValue op x y ≠ 0 then (⟨Q.mem.set n ⟨s64,z⟩,Q.bs⟩ : PS) else Q) ∧ r.cost ≤ 10 ∧
      r.need ≤ Q.mem.length + Q.bs.length + 10 := by
  have cd := cmp_den op i j (penv Q) x y hi hj hx hy hop
  by_cases hc : binaryValue op x y = 0
  · rw [hc] at cd
    have sk := pexec_skip fu Q
    have := (pexec_branch_false fu _ _ _ Q cd _ sk : pexec fu (brA op i j slot src) Q = _)
    refine ⟨_, this, rfl, ?_, ?_, ?_⟩
    · simp [hc]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]; omega
  · have vz : (NExpr.variable s64 src).denote (penv Q) = some z := by rw [den_variable]; exact hz
    have st := pstmt_assign_ok Q slot s64 (.variable s64 src) z vz ⟨n,true⟩ ⟨s64,old⟩ hbs hm rfl hvold rfl z
      (convS _ hvz)
    have br := pexec_braced fu _ Q _ st rfl (by simp) (by simp)
    have := (pexec_branch_true fu _ _ _ Q _ cd hc _ br : pexec fu (brA op i j slot src) Q = _)
    refine ⟨_, this, rfl, ?_, ?_, ?_⟩
    · simp [hc]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]; omega


abbrev ccond : NExpr := .logical false (.binary bl .ge (.variable s64 3) (.variable s64 1))
  (.binary bl .ge (.variable s64 0) (.variable s64 4))

abbrev bodyI (R0 R1 : NExpr) : Command :=
  .sequence (.branch ccond (.sequence (.scope (.sequence (.primitive (.ret R0)) Sk)) Sk) Sk)
    (.sequence (.primitive (.declare s64 true (.variable s64 0)))
    (.sequence (brA .gt 3 0 6 3)
    (.sequence (.primitive (.declare s64 true (.variable s64 1)))
    (.sequence (brA .lt 4 1 7 4)
    (.sequence (.primitive (.check (.binary bl .le (.variable s64 6) (.variable s64 7))))
    (.sequence (.primitive (.ret R1)) Sk))))))

theorem ccond_nodes : ccond.nodes = 7 := rfl

theorem ccond_den (env : Nat → Ty → Option Int) (sv ev bsv bev : Int) (h0 : env 0 s64 = some sv)
    (h1 : env 1 s64 = some ev) (h3 : env 3 s64 = some bsv) (h4 : env 4 s64 = some bev)
    (g0 : s64.valid sv = true) (g1 : s64.valid ev = true) (g3 : s64.valid bsv = true) (g4 : s64.valid bev = true) :
    ccond.denote env = some (if bsv ≥ ev ∨ sv ≥ bev then 1 else 0) := by
  have c1 := cmp_den .ge 3 1 env bsv ev h3 h1 g3 g1 (by simp)
  have c2 := cmp_den .ge 0 4 env sv bev h0 h4 g0 g4 (by simp)
  have hl : ccond.denote env = (((NExpr.binary bl .ge (.variable s64 3) (.variable s64 1)).denote env).bind fun a =>
      if a == 0 then ((NExpr.binary bl .ge (.variable s64 0) (.variable s64 4)).denote env).bind fun b =>
        some (if b == 0 then 0 else 1) else some 1) := rfl
  rw [hl, c1, c2]
  simp only [Option.bind_some, binaryValue]
  by_cases a : bsv ≥ ev <;> by_cases b : sv ≥ bev <;> simp [a, b]


def B6 (a0 a1 a2 a3 a4 a5 : Nat) : List CppState.Binding :=
  [⟨a0,false⟩,⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩,⟨a5,false⟩]

theorem penv_pre (P L : List Cell) (B X : List CppState.Binding) (k a : Nat) (ty : Ty) (v : Int)
    (hb : B[k]? = some ⟨a,false⟩) (hP : P[a]? = some ⟨ty,v⟩) (hv : ty.valid v = true) :
    penv ⟨P ++ L,B ++ X⟩ k ty = some v := by
  have l : a < P.length := (List.getElem?_eq_some_iff.mp hP).1
  have hk : k < B.length := (List.getElem?_eq_some_iff.mp hb).1
  refine penv_old _ k ty ⟨a,false⟩ v ?_ ?_ hv
  · show (B ++ X)[k]? = _
    rw [List.getElem?_append_left hk]; exact hb
  · show (P ++ L)[a]? = _
    rw [List.getElem?_append_left l]; exact hP

theorem penv_new (P : List Cell) (B : List CppState.Binding) (L : List Cell) (X : List CppState.Binding) (j : Nat)
    (ty : Ty) (v : Int) (hb : (B ++ X)[B.length + j]? = some ⟨P.length + j,true⟩)
    (hm : L[j]? = some ⟨ty,v⟩) (hv : ty.valid v = true) : penv ⟨P ++ L,B ++ X⟩ (B.length + j) ty = some v := by
  refine penv_old _ _ ty ⟨P.length + j,true⟩ v hb ?_ hv
  show (P ++ L)[P.length + j]? = _
  rw [Proofs.ModIntExec.get_tail P L j]; exact hm


set_option maxHeartbeats 4000000 in
theorem inter_exec (R0 R1 : NExpr) (c0 : Int) (hR0 : ∀ env, R0.denote env = some c0)
    (f : Int → Int → Int)
    (hR1 : ∀ (env : Nat → Ty → Option Int) (ns ne : Int), env 6 s64 = some ns → env 7 s64 = some ne →
      R1.denote env = some (f ns ne))
    (hn0 : R0.nodes ≤ 8) (hn1 : R1.nodes ≤ 8)
    (fu : Nat) (P : List Cell) (a0 a1 a2 a3 a4 a5 : Nat) (sv ev bsv bev : Int)
    (h0 : P[a0]? = some ⟨s64,sv⟩) (h1 : P[a1]? = some ⟨s64,ev⟩) (h3 : P[a3]? = some ⟨s64,bsv⟩)
    (h4 : P[a4]? = some ⟨s64,bev⟩) (g0 : s64.valid sv = true) (g1 : s64.valid ev = true)
    (g3 : s64.valid bsv = true) (g4 : s64.valid bev = true) (hse : sv ≤ ev) (hbe : bsv ≤ bev) :
    ∃ r, pexec fu (bodyI R0 R1) ⟨P,B6 a0 a1 a2 a3 a4 a5⟩ = some r ∧
      r.ret = some (if bsv ≥ ev ∨ sv ≥ bev then c0
        else f (if sv < bsv then bsv else sv) (if bev < ev then bev else ev)) ∧
      r.cost ≤ 100 ∧ r.need ≤ P.length + 60 ∧ r.ps.mem.take P.length = P := by
  have e0 : penv ⟨P,B6 a0 a1 a2 a3 a4 a5⟩ 0 s64 = some sv :=
    penv_old _ 0 s64 ⟨a0,false⟩ sv rfl h0 g0
  have e1 : penv ⟨P,B6 a0 a1 a2 a3 a4 a5⟩ 1 s64 = some ev :=
    penv_old _ 1 s64 ⟨a1,false⟩ ev rfl h1 g1
  have e3 : penv ⟨P,B6 a0 a1 a2 a3 a4 a5⟩ 3 s64 = some bsv :=
    penv_old _ 3 s64 ⟨a3,false⟩ bsv rfl h3 g3
  have e4 : penv ⟨P,B6 a0 a1 a2 a3 a4 a5⟩ 4 s64 = some bev :=
    penv_old _ 4 s64 ⟨a4,false⟩ bev rfl h4 g4
  have hC := ccond_den _ sv ev bsv bev e0 e1 e3 e4 g0 g1 g3 g4
  by_cases hov : bsv ≥ ev ∨ sv ≥ bev
  · rw [if_pos hov] at hC
    have rs := pstmt_ret_ok ⟨P,B6 a0 a1 a2 a3 a4 a5⟩ R0 c0 (hR0 _)
    have in1 := seq_ret (b := Sk) ((pexec_prim fu (.ret R0) _).trans rs) rfl
    have sc := pexec_scope fu _ _ _ in1
    have in2 := seq_ret (b := Sk) sc rfl
    have br := pexec_branch_true fu ccond _ Sk _ 1 hC (by simp) _ in2
    refine ⟨_, seq_ret br rfl, by simp [hov], ?_, ?_, ?_⟩
    · simp [ccond_nodes]; omega
    · simp [ccond_nodes, B6]; omega
    · simp
  · rw [if_neg hov] at hC
    have hov1 : bsv < ev := by omega
    have hov2 : sv < bev := by omega
    have b1 := pexec_branch_false fu ccond (.sequence (.scope (.sequence (.primitive (.ret R0)) Sk)) Sk) Sk
      ⟨P,B6 a0 a1 a2 a3 a4 a5⟩ hC _ (pexec_skip fu _)
    have d1 := pstmt_declare_ok ⟨P,B6 a0 a1 a2 a3 a4 a5⟩ s64 true (.variable s64 0) sv
      (by rw [den_variable]; exact e0) sv (convS _ g0)
    have d1' := (pexec_prim fu (.declare s64 true (.variable s64 0)) _).trans d1
    -- stage 1: ns = max sv bsv
    have hb6 : ∀ k a, (B6 a0 a1 a2 a3 a4 a5)[k]? = some ⟨a,false⟩ → k < 6 := by
      intro k a h; have := (List.getElem?_eq_some_iff.mp h).1; simpa [B6] using this
    have pi : penv ⟨P ++ [⟨s64,sv⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩]⟩ 3 s64 = some bsv :=
      penv_pre P _ _ _ 3 a3 s64 bsv (by simp [B6]) h3 g3
    have pj : penv ⟨P ++ [⟨s64,sv⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩]⟩ 0 s64 = some sv :=
      penv_pre P _ _ _ 0 a0 s64 sv (by simp [B6]) h0 g0
    have hQ1b : (B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩])[6]? = some ⟨P.length,true⟩ := by simp [B6]
    obtain ⟨r2, hr2, hret2, hps2, hc2, hn2⟩ := stage_assign .gt (Or.inl rfl) 3 0 6 3
      ⟨P ++ [⟨s64,sv⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩]⟩ bsv sv bsv sv P.length fu pi pj pi hQ1b
      (by simp) g0 g3 g3 g0
    obtain ⟨ns, hns⟩ : ∃ ns, ns = if sv < bsv then bsv else sv := ⟨_, rfl⟩
    have hQ2 : r2.ps = ⟨P ++ [⟨s64,ns⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩]⟩ := by
      rw [hps2, hns]
      by_cases hh : sv < bsv
      · simp [binaryValue, hh, List.set_append_right]
      · simp [binaryValue, hh]
    -- stage 2: declare ne, then ne = min ev bev
    have pe1 : penv r2.ps 1 s64 = some ev := by
      rw [hQ2]
      exact penv_pre P [⟨s64,ns⟩] _ [⟨P.length,true⟩] 1 a1 s64 ev (by simp [B6]) h1 g1
    have d2 := pstmt_declare_ok r2.ps s64 true (.variable s64 1) ev (by rw [den_variable]; exact pe1) ev (convS _ g1)
    have d2' := (pexec_prim fu (.declare s64 true (.variable s64 1)) _).trans d2
    obtain ⟨ne, hne⟩ : ∃ ne, ne = if bev < ev then bev else ev := ⟨_, rfl⟩
    have hQ3 : (⟨r2.ps.mem ++ [⟨s64,ev⟩],r2.ps.bs ++ [⟨r2.ps.mem.length,true⟩]⟩ : PS) =
        ⟨P ++ [⟨s64,ns⟩,⟨s64,ev⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ := by
      rw [hQ2]; simp
    rw [hQ3] at d2'
    have pi2 : penv ⟨P ++ [⟨s64,ns⟩,⟨s64,ev⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ 4 s64
        = some bev := penv_pre P [⟨s64,ns⟩,⟨s64,ev⟩] _ [⟨P.length,true⟩,⟨P.length+1,true⟩] 4 a4 s64 bev
          (by simp [B6]) h4 g4
    have pj2 : penv ⟨P ++ [⟨s64,ns⟩,⟨s64,ev⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ 1 s64
        = some ev := penv_pre P [⟨s64,ns⟩,⟨s64,ev⟩] _ [⟨P.length,true⟩,⟨P.length+1,true⟩] 1 a1 s64 ev
          (by simp [B6]) h1 g1
    obtain ⟨r4, hr4, hret4, hps4, hc4, hn4⟩ := stage_assign .lt (Or.inr (Or.inl rfl)) 4 1 7 4
      ⟨P ++ [⟨s64,ns⟩,⟨s64,ev⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ bev ev bev ev
      (P.length+1) fu pi2 pj2 pi2 (by simp [B6]) (by simp) g1 g4 g4 g1
    have hQ4 : r4.ps = ⟨P ++ [⟨s64,ns⟩,⟨s64,ne⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ := by
      rw [hps4, hne]
      by_cases hh : bev < ev
      · simp [binaryValue, hh, List.set_append_right]
      · simp [binaryValue, hh]
    have vns : s64.valid ns = true := by rw [hns]; split <;> assumption
    have vne : s64.valid ne = true := by rw [hne]; split <;> assumption
    have e6 : penv ⟨P ++ [⟨s64,ns⟩,⟨s64,ne⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ 6 s64
        = some ns := penv_old _ 6 s64 ⟨P.length,true⟩ ns (by simp [B6]) (by simp) vns
    have e7 : penv ⟨P ++ [⟨s64,ns⟩,⟨s64,ne⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ 7 s64
        = some ne := penv_old _ 7 s64 ⟨P.length+1,true⟩ ne (by simp [B6]) (by simp) vne
    have hle : ns ≤ ne := by
      rw [hns, hne]
      split <;> split <;> omega
    have chk := cmp_den .le 6 7 _ ns ne e6 e7 vns vne (Or.inr (Or.inr (Or.inl rfl)))
    have hone : binaryValue .le ns ne = 1 := by simp [binaryValue, hle]
    rw [hone] at chk
    have ck := pstmt_check_ok _ _ 1 chk (by simp)
    have rs := pstmt_ret_ok ⟨P ++ [⟨s64,ns⟩,⟨s64,ne⟩],B6 a0 a1 a2 a3 a4 a5 ++ [⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ R1
      (f ns ne) (hR1 _ ns ne e6 e7)
    have t7 := seq_ret (b := Sk) ((pexec_prim fu (.ret R1) _).trans rs) rfl
    have t6 := seq_some ((pexec_prim fu _ _).trans ck) rfl t7
    have t5 := seq_some hr4 hret4 (by rw [hQ4]; exact t6)
    have t4 := seq_some d2' rfl t5
    have t3 := seq_some hr2 hret2 t4
    have t2 := seq_some d1' rfl (by exact t3)
    have t1 := seq_some b1 rfl (by exact t2)
    refine ⟨_, t1, ?_, ?_, ?_, ?_⟩
    · simp [hov, hns, hne]
    · simp [ccond_nodes, NExpr.nodes]
      omega
    · simp [ccond_nodes, NExpr.nodes, B6, hQ2]
      simp [B6] at hn2 hn4
      omega
    · simp


theorem refs3_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (t2 : Ty) (t3 : Ty)
    (hp : prog.parameters = [.scalar t1 true false,.scalar t2 true false,.scalar t3 true false])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (s2 : Nat) (s3 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (b3 : CppState.Binding) (v1 : Int) (v2 : Int) (v3 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (c3 : caller.scalarCell s3 t3 = some (b3,⟨t3,v3⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_refs3 caller _ t1 t2 t3 s1 s2 s3 b1 b2 b3 v1 v2 v3 hp c1 c2 c3 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.scalarReference s3] Sinit
    (callerP caller) [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

set_option maxHeartbeats 4000000 in
theorem refs6_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (t2 : Ty) (t3 : Ty) (t4 : Ty) (t5 : Ty) (t6 : Ty)
    (hp : prog.parameters = [.scalar t1 true false,.scalar t2 true false,.scalar t3 true false,.scalar t4 true false,.scalar t5 true false,.scalar t6 true false])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (s2 : Nat) (s3 : Nat) (s4 : Nat) (s5 : Nat) (s6 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (b3 : CppState.Binding) (b4 : CppState.Binding) (b5 : CppState.Binding) (b6 : CppState.Binding) (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) (v5 : Int) (v6 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (c3 : caller.scalarCell s3 t3 = some (b3,⟨t3,v3⟩))
    (c4 : caller.scalarCell s4 t4 = some (b4,⟨t4,v4⟩))
    (c5 : caller.scalarCell s5 t5 = some (b5,⟨t5,v5⟩))
    (c6 : caller.scalarCell s6 t6 = some (b6,⟨t6,v6⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩,⟨b5.address,false⟩,⟨b6.address,false⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,.scalarReference s6] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,.scalarReference s6] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_refs6 caller _ t1 t2 t3 t4 t5 t6 s1 s2 s3 s4 s5 s6 b1 b2 b3 b4 b5 b6 v1 v2 v3 v4 v5 v6 hp c1 c2 c3 c4 c5 c6 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,.scalarReference s6] Sinit
    (callerP caller) [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩,⟨b5.address,false⟩,⟨b6.address,false⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post


theorem P_cell_ty (caller : NState) (sa : Nat) (ty : Ty) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa ty = some (ba,⟨ty,x⟩)) : (callerP caller)[ba.address]? = some ⟨ty,x⟩ := by
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma

theorem cell_valid (caller : NState) (sa : Nat) (ty : Ty) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa ty = some (ba,⟨ty,x⟩)) : ty.valid x = true := by
  obtain ⟨ia,_,_,hma,_,hv⟩ := scalarCell_facts ca
  exact hv

theorem take_callerP (caller : NState) : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
  simp only [callerP]; exact List.take_left' rfl

theorem length_den (env : Nat → Ty → Option Int) (v1 v2 : Int) (h1 : env 0 s64 = some v1) (h2 : env 1 s64 = some v2)
    (hd : s64.valid (v2 - v1) = true) :
    (NExpr.binary s64 .sub (.variable s64 1) (.variable s64 0)).denote env = some (v2 - v1) := by
  rw [den_binary, den_variable, den_variable, h2, h1]
  simp only [Option.bind_some]
  have e : binaryValue .sub v2 v1 = v2 - v1 := rfl
  rw [e]; exact convS _ hd

-- A body that returns one expression: the three-reference accessors of the class.
theorem accessor3_exec (e : NExpr) (v : Int) (caller : NState) (P : List Cell) (hP : P = callerP caller)
    (a1 a2 a3 : Nat) (hden : e.denote (penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩]⟩) = some v) (hn : e.nodes ≤ 8) :
    ∃ r, pexec 1 (.sequence (.primitive (.ret e)) Sk) ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩]⟩ = some r ∧
      r.ret = some v ∧ r.cost ≤ 10 ∧ r.need ≤ P.length + 100 ∧
      r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
  refine ⟨_, exec_ret 1 _ e v hden, rfl, ?_, ?_, ?_⟩
  · simp; omega
  · simp; omega
  · subst hP; exact take_callerP caller

theorem interval_start_correct (caller : NState) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (v1 v2 v3 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (c3 : caller.scalarCell s3 bl = some (b3,⟨bl,v3⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.IntervalInstance.Interval_long_long_start.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      Proofs.IntervalInstance.Interval_long_long_start.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = .finished (res,.scalar (v1)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  have g1 := cell_valid caller s1 s64 b1 v1 c1
  have g2 := cell_valid caller s2 s64 b2 v2 c2
  have g3 := cell_valid caller s3 bl b3 v3 c3
  have p1 := P_cell_ty caller s1 s64 b1 v1 c1
  have p2 := P_cell_ty caller s2 s64 b2 v2 c2
  have p3 := P_cell_ty caller s3 bl b3 v3 c3
  have E1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 0 s64 = some v1 :=
    penv_old _ 0 s64 ⟨b1.address,false⟩ v1 rfl p1 g1
  have E2 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 1 s64 = some v2 :=
    penv_old _ 1 s64 ⟨b2.address,false⟩ v2 rfl p2 g2
  have E3 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 2 bl = some v3 :=
    penv_old _ 2 bl ⟨b3.address,false⟩ v3 rfl p3 g3
  refine refs3_correct _ s64 s64 s64 bl rfl rfl rfl caller s1 s2 s3 b1 b2 b3 v1 v2 v3
    c1 c2 c3 valid lengths strict base 1 (v1) g1 10 ?_
  intro P hP
  subst hP
  exact accessor3_exec (.variable s64 0) (v1) caller _ rfl b1.address b2.address b3.address
    (by rw [den_variable]; exact E1) (by decide)

theorem interval_end_correct (caller : NState) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (v1 v2 v3 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (c3 : caller.scalarCell s3 bl = some (b3,⟨bl,v3⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.IntervalInstance.Interval_long_long_end.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      Proofs.IntervalInstance.Interval_long_long_end.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = .finished (res,.scalar (v2)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  have g1 := cell_valid caller s1 s64 b1 v1 c1
  have g2 := cell_valid caller s2 s64 b2 v2 c2
  have g3 := cell_valid caller s3 bl b3 v3 c3
  have p1 := P_cell_ty caller s1 s64 b1 v1 c1
  have p2 := P_cell_ty caller s2 s64 b2 v2 c2
  have p3 := P_cell_ty caller s3 bl b3 v3 c3
  have E1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 0 s64 = some v1 :=
    penv_old _ 0 s64 ⟨b1.address,false⟩ v1 rfl p1 g1
  have E2 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 1 s64 = some v2 :=
    penv_old _ 1 s64 ⟨b2.address,false⟩ v2 rfl p2 g2
  have E3 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 2 bl = some v3 :=
    penv_old _ 2 bl ⟨b3.address,false⟩ v3 rfl p3 g3
  refine refs3_correct _ s64 s64 s64 bl rfl rfl rfl caller s1 s2 s3 b1 b2 b3 v1 v2 v3
    c1 c2 c3 valid lengths strict base 1 (v2) g2 10 ?_
  intro P hP
  subst hP
  exact accessor3_exec (.variable s64 1) (v2) caller _ rfl b1.address b2.address b3.address
    (by rw [den_variable]; exact E2) (by decide)

theorem interval_is_null_correct (caller : NState) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (v1 v2 v3 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (c3 : caller.scalarCell s3 bl = some (b3,⟨bl,v3⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.IntervalInstance.Interval_long_long_is_null.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      Proofs.IntervalInstance.Interval_long_long_is_null.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = .finished (res,.scalar (v3)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  have g1 := cell_valid caller s1 s64 b1 v1 c1
  have g2 := cell_valid caller s2 s64 b2 v2 c2
  have g3 := cell_valid caller s3 bl b3 v3 c3
  have p1 := P_cell_ty caller s1 s64 b1 v1 c1
  have p2 := P_cell_ty caller s2 s64 b2 v2 c2
  have p3 := P_cell_ty caller s3 bl b3 v3 c3
  have E1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 0 s64 = some v1 :=
    penv_old _ 0 s64 ⟨b1.address,false⟩ v1 rfl p1 g1
  have E2 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 1 s64 = some v2 :=
    penv_old _ 1 s64 ⟨b2.address,false⟩ v2 rfl p2 g2
  have E3 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 2 bl = some v3 :=
    penv_old _ 2 bl ⟨b3.address,false⟩ v3 rfl p3 g3
  refine refs3_correct _ bl s64 s64 bl rfl rfl rfl caller s1 s2 s3 b1 b2 b3 v1 v2 v3
    c1 c2 c3 valid lengths strict base 1 (v3) g3 10 ?_
  intro P hP
  subst hP
  exact accessor3_exec (.variable bl 2) (v3) caller _ rfl b1.address b2.address b3.address
    (by rw [den_variable]; exact E3) (by decide)

theorem interval_length_correct (caller : NState) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (v1 v2 v3 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (c3 : caller.scalarCell s3 bl = some (b3,⟨bl,v3⟩))
    (hd : s64.valid (v2 - v1) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.IntervalInstance.Interval_long_long_length.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      Proofs.IntervalInstance.Interval_long_long_length.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = .finished (res,.scalar (v2 - v1)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  have g1 := cell_valid caller s1 s64 b1 v1 c1
  have g2 := cell_valid caller s2 s64 b2 v2 c2
  have g3 := cell_valid caller s3 bl b3 v3 c3
  have p1 := P_cell_ty caller s1 s64 b1 v1 c1
  have p2 := P_cell_ty caller s2 s64 b2 v2 c2
  have p3 := P_cell_ty caller s3 bl b3 v3 c3
  have E1 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 0 s64 = some v1 :=
    penv_old _ 0 s64 ⟨b1.address,false⟩ v1 rfl p1 g1
  have E2 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 1 s64 = some v2 :=
    penv_old _ 1 s64 ⟨b2.address,false⟩ v2 rfl p2 g2
  have E3 : penv ⟨callerP caller,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ 2 bl = some v3 :=
    penv_old _ 2 bl ⟨b3.address,false⟩ v3 rfl p3 g3
  refine refs3_correct _ s64 s64 s64 bl rfl rfl rfl caller s1 s2 s3 b1 b2 b3 v1 v2 v3
    c1 c2 c3 valid lengths strict base 1 (v2 - v1) hd 10 ?_
  intro P hP
  subst hP
  exact accessor3_exec (.binary s64 .sub (.variable s64 1) (.variable s64 0)) (v2 - v1) caller _ rfl b1.address b2.address b3.address
    (length_den _ v1 v2 E1 E2 hd) (by decide)


theorem R0z (env : Nat → Ty → Option Int) : (NExpr.cast s64 (.literal i32 0)).denote env = some 0 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
  exact convS 0 rfl

theorem R0o (env : Nat → Ty → Option Int) : (NExpr.literal bl 1).denote env = some 1 := by
  rw [den_literal, if_pos (show bl.valid 1 = true from rfl)]

theorem R1eq (env : Nat → Ty → Option Int) (ns ne : Int) (h6 : env 6 s64 = some ns) (h7 : env 7 s64 = some ne) :
    (NExpr.binary bl .eq (.variable s64 6) (.variable s64 7)).denote env = some (if ns = ne then 1 else 0) := by
  rw [den_binary, den_variable, den_variable, h6, h7]
  simp only [Option.bind_some]
  have : binaryValue .eq ns ne = if ns = ne then 1 else 0 := by
    by_cases h : ns = ne <;> simp [binaryValue, h]
  rw [this]
  unfold Ty.convert
  by_cases h : ns = ne <;> simp [h, bl, Ty.valid]

abbrev bodyIs : Command := bodyI (.cast s64 (.literal i32 0)) (.variable s64 6)
abbrev bodyIe : Command := bodyI (.cast s64 (.literal i32 0)) (.variable s64 7)
abbrev bodyIn : Command := bodyI (.literal bl 1) (.binary bl .eq (.variable s64 6) (.variable s64 7))
theorem body_eqIs : Proofs.IntervalInstance.Interval_long_long_intersection_s.body = bodyIs := rfl
theorem body_eqIe : Proofs.IntervalInstance.Interval_long_long_intersection_e.body = bodyIe := rfl
theorem body_eqIn : Proofs.IntervalInstance.Interval_long_long_intersection_is_n.body = bodyIn := rfl

set_option maxHeartbeats 4000000 in
theorem interval_intersection_s_correct (caller : NState) (s1 s2 s3 s4 s5 s6 : Nat) (b1 b2 b3 b4 b5 b6 : CppState.Binding)
    (sv ev nv bsv bev bnv : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,sv⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,ev⟩))
    (c3 : caller.scalarCell s3 bl = some (b3,⟨bl,nv⟩)) (c4 : caller.scalarCell s4 s64 = some (b4,⟨s64,bsv⟩))
    (c5 : caller.scalarCell s5 s64 = some (b5,⟨s64,bev⟩)) (c6 : caller.scalarCell s6 bl = some (b6,⟨bl,bnv⟩))
    (hse : sv ≤ ev) (hbe : bsv ≤ bev)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.IntervalInstance.Interval_long_long_intersection_s.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,
          .scalarReference s6] = some Sinit ∧
      Proofs.IntervalInstance.Interval_long_long_intersection_s.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,
          .scalarReference s6] = .finished (res,.scalar (if bsv ≥ ev ∨ sv ≥ bev then 0 else (if sv < bsv then bsv else sv))) ∧
      ScalarPost2 caller Sinit res 0 160 caller.scalars.memory := by
  have g1 := cell_valid caller s1 s64 b1 sv c1
  have g2 := cell_valid caller s2 s64 b2 ev c2
  have g4 := cell_valid caller s4 s64 b4 bsv c4
  have g5 := cell_valid caller s5 s64 b5 bev c5
  have p1 := P_cell_ty caller s1 s64 b1 sv c1
  have p2 := P_cell_ty caller s2 s64 b2 ev c2
  have p4 := P_cell_ty caller s4 s64 b4 bsv c4
  have p5 := P_cell_ty caller s5 s64 b5 bev c5
  have hvv : s64.valid (if bsv ≥ ev ∨ sv ≥ bev then 0 else (if sv < bsv then bsv else sv)) = true := by
    by_cases h : bsv ≥ ev ∨ sv ≥ bev <;> by_cases h2 : sv < bsv <;> simp [h, h2, g1, g4] <;> exact rfl
  refine refs6_correct _ s64 s64 s64 bl s64 s64 bl rfl rfl rfl caller s1 s2 s3 s4 s5 s6 b1 b2 b3 b4 b5 b6
    sv ev nv bsv bev bnv c1 c2 c3 c4 c5 c6 valid lengths strict base 1 (if bsv ≥ ev ∨ sv ≥ bev then 0 else (if sv < bsv then bsv else sv)) hvv 100 ?_
  intro P hP
  subst hP
  obtain ⟨r, hr, hret, hc, hn, htake⟩ := inter_exec (NExpr.cast s64 (.literal i32 0)) (NExpr.variable s64 6) 0 R0z
    (fun ns _ => ns) (fun env ns ne h6 _ => by rw [den_variable]; exact h6) (by decide) (by decide) 1 (callerP caller) b1.address b2.address b3.address b4.address b5.address
    b6.address sv ev bsv bev p1 p2 p4 p5 g1 g2 g4 g5 hse hbe
  refine ⟨r, by rw [body_eqIs]; exact hr, ?_, hc, by omega, ?_⟩
  · rw [hret]
  · have hle : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    calc r.ps.mem.take caller.scalars.memory.length
        = (r.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take, Nat.min_eq_left hle]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [htake]
      _ = caller.scalars.memory := take_callerP caller

set_option maxHeartbeats 4000000 in
theorem interval_intersection_e_correct (caller : NState) (s1 s2 s3 s4 s5 s6 : Nat) (b1 b2 b3 b4 b5 b6 : CppState.Binding)
    (sv ev nv bsv bev bnv : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,sv⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,ev⟩))
    (c3 : caller.scalarCell s3 bl = some (b3,⟨bl,nv⟩)) (c4 : caller.scalarCell s4 s64 = some (b4,⟨s64,bsv⟩))
    (c5 : caller.scalarCell s5 s64 = some (b5,⟨s64,bev⟩)) (c6 : caller.scalarCell s6 bl = some (b6,⟨bl,bnv⟩))
    (hse : sv ≤ ev) (hbe : bsv ≤ bev)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.IntervalInstance.Interval_long_long_intersection_e.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,
          .scalarReference s6] = some Sinit ∧
      Proofs.IntervalInstance.Interval_long_long_intersection_e.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,
          .scalarReference s6] = .finished (res,.scalar (if bsv ≥ ev ∨ sv ≥ bev then 0 else (if bev < ev then bev else ev))) ∧
      ScalarPost2 caller Sinit res 0 160 caller.scalars.memory := by
  have g1 := cell_valid caller s1 s64 b1 sv c1
  have g2 := cell_valid caller s2 s64 b2 ev c2
  have g4 := cell_valid caller s4 s64 b4 bsv c4
  have g5 := cell_valid caller s5 s64 b5 bev c5
  have p1 := P_cell_ty caller s1 s64 b1 sv c1
  have p2 := P_cell_ty caller s2 s64 b2 ev c2
  have p4 := P_cell_ty caller s4 s64 b4 bsv c4
  have p5 := P_cell_ty caller s5 s64 b5 bev c5
  have hvv : s64.valid (if bsv ≥ ev ∨ sv ≥ bev then 0 else (if bev < ev then bev else ev)) = true := by
    by_cases h : bsv ≥ ev ∨ sv ≥ bev <;> by_cases h2 : bev < ev <;> simp [h, h2, g2, g5] <;> exact rfl
  refine refs6_correct _ s64 s64 s64 bl s64 s64 bl rfl rfl rfl caller s1 s2 s3 s4 s5 s6 b1 b2 b3 b4 b5 b6
    sv ev nv bsv bev bnv c1 c2 c3 c4 c5 c6 valid lengths strict base 1 (if bsv ≥ ev ∨ sv ≥ bev then 0 else (if bev < ev then bev else ev)) hvv 100 ?_
  intro P hP
  subst hP
  obtain ⟨r, hr, hret, hc, hn, htake⟩ := inter_exec (NExpr.cast s64 (.literal i32 0)) (NExpr.variable s64 7) 0 R0z
    (fun _ ne => ne) (fun env ns ne _ h7 => by rw [den_variable]; exact h7) (by decide) (by decide) 1 (callerP caller) b1.address b2.address b3.address b4.address b5.address
    b6.address sv ev bsv bev p1 p2 p4 p5 g1 g2 g4 g5 hse hbe
  refine ⟨r, by rw [body_eqIe]; exact hr, ?_, hc, by omega, ?_⟩
  · rw [hret]
  · have hle : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    calc r.ps.mem.take caller.scalars.memory.length
        = (r.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take, Nat.min_eq_left hle]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [htake]
      _ = caller.scalars.memory := take_callerP caller

set_option maxHeartbeats 4000000 in
theorem interval_intersection_is_n_correct (caller : NState) (s1 s2 s3 s4 s5 s6 : Nat) (b1 b2 b3 b4 b5 b6 : CppState.Binding)
    (sv ev nv bsv bev bnv : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,sv⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,ev⟩))
    (c3 : caller.scalarCell s3 bl = some (b3,⟨bl,nv⟩)) (c4 : caller.scalarCell s4 s64 = some (b4,⟨s64,bsv⟩))
    (c5 : caller.scalarCell s5 s64 = some (b5,⟨s64,bev⟩)) (c6 : caller.scalarCell s6 bl = some (b6,⟨bl,bnv⟩))
    (hse : sv ≤ ev) (hbe : bsv ≤ bev)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.IntervalInstance.Interval_long_long_intersection_is_n.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,
          .scalarReference s6] = some Sinit ∧
      Proofs.IntervalInstance.Interval_long_long_intersection_is_n.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4,.scalarReference s5,
          .scalarReference s6] = .finished (res,.scalar (if bsv ≥ ev ∨ sv ≥ bev then 1 else (if (if sv < bsv then bsv else sv) = (if bev < ev then bev else ev) then 1 else 0))) ∧
      ScalarPost2 caller Sinit res 0 160 caller.scalars.memory := by
  have g1 := cell_valid caller s1 s64 b1 sv c1
  have g2 := cell_valid caller s2 s64 b2 ev c2
  have g4 := cell_valid caller s4 s64 b4 bsv c4
  have g5 := cell_valid caller s5 s64 b5 bev c5
  have p1 := P_cell_ty caller s1 s64 b1 sv c1
  have p2 := P_cell_ty caller s2 s64 b2 ev c2
  have p4 := P_cell_ty caller s4 s64 b4 bsv c4
  have p5 := P_cell_ty caller s5 s64 b5 bev c5
  have hvv : bl.valid (if bsv ≥ ev ∨ sv ≥ bev then 1 else (if (if sv < bsv then bsv else sv) = (if bev < ev then bev else ev) then 1 else 0)) = true := by
    by_cases h : bsv ≥ ev ∨ sv ≥ bev <;> by_cases h2 : (if sv < bsv then bsv else sv) = (if bev < ev then bev else ev) <;> simp [h, h2, bl, Ty.valid]
  refine refs6_correct _ bl s64 s64 bl s64 s64 bl rfl rfl rfl caller s1 s2 s3 s4 s5 s6 b1 b2 b3 b4 b5 b6
    sv ev nv bsv bev bnv c1 c2 c3 c4 c5 c6 valid lengths strict base 1 (if bsv ≥ ev ∨ sv ≥ bev then 1 else (if (if sv < bsv then bsv else sv) = (if bev < ev then bev else ev) then 1 else 0)) hvv 100 ?_
  intro P hP
  subst hP
  obtain ⟨r, hr, hret, hc, hn, htake⟩ := inter_exec (NExpr.literal bl 1) (NExpr.binary bl .eq (.variable s64 6) (.variable s64 7)) 1 R0o
    (fun ns ne => if ns = ne then 1 else 0) (fun env ns ne h6 h7 => R1eq env ns ne h6 h7) (by decide) (by decide) 1 (callerP caller) b1.address b2.address b3.address b4.address b5.address
    b6.address sv ev bsv bev p1 p2 p4 p5 g1 g2 g4 g5 hse hbe
  refine ⟨r, by rw [body_eqIn]; exact hr, ?_, hc, by omega, ?_⟩
  · rw [hret]
  · have hle : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    calc r.ps.mem.take caller.scalars.memory.length
        = (r.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take, Nat.min_eq_left hle]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [htake]
      _ = caller.scalars.memory := take_callerP caller

end Proofs.IntervalCall
