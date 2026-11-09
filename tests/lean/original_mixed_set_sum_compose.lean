namespace SetComposeAudit
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall


open Proofs.MonoidLazyCall Proofs.MonoidCall

open CopiedScalarFieldsAudit

def composeBody (k : Nat) (second : Bool) : Command :=
  .sequence (.branch (.variable bl 1)
    (copyBlock k s64 bl (.variable s64 2) (.variable bl 3) second)
    (copyBlock k s64 bl (.variable s64 0) (.variable bl 1) second)) Sk

theorem compose_body (second : Bool) :
    (if second then OriginalSetSum.RangeSet_compose_noop else OriginalSetSum.RangeSet_compose_v).body =
      composeBody 4 second := by cases second <;> rfl

theorem compose_exec (P : List Cell) (a1 a2 a3 a4 : Nat) (v1 n1 v2 n2 : Int) (second : Bool)
    (c1 : P[a1]? = some ⟨s64,v1⟩) (c2 : P[a2]? = some ⟨bl,n1⟩)
    (c3 : P[a3]? = some ⟨s64,v2⟩) (c4 : P[a4]? = some ⟨bl,n2⟩)
    (g1 : s64.valid v1 = true) (g2 : bl.valid n1 = true)
    (g3 : s64.valid v2 = true) (g4 : bl.valid n2 = true) :
    let R : List CppState.Binding := [⟨a1,true⟩,⟨a2,true⟩,⟨a3,true⟩,⟨a4,true⟩]
    ∃ r, pexec 1 (if second then OriginalSetSum.RangeSet_compose_noop else OriginalSetSum.RangeSet_compose_v).body
        ⟨P,R⟩ = some r ∧
      r.ret = some (if n1 ≠ 0 then (if second then n2 else v2) else (if second then n1 else v1)) ∧
      r.cost ≤ 20 ∧ r.need ≤ P.length+40 ∧ r.ps = ⟨P,R⟩ := by
  let R : List CppState.Binding := [⟨a1,true⟩,⟨a2,true⟩,⟨a3,true⟩,⟨a4,true⟩]
  have df : (NExpr.variable s64 0).denote (penv (ws P R [])) = some v1 := by
    rw [den_variable]; exact ws_env_ref P R [] 0 a1 true s64 v1 rfl c1 g1
  have nf : (NExpr.variable bl 1).denote (penv (ws P R [⟨s64,v1⟩])) = some n1 := by
    rw [den_variable]; exact ws_env_ref P R _ 1 a2 true bl n1 rfl c2 g2
  have dg : (NExpr.variable s64 2).denote (penv (ws P R [])) = some v2 := by
    rw [den_variable]; exact ws_env_ref P R [] 2 a3 true s64 v2 rfl c3 g3
  have ng : (NExpr.variable bl 3).denote (penv (ws P R [⟨s64,v2⟩])) = some n2 := by
    rw [den_variable]; exact ws_env_ref P R _ 3 a4 true bl n2 rfl c4 g4
  have cond : (NExpr.variable bl 1).denote (penv (⟨P,R⟩ : PS)) = some n1 := by
    rw [den_variable]
    simpa only [ws_nil] using ws_env_ref P R [] 1 a2 true bl n1 rfl c2 g2
  obtain ⟨rf,ranf,retf,costf,needf,psf⟩ := copy_block_exec P R s64 bl
    (.variable s64 0) (.variable bl 1) v1 n1 second g1 g2 df nf
  obtain ⟨rg,rang,retg,costg,needg,psg⟩ := copy_block_exec P R s64 bl
    (.variable s64 2) (.variable bl 3) v2 n2 second g3 g4 dg ng
  have body : (if second then OriginalSetSum.RangeSet_compose_noop else OriginalSetSum.RangeSet_compose_v).body =
      composeBody R.length second := by simpa [R] using compose_body second
  by_cases zero : n1 = 0
  · have br := pexec_branch_false 1 (.variable bl 1)
      (copyBlock R.length s64 bl (.variable s64 2) (.variable bl 3) second)
      (copyBlock R.length s64 bl (.variable s64 0) (.variable bl 1) second)
      (⟨P,R⟩ : PS) (by simpa [zero] using cond) rf ranf
    have whole := seq_ret (b:=Sk) br retf
    refine ⟨⟨rf.ps,rf.ret,rf.cost+2,max (P.length+7) rf.need⟩,?_,?_,?_,?_,psf⟩
    · rw [body]; simpa [composeBody,R,NExpr.nodes] using whole
    · simpa [zero] using retf
    · change rf.cost+2 ≤ 20
      simp [NExpr.nodes] at costf
      omega
    · change max (P.length+7) rf.need ≤ P.length+40
      simp [R,NExpr.nodes] at needf
      omega
  · have br := pexec_branch_true 1 (.variable bl 1)
      (copyBlock R.length s64 bl (.variable s64 2) (.variable bl 3) second)
      (copyBlock R.length s64 bl (.variable s64 0) (.variable bl 1) second)
      (⟨P,R⟩ : PS) n1 cond zero rg rang
    have whole := seq_ret (b:=Sk) br retg
    refine ⟨⟨rg.ps,rg.ret,rg.cost+2,max (P.length+7) rg.need⟩,?_,?_,?_,?_,psg⟩
    · rw [body]; simpa [composeBody,R,NExpr.nodes] using whole
    · simpa [zero] using retg
    · change rg.cost+2 ≤ 20
      simp [NExpr.nodes] at costg
      omega
    · change max (P.length+7) rg.need ≤ P.length+40
      simp [R,NExpr.nodes] at needg
      omega

end SetComposeAudit
namespace SetComposePrepareAudit
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall


open Proofs.MonoidLazyCall Proofs.MonoidCall


theorem prepare_values4 (ty1 ty2 ty3 ty4 : Ty) (caller : NState)
    (params : List Proofs.CppVectorBindings.Parameter)
    (hp : params = [.scalar ty1 false true,.scalar ty2 false true,.scalar ty3 false true,.scalar ty4 false true])
    (e1 e2 e3 e4 : NExpr) (v1 v2 v3 v4 : Int)
    (h1 : e1.scalarOnly = true) (h2 : e2.scalarOnly = true)
    (h3 : e3.scalarOnly = true) (h4 : e4.scalarOnly = true)
    (t1ty : e1.resultType = ty1) (t2ty : e2.resultType = ty2)
    (t3ty : e3.resultType = ty3) (t4ty : e4.resultType = ty4)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3) (d4 : e4.denote (envOf caller) = some v4)
    (valid : caller.frame.state.wellFormed = true)
    (n1 : ty1.valid v1 = true) (n2 : ty2.valid v2 = true)
    (n3 : ty3.valid v3 = true) (n4 : ty4.valid v4 = true) :
    ∃ t1 t2 t3 t4, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      Good t2 t3 e3.nodes e3.nodes ∧ Good t3 t4 e4.nodes e4.nodes ∧
      ∃ Sinit, prepare caller params [.value e1,.value e2,.value e3,.value e4] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨ty1,v1⟩,⟨ty2,v2⟩,⟨ty3,v3⟩,⟨ty4,v4⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,
          ⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t4.scalars.work+5 ∧ t4.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 h1 d1
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1];exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 h3 (by rw [envOf_core g2.1,envOf_core g1.1];exact d3)
  obtain ⟨t4,ran4,g4⟩ := scalar_eval e4 t3 v4 h4 (by rw [envOf_core g3.1,envOf_core g2.1,envOf_core g1.1];exact d4)
  refine ⟨t1,t2,t3,t4,g1,g2,g3,g4,?_⟩
  have frameT : t4.frame = caller.frame := g4.1.1.trans (g3.1.1.trans (g2.1.1.trans g1.1.1))
  have fs : t4.frame.state = caller.frame.state := by rw [frameT]
  have fr : t4.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t4.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t4.scalars.memory = caller.scalars.memory :=
    g4.1.2.2.2.1.trans (g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans g1.1.2.2.2.1))
  have hbind : t4.scalars.bindings = caller.scalars.bindings :=
    g4.1.2.2.2.2.1.trans (g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans g1.1.2.2.2.2.1))
  have hbase : t4.scalars.baseMemory = caller.scalars.baseMemory :=
    g4.1.2.2.2.2.2.trans (g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans g1.1.2.2.2.2.2))
  have res1 : resolve caller (.scalar ty1 false true) (.value e1) = some (t1,.scalar ty1 true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar ty2 false true) (.value e2) = some (t2,.scalar ty2 true v2) := by
    simp [resolve,t2ty,ran2]
  have res3 : resolve t2 (.scalar ty3 false true) (.value e3) = some (t3,.scalar ty3 true v3) := by
    simp [resolve,t3ty,ran3]
  have res4 : resolve t3 (.scalar ty4 false true) (.value e4) = some (t4,.scalar ty4 true v4) := by
    simp [resolve,t4ty,ran4]
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2,res3,res4]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,n1,n2,n3,n4,callerP,
    NState.observe,CppState.State.observe]
  omega

end SetComposePrepareAudit
namespace SetComposeCallerAudit
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall


open Proofs.MonoidLazyCall Proofs.MonoidCall

open CopiedScalarFieldsAudit

open SetComposeAudit SetComposePrepareAudit

theorem four_values_body_correct (prog : NProgram) (ty : Ty)
    (hp : prog.parameters = [.scalar s64 false true,.scalar bl false true,.scalar s64 false true,.scalar bl false true])
    (hr : prog.result = .scalar ty) (hbody : Scalar prog.body = true)
    (caller : NState) (e1 e2 e3 e4 : NExpr) (v1 n1 v2 n2 rv : Int)
    (h1 : e1.scalarOnly = true) (h2 : e2.scalarOnly = true)
    (h3 : e3.scalarOnly = true) (h4 : e4.scalarOnly = true)
    (t1 : e1.resultType = s64) (t2 : e2.resultType = bl)
    (t3 : e3.resultType = s64) (t4 : e4.resultType = bl)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some n1)
    (d3 : e3.denote (envOf caller) = some v2) (d4 : e4.denote (envOf caller) = some n2)
    (g1 : s64.valid v1 = true) (g2 : bl.valid n1 = true)
    (g3 : s64.valid v2 = true) (g4 : bl.valid n2 = true) (gv : ty.valid rv = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hex : ∀ M : List Cell, M = callerP caller ++ [⟨s64,v1⟩,⟨bl,n1⟩,⟨s64,v2⟩,⟨bl,n2⟩] →
      ∃ r, pexec 1 prog.body ⟨M,[⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,
          ⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩]⟩ = some r ∧
        r.ret = some rv ∧ r.cost ≤ 20 ∧ r.need ≤ M.length+40 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e1,.value e2,.value e3,.value e4] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2,.value e3,.value e4] = .finished (res,.scalar rv) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes+e3.nodes+e4.nodes) 70 caller.scalars.memory := by
  obtain ⟨q1,q2,q3,q4,G1,G2,G3,G4,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_values4 s64 bl s64 bl caller _ hp e1 e2 e3 e4 v1 n1 v2 n2 h1 h2 h3 h4 t1 t2 t3 t4
      d1 d2 d3 d4 valid g1 g2 g3 g4
  let M := callerP caller ++ [(⟨s64,v1⟩ : Cell),⟨bl,n1⟩,⟨s64,v2⟩,⟨bl,n2⟩]
  let B : List CppState.Binding := [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,
    ⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩]
  have takeM : M.take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  obtain ⟨r,ran,ret,cost,need,mem⟩ := hex M rfl
  have w1 := G1.2.2.1
  have w2 := G2.2.2.1
  have w3 := G3.2.2.1
  have w4 := G4.2.2.1
  have p1 := G1.2.2.2.2.1
  have p2 := G2.2.2.2.2.1
  have p3 := G3.2.2.2.2.1
  have p4 := G4.2.2.2.2.1
  have post := call_scalar caller prog [.value e1,.value e2,.value e3,.value e4] Sinit M B
    hprep (by rw [sSlots];rfl) sMem sBind sBase sScope sFrame (by omega)
    (by simp [M,callerP]) (by rw [takeM]) valid lengths strict base hbody 1 r ran rv ret ty hr gv
    (by simp [M] at need;omega) (by simp [M,B]) (e1.nodes+e2.nodes+e3.nodes+e4.nodes) 70 (by omega)
  obtain ⟨fuel,res,hrun,hpost⟩ := post
  exact ⟨Sinit,fuel,res,hprep,hrun,by simpa only [mem] using hpost⟩

theorem compose_correct (second : Bool) (caller : NState) (e1 e2 e3 e4 : NExpr) (v1 n1 v2 n2 : Int)
    (h1 : e1.scalarOnly = true) (h2 : e2.scalarOnly = true)
    (h3 : e3.scalarOnly = true) (h4 : e4.scalarOnly = true)
    (t1 : e1.resultType = s64) (t2 : e2.resultType = bl)
    (t3 : e3.resultType = s64) (t4 : e4.resultType = bl)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some n1)
    (d3 : e3.denote (envOf caller) = some v2) (d4 : e4.denote (envOf caller) = some n2)
    (g1 : s64.valid v1 = true) (g2 : bl.valid n1 = true)
    (g3 : s64.valid v2 = true) (g4 : bl.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := if second then OriginalSetSum.RangeSet_compose_noop else OriginalSetSum.RangeSet_compose_v
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e1,.value e2,.value e3,.value e4] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2,.value e3,.value e4] =
        .finished (res,.scalar (if n1 ≠ 0 then (if second then n2 else v2) else (if second then n1 else v1))) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes+e3.nodes+e4.nodes) 70 caller.scalars.memory := by
  let prog := if second then OriginalSetSum.RangeSet_compose_noop else OriginalSetSum.RangeSet_compose_v
  refine four_values_body_correct prog (if second then bl else s64)
    (by cases second <;> rfl) (by cases second <;> rfl) (by cases second <;> decide)
    caller e1 e2 e3 e4 v1 n1 v2 n2 _ h1 h2 h3 h4 t1 t2 t3 t4 d1 d2 d3 d4 g1 g2 g3 g4
    (by
      cases second
      · change s64.valid (if n1 ≠ 0 then v2 else v1) = true
        split <;> assumption
      · change bl.valid (if n1 ≠ 0 then n2 else n1) = true
        split <;> assumption) valid lengths strict base ?_
  intro M hM
  subst hM
  let Q := callerP caller
  let M := Q ++ [(⟨s64,v1⟩ : Cell),⟨bl,n1⟩,⟨s64,v2⟩,⟨bl,n2⟩]
  obtain ⟨r,ran,ret,cost,need,ps⟩ := compose_exec M Q.length (Q.length+1) (Q.length+2) (Q.length+3)
    v1 n1 v2 n2 second (by simp [M]) (by simp [M]) (by simp [M]) (by simp [M]) g1 g2 g3 g4
  refine ⟨r,ran,ret,cost,need,?_⟩
  rw [ps]
  exact take_P caller _

end SetComposeCallerAudit
