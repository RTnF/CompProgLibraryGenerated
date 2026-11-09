namespace SetValueCtorAudit
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

def newValueBody (second : Bool) : Command :=
  .sequence (.primitive (.declare s64 true (.variable s64 0)))
    (copyBody 2 s64 bl (.variable s64 1) (.literal bl 0) second)

theorem new_value_exec (P : List Cell) (a : Nat) (v : Int) (second : Bool)
    (cell : P[a]? = some ⟨s64,v⟩) (hv : s64.valid v = true) :
    ∃ r, pexec 1 (newValueBody second) ⟨P,[⟨a,true⟩]⟩ = some r ∧
      r.ret = some (if second then 0 else v) ∧ r.cost ≤ 20 ∧
      r.need ≤ P.length+40 ∧ r.ps.mem = P ++ [⟨s64,v⟩,⟨s64,v⟩,⟨bl,0⟩] := by
  let R : List CppState.Binding := [⟨a,true⟩]
  let M := P ++ [(⟨s64,v⟩ : Cell)]
  let B : List CppState.Binding := [⟨a,true⟩,⟨P.length,true⟩]
  have d0 : (NExpr.variable s64 0).denote (penv (ws P R [])) = some v := by
    rw [den_variable]; exact ws_env_ref P R [] 0 a true s64 v rfl cell hv
  have first := (pexec_prim 1 _ _).trans (ws_declare P R [] s64 (.variable s64 0) v d0 (Ty.convert_of_valid _ _ hv))
  have d1 : (NExpr.variable s64 1).denote (penv (ws M B [])) = some v := by
    rw [den_variable]
    exact ws_env_ref M B [] 1 P.length true s64 v rfl (by simp [M]) hv
  obtain ⟨r,ran,ret,cost,need,ps⟩ := copy_exec M B s64 bl (.variable s64 1) (.literal bl 0) v 0 second hv rfl d1 rfl
  have rest : pexec 1 (copyBody 2 s64 bl (.variable s64 1) (.literal bl 0) second)
      (ws P R [⟨s64,v⟩]) = some r := by
    simpa [M,B,R,ws] using ran
  have all := seq_some first rfl rest
  refine ⟨⟨r.ps,r.ret,2+r.cost,max (P.length+6) r.need⟩,?_,ret,?_,?_,?_⟩
  · simpa [newValueBody,R,ws_nil,NExpr.nodes] using all
  · simp [NExpr.nodes] at cost ⊢
    omega
  · simp [M,B,NExpr.nodes] at need ⊢
    omega
  · rw [ps]
    simp [ws,M,List.append_assoc]

theorem one_value_body_correct (prog : NProgram) (ty : Ty) (rv : Int)
    (hp : prog.parameters = [.scalar s64 false true]) (hr : prog.result = .scalar ty)
    (hbody : Scalar prog.body = true) (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (ht : e.resultType = s64) (den : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (hrv : ty.valid rv = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hex : ∀ M : List Cell, M = callerP caller ++ [⟨s64,v⟩] →
      ∃ r, pexec 1 prog.body ⟨M,[⟨(callerP caller).length,true⟩]⟩ = some r ∧
        r.ret = some rv ∧ r.cost ≤ 20 ∧ r.need ≤ M.length+40 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e] = some Sinit ∧
      prog.callFuel fuel caller [.value e] = .finished (res,.scalar rv) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeak0⟩ :=
    prep_val caller _ s64 hp e v hs ht den valid hv
  let M := callerP caller ++ [(⟨s64,v⟩ : Cell)]
  let B : List CppState.Binding := [⟨(callerP caller).length,true⟩]
  have takeM : M.take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  obtain ⟨r,ran,ret,cost,need,mem⟩ := hex M rfl
  have gw := good.2.2.1
  have post := call_scalar caller prog [.value e] Sinit M B
    hprep (by rw [sSlots];rfl) sMem sBind sBase sScope sFrame (by omega)
    (by simp [M,callerP]) (by rw [takeM]) valid lengths strict base hbody 1 r ran rv ret ty hr hrv
    (by simp [M] at need;omega) (by simp [M,B]) e.nodes 70 (by omega)
  obtain ⟨fuel,res,hrun,hpost⟩ := post
  exact ⟨Sinit,fuel,res,hprep,hrun,by simpa only [mem] using hpost⟩

theorem new_value_correct (second : Bool) (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (ht : e.resultType = s64) (den : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := if second then OriginalSetSum.RangeSet_new0_noop else OriginalSetSum.RangeSet_new0_v
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e] = some Sinit ∧
      prog.callFuel fuel caller [.value e] = .finished (res,.scalar (if second then 0 else v)) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory := by
  let prog := if second then OriginalSetSum.RangeSet_new0_noop else OriginalSetSum.RangeSet_new0_v
  refine one_value_body_correct prog (if second then bl else s64) (if second then 0 else v)
    (by cases second <;> rfl) (by cases second <;> rfl) (by cases second <;> decide)
    caller e v hs ht den hv (by
      cases second
      · exact hv
      · change bl.valid 0 = true
        rfl) valid lengths strict base ?_
  intro M hM
  subst hM
  obtain ⟨r,ran,ret,cost,need,mem⟩ := new_value_exec (callerP caller ++ [⟨s64,v⟩])
    (callerP caller).length v second (by simp) hv
  have body : prog.body = newValueBody second := by cases second <;> rfl
  refine ⟨r,?_,ret,cost,need,?_⟩
  · rw [body]; exact ran
  · rw [mem]
    simpa [List.append_assoc] using take_P caller [⟨s64,v⟩,⟨s64,v⟩,⟨s64,v⟩,⟨bl,0⟩]

end SetValueCtorAudit
