namespace GenericRecordApply
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

open Proofs.MonoidCall Proofs.ScalarRefsV

theorem prep_mutable_value (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (u1 : Ty) (s1 : Nat) (b1 : CppState.Binding) (v1 : Int) (e1 : NExpr) (n1 : Int)
    (hp : params = [.scalar t1 true true,.scalar u1 false true])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (writable : b1.writable = true)
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work + 1 + e1.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.value e1] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u1,n1⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,true⟩,⟨(callerP caller).length+0,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = q.scalars.work+3 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreC : Core caller (caller.charge 1 1) := (core_charge caller 1 1)
  obtain ⟨q1,ran1,good1⟩ := scalar_eval e1 (caller.charge 1 1) n1 hs1 (by rw [envOf_core coreC]; exact value1)
  have core1 : Core caller q1 := coreC.trans good1.1
  obtain ⟨cf,_,_,cm,cb,ck⟩ := core1
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1

  have fs : q1.frame.state = caller.frame.state := by rw [cf]
  have fr : q1.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : q1.frame.bindings = caller.frame.bindings := by rw [cf]
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have res1 : resolve caller (.scalar t1 true true) (.scalarReference s1) =
      some ((caller.charge 1 1),.scalarAddress t1 b1.address true) := by simp [resolve,c1,writable]
  have resv1 : resolve (caller.charge 1 1) (.scalar u1 false true) (.value e1) = some (q1,.scalar u1 true n1) := by
    simp [resolve,hty1,ran1]
  refine ⟨q1,?_,?_⟩
  · have g1 := good1.2.2.1

    simp only [NState.charge, NState.observe, CppState.State.observe] at *
    omega
  rw [hp]
  simp [prepare,valid,resolveAll,res1,resv1]
  simp [fs,fr,fb,cm,cb,ck,bindAll,bindOne,CppState.bindArgument,nv1,callerP,NState.observe,
    CppState.State.observe,h1,w1]
  have g1 := good1.2.2.2.2.1
  simp only [NState.charge, NState.observe, CppState.State.observe] at g1 ⊢
  omega


variable (ty : Ty)
abbrev addExpression : NExpr := .binary ty .add (.variable ty 1) (.variable ty 0)
abbrev addBody : Command :=
  .sequence (.primitive (.declare ty true (addExpression ty)))
    (.sequence (.primitive (.declare ty true (.variable ty 2)))
      (.sequence (.primitive (.ret (.variable ty 3))) Sk))

theorem add_exec (P : List Cell) (R : List CppState.Binding) (x y : Int)
    (hR : R.length = 2) (_hx : ty.valid x = true) (_hy : ty.valid y = true)
    (s : Int) (hc : ty.convert (x+y) = some s) (hsum : ty.valid s = true)
    (e0 : penv (ws P R []) 0 ty = some y)
    (e1 : penv (ws P R []) 1 ty = some x) :
    ∃ r, pexec 1 (addBody ty) (ws P R []) = some r ∧ r.ret = some s ∧
      r.cost ≤ 20 ∧ r.need ≤ P.length+40 ∧
      r.ps.mem = P ++ [⟨ty,s⟩,⟨ty,s⟩] := by
  have den : (addExpression ty).denote (penv (ws P R [])) = some s := by
    simp only [NExpr.denote,e0,e1,Option.bind_some,binaryValue]
    exact hc
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R [] ty (addExpression ty) s den (Proofs.GenericCall.convG ty _ hsum))
  have d2 : penv (ws P R [⟨ty,s⟩]) 2 ty = some s := by
    simpa only [hR] using ws_env_loc P R [⟨ty,s⟩] 0 ⟨ty,s⟩ ty rfl rfl hsum
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P R [⟨ty,s⟩] ty (.variable ty 2) s
    (by rw [den_variable]; exact d2) (Proofs.GenericCall.convG ty _ hsum))
  have d3 : penv (ws P R [⟨ty,s⟩,⟨ty,s⟩]) 3 ty = some s := by
    simpa only [hR] using ws_env_loc P R [⟨ty,s⟩,⟨ty,s⟩] 1 ⟨ty,s⟩ ty rfl rfl hsum
  have qr := exec_ret 1 (ws P R [⟨ty,s⟩,⟨ty,s⟩]) (.variable ty 3) s
    (by rw [den_variable]; exact d3)
  refine ⟨_,seq_some q1 rfl (seq_some q2 rfl qr),rfl,?_,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes,ws,hR]
  · simp [ws]

def gRecApply : NProgram :=
  ⟨[.scalar ty true true,.scalar ty false true],.scalar ty,(addBody ty)⟩

theorem apply_correct (caller : NState) (slot : Nat) (binding : CppState.Binding) (v x : Int)
    (cell : caller.scalarCell slot ty = some (binding,⟨ty,v⟩))
    (writable : binding.writable = true) (hv : ty.valid v = true)
    (e : NExpr) (scalar : e.scalarOnly = true) (typed : e.resultType = ty)
    (value : e.denote (envOf caller) = some x) (hx : ty.valid x = true)
    (s : Int) (hc : ty.convert (x+v) = some s) (hsum : ty.valid s = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (gRecApply ty).parameters [.scalarReference slot,.value e] = some Sinit ∧
      (gRecApply ty).callFuel fuel caller [.scalarReference slot,.value e] = .finished (res,.scalar s) ∧
      ScalarPost2 caller Sinit res (1+e.nodes) 100 caller.scalars.memory := by
  obtain ⟨q,qWork,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_mutable_value caller _ ty ty slot binding v e x rfl cell writable scalar typed value hx valid
  let P := callerP caller ++ [⟨ty,x⟩]
  let R : List CppState.Binding := [⟨binding.address,true⟩,⟨(callerP caller).length,true⟩]
  have ev : penv (ws P R []) 0 ty = some v := by
    rw [ws_nil]
    exact penv_ok _ 0 ty ⟨binding.address,true⟩ ⟨ty,v⟩ rfl
      (by exact Proofs.MonoidLazyCall.refVal caller slot ty binding v cell [⟨ty,x⟩]) rfl hv
  have ex : penv (ws P R []) 1 ty = some x := by
    rw [ws_nil]
    exact penv_ok _ 1 ty ⟨(callerP caller).length,true⟩ ⟨ty,x⟩ rfl (by simp [P]) rfl hx
  obtain ⟨r,ran,ret,cost,need,mem⟩ := add_exec ty P R x v rfl hx hv s hc hsum ev ex
  have body : (gRecApply ty).body = (addBody ty) := rfl
  have hex : pexec 1 (gRecApply ty).body ⟨P,R⟩ = some r := by rw [body]; simpa only [ws_nil] using ran
  have takeM : P.take caller.scalars.memory.length = caller.scalars.memory := Proofs.MonoidCallCore.take_P caller _
  have takeR : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; simpa only [P,List.append_assoc] using Proofs.MonoidCallCore.take_P caller ([⟨ty,x⟩]++[⟨ty,s⟩,⟨ty,s⟩])
  have hlen : P.length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length)+1 := by simp [P,callerP]; omega
  have plen : P.length = (callerP caller).length+1 := by simp [P]
  have post := call_scalar caller (gRecApply ty) [.scalarReference slot,.value e] Sinit P R
    hprep (by rw [sSlots];rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base (by simp [gRecApply, addBody, addExpression, Scalar, NExpr.scalarOnly]) 1 r hex s ret ty rfl hsum
    (by omega) (by simp [R]; omega) (1+e.nodes) 100 (by omega)
  obtain ⟨fuel,res,hrun,hpost⟩ := post
  exact ⟨Sinit,fuel,res,hprep,hrun,by simpa only [takeR] using hpost⟩

end GenericRecordApply
