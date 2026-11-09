namespace RecordApplyAudit
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


abbrev addExpression : NExpr := .binary s64 .add (.variable s64 1) (.variable s64 0)
abbrev addBody : Command :=
  .sequence (.primitive (.declare s64 true addExpression))
    (.sequence (.primitive (.declare s64 true (.variable s64 2)))
      (.sequence (.primitive (.ret (.variable s64 3))) Sk))

theorem add_exec (P : List Cell) (R : List CppState.Binding) (x y : Int)
    (hR : R.length = 2) (_hx : s64.valid x = true) (_hy : s64.valid y = true)
    (hsum : s64.valid (x+y) = true)
    (e0 : penv (ws P R []) 0 s64 = some y)
    (e1 : penv (ws P R []) 1 s64 = some x) :
    ∃ r, pexec 1 addBody (ws P R []) = some r ∧ r.ret = some (x+y) ∧
      r.cost ≤ 20 ∧ r.need ≤ P.length+40 ∧
      r.ps.mem = P ++ [⟨s64,x+y⟩,⟨s64,x+y⟩] := by
  have den : addExpression.denote (penv (ws P R [])) = some (x+y) := by
    simp only [NExpr.denote,e0,e1,Option.bind_some,binaryValue]
    exact convS _ hsum
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R [] s64 addExpression (x+y) den (convS _ hsum))
  have d2 : penv (ws P R [⟨s64,x+y⟩]) 2 s64 = some (x+y) := by
    simpa only [hR] using ws_env_loc P R [⟨s64,x+y⟩] 0 ⟨s64,x+y⟩ s64 rfl rfl hsum
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P R [⟨s64,x+y⟩] s64 (.variable s64 2) (x+y)
    (by rw [den_variable]; exact d2) (convS _ hsum))
  have d3 : penv (ws P R [⟨s64,x+y⟩,⟨s64,x+y⟩]) 3 s64 = some (x+y) := by
    simpa only [hR] using ws_env_loc P R [⟨s64,x+y⟩,⟨s64,x+y⟩] 1 ⟨s64,x+y⟩ s64 rfl rfl hsum
  have qr := exec_ret 1 (ws P R [⟨s64,x+y⟩,⟨s64,x+y⟩]) (.variable s64 3) (x+y)
    (by rw [den_variable]; exact d3)
  refine ⟨_,seq_some q1 rfl (seq_some q2 rfl qr),rfl,?_,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes,ws,hR]
  · simp [ws]

abbrev applyMax := OriginalRecordApply.RangeAdd_apply__template_RangeAddRangeMaxMin_long_long___RangeMax
abbrev applyMin := OriginalRecordApply.RangeAdd_apply__template_RangeAddRangeMaxMin_long_long___RangeMin

theorem apply_same : applyMax = applyMin := rfl

theorem apply_correct (caller : NState) (slot : Nat) (binding : CppState.Binding) (v x : Int)
    (cell : caller.scalarCell slot s64 = some (binding,⟨s64,v⟩))
    (writable : binding.writable = true) (hv : s64.valid v = true)
    (e : NExpr) (scalar : e.scalarOnly = true) (typed : e.resultType = s64)
    (value : e.denote (envOf caller) = some x) (hx : s64.valid x = true)
    (hsum : s64.valid (x+v) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller applyMax.parameters [.scalarReference slot,.value e] = some Sinit ∧
      applyMax.callFuel fuel caller [.scalarReference slot,.value e] = .finished (res,.scalar (x+v)) ∧
      ScalarPost2 caller Sinit res (1+e.nodes) 100 caller.scalars.memory := by
  obtain ⟨q,qWork,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_mutable_value caller _ s64 s64 slot binding v e x rfl cell writable scalar typed value hx valid
  let P := callerP caller ++ [⟨s64,x⟩]
  let R : List CppState.Binding := [⟨binding.address,true⟩,⟨(callerP caller).length,true⟩]
  have ev : penv (ws P R []) 0 s64 = some v := by
    rw [ws_nil]
    exact penv_ok _ 0 s64 ⟨binding.address,true⟩ ⟨s64,v⟩ rfl
      (by exact Proofs.MonoidLazyCall.refVal caller slot s64 binding v cell [⟨s64,x⟩]) rfl hv
  have ex : penv (ws P R []) 1 s64 = some x := by
    rw [ws_nil]
    exact penv_ok _ 1 s64 ⟨(callerP caller).length,true⟩ ⟨s64,x⟩ rfl (by simp [P]) rfl hx
  obtain ⟨r,ran,ret,cost,need,mem⟩ := add_exec P R x v rfl hx hv hsum ev ex
  have body : applyMax.body = addBody := rfl
  have hex : pexec 1 applyMax.body ⟨P,R⟩ = some r := by rw [body]; simpa only [ws_nil] using ran
  have takeM : P.take caller.scalars.memory.length = caller.scalars.memory := Proofs.MonoidCallCore.take_P caller _
  have takeR : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]; simpa only [P,List.append_assoc] using Proofs.MonoidCallCore.take_P caller ([⟨s64,x⟩]++[⟨s64,x+v⟩,⟨s64,x+v⟩])
  have hlen : P.length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length)+1 := by simp [P,callerP]; omega
  have plen : P.length = (callerP caller).length+1 := by simp [P]
  have post := call_scalar caller applyMax [.scalarReference slot,.value e] Sinit P R
    hprep (by rw [sSlots];rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base (by decide) 1 r hex (x+v) ret s64 rfl hsum
    (by omega) (by simp [R]; omega) (1+e.nodes) 100 (by omega)
  obtain ⟨fuel,res,hrun,hpost⟩ := post
  exact ⟨Sinit,fuel,res,hprep,hrun,by simpa only [takeR] using hpost⟩

theorem apply_min_correct (caller : NState) (slot : Nat) (binding : CppState.Binding) (v x : Int)
    (cell : caller.scalarCell slot s64 = some (binding,⟨s64,v⟩))
    (writable : binding.writable = true) (hv : s64.valid v = true)
    (e : NExpr) (scalar : e.scalarOnly = true) (typed : e.resultType = s64)
    (value : e.denote (envOf caller) = some x) (hx : s64.valid x = true)
    (hsum : s64.valid (x+v) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller applyMin.parameters [.scalarReference slot,.value e] = some Sinit ∧
      applyMin.callFuel fuel caller [.scalarReference slot,.value e] = .finished (res,.scalar (x+v)) ∧
      ScalarPost2 caller Sinit res (1+e.nodes) 100 caller.scalars.memory := by
  simpa only [apply_same] using apply_correct caller slot binding v x cell writable hv e scalar typed value hx hsum valid lengths strict base

theorem apply_call (fuel : Nat) (caller : NState) (args : List NArgument) :
    applyMax.callFuel fuel caller args = applyMin.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) apply_same

theorem add_new : OriginalRecordApply.RangeAdd_new0 = Proofs.GroupInstance.GroupSum_long_long_new0 := rfl
theorem call_add_new (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeAdd_new0.callFuel fuel caller args = Proofs.GroupInstance.GroupSum_long_long_new0.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) add_new

theorem add_id : OriginalRecordApply.RangeAdd_id = Proofs.GroupInstance.GroupSum_long_long_e := rfl
theorem call_add_id (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeAdd_id.callFuel fuel caller args = Proofs.GroupInstance.GroupSum_long_long_e.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) add_id

theorem max_new0 : OriginalRecordApply.RangeMax_new0 = Proofs.MonoidInstance.MonoidMax_long_long_new0 := rfl
theorem call_max_new0 (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeMax_new0.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMax_long_long_new0.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) max_new0

theorem max_new1 : OriginalRecordApply.RangeMax_new1 = Proofs.MonoidInstance.MonoidMax_long_long_new1 := rfl
theorem call_max_new1 (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeMax_new1.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMax_long_long_new1.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) max_new1

theorem max_e : OriginalRecordApply.RangeMax_e = Proofs.MonoidInstance.MonoidMax_long_long_e := rfl
theorem call_max_e (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeMax_e.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMax_long_long_e.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) max_e

theorem max_op : OriginalRecordApply.RangeMax_op = Proofs.MonoidInstance.op_MonoidMax_long_long := rfl
theorem call_max_op (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeMax_op.callFuel fuel caller args = Proofs.MonoidInstance.op_MonoidMax_long_long.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) max_op

theorem min_new0 : OriginalRecordApply.RangeMin_new0 = Proofs.MonoidInstance.MonoidMin_long_long_new0 := rfl
theorem call_min_new0 (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeMin_new0.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMin_long_long_new0.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) min_new0

theorem min_new1 : OriginalRecordApply.RangeMin_new1 = Proofs.MonoidInstance.MonoidMin_long_long_new1 := rfl
theorem call_min_new1 (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeMin_new1.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMin_long_long_new1.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) min_new1

theorem min_e : OriginalRecordApply.RangeMin_e = Proofs.MonoidInstance.MonoidMin_long_long_e := rfl
theorem call_min_e (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeMin_e.callFuel fuel caller args = Proofs.MonoidInstance.MonoidMin_long_long_e.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) min_e

theorem min_op : OriginalRecordApply.RangeMin_op = Proofs.MonoidInstance.op_MonoidMin_long_long := rfl
theorem call_min_op (fuel : Nat) (caller : NState) (args : List NArgument) :
  OriginalRecordApply.RangeMin_op.callFuel fuel caller args = Proofs.MonoidInstance.op_MonoidMin_long_long.callFuel fuel caller args :=
  congrArg (fun p : NProgram => p.callFuel fuel caller args) min_op

end RecordApplyAudit

namespace RecordComposeAudit
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

theorem compose_correct (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = s64)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : s64.valid x = true) (hy : s64.valid y = true) (hxy : s64.valid (x+y) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller OriginalRecordApply.RangeAdd_compose.parameters [.value e1,.value e2] = some Sinit ∧
      OriginalRecordApply.RangeAdd_compose.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar (x+y)) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory := by
  obtain ⟨q1,q2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_values2 s64 caller _ rfl e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 valid hx hy
  let P := callerP caller ++ [(⟨s64,x⟩ : Cell),⟨s64,y⟩]
  let R : List CppState.Binding := [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
  have e0 : penv (ws P R []) 0 s64 = some x :=
    ws_env_ref P R [] 0 (callerP caller).length true s64 x rfl (by simp [P]) hx
  have e1' : penv (ws P R []) 1 s64 = some y :=
    ws_env_ref P R [] 1 ((callerP caller).length+1) true s64 y rfl (by simp [P]) hy
  obtain ⟨r,ran,ret,cost,need,mem⟩ := shapeA_exec P R Proofs.GroupCall.addE (x+y) hxy (addE_den _ x y e0 e1' hxy) (by decide)
  have ran' : pexec 1 OriginalRecordApply.RangeAdd_compose.body ⟨P,R⟩ = some r := by
    simpa [R,ws_nil,shapeA,Proofs.GroupCall.addE,OriginalRecordApply.RangeAdd_compose] using ran
  have hlen : P.length = (callerP caller).length+2 := by simp [P]
  have takeM : P.take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  have peak1 := g1.2.2.2.2.1
  have peak2 := g2.2.2.2.2.1
  have work1 := g1.2.2.1
  have work2 := g2.2.2.1
  have post := call_scalar caller OriginalRecordApply.RangeAdd_compose [.value e1,.value e2] Sinit P R
    hprep (by rw [sSlots];rfl) sMem sBind sBase sScope sFrame (by omega)
    (by simp [P,callerP]) (by rw [takeM]) valid lengths strict base (by decide) 1 r ran' (x+y) ret s64 rfl hxy
    (by simp [P,R] at need ⊢; omega) (by simp [R];omega) (e1.nodes+e2.nodes) 70 (by omega)
  obtain ⟨fuel,res,hrun,hpost⟩ := post
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [mem] at hpost
  have takeR : (P ++ [(⟨s64,x+y⟩ : Cell),⟨s64,x+y⟩]).take caller.scalars.memory.length = caller.scalars.memory := by
    simpa only [P,List.append_assoc] using Proofs.MonoidCallCore.take_P caller
      ([(⟨s64,x⟩ : Cell),⟨s64,y⟩]++[⟨s64,x+y⟩,⟨s64,x+y⟩])
  simpa only [takeR] using hpost

end RecordComposeAudit
