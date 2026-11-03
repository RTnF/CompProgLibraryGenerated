import Proofs.ScalarRefs

namespace Proofs.ScalarRefsV
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCall
open Proofs.GroupCall
open Proofs.CppState (Cell)

theorem prep_R1V1 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (u1 : Ty) (s1 : Nat) (b1 : CppState.Binding) (v1 : Int) (e1 : NExpr) (n1 : Int)
    (hp : params = [.scalar t1 true false,.scalar u1 false true])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work + 1 + e1.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.value e1] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u1,n1⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩] ∧
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
  have res1 : resolve caller (.scalar t1 true false) (.scalarReference s1) =
      some ((caller.charge 1 1),.scalarAddress t1 b1.address false) := by simp [resolve,c1]
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

theorem prep_R2V1 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (t2 : Ty) (u1 : Ty) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int) (e1 : NExpr) (n1 : Int)
    (hp : params = [.scalar t1 true false,.scalar t2 true false,.scalar u1 false true])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work + 2 + e1.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.value e1] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u1,n1⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = q.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreC : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge (caller.charge 1 1) 1 1))
  obtain ⟨q1,ran1,good1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) n1 hs1 (by rw [envOf_core coreC]; exact value1)
  have core1 : Core caller q1 := coreC.trans good1.1
  obtain ⟨cf,_,_,cm,cb,ck⟩ := core1
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have fs : q1.frame.state = caller.frame.state := by rw [cf]
  have fr : q1.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : q1.frame.bindings = caller.frame.bindings := by rw [cf]
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have h2 := pad t2 b2 v2 l2 m2
  have res1 : resolve caller (.scalar t1 true false) (.scalarReference s1) =
      some ((caller.charge 1 1),.scalarAddress t1 b1.address false) := by simp [resolve,c1]
  have res2 : resolve (caller.charge 1 1) (.scalar t2 true false) (.scalarReference s2) =
      some (((caller.charge 1 1).charge 1 1),.scalarAddress t2 b2.address false) := by simp [resolve,c2']
  have resv1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar u1 false true) (.value e1) = some (q1,.scalar u1 true n1) := by
    simp [resolve,hty1,ran1]
  refine ⟨q1,?_,?_⟩
  · have g1 := good1.2.2.1
    
    simp only [NState.charge, NState.observe, CppState.State.observe] at *
    omega
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2,resv1]
  simp [fs,fr,fb,cm,cb,ck,bindAll,bindOne,CppState.bindArgument,nv1,callerP,NState.observe,
    CppState.State.observe,h1,h2,w1,w2]
  have g1 := good1.2.2.2.2.1
  simp only [NState.charge, NState.observe, CppState.State.observe] at g1 ⊢
  omega

theorem prep_R1V2 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (u1 : Ty) (u2 : Ty) (s1 : Nat) (b1 : CppState.Binding) (v1 : Int) (e1 : NExpr) (n1 : Int) (e2 : NExpr) (n2 : Int)
    (hp : params = [.scalar t1 true false,.scalar u1 false true,.scalar u2 false true])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (hs2 : e2.scalarOnly = true) (hty2 : e2.resultType = u2)
    (value2 : e2.denote (envOf caller) = some n2) (nv2 : u2.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work + 1 + e1.nodes+e2.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u1,n1⟩,⟨u2,n2⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = q.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreC : Core caller (caller.charge 1 1) := (core_charge caller 1 1)
  obtain ⟨q1,ran1,good1⟩ := scalar_eval e1 (caller.charge 1 1) n1 hs1 (by rw [envOf_core coreC]; exact value1)
  have core1 : Core caller q1 := coreC.trans good1.1
  obtain ⟨q2,ran2,good2⟩ := scalar_eval e2 q1 n2 hs2 (by rw [envOf_core core1]; exact value2)
  have core2 : Core caller q2 := core1.trans good2.1
  obtain ⟨cf,_,_,cm,cb,ck⟩ := core2
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1

  have fs : q2.frame.state = caller.frame.state := by rw [cf]
  have fr : q2.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : q2.frame.bindings = caller.frame.bindings := by rw [cf]
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have res1 : resolve caller (.scalar t1 true false) (.scalarReference s1) =
      some ((caller.charge 1 1),.scalarAddress t1 b1.address false) := by simp [resolve,c1]
  have resv1 : resolve (caller.charge 1 1) (.scalar u1 false true) (.value e1) = some (q1,.scalar u1 true n1) := by
    simp [resolve,hty1,ran1]
  have resv2 : resolve q1 (.scalar u2 false true) (.value e2) = some (q2,.scalar u2 true n2) := by
    simp [resolve,hty2,ran2]
  refine ⟨q2,?_,?_⟩
  · have g1 := good1.2.2.1
    have g2 := good2.2.2.1
    simp only [NState.charge, NState.observe, CppState.State.observe] at *
    omega
  rw [hp]
  simp [prepare,valid,resolveAll,res1,resv1,resv2]
  simp [fs,fr,fb,cm,cb,ck,bindAll,bindOne,CppState.bindArgument,nv1,nv2,callerP,NState.observe,
    CppState.State.observe,h1,w1]
  have g1 := good1.2.2.2.2.1
  have g2 := good2.2.2.2.2.1
  simp only [NState.charge, NState.observe, CppState.State.observe] at g1 g2 ⊢
  omega

theorem prep_R2V2 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (t2 : Ty) (u1 : Ty) (u2 : Ty) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int) (e1 : NExpr) (n1 : Int) (e2 : NExpr) (n2 : Int)
    (hp : params = [.scalar t1 true false,.scalar t2 true false,.scalar u1 false true,.scalar u2 false true])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (hs2 : e2.scalarOnly = true) (hty2 : e2.resultType = u2)
    (value2 : e2.denote (envOf caller) = some n2) (nv2 : u2.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work + 2 + e1.nodes+e2.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u1,n1⟩,⟨u2,n2⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = q.scalars.work+5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreC : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge (caller.charge 1 1) 1 1))
  obtain ⟨q1,ran1,good1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) n1 hs1 (by rw [envOf_core coreC]; exact value1)
  have core1 : Core caller q1 := coreC.trans good1.1
  obtain ⟨q2,ran2,good2⟩ := scalar_eval e2 q1 n2 hs2 (by rw [envOf_core core1]; exact value2)
  have core2 : Core caller q2 := core1.trans good2.1
  obtain ⟨cf,_,_,cm,cb,ck⟩ := core2
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have fs : q2.frame.state = caller.frame.state := by rw [cf]
  have fr : q2.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : q2.frame.bindings = caller.frame.bindings := by rw [cf]
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have h2 := pad t2 b2 v2 l2 m2
  have res1 : resolve caller (.scalar t1 true false) (.scalarReference s1) =
      some ((caller.charge 1 1),.scalarAddress t1 b1.address false) := by simp [resolve,c1]
  have res2 : resolve (caller.charge 1 1) (.scalar t2 true false) (.scalarReference s2) =
      some (((caller.charge 1 1).charge 1 1),.scalarAddress t2 b2.address false) := by simp [resolve,c2']
  have resv1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar u1 false true) (.value e1) = some (q1,.scalar u1 true n1) := by
    simp [resolve,hty1,ran1]
  have resv2 : resolve q1 (.scalar u2 false true) (.value e2) = some (q2,.scalar u2 true n2) := by
    simp [resolve,hty2,ran2]
  refine ⟨q2,?_,?_⟩
  · have g1 := good1.2.2.1
    have g2 := good2.2.2.1
    simp only [NState.charge, NState.observe, CppState.State.observe] at *
    omega
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2,resv1,resv2]
  simp [fs,fr,fb,cm,cb,ck,bindAll,bindOne,CppState.bindArgument,nv1,nv2,callerP,NState.observe,
    CppState.State.observe,h1,h2,w1,w2]
  have g1 := good1.2.2.2.2.1
  have g2 := good2.2.2.2.2.1
  simp only [NState.charge, NState.observe, CppState.State.observe] at g1 g2 ⊢
  omega

theorem R1V1_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (u1 : Ty)
    (hp : prog.parameters = [.scalar t1 true false,.scalar u1 false true])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (b1 : CppState.Binding) (v1 : Int) (e1 : NExpr) (n1 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller ++ [(⟨u1,n1⟩ : Cell)] →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.value e1] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.value e1] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res (1+e1.nodes) (C+80) caller.scalars.memory := by
  obtain ⟨q,hq,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_R1V1 caller _ t1 u1 s1 b1 v1 e1 n1 hp c1 hs1 hty1 value1 nv1 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM2 : (callerP caller ++ [(⟨u1,n1⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller ++ [(⟨u1,n1⟩ : Cell)]) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.value e1] Sinit
    (callerP caller ++ [(⟨u1,n1⟩ : Cell)]) [⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by simp; omega) (by rw [takeM2]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by simp at hneed ⊢; omega) (by simp) (1+e1.nodes) (C+80) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

theorem R2V1_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (t2 : Ty) (u1 : Ty)
    (hp : prog.parameters = [.scalar t1 true false,.scalar t2 true false,.scalar u1 false true])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int) (e1 : NExpr) (n1 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller ++ [(⟨u1,n1⟩ : Cell)] →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2,.value e1] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.value e1] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res (2+e1.nodes) (C+80) caller.scalars.memory := by
  obtain ⟨q,hq,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_R2V1 caller _ t1 t2 u1 s1 s2 b1 b2 v1 v2 e1 n1 hp c1 c2 hs1 hty1 value1 nv1 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM2 : (callerP caller ++ [(⟨u1,n1⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller ++ [(⟨u1,n1⟩ : Cell)]) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.value e1] Sinit
    (callerP caller ++ [(⟨u1,n1⟩ : Cell)]) [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by simp; omega) (by rw [takeM2]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by simp at hneed ⊢; omega) (by simp) (2+e1.nodes) (C+80) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

theorem R1V2_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (u1 : Ty) (u2 : Ty)
    (hp : prog.parameters = [.scalar t1 true false,.scalar u1 false true,.scalar u2 false true])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (b1 : CppState.Binding) (v1 : Int) (e1 : NExpr) (n1 : Int) (e2 : NExpr) (n2 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (hs2 : e2.scalarOnly = true) (hty2 : e2.resultType = u2)
    (value2 : e2.denote (envOf caller) = some n2) (nv2 : u2.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)] →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.value e1,.value e2] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res (1+e1.nodes+e2.nodes) (C+80) caller.scalars.memory := by
  obtain ⟨q,hq,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_R1V2 caller _ t1 u1 u2 s1 b1 v1 e1 n1 e2 n2 hp c1 hs1 hty1 value1 nv1 hs2 hty2 value2 nv2 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM2 : (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]) [⟨b1.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by simp; omega) (by rw [takeM2]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by simp at hneed ⊢; omega) (by simp) (1+e1.nodes+e2.nodes) (C+80) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

theorem R2V2_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (t2 : Ty) (u1 : Ty) (u2 : Ty)
    (hp : prog.parameters = [.scalar t1 true false,.scalar t2 true false,.scalar u1 false true,.scalar u2 false true])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int) (e1 : NExpr) (n1 : Int) (e2 : NExpr) (n2 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (hs1 : e1.scalarOnly = true) (hty1 : e1.resultType = u1)
    (value1 : e1.denote (envOf caller) = some n1) (nv1 : u1.valid n1 = true)
    (hs2 : e2.scalarOnly = true) (hty2 : e2.resultType = u2)
    (value2 : e2.denote (envOf caller) = some n2) (nv2 : u2.valid n2 = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)] →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2,.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.value e1,.value e2] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res (2+e1.nodes+e2.nodes) (C+80) caller.scalars.memory := by
  obtain ⟨q,hq,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_R2V2 caller _ t1 t2 u1 u2 s1 s2 b1 b2 v1 v2 e1 n1 e2 n2 hp c1 c2 hs1 hty1 value1 nv1 hs2 hty2 value2 nv2 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM2 : (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨u1,n1⟩ : Cell),(⟨u2,n2⟩ : Cell)]) [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length+0,true⟩,⟨(callerP caller).length+1,true⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by simp; omega) (by rw [takeM2]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by simp at hneed ⊢; omega) (by simp) (2+e1.nodes+e2.nodes) (C+80) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

end Proofs.ScalarRefsV
