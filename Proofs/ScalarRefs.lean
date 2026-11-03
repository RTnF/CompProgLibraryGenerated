import Proofs.IntervalCall

namespace Proofs.ScalarRefs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCall
open Proofs.GroupCall
open Proofs.CppState (Cell)

theorem prep_refs4t (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (t2 : Ty) (t3 : Ty) (t4 : Ty) (s1 : Nat) (s2 : Nat) (s3 : Nat) (s4 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (b3 : CppState.Binding) (b4 : CppState.Binding) (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int)
    (hp : params = [.scalar t1 true false,.scalar t2 true false,.scalar t3 true false,.scalar t4 true false])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (c3 : caller.scalarCell s3 t3 = some (b3,⟨t3,v3⟩))
    (c4 : caller.scalarCell s4 t4 = some (b4,⟨t4,v4⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+9 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  obtain ⟨i3,_,_,m3,_,w3⟩ := scalarCell_facts c3
  obtain ⟨i4,_,_,m4,_,w4⟩ := scalarCell_facts c4
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have l3 : b3.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m3).1
  have l4 : b4.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m4).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have c3' : ((caller.charge 1 1).charge 1 1).scalarCell s3 t3 = some (b3,⟨t3,v3⟩) := c3
  have c4' : (((caller.charge 1 1).charge 1 1).charge 1 1).scalarCell s4 t4 = some (b4,⟨t4,v4⟩) := c4
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have h2 := pad t2 b2 v2 l2 m2
  have h3 := pad t3 b3 v3 l3 m3
  have h4 := pad t4 b4 v4 l4 m4
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,c1,c2',c3',c4']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,h3,h4,w1,w2,w3,w4]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  repeat first
    | exact Nat.le_max_left _ _
    | (apply Nat.le_trans (Nat.le_max_left _ _); skip)

theorem refs4t_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (t2 : Ty) (t3 : Ty) (t4 : Ty)
    (hp : prog.parameters = [.scalar t1 true false,.scalar t2 true false,.scalar t3 true false,.scalar t4 true false])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (s2 : Nat) (s3 : Nat) (s4 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (b3 : CppState.Binding) (b4 : CppState.Binding) (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (c3 : caller.scalarCell s3 t3 = some (b3,⟨t3,v3⟩))
    (c4 : caller.scalarCell s4 t4 = some (b4,⟨t4,v4⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_refs4t caller _ t1 t2 t3 t4 s1 s2 s3 s4 b1 b2 b3 b4 v1 v2 v3 v4 hp c1 c2 c3 c4 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] Sinit
    (callerP caller) [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

theorem prep_refs2t (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 : Ty) (t2 : Ty) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int)
    (hp : params = [.scalar t1 true false,.scalar t2 true false])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2] = some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have h2 := pad t2 b2 v2 l2 m2
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,c1,c2']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,w1,w2]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  repeat first
    | exact Nat.le_max_left _ _
    | (apply Nat.le_trans (Nat.le_max_left _ _); skip)

theorem refs2t_correct (prog : NProgram) (tn : Ty)
    (t1 : Ty) (t2 : Ty)
    (hp : prog.parameters = [.scalar t1 true false,.scalar t2 true false])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 : Nat) (s2 : Nat) (b1 : CppState.Binding) (b2 : CppState.Binding) (v1 : Int) (v2 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨b2.address,false⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_refs2t caller _ t1 t2 s1 s2 b1 b2 v1 v2 hp c1 c2 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2] Sinit
    (callerP caller) [⟨b1.address,false⟩,⟨b2.address,false⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

end Proofs.ScalarRefs
