import Proofs.UfFieldsUnite

namespace Proofs.UfMethodPreparePeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.UfRootCall Proofs.UfFindCall
open Proofs.UfCompression Proofs.VectorFillCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedCall Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppNestedStmt
open Proofs.IntSim Proofs.CppNestedFacts
open Proofs.CppNestedRows
open Proofs.VecKit
open Proofs.QuotientFrame Proofs.DoublingCall Proofs.ScalarCall Proofs.ExtremaCall Proofs.VecWriteCall

open Proofs.VecKitW Proofs.PowModStep
open Proofs.UfClassInvariant Proofs.UfFieldsUnite

theorem prepare_counter_peak (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (en : NExpr) (n : Int) (ns : en.scalarOnly = true)
    (nt : en.resultType = i32)
    (nv : en.denote (envOf caller) = some n)
    (nvalid : i32.valid n = true) :
    ∃ Sinit : NState, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters
      [.vectorReference vslot,.scalarReference cslot,.value en] = some Sinit ∧
      Sinit.scalars.peak ≤ max caller.scalars.peak (liveS caller+caller.frame.bindings.length+en.nodes+12) := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector i32 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 true) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  let charged := (caller.charge 1 1).charge 1 1
  have rcount : resolve (caller.charge 1 1) (.scalar i32 true true) (.scalarReference cslot) =
      some (charged,.scalarAddress i32 countBinding.address true) := by
    have same : (caller.charge 1 1).scalarCell cslot i32 = some (countBinding,⟨i32,count⟩) := cell
    simp [resolve,same,writable,charged]
  have core0 : Core caller charged := (core_charge caller 1 1).trans (core_charge (caller.charge 1 1) 1 1)
  obtain ⟨qn,nrun,ngood⟩ := scalar_eval en charged n ns (by rw [envOf_core core0]; exact nv)
  have coreN : Core caller qn := core0.trans ngood.1
  have rn : resolve charged (.scalar i32 false true) (.value en) = some (qn,.scalar i32 true n) := by
    simp [resolve,nt,nrun]
  obtain ⟨cf,_,_,cm,cb,ck⟩ := coreN
  obtain ⟨_,_,_,found,_,cvalid⟩ := scalarCell_facts cell
  have inside : countBinding.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp found).1
  have inPrefix : (callerP caller)[countBinding.address]? = some ⟨i32,count⟩ := by
    rw [callerP,List.getElem?_append_left inside]
    exact found
  have fs : qn.frame.state = caller.frame.state := by rw [cf]
  have fr : qn.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : qn.frame.bindings = caller.frame.bindings := by rw [cf]
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩,0) := by
    have obj : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) := object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have rooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have maximum : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths rooted ok.flag
    simp only [Frame.bindRoot,obj,maximum,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters =
      [.vector i32 true,.scalar i32 true true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,rcount,rn]
  simp only [callerP] at inPrefix
  simp [fs,fr,fb,cm,cb,ck,bound,bindAll,bindOne,CppState.bindArgument,nvalid,cvalid,
    inPrefix,NState.observe,CppState.State.observe,callerP,liveS]
  have scalarPeak := ngood.2.2.2.2.2.1
  simp only [charged,NState.charge,NState.observe,CppState.State.observe,liveS] at scalarPeak
  have baseline := ok.base
  omega


theorem prepare_fields_peak (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (en ea : NExpr) (n a : Int) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32)
    (nv : en.denote (envOf caller) = some n) (av : ea.denote (envOf caller) = some a)
    (nvalid : i32.valid n = true) (avalid : i32.valid a = true) :
    ∃ Sinit : NState, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_root.parameters
      [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = some Sinit ∧
      Sinit.scalars.peak ≤ max caller.scalars.peak (liveS caller+caller.frame.bindings.length+en.nodes+ea.nodes+12) := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector i32 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 true) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  let charged := (caller.charge 1 1).charge 1 1
  have rcount : resolve (caller.charge 1 1) (.scalar i32 true true) (.scalarReference cslot) =
      some (charged,.scalarAddress i32 countBinding.address true) := by
    have same : (caller.charge 1 1).scalarCell cslot i32 = some (countBinding,⟨i32,count⟩) := cell
    simp [resolve,same,writable,charged]
  have core0 : Core caller charged := (core_charge caller 1 1).trans (core_charge (caller.charge 1 1) 1 1)
  obtain ⟨qn,nrun,ngood⟩ := scalar_eval en charged n ns (by rw [envOf_core core0]; exact nv)
  have coreN : Core caller qn := core0.trans ngood.1
  obtain ⟨qa,arun,agood⟩ := scalar_eval ea qn a as_ (by rw [envOf_core coreN]; exact av)
  have coreA : Core caller qa := coreN.trans agood.1
  have rn : resolve charged (.scalar i32 false true) (.value en) = some (qn,.scalar i32 true n) := by
    simp [resolve,nt,nrun]
  have ra : resolve qn (.scalar i32 false true) (.value ea) = some (qa,.scalar i32 true a) := by
    simp [resolve,at_,arun]
  obtain ⟨cf,_,_,cm,cb,ck⟩ := coreA
  obtain ⟨_,_,_,found,_,cvalid⟩ := scalarCell_facts cell
  have inside : countBinding.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp found).1
  have inPrefix : (callerP caller)[countBinding.address]? = some ⟨i32,count⟩ := by
    rw [callerP,List.getElem?_append_left inside]
    exact found
  have fs : qa.frame.state = caller.frame.state := by rw [cf]
  have fr : qa.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : qa.frame.bindings = caller.frame.bindings := by rw [cf]
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩,0) := by
    have obj : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) := object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have rooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have maximum : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths rooted ok.flag
    simp only [Frame.bindRoot,obj,maximum,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.UnionFindCandidateInstance.UnionFind_root.parameters =
      [.vector i32 true,.scalar i32 true true,.scalar i32 false true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,rcount,rn,ra]
  simp only [callerP] at inPrefix
  simp [fs,fr,fb,cm,cb,ck,bound,bindAll,bindOne,CppState.bindArgument,nvalid,avalid,cvalid,
    inPrefix,NState.observe,CppState.State.observe,callerP,liveS]
  have pn := ngood.2.2.2.2.2.1
  have pa := agood.2.2.2.2.2.1
  have liveN : liveS qn = liveS caller := by
    obtain ⟨_,_,_,hm,hb,hbase⟩ := coreN
    simp only [liveS,hm,hb,hbase]
  simp only [charged,NState.charge,NState.observe,CppState.State.observe,liveS] at pn
  rw [liveN] at pa
  have baseline := ok.base
  unfold liveS at *
  clear * - pn pa baseline
  omega


theorem prepare_same_peak (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (en ea eb : NExpr) (n a b : Int) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true) (bs_ : eb.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32) (bt_ : eb.resultType = i32)
    (nv : en.denote (envOf caller) = some n) (av : ea.denote (envOf caller) = some a) (bv : eb.denote (envOf caller) = some b)
    (nvalid : i32.valid n = true) (avalid : i32.valid a = true) (bvalid : i32.valid b = true) :
    ∃ Sinit : NState, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_same.parameters
      [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = some Sinit ∧
      Sinit.scalars.peak ≤ max caller.scalars.peak (liveS caller+caller.frame.bindings.length+en.nodes+ea.nodes+eb.nodes+12) := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector i32 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 true) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  let charged := (caller.charge 1 1).charge 1 1
  have rcount : resolve (caller.charge 1 1) (.scalar i32 true true) (.scalarReference cslot) =
      some (charged,.scalarAddress i32 countBinding.address true) := by
    have same : (caller.charge 1 1).scalarCell cslot i32 = some (countBinding,⟨i32,count⟩) := cell
    simp [resolve,same,writable,charged]
  have core0 : Core caller charged := (core_charge caller 1 1).trans (core_charge (caller.charge 1 1) 1 1)
  obtain ⟨qn,nrun,ngood⟩ := scalar_eval en charged n ns (by rw [envOf_core core0]; exact nv)
  have coreN : Core caller qn := core0.trans ngood.1
  obtain ⟨qa,arun,agood⟩ := scalar_eval ea qn a as_ (by rw [envOf_core coreN]; exact av)
  have coreA : Core caller qa := coreN.trans agood.1
  obtain ⟨qb,brun,bgood⟩ := scalar_eval eb qa b bs_ (by rw [envOf_core coreA]; exact bv)
  have coreB : Core caller qb := coreA.trans bgood.1
  have rn : resolve charged (.scalar i32 false true) (.value en) = some (qn,.scalar i32 true n) := by
    simp [resolve,nt,nrun]
  have ra : resolve qn (.scalar i32 false true) (.value ea) = some (qa,.scalar i32 true a) := by
    simp [resolve,at_,arun]
  have rb : resolve qa (.scalar i32 false true) (.value eb) = some (qb,.scalar i32 true b) := by
    simp [resolve,bt_,brun]
  obtain ⟨cf,_,_,cm,cb,ck⟩ := coreB
  obtain ⟨_,_,_,found,_,cvalid⟩ := scalarCell_facts cell
  have inside : countBinding.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp found).1
  have inPrefix : (callerP caller)[countBinding.address]? = some ⟨i32,count⟩ := by
    rw [callerP,List.getElem?_append_left inside]
    exact found
  have fs : qb.frame.state = caller.frame.state := by rw [cf]
  have fr : qb.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : qb.frame.bindings = caller.frame.bindings := by rw [cf]
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩,0) := by
    have obj : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) := object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have rooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have maximum : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths rooted ok.flag
    simp only [Frame.bindRoot,obj,maximum,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.UnionFindCandidateInstance.UnionFind_same.parameters =
      [.vector i32 true,.scalar i32 true true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,rcount,rn,ra,rb]
  simp only [callerP] at inPrefix
  simp [fs,fr,fb,cm,cb,ck,bound,bindAll,bindOne,CppState.bindArgument,nvalid,avalid,bvalid,cvalid,
    inPrefix,NState.observe,CppState.State.observe,callerP,liveS]
  have pn := ngood.2.2.2.2.2.1
  have pa := agood.2.2.2.2.2.1
  have pb := bgood.2.2.2.2.2.1
  have liveN : liveS qn = liveS caller := by
    obtain ⟨_,_,_,hm,hb,hbase⟩ := coreN
    simp only [liveS,hm,hb,hbase]
  have liveA : liveS qa = liveS caller := by
    obtain ⟨_,_,_,hm,hb,hbase⟩ := coreA
    simp only [liveS,hm,hb,hbase]
  simp only [charged,NState.charge,NState.observe,CppState.State.observe,liveS] at pn
  rw [liveN] at pa
  rw [liveA] at pb
  have baseline := ok.base
  unfold liveS at *
  clear * - pn pa pb baseline
  omega

end Proofs.UfMethodPreparePeak
