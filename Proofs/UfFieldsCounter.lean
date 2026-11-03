import Proofs.UfFieldsUnite

namespace Proofs.UfFieldsCounter
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

theorem prepare_counter (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (en : NExpr) (n : Int) (ns : en.scalarOnly = true)
    (nt : en.resultType = i32)
    (nv : en.denote (envOf caller) = some n)
    (nvalid : i32.valid n = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work+2+en.nodes ∧
      ∃ Sinit : NState, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en] = some Sinit ∧
      Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧
      Sinit.scalars.memory = callerP caller ++ [⟨i32,n⟩] ∧
      Sinit.scalars.bindings = [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩ ∧
      Sinit.scalars.work = q.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
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
  refine ⟨qn,?_,?_⟩
  · have wn := ngood.2.2.1
    simp only [charged,NState.charge,NState.observe,CppState.State.observe] at wn
    omega
  · have hp : Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters =
        [.vector i32 true,.scalar i32 true true,.scalar i32 false true] := rfl
    rw [hp]
    simp [prepare,ok.valid,resolveAll,rvec,rcount,rn]
    simp only [callerP] at inPrefix
    simp [fs,fr,fb,cm,cb,ck,bound,bindAll,bindOne,CppState.bindArgument,nvalid,cvalid,
      inPrefix,NState.observe,CppState.State.observe,callerP]
    have pn := ngood.2.2.2.2.1
    simp only [charged,NState.charge,NState.observe,CppState.State.observe] at pn
    omega

def fields (P : List Cell) (counter : Nat) (n : Int) : PS :=
  ⟨P++[⟨i32,n⟩],[⟨counter,true⟩,⟨P.length,true⟩]⟩

theorem body_eq : Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body =
    .sequence (.primitive (.ret (.variable i32 1))) Sk := rfl

theorem body_correct (P : List Cell) (counter : Nat) (n groups : Int) (vec : List Int)
    (found : P[counter]? = some ⟨i32,groups⟩) (valid : i32.valid groups = true) (fuel : Nat) :
    pexecW i32 fuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body (fields P counter n) vec =
      some ⟨fields P counter n,vec,some groups,2,P.length+6,0⟩ := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have env : penv1 (fields P counter n) 1 i32 = some groups := by
    simp [fields,penv1,penv,List.getElem?_append_left inside,found,valid]
  have value : vdenL i32 vec (penv1 (fields P counter n)) (.variable i32 1) = some groups := by
    rw [vdenL_scalar _ _ _ _ rfl]
    exact env
  have returned := seqW_ret (b := Sk) ((pexecW_prim i32 fuel _ _ _).trans
    (pstmtW_ret_ok i32 (fields P counter n) vec (.variable i32 1) groups value)) rfl
  rw [body_eq]
  simpa [fields,vwp,NExpr.nodes] using returned

theorem counter_call (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (vec : List Int) (items : vbuf.items = vec.map Value.integer) (small : vec.length < 18446744073709551616)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32) (owner : vbuf.owner = V)
    (en : NExpr) (n : Int) (scalar : en.scalarOnly = true) (type : en.resultType = i32)
    (value : en.denote (envOf caller) = some n) (nvalid : i32.valid n = true) :
    ∃ Sinit fuel out, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en] = .finished (out,.scalar count) ∧
      out.scalars.bindings = caller.scalars.bindings ∧ out.scalars.baseMemory = caller.scalars.baseMemory ∧
      ScalarPost3 caller Sinit out en.nodes 40 caller.scalars.memory 0 V vec := by
  obtain ⟨q,qwork,Sinit,prep,slots,memory,bindings,base,scopeEq,frame,work0,peak0⟩ :=
    prepare_counter caller ok countBinding count cell writable en n scalar type value nvalid
  obtain ⟨_,_,_,found,_,cvalid⟩ := scalarCell_facts cell
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have countFound : (callerP caller)[countBinding.address]? = some ⟨i32,count⟩ := by
    simpa [callerP,List.getElem?_append_left inside] using found
  let vc : VCtx := ⟨i32,true,true,V,vsc,vbuf,vec,items,fun _ => rfl,small,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have initial : FW vc vec vbuf 0 Sinit.frame := by
    rw [frame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,items,bvalid,limit,owner,small⟩
    intro root scope found
    have := ok.strict root scope found
    show scope < caller.scope+1
    omega
  have prefixLength : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have unchanged : (callerP caller ++ [(⟨i32,n⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    UfRootCall.take_P caller _
  let res : PRW := ⟨fields (callerP caller) countBinding.address n,vec,some count,2,(callerP caller).length+6,0⟩
  have executed : pexecW i32 0 Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body
      (fields (callerP caller) countBinding.address n) vec = some res :=
    body_correct (callerP caller) countBinding.address n count vec countFound cvalid 0
  obtain ⟨fuel,out,call,post⟩ := call_vecw vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_num_groups [.vectorReference vslot,.scalarReference cslot,.value en]
    Sinit (callerP caller ++ [⟨i32,n⟩]) [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    0 res executed count rfl i32 rfl cvalid (by simp [res]) (by simp)
    en.nodes 40 (by simp only [res]; omega)
  have saved : res.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := unchanged
  rw [saved] at post
  have metadata := call_scalar_metadata _ _ _ _ _ _ i32 rfl call
  exact ⟨Sinit,fuel,out,prep,call,metadata.1,metadata.2,post⟩

theorem _root_.Proofs.UfClassInvariant.Valid.root_representative {vec : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid vec groups rank) (i : Nat) (inside : i < vec.length) :
    ∃! r, r ∈ roots vec ∧ Reach vec i r := by
  classical
  obtain ⟨out,r,run,ret,reach,ir,root,rest⟩ :=
    Proofs.UfFindCall.body_exec_find [] vec rank valid.forest valid.length i inside (rank i+2) (by omega)
  refine ⟨r,?_,?_⟩
  · simp only [roots,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨⟨ir,root⟩,reach⟩
  · intro z present
    have other : ∃ w, vec[z]? = some w ∧ w < 0 := by
      have member := present.1
      simp only [roots,List.mem_filter,List.mem_range,decide_eq_true_eq] at member
      exact member.2
    exact root_unique present.2 reach other root

theorem roots_distinct_components (vec : List Int) (r z : Nat) (hr : r ∈ roots vec) (hz : z ∈ roots vec) :
    Proofs.UfFieldsSame.Connected vec r z ↔ r=z := by
  classical
  simp only [roots,List.mem_filter,List.mem_range,decide_eq_true_eq] at hr hz
  exact (Proofs.UfFieldsSame.roots_connected vec r z r z (Reach.refl r) (Reach.refl z) hr.2 hz.2).symm

theorem num_groups_call (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (vec : List Int) (rank : Nat → Nat) (valid : Valid vec count rank)
    (items : vbuf.items = vec.map Value.integer) (bvalid : vbuf.Valid (accepts (.integer i32)))
    (limit : vbuf.limit = CppVectorBindings.sizeLimit i32) (owner : vbuf.owner = V)
    (en : NExpr) (scalar : en.scalarOnly = true) (type : en.resultType = i32)
    (value : en.denote (envOf caller) = some (vec.length : Int)) :
    ∃ Sinit fuel out, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en] = .finished (out,.scalar ((roots vec).length : Int)) ∧
      out.scalars.bindings = caller.scalars.bindings ∧ out.scalars.baseMemory = caller.scalars.baseMemory ∧
      ScalarPost3 caller Sinit out en.nodes 40 caller.scalars.memory 0 V vec := by
  have length := valid.length
  obtain ⟨Sinit,fuel,out,prep,call,metadata,base,post⟩ := counter_call caller ok countBinding count cell writable vec items
    (by omega) bvalid limit owner en vec.length scalar type value (Proofs.VectorSumCall.i32_valid _ (by omega) (by omega))
  rw [valid.count] at call
  exact ⟨Sinit,fuel,out,prep,call,metadata,base,post⟩

end Proofs.UfFieldsCounter
