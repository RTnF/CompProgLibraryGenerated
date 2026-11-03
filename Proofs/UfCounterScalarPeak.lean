import Proofs.VecWriteScalarPeak
import Proofs.UfRootReady
import Proofs.UfFieldsCounter

namespace Proofs.UfCounterScalarPeak
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
open Proofs.UfRootReady Proofs.VecWriteFrame

open Proofs.VecWriteScalarPeak

theorem counter_scalar_peak (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (vec : List Int) (items : vbuf.items = vec.map Value.integer) (small : vec.length < 18446744073709551616)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32) (owner : vbuf.owner = V)
    (en : NExpr) (n : Int) (scalar : en.scalarOnly = true) (type : en.resultType = i32)
    (value : en.denote (envOf caller) = some n) (nvalid : i32.valid n = true) :
    ∃ Sinit fuel out result,
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters [.vectorReference vslot,.scalarReference cslot,.value en] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel fuel caller [.vectorReference vslot,.scalarReference cslot,.value en] = .finished (out,.scalar result) ∧
      out.scalars.peak ≤ max Sinit.scalars.peak ((callerP caller).length+12-caller.scalars.baseMemory+100) := by
  obtain ⟨q,qwork,Sinit,prep,slots,memory,bindings,base,scopeEq,frame,work0,peak0⟩ :=
    Proofs.UfFieldsCounter.prepare_counter caller ok countBinding count cell writable en n scalar type value nvalid
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
  let res : PRW := ⟨Proofs.UfFieldsCounter.fields (callerP caller) countBinding.address n,vec,some count,2,(callerP caller).length+6,0⟩
  have executed : pexecW i32 0 Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body
      (Proofs.UfFieldsCounter.fields (callerP caller) countBinding.address n) vec = some res :=
    Proofs.UfFieldsCounter.body_correct (callerP caller) countBinding.address n count vec countFound cvalid 0
  obtain ⟨fuel,out,call,peak⟩ := call_vecw_scalar_peak vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_num_groups [.vectorReference vslot,.scalarReference cslot,.value en]
    Sinit (callerP caller ++ [⟨i32,n⟩]) [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    0 res executed count rfl i32 rfl cvalid (by simp [res]) (by simp)
    en.nodes 40 (by simp only [res]; omega)
  exact ⟨Sinit,fuel,out,count,prep,call,peak⟩


theorem counter_scalar_peak_actual (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (vec : List Int) (items : vbuf.items = vec.map Value.integer) (small : vec.length < 18446744073709551616)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32) (owner : vbuf.owner = V)
    (en : NExpr) (n : Int) (scalar : en.scalarOnly = true) (type : en.resultType = i32)
    (value : en.denote (envOf caller) = some n) (nvalid : i32.valid n = true)
    (actualFuel : Nat) (out : NState) (result : Ret)
    (actual : Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel actualFuel caller [.vectorReference vslot,.scalarReference cslot,.value en] = .finished (out,result)) :
    ∃ Sinit, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters [.vectorReference vslot,.scalarReference cslot,.value en] = some Sinit ∧
      out.scalars.peak ≤ max Sinit.scalars.peak ((callerP caller).length+12-caller.scalars.baseMemory+100) := by
  obtain ⟨Sinit,fuel,computed,answer,prep,ran,peak⟩ := counter_scalar_peak caller ok countBinding count cell writable
    vec items small bvalid limit owner en n scalar type value nvalid
  have same := Proofs.CppCallUnique.call_unique Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel actualFuel caller
    [.vectorReference vslot,.scalarReference cslot,.value en] (computed,.scalar answer) (out,result) ran actual
  have outEq := congrArg Prod.fst same
  change computed = out at outEq
  refine ⟨Sinit,prep,?_⟩
  rw [← outEq]
  exact peak

end Proofs.UfCounterScalarPeak
