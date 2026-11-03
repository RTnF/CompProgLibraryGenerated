import Proofs.UfRootReady
import Proofs.UfFieldsCounter

namespace Proofs.UfCounterReady
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

theorem counter_call_ready (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
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
      ScalarPost3 caller Sinit out en.nodes 40 caller.scalars.memory 0 V vec ∧
      (∃ buf, VOKWF out vslot vb V vsc buf ∧ buf.items = vec.map Value.integer ∧
        buf.Valid (accepts (.integer i32)) ∧ buf.limit = CppVectorBindings.sizeLimit i32 ∧ buf.owner = V) ∧
      (∀ slot ty, out.scalarCell slot ty = caller.scalarCell slot ty) := by
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
  obtain ⟨fuel,out,call,post,framePost⟩ := call_vecw_frame vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_num_groups [.vectorReference vslot,.scalarReference cslot,.value en]
    Sinit (callerP caller ++ [⟨i32,n⟩]) [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    0 res executed count rfl i32 rfl cvalid (by simp [res]) (by simp)
    en.nodes 40 (by simp only [res]; omega)
  have saved : res.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := unchanged
  rw [saved] at post
  have metadata := call_scalar_metadata _ _ _ _ _ _ i32 rfl call
  have ready := ready_of_frame caller out vc vec framePost post.slots post.bindings
    (by rw [post.scalarMemory]) post.valid vslot vb ok rfl rfl
  refine ⟨Sinit,fuel,out,prep,call,metadata.1,metadata.2,post,ready,?_⟩
  intro slot ty
  simp only [NState.scalarCell,NState.scalarSlot,post.slots,post.scalarMemory,framePost.scalarBindings]

theorem num_groups_call_ready (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
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
      ScalarPost3 caller Sinit out en.nodes 40 caller.scalars.memory 0 V vec ∧
      (∃ buf, VOKWF out vslot vb V vsc buf ∧ buf.items = vec.map Value.integer ∧
        buf.Valid (accepts (.integer i32)) ∧ buf.limit = CppVectorBindings.sizeLimit i32 ∧ buf.owner = V) ∧
      (∀ slot ty, out.scalarCell slot ty = caller.scalarCell slot ty) := by
  have length := valid.length
  obtain ⟨Sinit,fuel,out,prep,call,metadata,base,post,ready,cells⟩ := counter_call_ready caller ok countBinding count cell writable vec items
    (by omega) bvalid limit owner en vec.length scalar type value (Proofs.VectorSumCall.i32_valid _ (by omega) (by omega))
  rw [valid.count] at call
  exact ⟨Sinit,fuel,out,prep,call,metadata,base,post,ready,cells⟩


end Proofs.UfCounterReady
