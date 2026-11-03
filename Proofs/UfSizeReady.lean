import Proofs.UfRootReady
import Proofs.UfFieldsSize

set_option maxRecDepth 4000

namespace Proofs.UfSizeReady
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
open Proofs.UfInlineRoot Proofs.VecCapture Proofs.UfFieldsRoot

open Proofs.UfRootReady Proofs.VecWriteFrame

theorem size_call_ready (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (ps : List Int) (rank : Nat → Nat) (forest : Forest ps rank)
    (weights : Proofs.UfFieldsSize.Weights ps) (items : vbuf.items = ps.map Value.integer) (length : ps.length < 2147483648)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (owner : vbuf.owner = V)
    (en ea : NExpr) (a : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32)
    (nv : en.denote (envOf caller) = some (ps.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (inside : a < ps.length) :
    ∃ Sinit fuel out, ∃ (r : Nat) (w : Int) (vec : List Int),
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_size.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = .finished (out,.scalar (-w)) ∧
      ps[r]? = some w ∧ w < 0 ∧ Compressed ps vec a r ∧ Forest vec rank ∧ Proofs.UfFieldsSize.Weights vec ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes) (90 * rank a+160) caller.scalars.memory (rank a) V vec ∧
      (∃ buf, VOKWF out vslot vb V vsc buf ∧ buf.items = vec.map Value.integer ∧
        buf.Valid (accepts (.integer i32)) ∧ buf.limit = CppVectorBindings.sizeLimit i32 ∧ buf.owner = V) ∧
      (∀ slot ty, out.scalarCell slot ty = caller.scalarCell slot ty) := by
  have nvalid := Proofs.VectorSumCall.i32_valid (ps.length : Int) (by omega) (by omega)
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  obtain ⟨q,qwork,Sinit,prep,slots,memory,bindings,base,scopeEq,frame,work0,peak0⟩ :=
    prepare_fields caller ok countBinding count cell writable en ea ps.length a ns as_ nt at_ nv av nvalid avalid
  let vc : VCtx := ⟨i32,true,true,V,vsc,vbuf,ps,items,fun _ => rfl,by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have initial : FW vc ps vbuf 0 Sinit.frame := by
    rw [frame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,items,bvalid,limit,owner,by omega⟩
    intro root scope found
    have := ok.strict root scope found
    show scope < caller.scope+1
    omega
  obtain ⟨res,r,w,ran,ret,found,negative,resultValid,compressed,newForest,newWeights,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsSize.body_correct (callerP caller) ⟨countBinding.address,true⟩ ps rank forest length weights a inside (rank a+2) (by omega)
  have prefixLength : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have unchanged : (callerP caller ++ [(⟨i32,(ps.length : Int)⟩ : Cell),⟨i32,(a : Int)⟩]).take caller.scalars.memory.length =
      caller.scalars.memory := UfRootCall.take_P caller _
  have preparedRun : pexecW i32 (rank a+2) Proofs.UnionFindCandidateInstance.UnionFind_size.body
      ⟨callerP caller ++ [⟨i32,(ps.length : Int)⟩,⟨i32,(a : Int)⟩],
        [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ ps = some res := by
    simpa [fields,VecShift.pad,stI,List.append_assoc] using ran
  obtain ⟨fuel,out,call,post,framePost⟩ := call_vecw_frame vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_size [.vectorReference vslot,.scalarReference cslot,.value en,.value ea]
    Sinit (callerP caller ++ [⟨i32,(ps.length : Int)⟩,⟨i32,(a : Int)⟩])
    [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    (rank a+2) res preparedRun (-w) ret i32 rfl resultValid (by omega) (by simp)
    (en.nodes+ea.nodes) (90 * rank a+160) (by omega)
  have savedCaller : res.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    calc res.ps.mem.take caller.scalars.memory.length =
        (res.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take,Nat.min_eq_left (by omega)]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [saved]
      _ = caller.scalars.memory := by simp only [callerP]; exact List.take_left' rfl
  rw [savedCaller] at post
  have ready := ready_of_frame caller out vc res.vec framePost post.slots post.bindings
    (by rw [post.scalarMemory]) post.valid vslot vb ok rfl rfl
  refine ⟨Sinit,fuel,out,r,w,res.vec,prep,call,found,negative,compressed,newForest,newWeights,post.relax (le_refl _) (le_refl _) writes,ready,?_⟩

  intro slot ty
  simp only [NState.scalarCell,NState.scalarSlot,post.slots,post.scalarMemory,framePost.scalarBindings]


end Proofs.UfSizeReady
