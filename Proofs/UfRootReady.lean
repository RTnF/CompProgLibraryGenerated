import Proofs.VecWriteFrame
import Proofs.UfFieldsRoot

set_option maxRecDepth 4000

namespace Proofs.UfRootReady
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

open Proofs.UfFieldsRoot Proofs.VecWriteFrame

theorem ready_of_frame (caller out : NState) (vc : VCtx) (vec : List Int)
    (post : FramePost caller out vc vec)
    (slots : out.slots = caller.slots) (bindings : out.frame.bindings = caller.frame.bindings)
    (memoryLength : out.scalars.memory.length = caller.scalars.memory.length)
    (outValid : out.frame.state.wellFormed = true)
    (vslot vb : Nat) (before : VOKWF caller vslot vb vc.R vc.vsc vc.buf)
    (typeEq : vc.ty = i32) (flagTrue : vc.flag = true) :
    ∃ buf, VOKWF out vslot vb vc.R vc.vsc buf ∧ buf.items = vec.map Value.integer ∧
      buf.Valid (accepts (.integer i32)) ∧ buf.limit = CppVectorBindings.sizeLimit i32 ∧ buf.owner = vc.R := by
  obtain ⟨buf,found,items,valid,limit,owner⟩ := post.buffer
  refine ⟨buf,?_,items,?_,?_,owner⟩
  · refine ⟨?_,?_,?_,?_,found,post.lengths,?_,post.strict,?_⟩
    · exact outValid
    · simpa [NState.vectorSlot,slots] using before.slot
    · rw [bindings]
      exact before.binding
    · simpa [typeEq] using post.tag
    · simpa [flagTrue] using post.flag
    · rw [post.base,memoryLength]
      exact before.base
  · simpa [typeEq] using valid
  · simpa [typeEq] using limit

theorem root_call_ready (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (ps : List Int) (rank : Nat → Nat) (forest : Forest ps rank)
    (items : vbuf.items = ps.map Value.integer) (length : ps.length < 2147483648)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (owner : vbuf.owner = V)
    (en ea : NExpr) (a : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32)
    (nv : en.denote (envOf caller) = some (ps.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (inside : a < ps.length) :
    ∃ Sinit fuel out, ∃ (r : Nat) (vec : List Int),
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_root.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = .finished (out,.scalar (r : Int)) ∧
      Compressed ps vec a r ∧ Forest vec rank ∧ recursive (rank a+1) ps a = some (vec,r) ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes) (90 * rank a+140) caller.scalars.memory (rank a) V vec ∧
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
  obtain ⟨res,r,ran,ret,compressed,newForest,oldRun,saved,cost,need,writes⟩ :=
    body_correct (callerP caller) ⟨countBinding.address,true⟩ ps rank forest length a inside (rank a+2) (by omega)
  have rootInside : r < ps.length := by
    obtain ⟨w,found,_⟩ := compressed.root
    exact (List.getElem?_eq_some_iff.mp found).1
  have resultValid := Proofs.VectorSumCall.i32_valid (r : Int) (by omega) (by omega)
  have prefixLength : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have unchanged : (callerP caller ++ [(⟨i32,(ps.length : Int)⟩ : Cell),⟨i32,(a : Int)⟩]).take caller.scalars.memory.length =
      caller.scalars.memory := UfRootCall.take_P caller _
  have preparedRun : pexecW i32 (rank a+2) Proofs.UnionFindCandidateInstance.UnionFind_root.body
      ⟨callerP caller ++ [⟨i32,(ps.length : Int)⟩,⟨i32,(a : Int)⟩],
        [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ ps = some res := by
    simpa [fields,VecShift.pad,stI,List.append_assoc] using ran
  obtain ⟨fuel,out,call,post,framePost⟩ := call_vecw_frame vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_root [.vectorReference vslot,.scalarReference cslot,.value en,.value ea]
    Sinit (callerP caller ++ [⟨i32,(ps.length : Int)⟩,⟨i32,(a : Int)⟩])
    [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    (rank a+2) res preparedRun (r : Int) ret i32 rfl resultValid (by omega) (by simp)
    (en.nodes+ea.nodes) (90 * rank a+140) (by omega)
  have savedCaller : res.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    calc res.ps.mem.take caller.scalars.memory.length =
        (res.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take,Nat.min_eq_left (by omega)]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [saved]
      _ = caller.scalars.memory := by simp only [callerP]; exact List.take_left' rfl
  rw [savedCaller] at post
  have ready := ready_of_frame caller out vc res.vec framePost post.slots post.bindings
    (by rw [post.scalarMemory]) post.valid vslot vb ok rfl rfl
  refine ⟨Sinit,fuel,out,r,res.vec,prep,call,compressed,newForest,oldRun,
    post.relax (le_refl _) (le_refl _) writes,ready,?_⟩
  intro slot ty
  simp only [NState.scalarCell,NState.scalarSlot,post.slots,post.scalarMemory,framePost.scalarBindings]


-- The second call consumes the first call's actual compressed receiver.
theorem two_roots (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (ps : List Int) (rank : Nat → Nat) (forest : Forest ps rank)
    (items : vbuf.items = ps.map Value.integer) (length : ps.length < 2147483648)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (owner : vbuf.owner = V)
    (en ea eb : NExpr) (a b : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true) (bs_ : eb.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32) (bt_ : eb.resultType = i32)
    (nv : en.denote (envOf caller) = some (ps.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (bv : eb.denote (envOf caller) = some (b : Int))
    (ha : a < ps.length) (hb : b < ps.length) :
    ∃ fuel1 out1, ∃ (r1 : Nat) (vec1 : List Int), ∃ fuel2 out2, ∃ (r2 : Nat) (vec2 : List Int),
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel1 caller
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = .finished (out1,.scalar (r1 : Int)) ∧
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel2 out1
        [.vectorReference vslot,.scalarReference cslot,.value en,.value eb] = .finished (out2,.scalar (r2 : Int)) ∧
      Compressed ps vec1 a r1 ∧ Compressed vec1 vec2 b r2 ∧ Forest vec2 rank ∧
      (∃ buf, VOKWF out2 vslot vb V vsc buf ∧ buf.items = vec2.map Value.integer ∧
        buf.Valid (accepts (.integer i32)) ∧ buf.limit = CppVectorBindings.sizeLimit i32 ∧ buf.owner = V) ∧
      (∀ slot ty, out2.scalarCell slot ty = caller.scalarCell slot ty) := by
  obtain ⟨init1,fuel1,out1,r1,vec1,prep1,call1,compressed1,forest1,old1,post1,ready1,cells1⟩ :=
    root_call_ready caller ok countBinding count cell writable ps rank forest items length bvalid limit owner
      en ea a ns as_ nt at_ nv av ha
  obtain ⟨buf1,ok1,items1,valid1,limit1,owner1⟩ := ready1
  have env1 : envOf out1 = envOf caller := by
    funext slot ty
    simp [envOf,cells1]
  have cell1 : out1.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩) := by rw [cells1]; exact cell
  obtain ⟨init2,fuel2,out2,r2,vec2,prep2,call2,compressed2,forest2,old2,post2,ready2,cells2⟩ :=
    root_call_ready out1 ok1 countBinding count cell1 writable vec1 rank forest1 items1
      (by rw [compressed1.length]; exact length) valid1 limit1 owner1 en eb b ns bs_ nt bt_
      (by rw [env1,compressed1.length]; exact nv) (by rw [env1]; exact bv)
      (by rw [compressed1.length]; exact hb)
  refine ⟨fuel1,out1,r1,vec1,fuel2,out2,r2,vec2,call1,call2,compressed1,compressed2,forest2,ready2,?_⟩
  intro slot ty
  rw [cells2,cells1]

end Proofs.UfRootReady
