import Proofs.UfRootReady
import Proofs.UfFieldsSame

set_option maxRecDepth 4000

namespace Proofs.UfSameReady
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.VecKitW Proofs.PowModStep Proofs.DoublingNested Proofs.PrefixSumsCall
open Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression Proofs.UfInlineRoot Proofs.VecCapture
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedCall Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppNestedStmt
open Proofs.IntSim Proofs.CppNestedFacts
open Proofs.CppNestedRows
open Proofs.VecKit
open Proofs.QuotientFrame Proofs.DoublingCall Proofs.ScalarCall Proofs.ExtremaCall Proofs.VecWriteCall


open Proofs.UfRootReady Proofs.VecWriteFrame

theorem same_call_ready (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (vec : List Int) (rank : Nat → Nat) (forest : Forest vec rank)
    (items : vbuf.items = vec.map Value.integer) (length : vec.length < 2147483648)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (owner : vbuf.owner = V)
    (en ea eb : NExpr) (a b : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true) (bs_ : eb.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32) (bt_ : eb.resultType = i32)
    (nv : en.denote (envOf caller) = some (vec.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (bv : eb.denote (envOf caller) = some (b : Int))
    (ha : a < vec.length) (hb : b < vec.length) :
    ∃ Sinit fuel out, ∃ (r1 r2 : Nat) (middle final : List Int),
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_same.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] =
          .finished (out,.scalar (if r1=r2 then 1 else 0)) ∧
      Compressed vec middle a r1 ∧ Compressed middle final b r2 ∧ Forest final rank ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected vec a b) ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes+eb.nodes) (90 * rank a+90 * rank b+220)
        caller.scalars.memory (rank a+rank b) V final ∧
      (∃ buf, VOKWF out vslot vb V vsc buf ∧ buf.items = final.map Value.integer ∧
        buf.Valid (accepts (.integer i32)) ∧ buf.limit = CppVectorBindings.sizeLimit i32 ∧ buf.owner = V) ∧
      (∀ slot ty, out.scalarCell slot ty = caller.scalarCell slot ty) := by
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bvalueValid := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  obtain ⟨q,qwork,Sinit,prep,slots,memory,bindings,base,scopeEq,frame,work0,peak0⟩ :=
    Proofs.UfFieldsSame.prepare_same caller ok countBinding count cell writable en ea eb vec.length a b ns as_ bs_ nt at_ bt_ nv av bv
      nvalid avalid bvalueValid
  let vc : VCtx := ⟨i32,true,true,V,vsc,vbuf,vec,items,fun _ => rfl,by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have initial : FW vc vec vbuf 0 Sinit.frame := by
    rw [frame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,items,bvalid,limit,owner,by omega⟩
    intro root scope found
    have := ok.strict root scope found
    show scope < caller.scope+1
    omega
  obtain ⟨res,r1,r2,middle,ran,ret,c1,c2,newForest,reach1,reach2,oldRoot2,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsSame.body_correct (callerP caller) ⟨countBinding.address,true⟩ vec rank forest length a b ha hb
      (max (rank a) (rank b)+2) (by omega) (by omega)
  have resultValid : Proofs.PrefixSumsCall.bT.valid (if r1=r2 then 1 else 0) = true := by
    by_cases eq : r1=r2 <;> simp [eq,Proofs.PrefixSumsCall.bT,Ty.valid]
  have prefixLength : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have unchanged : (callerP caller ++ [(⟨i32,(vec.length : Int)⟩ : Cell),⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := UfRootCall.take_P caller _
  have preparedRun : pexecW i32 (max (rank a) (rank b)+2) Proofs.UnionFindCandidateInstance.UnionFind_same.body
      ⟨callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩],
        [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩
      vec = some res := ran
  obtain ⟨fuel,out,call,post,framePost⟩ := call_vecw_frame vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_same [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb]
    Sinit (callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩])
    [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    (max (rank a) (rank b)+2) res preparedRun _ ret Proofs.PrefixSumsCall.bT rfl resultValid
    (by omega) (by simp) (en.nodes+ea.nodes+eb.nodes) (90 * rank a+90 * rank b+220) (by omega)
  have savedCaller : res.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    calc res.ps.mem.take caller.scalars.memory.length =
        (res.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take,Nat.min_eq_left (by omega)]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [saved]
      _ = caller.scalars.memory := by simp only [callerP]; exact List.take_left' rfl
  rw [savedCaller] at post
  have ready := ready_of_frame caller out vc res.vec framePost post.slots post.bindings
    (by rw [post.scalarMemory]) post.valid vslot vb ok rfl rfl
  refine ⟨Sinit,fuel,out,r1,r2,middle,res.vec,prep,call,c1,c2,newForest,
    Proofs.UfFieldsSame.roots_connected vec a b r1 r2 reach1 reach2 c1.root oldRoot2,post.relax (le_refl _) (le_refl _) writes,ready,?_⟩

  intro slot ty
  simp only [NState.scalarCell,NState.scalarSlot,post.slots,post.scalarMemory,framePost.scalarBindings]


end Proofs.UfSameReady
