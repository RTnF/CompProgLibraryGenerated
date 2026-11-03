import Proofs.VecWriteScalarPeak
import Proofs.UfRootReady
import Proofs.UfFieldsUnite

set_option maxRecDepth 4000

namespace Proofs.UfUniteScalarPeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.VecKitW Proofs.PowModStep Proofs.DoublingNested Proofs.PrefixSumsCall
open Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression Proofs.UfInlineRoot Proofs.VecCapture
open Proofs.UfSameCall Proofs.UfFieldsSame Proofs.UfClassInvariant
open Proofs.VectorFillCall
open Proofs.CppState (Cell)

open Proofs.UfRootReady Proofs.VecWriteFrame

-- Aliases of other scalar cells remain valid after the counter update.
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedCall Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppNestedStmt
open Proofs.IntSim Proofs.CppNestedFacts
open Proofs.CppNestedRows
open Proofs.VecKit
open Proofs.QuotientFrame Proofs.DoublingCall Proofs.ScalarCall Proofs.ExtremaCall Proofs.VecWriteCall

open Proofs.VecWriteScalarPeak

theorem unite_scalar_peak (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (vec : List Int) (rank : Nat → Nat) (valid : Valid vec count rank)
    (items : vbuf.items = vec.map Value.integer) (bvalid : vbuf.Valid (accepts (.integer i32)))
    (limit : vbuf.limit = CppVectorBindings.sizeLimit i32) (owner : vbuf.owner = V)
    (en ea eb : NExpr) (a b : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true) (bs_ : eb.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32) (bt_ : eb.resultType = i32)
    (nv : en.denote (envOf caller) = some (vec.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (bv : eb.denote (envOf caller) = some (b : Int))
    (ha : a < vec.length) (hb : b < vec.length) :
    ∃ Sinit fuel out result,
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel fuel caller [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = .finished (out,.scalar result) ∧
      out.scalars.peak ≤ max Sinit.scalars.peak ((callerP caller).length+12-caller.scalars.baseMemory+100) := by
  have length := valid.length
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bvalidValue := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  obtain ⟨q,qwork,Sinit,prep,slots,memory,bindings,base,scopeEq,frame,work0,peak0⟩ :=
    prepare_same caller ok countBinding count cell writable en ea eb vec.length a b ns as_ bs_ nt at_ bt_ nv av bv
      nvalid avalid bvalidValue
  obtain ⟨_,_,_,found,_,_⟩ := scalarCell_facts cell
  have countInside := (List.getElem?_eq_some_iff.mp found).1
  have countFound : (callerP caller)[countBinding.address]? = some ⟨i32,count⟩ := by
    simpa [callerP,List.getElem?_append_left countInside] using found
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
  obtain ⟨res,r1,r2,middle,two,ran,ret,c1,c2,finalEq,newValid,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsUnite.body_correct (callerP caller) countBinding.address count vec rank valid countFound a b ha hb
      (max (rank a) (rank b)+2) (by omega) (by omega)
  have r1inside : r1 < two.length := by
    have inside := (List.getElem?_eq_some_iff.mp (Classical.choose_spec c1.root).1).1
    rw [c2.length,c1.length]
    exact inside
  have r2inside : r2 < two.length := by
    have inside := (List.getElem?_eq_some_iff.mp (Classical.choose_spec c2.root).1).1
    rw [c2.length]
    exact inside
  have resultInside := Proofs.UfUniteCall.uniteX_lt two r1 r2 r1inside r2inside
  have resultValid := Proofs.VectorSumCall.i32_valid (Proofs.UfUniteCall.uniteX two r1 r2 : Int) (by omega)
    (by rw [c2.length,c1.length] at resultInside; omega)
  have prefixLength : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have unchanged : (callerP caller ++ [(⟨i32,(vec.length : Int)⟩ : Cell),⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := UfRootCall.take_P caller _
  have preparedRun : pexecW i32 (max (rank a) (rank b)+2) Proofs.UnionFindCandidateInstance.UnionFind_unite.body
      ⟨callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩],
        [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩
      vec = some res := ran
  obtain ⟨fuel,out,call,peak⟩ := call_vecw_scalar_peak vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_unite [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb]
    Sinit (callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩])
    [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    (max (rank a) (rank b)+2) res preparedRun _ ret i32 rfl resultValid (by omega) (by simp)
    (en.nodes+ea.nodes+eb.nodes) (90*rank a+90*rank b+400) (by omega)
  exact ⟨Sinit,fuel,out,(Proofs.UfUniteCall.uniteX two r1 r2 : Int),prep,call,peak⟩


theorem unite_scalar_peak_actual (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (vec : List Int) (rank : Nat → Nat) (valid : Valid vec count rank)
    (items : vbuf.items = vec.map Value.integer) (bvalid : vbuf.Valid (accepts (.integer i32)))
    (limit : vbuf.limit = CppVectorBindings.sizeLimit i32) (owner : vbuf.owner = V)
    (en ea eb : NExpr) (a b : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true) (bs_ : eb.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32) (bt_ : eb.resultType = i32)
    (nv : en.denote (envOf caller) = some (vec.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (bv : eb.denote (envOf caller) = some (b : Int))
    (ha : a < vec.length) (hb : b < vec.length)
    (actualFuel : Nat) (out : NState) (result : Ret)
    (actual : Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel actualFuel caller [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = .finished (out,result)) :
    ∃ Sinit, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = some Sinit ∧
      out.scalars.peak ≤ max Sinit.scalars.peak ((callerP caller).length+12-caller.scalars.baseMemory+100) := by
  obtain ⟨Sinit,fuel,computed,answer,prep,ran,peak⟩ := unite_scalar_peak caller ok countBinding count cell writable
    vec rank valid items bvalid limit owner en ea eb a b ns as_ bs_ nt at_ bt_ nv av bv ha hb
  have same := Proofs.CppCallUnique.call_unique Proofs.UnionFindCandidateInstance.UnionFind_unite fuel actualFuel caller
    [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] (computed,.scalar answer) (out,result) ran actual
  have outEq := congrArg Prod.fst same
  change computed = out at outEq
  refine ⟨Sinit,prep,?_⟩
  rw [← outEq]
  exact peak

end Proofs.UfUniteScalarPeak
