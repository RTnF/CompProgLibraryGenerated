import Proofs.VecWriteScalarPeak
import Proofs.CppCallUnique
import Proofs.UfFieldsRoot

set_option maxRecDepth 4000

namespace Proofs.UfRootScalarPeak
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

open Proofs.VecWriteScalarPeak

theorem root_scalar_peak (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
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
    ∃ Sinit fuel out result,
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_root.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = .finished (out,.scalar result) ∧
      out.scalars.peak ≤ max Sinit.scalars.peak ((callerP caller).length+12-caller.scalars.baseMemory+100) := by
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
  obtain ⟨fuel,out,call,peak⟩ := call_vecw_scalar_peak vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_root [.vectorReference vslot,.scalarReference cslot,.value en,.value ea]
    Sinit (callerP caller ++ [⟨i32,(ps.length : Int)⟩,⟨i32,(a : Int)⟩])
    [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    (rank a+2) res preparedRun (r : Int) ret i32 rfl resultValid (by omega) (by simp)
    (en.nodes+ea.nodes) (90 * rank a+140) (by omega)
  exact ⟨Sinit,fuel,out,(r : Int),prep,call,peak⟩


theorem root_scalar_peak_actual (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (ps : List Int) (rank : Nat → Nat) (forest : Forest ps rank)
    (items : vbuf.items = ps.map Value.integer) (length : ps.length < 2147483648)
    (bvalid : vbuf.Valid (accepts (.integer i32))) (limit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (owner : vbuf.owner = V)
    (en ea : NExpr) (a : Nat) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32)
    (nv : en.denote (envOf caller) = some (ps.length : Int))
    (av : ea.denote (envOf caller) = some (a : Int)) (inside : a < ps.length)
    (actualFuel : Nat) (out : NState) (result : Ret)
    (actual : Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel actualFuel caller
      [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = .finished (out,result)) :
    ∃ Sinit, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_root.parameters
      [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = some Sinit ∧
      out.scalars.peak ≤ max Sinit.scalars.peak ((callerP caller).length+12-caller.scalars.baseMemory+100) := by
  obtain ⟨Sinit,fuel,computed,value,prep,ran,peak⟩ := root_scalar_peak caller ok countBinding count cell writable
    ps rank forest items length bvalid limit owner en ea a ns as_ nt at_ nv av inside
  have same := Proofs.CppCallUnique.call_unique Proofs.UnionFindCandidateInstance.UnionFind_root fuel actualFuel caller
    [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] (computed,.scalar value) (out,result) ran actual
  have outEq := congrArg Prod.fst same
  change computed = out at outEq
  refine ⟨Sinit,prep,?_⟩
  rw [← outEq]
  exact peak

end Proofs.UfRootScalarPeak
