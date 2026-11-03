import Proofs.UfRootReady
import Proofs.UfFieldsUnite

set_option maxRecDepth 4000

namespace Proofs.UfUniteReady
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

theorem updated_other (caller out : NState) (counter : Nat) (count : Int) (r1 r2 : Nat)
    (memory : out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory counter count r1 r2)
    (bindings : out.scalars.bindings = caller.scalars.bindings) (slots : out.slots = caller.slots)
    (slot : Nat) (ty : Ty) (binding : CppState.Binding) (value : Cell)
    (found : caller.scalarCell slot ty = some (binding,value)) (different : binding.address ≠ counter) :
    out.scalarCell slot ty = some (binding,value) := by
  obtain ⟨idx,oldSlot,oldBinding,oldValue,typed,valid⟩ := Proofs.ExtremaCall.scalarCell_facts found
  by_cases same : r1=r2
  · simp [NState.scalarCell,NState.scalarSlot,slots,bindings,memory,Proofs.UfFieldsUnite.updatedMemory,
      same,oldSlot,oldBinding,oldValue,typed,valid]
  · simp [NState.scalarCell,NState.scalarSlot,slots,bindings,memory,Proofs.UfFieldsUnite.updatedMemory,
      same,oldSlot,oldBinding,List.getElem?_set_ne (Ne.symm different),oldValue,typed,valid]

theorem updated_counter (caller out : NState) (countBinding : CppState.Binding) (count : Int) (r1 r2 cslot : Nat)
    (memory : out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory countBinding.address count r1 r2)
    (bindings : out.scalars.bindings = caller.scalars.bindings) (slots : out.slots = caller.slots)
    (found : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩))
    (valid : i32.valid (Proofs.UfFieldsUnite.countAfter count r1 r2) = true) :
    out.scalarCell cslot i32 = some (countBinding,⟨i32,Proofs.UfFieldsUnite.countAfter count r1 r2⟩) := by
  obtain ⟨idx,oldSlot,oldBinding,oldValue,typed,oldValid⟩ := Proofs.ExtremaCall.scalarCell_facts found
  have inside := (List.getElem?_eq_some_iff.mp oldValue).1
  by_cases same : r1=r2
  · simp [NState.scalarCell,NState.scalarSlot,slots,bindings,memory,Proofs.UfFieldsUnite.updatedMemory,
      Proofs.UfFieldsUnite.countAfter,same,oldSlot,oldBinding,oldValue,oldValid]
  · simp [Proofs.UfFieldsUnite.countAfter,same] at valid
    simp [NState.scalarCell,NState.scalarSlot,slots,bindings,memory,Proofs.UfFieldsUnite.updatedMemory,
      Proofs.UfFieldsUnite.countAfter,same,oldSlot,oldBinding,List.getElem?_set_self inside,valid]

theorem unite_call_ready (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
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
    ∃ Sinit fuel out, ∃ (r1 r2 : Nat) (middle two final : List Int),
      prepare caller Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = some Sinit ∧
      Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel fuel caller
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] =
          .finished (out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧
      Compressed vec middle a r1 ∧ Compressed middle two b r2 ∧ final = Proofs.UfUniteCall.uniteVec two r1 r2 ∧
      (∃ rank', Valid final (Proofs.UfFieldsUnite.countAfter count r1 r2) rank') ∧ (r1=r2 ↔ Connected vec a b) ∧
      out.scalars.bindings = caller.scalars.bindings ∧ out.scalars.baseMemory = caller.scalars.baseMemory ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes+eb.nodes) (90*rank a+90*rank b+400)
        (Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory countBinding.address count r1 r2) (rank a+rank b+2) V final ∧
      (∃ buf, VOKWF out vslot vb V vsc buf ∧ buf.items = final.map Value.integer ∧
        buf.Valid (accepts (.integer i32)) ∧ buf.limit = CppVectorBindings.sizeLimit i32 ∧ buf.owner = V) ∧
      out.scalarCell cslot i32 = some (countBinding,⟨i32,Proofs.UfFieldsUnite.countAfter count r1 r2⟩) ∧
      (∀ slot ty binding value, caller.scalarCell slot ty = some (binding,value) →
        binding.address ≠ countBinding.address → out.scalarCell slot ty = some (binding,value)) ∧
      (∀ slot binding, caller.scalarCell slot i32 = some (binding,⟨i32,count⟩) →
        binding.address = countBinding.address → out.scalarCell slot i32 =
          some (binding,⟨i32,Proofs.UfFieldsUnite.countAfter count r1 r2⟩)) := by
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
  obtain ⟨fuel,out,call,post,framePost⟩ := call_vecw_frame vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_unite [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb]
    Sinit (callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩])
    [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    (max (rank a) (rank b)+2) res preparedRun _ ret i32 rfl resultValid (by omega) (by simp)
    (en.nodes+ea.nodes+eb.nodes) (90*rank a+90*rank b+400) (by omega)
  have savedCaller : res.ps.mem.take caller.scalars.memory.length =
      Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory countBinding.address count r1 r2 := by
    calc res.ps.mem.take caller.scalars.memory.length =
        (res.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take,Nat.min_eq_left (by omega)]
      _ = (Proofs.UfFieldsUnite.updatedMemory (callerP caller) countBinding.address count r1 r2).take caller.scalars.memory.length := by rw [saved]
      _ = Proofs.UfFieldsUnite.updatedMemory ((callerP caller).take caller.scalars.memory.length) countBinding.address count r1 r2 := Proofs.UfFieldsUnite.updated_take _ _ _ _ _ _
      _ = Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory countBinding.address count r1 r2 := by
        simp only [callerP]
        rw [List.take_left' rfl]
  rw [savedCaller] at post
  have metadata := Proofs.UfFieldsUnite.call_scalar_metadata _ _ _ _ _ _ i32 rfl call
  obtain ⟨w2,root2,neg2⟩ := c2.root
  have oldRoot2 : vec[r2]? = some w2 := (negative_entry c1 w2 neg2).mp root2
  have ready := ready_of_frame caller out vc res.vec framePost post.slots post.bindings
    (by rw [post.scalarMemory]; unfold Proofs.UfFieldsUnite.updatedMemory; split_ifs <;> simp) post.valid vslot vb ok rfl rfl
  have countValid : i32.valid (Proofs.UfFieldsUnite.countAfter count r1 r2) = true := by
    obtain ⟨rank',valid'⟩ := newValid
    exact valid'.count_range.2.2
  have counter := updated_counter caller out countBinding count r1 r2 cslot post.scalarMemory metadata.1 post.slots cell countValid
  refine ⟨Sinit,fuel,out,r1,r2,middle,two,res.vec,prep,call,c1,c2,finalEq,newValid,
    roots_connected vec a b r1 r2 c1.reach (reach_backward c1 c2.reach) c1.root ⟨w2,oldRoot2,neg2⟩,
    metadata.1,metadata.2,post.relax (le_refl _) (le_refl _) writes,ready,counter,?_,?_⟩
  · intro slot ty binding value found different
    exact updated_other caller out countBinding.address count r1 r2 post.scalarMemory metadata.1 post.slots slot ty binding value found different
  · intro slot binding found same
    apply updated_counter caller out binding count r1 r2 slot _ metadata.1 post.slots found countValid
    rw [same]
    exact post.scalarMemory


end Proofs.UfUniteReady
