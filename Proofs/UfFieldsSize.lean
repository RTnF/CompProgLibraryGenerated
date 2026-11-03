import Proofs.UfFieldsSame

namespace Proofs.UfFieldsSize
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

-- Root weights in a constructed UnionFind are bounded by the number of elements.
-- Forest alone does not imply this: it permits INT_MIN, whose negation is undefined.
def Weights (vec : List Int) : Prop := ∀ (i : Nat) (w : Int), vec[i]? = some w → w < 0 → -(vec.length : Int) ≤ w

theorem weights_compressed {before after : List Int} {a r : Nat}
    (weights : Weights before) (compressed : Compressed before after a r) : Weights after := by
  intro i w found negative
  have old := (negative_entry compressed w negative).mp found
  rw [compressed.length]
  exact weights i w old negative

abbrev resultExpr : NExpr := .unary i32 .neg (.read i32 (.local 0) (.cast u64 (.variable i32 7)))
abbrev retCmd : Command := .sequence (.primitive (.ret resultExpr)) Sk
abbrev body : Command := .sequence (.primitive (.check (condition 2 3)))
  (plug (inlined 3 2 3) retCmd)

theorem body_eq : Proofs.UnionFindCandidateInstance.UnionFind_size.body = body := rfl

theorem result_value (vec : List Int) (state : PS) (r : Nat) (w : Int)
    (bound : r < 18446744073709551616) (rv : penv1 state 7 i32 = some (r : Int)) (found : vec[r]? = some w)
    (valid : i32.valid w = true) (resultValid : i32.valid (-w) = true) :
    vdenL i32 vec (penv1 state) resultExpr = some (-w) := by
  have index : (NExpr.cast u64 (.variable i32 7)).denote (penv1 state) = some (r : Int) := by
    simp only [NExpr.denote,rv,Option.bind_some]
    apply Ty.convert_of_valid
    exact Proofs.Mod61Body.u64_lt r bound
  have read : vdenL i32 vec (penv1 state) (.read i32 (.local 0) (.cast u64 (.variable i32 7))) = some w := by
    unfold vdenL
    simp [NExpr.scalarOnly,index,elemAtL,found,valid]
  change (vdenL i32 vec (penv1 state) (.read i32 (.local 0) (.cast u64 (.variable i32 7)))).bind
    (fun x => i32.convert (unaryValue .neg x)) = some (-w)
  rw [read,Option.bind_some]
  exact Ty.convert_of_valid _ _ resultValid

theorem body_correct (P : List Cell) (counter : CppState.Binding) (vec : List Int)
    (rank : Nat → Nat) (forest : Forest vec rank) (length : vec.length < 2147483648)
    (weights : Weights vec) (a : Nat) (inside : a < vec.length) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (out : PRW) (r : Nat) (w : Int),
      pexecW i32 fuel Proofs.UnionFindCandidateInstance.UnionFind_size.body (fields P counter vec.length a) vec = some out ∧
      out.ret = some (-w) ∧ vec[r]? = some w ∧ w < 0 ∧ i32.valid (-w) = true ∧
      Compressed vec out.vec a r ∧ Forest out.vec rank ∧ Weights out.vec ∧
      out.ps.mem.take P.length = P ∧ out.cost ≤ 90 * rank a+100 ∧
      out.need ≤ P.length+80 ∧ out.wk ≤ rank a := by
  let initial := fields P counter (vec.length : Int) a
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have nv := env_n P counter vec.length a nvalid
  have av := env_a P counter vec.length a avalid
  have guard := condition_value initial vec 2 3 vec.length a nv av (by omega) (by omega)
  have checked := (pexecW_prim i32 fuel (.check (condition 2 3)) initial vec).trans
    (pstmtW_check_ok i32 initial vec (condition 2 3) 1 guard (by decide))
  obtain ⟨one,r,run,ret,state,compressed,newForest,cost,need,work,tail⟩ :=
    inlined_correct initial vec rank forest length 2 3 a nv av inside fuel enough
  obtain ⟨w,found,negative⟩ := compressed.root
  have lower := weights r w found negative
  have resultValid := Proofs.VectorSumCall.i32_valid (-w) (by omega) (by omega)
  have rinside : r < vec.length := (List.getElem?_eq_some_iff.mp found).1
  have rvalid := Proofs.VectorSumCall.i32_valid (r : Int) (by omega) (by omega)
  have rv : penv1 one.ps 7 i32 = some (r : Int) := by
    rw [state]
    simpa [initial,fields,VecShift.pad,stI] using inline_env_result initial vec.length r rvalid
  have sameRoot : one.vec[r]? = some w := (negative_entry compressed w negative).mpr found
  have value := result_value one.vec one.ps r w (by omega) rv sameRoot
    (forest.valid w (List.mem_of_getElem? found)) resultValid
  have returned := seqW_ret (b := Sk)
    ((pexecW_prim i32 fuel (.ret resultExpr) one.ps one.vec).trans
      (pstmtW_ret_ok i32 one.ps one.vec resultExpr (-w) value)) rfl
  have continued := tail retCmd _ returned
  have all := seqW_some checked rfl continued
  have slots : initial.bs.length = 3 := rfl
  rw [slots] at all
  change pexecW i32 fuel body initial vec = some _ at all
  rw [← body_eq] at all
  refine ⟨_,r,w,all,rfl,found,negative,resultValid,compressed,newForest,weights_compressed weights compressed,?_,?_,?_,?_⟩
  · change one.ps.mem.take P.length = P
    rw [state]
    simp [inlineState,initial,fields,VecShift.pad,stI,List.append_assoc]
  · have gw : vwp (condition 2 3) = (7,7) := rfl
    have vw : vwp resultExpr = (6,6) := rfl
    change (vwp (condition 2 3)).1+1+(one.cost+((vwp resultExpr).1+1)) ≤ _
    rw [gw,vw]; dsimp; omega
  · have gw : vwp (condition 2 3) = (7,7) := rfl
    have vw : vwp resultExpr = (6,6) := rfl
    change max (initial.mem.length+initial.bs.length+(vwp (condition 2 3)).2+2)
      (max one.need (one.ps.mem.length+one.ps.bs.length+(vwp resultExpr).2+2)) ≤ _
    have ml : one.ps.mem.length = P.length+6 := by rw [state]; simp [inlineState,initial,fields,VecShift.pad,stI]
    have bl : one.ps.bs.length = 7 := by rw [state]; simp [inlineState,initial,fields,VecShift.pad,stI]
    simp only [initial,fields,VecShift.pad,stI,List.length_append,List.length_cons,List.length_nil] at need
    simp [initial,fields,VecShift.pad,stI,ml,bl,gw,vw]; omega
  · change 0+(one.wk+0) ≤ _
    simpa using work

theorem size_call (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (ps : List Int) (rank : Nat → Nat) (forest : Forest ps rank)
    (weights : Weights ps) (items : vbuf.items = ps.map Value.integer) (length : ps.length < 2147483648)
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
      ps[r]? = some w ∧ w < 0 ∧ Compressed ps vec a r ∧ Forest vec rank ∧ Weights vec ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes) (90 * rank a+160) caller.scalars.memory (rank a) V vec := by
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
    body_correct (callerP caller) ⟨countBinding.address,true⟩ ps rank forest length weights a inside (rank a+2) (by omega)
  have prefixLength : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have unchanged : (callerP caller ++ [(⟨i32,(ps.length : Int)⟩ : Cell),⟨i32,(a : Int)⟩]).take caller.scalars.memory.length =
      caller.scalars.memory := UfRootCall.take_P caller _
  have preparedRun : pexecW i32 (rank a+2) Proofs.UnionFindCandidateInstance.UnionFind_size.body
      ⟨callerP caller ++ [⟨i32,(ps.length : Int)⟩,⟨i32,(a : Int)⟩],
        [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ ps = some res := by
    simpa [fields,VecShift.pad,stI,List.append_assoc] using ran
  obtain ⟨fuel,out,call,post⟩ := call_vecw vc true (fun _ => ⟨rfl,rfl⟩) caller
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
  exact ⟨Sinit,fuel,out,r,w,res.vec,prep,call,found,negative,compressed,newForest,newWeights,post.relax (le_refl _) (le_refl _) writes⟩

end Proofs.UfFieldsSize
