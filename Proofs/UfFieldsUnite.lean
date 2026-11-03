import Proofs.UfUniteTail

namespace Proofs.UfFieldsUnite
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite
open Proofs.VecKitW Proofs.PowModStep Proofs.DoublingNested Proofs.PrefixSumsCall
open Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression Proofs.UfInlineRoot Proofs.VecCapture
open Proofs.UfSameCall Proofs.UfFieldsSame Proofs.UfClassInvariant
open Proofs.VectorFillCall
open Proofs.CppState (Cell)

def countAfter (groups : Int) (r1 r2 : Nat) : Int := if r1=r2 then groups else groups-1
def updatedMemory (P : List Cell) (counter : Nat) (groups : Int) (r1 r2 : Nat) : List Cell :=
  if r1=r2 then P else P.set counter ⟨i32,groups-1⟩

theorem inline_loc (state : PS) (n r v : Int) (j ad : Nat) (loc : Loc state j ad v) :
    Loc (inlineState state n r) j ad v := by
  rw [inline_appended]
  exact loc_app_old _ _ _ _ _ (loc_app_old _ _ _ _ _ (loc_app_old _ _ _ _ _ (loc_app_old _ _ _ _ _ loc)))

theorem final_take (state : PS) (vec : List Int) (P : List Cell) (adX adY adC X Y : Nat) (groups : Int)
    (saved : state.mem.take P.length = P) (freshX : P.length ≤ adX) (freshY : P.length ≤ adY) :
    (UfUniteTail.finalState state vec adX adY adC X Y groups).mem.take P.length = updatedMemory P adC groups X Y := by
  by_cases same : X=Y
  · simp [UfUniteTail.finalState,updatedMemory,same,saved]
  · simp only [UfUniteTail.finalState,updatedMemory,if_neg same,setP,List.take_set]
    have orderSaved : (UfUniteTail.orderedState state adX adY X Y (vec.getD X 0) (vec.getD Y 0)).mem.take P.length = P := by
      unfold UfUniteTail.orderedState
      split
      · rw [take_setP _ _ _ _ freshY,take_setP _ _ _ _ freshX,saved]
      · exact saved
    rw [orderSaved]

theorem body_correct (P : List Cell) (counter : Nat) (groups : Int) (vec : List Int) (rank : Nat → Nat)
    (valid : Valid vec groups rank) (countFound : P[counter]? = some ⟨i32,groups⟩)
    (a b : Nat) (ha : a < vec.length) (hb : b < vec.length) (fuel : Nat)
    (fa : rank a+2 ≤ fuel) (fb : rank b+2 ≤ fuel) :
    ∃ (out : PRW) (r1 r2 : Nat) (middle two : List Int),
      pexecW i32 fuel Proofs.UnionFindCandidateInstance.UnionFind_unite.body
        (fields P ⟨counter,true⟩ vec.length a b) vec = some out ∧
      out.ret = some (Proofs.UfUniteCall.uniteX two r1 r2 : Int) ∧
      Compressed vec middle a r1 ∧ Compressed middle two b r2 ∧
      out.vec = Proofs.UfUniteCall.uniteVec two r1 r2 ∧
      (∃ rank', Valid out.vec (countAfter groups r1 r2) rank') ∧
      out.ps.mem.take P.length = updatedMemory P counter groups r1 r2 ∧
      out.cost ≤ 90*rank a+90*rank b+340 ∧ out.need ≤ P.length+100 ∧ out.wk ≤ rank a+rank b+2 := by
  let initial := fields P ⟨counter,true⟩ (vec.length : Int) a b
  have length := valid.length
  have counterInside := (List.getElem?_eq_some_iff.mp countFound).1
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  have nv := env_n P ⟨counter,true⟩ vec.length a b nvalid
  have aa := env_a P ⟨counter,true⟩ vec.length a b av
  have bb := env_b P ⟨counter,true⟩ vec.length a b bv
  have ca := (pexecW_prim i32 fuel (.check (condition 2 3)) initial vec).trans
    (pstmtW_check_ok i32 initial vec (condition 2 3) 1 (condition_value initial vec 2 3 vec.length a nv aa (by omega) (by omega)) (by decide))
  have cb := (pexecW_prim i32 fuel (.check (condition 2 4)) initial vec).trans
    (pstmtW_check_ok i32 initial vec (condition 2 4) 1 (condition_value initial vec 2 4 vec.length b nv bb (by omega) (by omega)) (by decide))
  have countLoc : Loc initial 0 counter groups := by
    refine ⟨rfl,?_⟩
    simpa [initial,fields,List.getElem?_append_left counterInside] using countFound
  obtain ⟨one,r1,run1,ret1,state1,c1,forest1,cost1,need1,work1,tail1⟩ :=
    inlined_correct initial vec rank valid.forest length 2 3 a nv aa ha fuel fa
  have r1inside := (List.getElem?_eq_some_iff.mp (Classical.choose_spec c1.root).1).1
  have r1valid := Proofs.VectorSumCall.i32_valid (r1 : Int) (by omega) (by omega)
  have bs1 : one.ps.bs.length = 8 := by rw [state1]; simp [inlineState,initial,fields]
  have mem1 : one.ps.mem.length = P.length+7 := by rw [state1]; simp [inlineState,initial,fields]
  have result1 : penv1 one.ps 8 i32 = some (r1 : Int) := by
    rw [state1]
    simpa [initial,fields] using inline_env_result initial vec.length r1 r1valid
  have dx := (pexecW_prim i32 fuel (.declare i32 true (.variable i32 8)) one.ps one.vec).trans
    (pstmtW_declare_ok i32 one.ps one.vec i32 true (.variable i32 8) r1
      (by rw [vdenL_scalar _ _ _ _ rfl]; exact result1) r1 (Ty.convert_of_valid _ _ r1valid))
  let afterX := appI one.ps r1
  have n1 : penv1 afterX 2 i32 = some (one.vec.length : Int) := by
    rw [c1.length]
    apply env_old one.ps i32 i32 _ r1 2
    rw [state1]
    exact inline_env_old initial vec.length r1 vec.length 2 nv
  have b1 : penv1 afterX 4 i32 = some (b : Int) := by
    apply env_old one.ps i32 i32 _ r1 4
    rw [state1]
    exact inline_env_old initial vec.length r1 b 4 bb
  have xloc : Loc afterX 8 (P.length+7) r1 := by
    simpa [bs1,mem1] using loc_app_new one.ps (r1 : Int)
  have cloc1 : Loc afterX 0 counter groups := by
    apply loc_app_old
    rw [state1]
    exact inline_loc initial vec.length r1 groups 0 counter countLoc
  obtain ⟨twoOut,r2,run2,ret2,state2,c2,forest2,cost2,need2,work2,tail2⟩ :=
    inlined_correct afterX one.vec rank forest1 (by rw [c1.length]; exact length) 2 4 b n1 b1
      (by rw [c1.length]; exact hb) fuel fb
  have bsX : afterX.bs.length = 9 := by simp [afterX,bs1]
  have memX : afterX.mem.length = P.length+8 := by simp [afterX,mem1]
  have bs2 : twoOut.ps.bs.length = 13 := by rw [state2]; simp [inlineState,bsX]
  have mem2 : twoOut.ps.mem.length = P.length+12 := by rw [state2]; simp [inlineState,memX]
  have r2inside : r2 < vec.length := by
    have inside := (List.getElem?_eq_some_iff.mp (Classical.choose_spec c2.root).1).1
    rw [c1.length] at inside
    exact inside
  have r2valid := Proofs.VectorSumCall.i32_valid (r2 : Int) (by omega) (by omega)
  have result2 : penv1 twoOut.ps 13 i32 = some (r2 : Int) := by
    rw [state2]
    simpa [bsX] using inline_env_result afterX one.vec.length r2 r2valid
  have dy := (pexecW_prim i32 fuel (.declare i32 true (.variable i32 13)) twoOut.ps twoOut.vec).trans
    (pstmtW_declare_ok i32 twoOut.ps twoOut.vec i32 true (.variable i32 13) r2
      (by rw [vdenL_scalar _ _ _ _ rfl]; exact result2) r2 (Ty.convert_of_valid _ _ r2valid))
  let ready := appI twoOut.ps r2
  have xl : Loc ready 8 (P.length+7) r1 := by
    apply loc_app_old
    rw [state2]
    exact inline_loc afterX one.vec.length r2 r1 8 (P.length+7) xloc
  have yl : Loc ready 13 (P.length+12) r2 := by simpa [bs2,mem2] using loc_app_new twoOut.ps (r2 : Int)
  have cl : Loc ready 0 counter groups := by
    apply loc_app_old
    rw [state2]
    exact inline_loc afterX one.vec.length r2 groups 0 counter cloc1
  have readyBS : ready.bs.length = 14 := by simp [ready,bs2]
  have readyMem : ready.mem.length = P.length+13 := by simp [ready,mem2]
  have readySaved : ready.mem.take P.length = P := by
    simp [ready,state2,afterX,state1,inlineState,appI,initial,fields,List.append_assoc]
  obtain ⟨vx,fx,nx⟩ := c1.root
  have xmid := (negative_entry c1 vx nx).mpr fx
  have xfinal := (negative_entry c2 vx nx).mpr xmid
  obtain ⟨vy,fy,ny⟩ := c2.root
  have yfinal := (negative_entry c2 vy ny).mpr fy
  have valid2 := (valid.compressed c1).compressed c2
  obtain ⟨last,runLast,retLast,vecLast,psLast,workLast,costLast,needLast,rankLast,validLast⟩ :=
    UfUniteTail.tail_correct ready twoOut.vec groups rank valid2 (P.length+7) (P.length+12) counter r1 r2
      xl yl cl (by omega) (by omega) (by omega) readyBS ⟨vx,xfinal,nx⟩ ⟨vy,yfinal,ny⟩ fuel
  have afterY := seqW_some dy rfl runLast
  have afterRoot2 := tail2 (.sequence (.primitive (.declare i32 true (.variable i32 13))) UfUniteTail.tail) _ afterY
  have afterDeclX := seqW_some dx rfl afterRoot2
  have afterRoot1 := tail1 (.sequence (.primitive (.declare i32 true (.variable i32 8)))
    (plug (inlined afterX.bs.length 2 4) (.sequence (.primitive (.declare i32 true (.variable i32 13))) UfUniteTail.tail))) _ afterDeclX
  have all := seqW_some ca rfl (seqW_some cb rfl afterRoot1)
  have bs0 : initial.bs.length = 4 := rfl
  rw [bs0,bsX] at all
  change pexecW i32 fuel (UfUniteTail.before_tail UfUniteTail.tail) initial vec = some _ at all
  rw [← UfUniteTail.body_eq] at all
  refine ⟨_,r1,r2,one.vec,twoOut.vec,all,retLast,c1,c2,vecLast,⟨rankLast,validLast⟩,?_,?_,?_,?_⟩
  · change last.ps.mem.take P.length = _
    rw [psLast]
    exact final_take ready twoOut.vec P (P.length+7) (P.length+12) counter r1 r2 groups readySaved (by omega) (by omega)
  · change 8+(8+(one.cost+(2+(twoOut.cost+(2+last.cost))))) ≤ _
    omega
  · change max (initial.mem.length+initial.bs.length+9) (max (initial.mem.length+initial.bs.length+9)
      (max one.need (max (one.ps.mem.length+one.ps.bs.length+5)
        (max twoOut.need (max (twoOut.ps.mem.length+twoOut.ps.bs.length+5) last.need))))) ≤ _
    simp only [initial,fields,List.length_append,List.length_cons,List.length_nil] at need1
    rw [memX,bsX] at need2
    rw [readyMem,readyBS] at needLast
    simp [initial,fields,mem1,bs1,mem2,bs2]
    omega
  · change 0+(0+(one.wk+(0+(twoOut.wk+(0+last.wk))))) ≤ _
    split at workLast <;> omega

open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedCall Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppNestedStmt
open Proofs.IntSim Proofs.CppNestedFacts
open Proofs.CppNestedRows
open Proofs.VecKit
open Proofs.QuotientFrame Proofs.DoublingCall Proofs.ScalarCall Proofs.ExtremaCall Proofs.VecWriteCall


theorem updated_take (P : List Cell) (n counter : Nat) (groups : Int) (r1 r2 : Nat) :
    (updatedMemory P counter groups r1 r2).take n = updatedMemory (P.take n) counter groups r1 r2 := by
  by_cases same : r1=r2 <;> simp [updatedMemory,same,List.take_set]

theorem finish_scalar_metadata (caller callee out : NState) (ty : Ty) (returned : Option Ret) (value : Ret)
    (done : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,value)) :
    out.scalars.bindings = caller.scalars.bindings ∧ out.scalars.baseMemory = caller.scalars.baseMemory := by
  unfold Proofs.CppNestedCall.finish at done
  split at done
  · cases returned with
    | none => simp at done
    | some incoming =>
      cases incoming with
      | vector owner element => simp at done
      | unit => simp at done
      | scalar v =>
        by_cases valid : ty.valid v = true
        · simp only [valid,ite_true,Option.bind_some] at done
          obtain ⟨selected,_,done⟩ := Option.bind_eq_some_iff.mp done
          obtain ⟨retired,_,done⟩ := Option.bind_eq_some_iff.mp done
          have stateEq := congrArg Prod.fst (Option.some.inj done)
          dsimp only at stateEq
          rw [← stateEq]
          exact ⟨rfl,rfl⟩
        · simp [valid] at done
  · simp at done

theorem call_scalar_metadata (prog : NProgram) (fuel : Nat) (caller : NState) (args : List NArgument)
    (out : NState) (value : Ret) (ty : Ty) (result : prog.result = .scalar ty) (call : prog.callFuel fuel caller args = .finished (out,value)) :
    out.scalars.bindings = caller.scalars.bindings ∧ out.scalars.baseMemory = caller.scalars.baseMemory := by
  unfold NProgram.callFuel at call
  cases prep : prepare caller prog.parameters args with
  | none => simp [prep,CppLoop.liftChecked,Bind.bind,CppLoop.Outcome.bind] at call
  | some initial =>
    simp only [prep,CppLoop.liftChecked,Bind.bind,CppLoop.Outcome.bind] at call
    cases ran : Proofs.CppNestedProgram.runFuel fuel prog.body initial with
    | fault => simp [ran,CppLoop.Outcome.bind] at call
    | exhausted => simp [ran,CppLoop.Outcome.bind] at call
    | finished step =>
      simp only [ran,CppLoop.Outcome.bind] at call
      cases breaking : step.breaking with
      | true => simp [breaking] at call
      | false =>
        simp only [breaking,Bool.false_eq_true,if_false] at call
        cases ended : Proofs.CppNestedCall.finish caller step.state prog.result step.returned with
        | none => simp [ended,CppLoop.liftChecked] at call
        | some pair =>
          have equal : pair = (out,value) := by simpa [ended,CppLoop.liftChecked] using call
          apply finish_scalar_metadata caller step.state out ty step.returned value
          rw [← equal,← result]
          exact ended

theorem unite_call (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
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
      (∃ rank', Valid final (countAfter count r1 r2) rank') ∧ (r1=r2 ↔ Connected vec a b) ∧
      out.scalars.bindings = caller.scalars.bindings ∧ out.scalars.baseMemory = caller.scalars.baseMemory ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes+eb.nodes) (90*rank a+90*rank b+400)
        (updatedMemory caller.scalars.memory countBinding.address count r1 r2) (rank a+rank b+2) V final := by
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
    body_correct (callerP caller) countBinding.address count vec rank valid countFound a b ha hb
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
  obtain ⟨fuel,out,call,post⟩ := call_vecw vc true (fun _ => ⟨rfl,rfl⟩) caller
    Proofs.UnionFindCandidateInstance.UnionFind_unite [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb]
    Sinit (callerP caller ++ [⟨i32,(vec.length : Int)⟩,⟨i32,(a : Int)⟩,⟨i32,(b : Int)⟩])
    [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    prep (by rw [slots]; rfl) memory bindings base scopeEq (by rw [frame]) (by rw [frame])
    initial rfl rfl rfl rfl peak0 (by simp [prefixLength]; omega) (by rw [unchanged]) ok.base (by decide)
    (max (rank a) (rank b)+2) res preparedRun _ ret i32 rfl resultValid (by omega) (by simp)
    (en.nodes+ea.nodes+eb.nodes) (90*rank a+90*rank b+400) (by omega)
  have savedCaller : res.ps.mem.take caller.scalars.memory.length =
      updatedMemory caller.scalars.memory countBinding.address count r1 r2 := by
    calc res.ps.mem.take caller.scalars.memory.length =
        (res.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take,Nat.min_eq_left (by omega)]
      _ = (updatedMemory (callerP caller) countBinding.address count r1 r2).take caller.scalars.memory.length := by rw [saved]
      _ = updatedMemory ((callerP caller).take caller.scalars.memory.length) countBinding.address count r1 r2 := updated_take _ _ _ _ _ _
      _ = updatedMemory caller.scalars.memory countBinding.address count r1 r2 := by
        simp only [callerP]
        rw [List.take_left' rfl]
  rw [savedCaller] at post
  have metadata := call_scalar_metadata _ _ _ _ _ _ i32 rfl call
  obtain ⟨w2,root2,neg2⟩ := c2.root
  have oldRoot2 : vec[r2]? = some w2 := (negative_entry c1 w2 neg2).mp root2
  exact ⟨Sinit,fuel,out,r1,r2,middle,two,res.vec,prep,call,c1,c2,finalEq,newValid,
    roots_connected vec a b r1 r2 c1.reach (reach_backward c1 c2.reach) c1.root ⟨w2,oldRoot2,neg2⟩,
    metadata.1,metadata.2,post.relax (le_refl _) (le_refl _) writes⟩

end Proofs.UfFieldsUnite
