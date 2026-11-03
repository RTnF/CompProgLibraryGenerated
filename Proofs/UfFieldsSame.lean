import Proofs.UfInlineRoot

namespace Proofs.UfFieldsSame
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


abbrev resultExpr : NExpr := .binary Proofs.PrefixSumsCall.bT .eq (.variable i32 8) (.variable i32 12)
abbrev retCmd : Command := .sequence (.primitive (.ret resultExpr)) Sk
abbrev body : Command := .sequence (.primitive (.check (condition 2 3)))
  (.sequence (.primitive (.check (condition 2 4)))
    (plug (inlined 4 2 3) (plug (inlined 8 2 4) retCmd)))

theorem body_eq : Proofs.UnionFindCandidateInstance.UnionFind_same.body = body := rfl

def fields (P : List Cell) (counter : CppState.Binding) (n a b : Int) : PS :=
  ⟨P++[⟨i32,n⟩,⟨i32,a⟩,⟨i32,b⟩],[counter,⟨P.length,true⟩,⟨P.length+1,true⟩,⟨P.length+2,true⟩]⟩

theorem env_n (P : List Cell) (counter : CppState.Binding) (n a b : Int) (valid : i32.valid n = true) :
    penv1 (fields P counter n a b) 2 i32 = some n := by
  simp [fields,penv1,penv,List.getElem?_append_right,valid]

theorem env_a (P : List Cell) (counter : CppState.Binding) (n a b : Int) (valid : i32.valid a = true) :
    penv1 (fields P counter n a b) 3 i32 = some a := by
  simp [fields,penv1,penv,List.getElem?_append_right,valid]

theorem env_b (P : List Cell) (counter : CppState.Binding) (n a b : Int) (valid : i32.valid b = true) :
    penv1 (fields P counter n a b) 4 i32 = some b := by
  simp [fields,penv1,penv,List.getElem?_append_right,valid]

theorem body_correct (P : List Cell) (counter : CppState.Binding) (vec : List Int)
    (rank : Nat → Nat) (forest : Forest vec rank) (length : vec.length < 2147483648)
    (a b : Nat) (ha : a < vec.length) (hb : b < vec.length) (fuel : Nat)
    (fa : rank a+2 ≤ fuel) (fb : rank b+2 ≤ fuel) :
    ∃ (out : PRW) (r1 r2 : Nat) (middle : List Int),
      pexecW i32 fuel Proofs.UnionFindCandidateInstance.UnionFind_same.body (fields P counter vec.length a b) vec = some out ∧
      out.ret = some (if r1=r2 then 1 else 0) ∧
      Compressed vec middle a r1 ∧ Compressed middle out.vec b r2 ∧ Forest out.vec rank ∧
      Reach vec a r1 ∧ Reach vec b r2 ∧ (∃ w, vec[r2]? = some w ∧ w < 0) ∧
      out.ps.mem.take P.length = P ∧ out.cost ≤ 90 * rank a+90 * rank b+180 ∧
      out.need ≤ P.length+80 ∧ out.wk ≤ rank a+rank b := by
  let initial := fields P counter (vec.length : Int) a b
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bvalid := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  have nv := env_n P counter vec.length a b nvalid
  have av := env_a P counter vec.length a b avalid
  have bv := env_b P counter vec.length a b bvalid
  have ga := condition_value initial vec 2 3 vec.length a nv av (by omega) (by omega)
  have gb := condition_value initial vec 2 4 vec.length b nv bv (by omega) (by omega)
  have ca := (pexecW_prim i32 fuel (.check (condition 2 3)) initial vec).trans
    (pstmtW_check_ok i32 initial vec (condition 2 3) 1 ga (by decide))
  have cb := (pexecW_prim i32 fuel (.check (condition 2 4)) initial vec).trans
    (pstmtW_check_ok i32 initial vec (condition 2 4) 1 gb (by decide))
  obtain ⟨one,r1,run1,ret1,state1,compressed1,forest1,cost1,need1,work1,tail1⟩ :=
    inlined_correct initial vec rank forest length 2 3 a nv av ha fuel fa
  have n1 : penv1 one.ps 2 i32 = some (one.vec.length : Int) := by
    rw [compressed1.length,state1]
    exact inline_env_old initial vec.length r1 vec.length 2 nv
  have b1 : penv1 one.ps 4 i32 = some (b : Int) := by
    rw [state1]
    exact inline_env_old initial vec.length r1 b 4 bv
  obtain ⟨two,r2,run2,ret2,state2,compressed2,forest2,cost2,need2,work2,tail2⟩ :=
    inlined_correct one.ps one.vec rank forest1 (by rw [compressed1.length]; exact length) 2 4 b n1 b1
      (by rw [compressed1.length]; exact hb) fuel fb
  have l0 : initial.bs.length = 4 := rfl
  have l1 : one.ps.bs.length = 8 := by rw [state1]; simp [inlineState,initial,fields]
  have r1inside : r1 < vec.length := by
    obtain ⟨w,found,_⟩ := compressed1.root
    exact (List.getElem?_eq_some_iff.mp found).1
  have r2inside : r2 < vec.length := by
    obtain ⟨w,found,_⟩ := compressed2.root
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [compressed1.length] at bound
    exact bound
  have r1valid := Proofs.VectorSumCall.i32_valid (r1 : Int) (by omega) (by omega)
  have r2valid := Proofs.VectorSumCall.i32_valid (r2 : Int) (by omega) (by omega)
  have firstValue : penv1 one.ps 8 i32 = some (r1 : Int) := by
    rw [state1]
    simpa only [l0] using inline_env_result initial vec.length r1 r1valid
  have firstFinal : penv1 two.ps 8 i32 = some (r1 : Int) := by
    rw [state2]
    exact inline_env_old one.ps one.vec.length r2 r1 8 firstValue
  have secondFinal : penv1 two.ps 12 i32 = some (r2 : Int) := by
    rw [state2]
    simpa only [l1] using inline_env_result one.ps one.vec.length r2 r2valid
  have value : vdenL i32 two.vec (penv1 two.ps) resultExpr = some (if r1=r2 then 1 else 0) := by
    rw [Proofs.VectorFillCall.vdenL_scalar _ _ _ _ rfl]
    simp only [resultExpr,NExpr.denote,firstFinal,secondFinal,Option.bind_some]
    have comparison : binaryValue .eq (r1 : Int) (r2 : Int) = if r1=r2 then 1 else 0 := by
      by_cases equal : r1=r2
      · simp [binaryValue,equal]
      · have unequal : (r1 : Int) ≠ (r2 : Int) := by omega
        simp [binaryValue,equal,unequal]
    rw [comparison]
    by_cases eq : r1=r2 <;> simp [eq,Proofs.PrefixSumsCall.bT,Ty.convert]
  have rprim := (pexecW_prim i32 fuel (.ret resultExpr) two.ps two.vec).trans
    (pstmtW_ret_ok i32 two.ps two.vec resultExpr _ value)
  have returned := seqW_ret (b := Sk) rprim rfl
  have after2 := tail2 retCmd _ returned
  have after1 := tail1 (plug (inlined one.ps.bs.length 2 4) retCmd) _ after2
  have all := seqW_some ca rfl (seqW_some cb rfl after1)
  rw [l0,l1] at all
  change pexecW i32 fuel body initial vec = some _ at all
  rw [← body_eq] at all
  obtain ⟨w,found,negative⟩ := compressed2.root
  have oldRoot : vec[r2]? = some w := (negative_entry compressed1 w negative).mp found
  refine ⟨_,r1,r2,one.vec,all,rfl,compressed1,compressed2,forest2,compressed1.reach,
    reach_backward compressed1 compressed2.reach,⟨w,oldRoot,negative⟩,?_,?_,?_,?_⟩
  · change two.ps.mem.take P.length = P
    rw [state2,state1]
    simp [inlineState,initial,fields,List.append_assoc]
  · have guardA : vwp (condition 2 3) = (7,7) := rfl
    have guardB : vwp (condition 2 4) = (7,7) := rfl
    have resultW : vwp resultExpr = (3,3) := rfl
    change (vwp (condition 2 3)).1+1+((vwp (condition 2 4)).1+1+
      (one.cost+(two.cost+((vwp resultExpr).1+1)))) ≤ _
    rw [guardA,guardB,resultW]; dsimp; omega
  · have guardA : vwp (condition 2 3) = (7,7) := rfl
    have guardB : vwp (condition 2 4) = (7,7) := rfl
    have resultW : vwp resultExpr = (3,3) := rfl
    change max (initial.mem.length+initial.bs.length+(vwp (condition 2 3)).2+2)
      (max (initial.mem.length+initial.bs.length+(vwp (condition 2 4)).2+2)
        (max one.need (max two.need (two.ps.mem.length+two.ps.bs.length+(vwp resultExpr).2+2)))) ≤ _
    have m1 : one.ps.mem.length = P.length+7 := by rw [state1]; simp [inlineState,initial,fields]
    have m2 : two.ps.mem.length = P.length+11 := by rw [state2]; simp [inlineState,m1]
    have l2 : two.ps.bs.length = 12 := by rw [state2]; simp [inlineState,l1]
    simp only [initial,fields,List.length_append,List.length_cons,List.length_nil] at need1
    rw [m1,l1] at need2
    simp [initial,fields,m2,l2,guardA,guardB,resultW]; omega
  · change 0+(0+(one.wk+(two.wk+0))) ≤ _
    omega

theorem prepare_same (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (en ea eb : NExpr) (n a b : Int) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true) (bs_ : eb.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32) (bt_ : eb.resultType = i32)
    (nv : en.denote (envOf caller) = some n) (av : ea.denote (envOf caller) = some a) (bv : eb.denote (envOf caller) = some b)
    (nvalid : i32.valid n = true) (avalid : i32.valid a = true) (bvalid : i32.valid b = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work+2+en.nodes+ea.nodes+eb.nodes ∧
      ∃ Sinit : NState, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_same.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea,.value eb] = some Sinit ∧
      Sinit.slots = [.vector 0,.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧
      Sinit.scalars.memory = callerP caller ++ [⟨i32,n⟩,⟨i32,a⟩,⟨i32,b⟩] ∧
      Sinit.scalars.bindings = [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩ ∧
      Sinit.scalars.work = q.scalars.work+6 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector i32 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 true) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  let charged := (caller.charge 1 1).charge 1 1
  have rcount : resolve (caller.charge 1 1) (.scalar i32 true true) (.scalarReference cslot) =
      some (charged,.scalarAddress i32 countBinding.address true) := by
    have same : (caller.charge 1 1).scalarCell cslot i32 = some (countBinding,⟨i32,count⟩) := cell
    simp [resolve,same,writable,charged]
  have core0 : Core caller charged := (core_charge caller 1 1).trans (core_charge (caller.charge 1 1) 1 1)
  obtain ⟨qn,nrun,ngood⟩ := scalar_eval en charged n ns (by rw [envOf_core core0]; exact nv)
  have coreN : Core caller qn := core0.trans ngood.1
  obtain ⟨qa,arun,agood⟩ := scalar_eval ea qn a as_ (by rw [envOf_core coreN]; exact av)
  have coreA : Core caller qa := coreN.trans agood.1
  obtain ⟨qb,brun,bgood⟩ := scalar_eval eb qa b bs_ (by rw [envOf_core coreA]; exact bv)
  have coreB : Core caller qb := coreA.trans bgood.1
  have rn : resolve charged (.scalar i32 false true) (.value en) = some (qn,.scalar i32 true n) := by
    simp [resolve,nt,nrun]
  have ra : resolve qn (.scalar i32 false true) (.value ea) = some (qa,.scalar i32 true a) := by
    simp [resolve,at_,arun]
  have rb : resolve qa (.scalar i32 false true) (.value eb) = some (qb,.scalar i32 true b) := by
    simp [resolve,bt_,brun]
  obtain ⟨cf,_,_,cm,cb,ck⟩ := coreB
  obtain ⟨_,_,_,found,_,cvalid⟩ := scalarCell_facts cell
  have inside : countBinding.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp found).1
  have inPrefix : (callerP caller)[countBinding.address]? = some ⟨i32,count⟩ := by
    rw [callerP,List.getElem?_append_left inside]
    exact found
  have fs : qb.frame.state = caller.frame.state := by rw [cf]
  have fr : qb.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : qb.frame.bindings = caller.frame.bindings := by rw [cf]
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩,0) := by
    have obj : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) := object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have rooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have maximum : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths rooted ok.flag
    simp only [Frame.bindRoot,obj,maximum,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  refine ⟨qb,?_,?_⟩
  · have wn := ngood.2.2.1
    have wa := agood.2.2.1
    have wb := bgood.2.2.1
    simp only [charged,NState.charge,NState.observe,CppState.State.observe] at wn
    omega
  · have hp : Proofs.UnionFindCandidateInstance.UnionFind_same.parameters =
        [.vector i32 true,.scalar i32 true true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true] := rfl
    rw [hp]
    simp [prepare,ok.valid,resolveAll,rvec,rcount,rn,ra,rb]
    simp only [callerP] at inPrefix
    simp [fs,fr,fb,cm,cb,ck,bound,bindAll,bindOne,CppState.bindArgument,nvalid,avalid,bvalid,cvalid,
      inPrefix,NState.observe,CppState.State.observe,callerP]
    have pn := ngood.2.2.2.2.1
    have pa := agood.2.2.2.2.1
    have pb := bgood.2.2.2.2.1
    simp only [charged,NState.charge,NState.observe,CppState.State.observe] at pn
    omega

def Connected (vec : List Int) (a b : Nat) : Prop :=
  ∃ z, Reach vec a z ∧ Reach vec b z ∧ ∃ w, vec[z]? = some w ∧ w < 0

theorem roots_connected (vec : List Int) (a b r1 r2 : Nat)
    (ra : Reach vec a r1) (rb : Reach vec b r2)
    (root1 : ∃ w, vec[r1]? = some w ∧ w < 0) (root2 : ∃ w, vec[r2]? = some w ∧ w < 0) :
    r1=r2 ↔ Connected vec a b := by
  constructor
  · intro same
    subst r2
    exact ⟨r1,ra,rb,root1⟩
  · rintro ⟨z,az,bz,root⟩
    exact (root_unique ra az root1 root).trans (root_unique rb bz root2 root).symm

theorem same_call (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
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
      (r1=r2 ↔ Connected vec a b) ∧
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes+eb.nodes) (90 * rank a+90 * rank b+220)
        caller.scalars.memory (rank a+rank b) V final := by
  have nvalid := Proofs.VectorSumCall.i32_valid (vec.length : Int) (by omega) (by omega)
  have avalid := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bvalueValid := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  obtain ⟨q,qwork,Sinit,prep,slots,memory,bindings,base,scopeEq,frame,work0,peak0⟩ :=
    prepare_same caller ok countBinding count cell writable en ea eb vec.length a b ns as_ bs_ nt at_ bt_ nv av bv
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
    body_correct (callerP caller) ⟨countBinding.address,true⟩ vec rank forest length a b ha hb
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
  obtain ⟨fuel,out,call,post⟩ := call_vecw vc true (fun _ => ⟨rfl,rfl⟩) caller
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
  exact ⟨Sinit,fuel,out,r1,r2,middle,res.vec,prep,call,c1,c2,newForest,
    roots_connected vec a b r1 r2 reach1 reach2 c1.root oldRoot2,post.relax (le_refl _) (le_refl _) writes⟩

end Proofs.UfFieldsSame
