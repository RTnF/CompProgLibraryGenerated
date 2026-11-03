import Proofs.VecShift
import Proofs.Generated.UnionFindCandidate
import Proofs.UfBounds
import Proofs.ExtremaCall

set_option maxRecDepth 4000

namespace Proofs.UfFieldsRoot
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

abbrev guardExpr : NExpr := .logical true
  (.binary bT .le (.literal i32 0) (.variable i32 3))
  (.binary bT .lt (.variable i32 3) (.variable i32 2))

def fields (P : List Cell) (counter : CppState.Binding) (n a : Int) : PS :=
  VecShift.pad [counter,⟨P.length,true⟩] (stI (P++[⟨i32,n⟩]) a)

theorem body_eq : Proofs.UnionFindCandidateInstance.UnionFind_root.body =
    UfBounds.checked guardExpr (VecShift.command 2 bodyF) := rfl

theorem env_n (P : List Cell) (counter : CppState.Binding) (n a : Int)
    (valid : i32.valid n = true) : penv1 (fields P counter n a) 2 i32 = some n := by
  simp [fields,VecShift.pad,stI,penv1,penv,List.append_assoc,valid]

theorem env_a (P : List Cell) (counter : CppState.Binding) (n a : Int)
    (valid : i32.valid a = true) : penv1 (fields P counter n a) 3 i32 = some a := by
  have shifted := VecShift.environment [counter,⟨P.length,true⟩] (stI (P++[(⟨i32,n⟩ : Cell)]) a) 1 i32
  have original := env_i1 (P++[(⟨i32,n⟩ : Cell)]) a valid
  simpa only [fields,VecShift.slot,List.length_cons,List.length_nil] using shifted.trans original

theorem guard_low (P : List Cell) (counter : CppState.Binding) (n a : Int)
    (valid : i32.valid a = true) (nonneg : 0 ≤ a) :
    (NExpr.binary bT .le (.literal i32 0) (.variable i32 3)).denote (penv1 (fields P counter n a)) = some 1 := by
  simp only [NExpr.denote,show i32.valid 0 = true from rfl,ite_true,env_a P counter n a valid,Option.bind_some]
  change bT.convert (if 0 ≤ a then 1 else 0) = some 1
  rw [ite_eq_left nonneg]; rfl

theorem guard_high (P : List Cell) (counter : CppState.Binding) (n a : Int)
    (nv : i32.valid n = true) (av : i32.valid a = true) (less : a < n) :
    (NExpr.binary bT .lt (.variable i32 3) (.variable i32 2)).denote (penv1 (fields P counter n a)) = some 1 := by
  simp only [NExpr.denote,env_a P counter n a av,env_n P counter n a nv,Option.bind_some]
  change bT.convert (if a < n then 1 else 0) = some 1
  rw [ite_eq_left less]; rfl

theorem guard_value (P : List Cell) (counter : CppState.Binding) (ps : List Int)
    (length : ps.length < 2147483648) (a : Nat) (inside : a < ps.length) :
    vdenL i32 ps (penv1 (fields P counter ps.length a)) guardExpr = some 1 := by
  have nv : i32.valid (ps.length : Int) = true := Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)
  have av : i32.valid (a : Int) = true := Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)
  rw [vdenL_scalar _ _ _ _ rfl]
  change (NExpr.logical true _ _).denote _ = some 1
  rw [NExpr.denote,guard_low P counter ps.length a av (by omega)]
  simp [guard_high P counter ps.length a nv av (by omega)]

theorem body_correct (P : List Cell) (counter : CppState.Binding) (ps : List Int)
    (rank : Nat → Nat) (forest : Forest ps rank) (length : ps.length < 2147483648)
    (a : Nat) (inside : a < ps.length) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (res : PRW) (r : Nat),
      pexecW i32 fuel Proofs.UnionFindCandidateInstance.UnionFind_root.body (fields P counter ps.length a) ps = some res ∧
      res.ret = some (r : Int) ∧ Compressed ps res.vec a r ∧ Forest res.vec rank ∧
      recursive (rank a+1) ps a = some (res.vec,r) ∧
      res.ps.mem.take P.length = P ∧
      res.cost ≤ 90 * rank a+80 ∧ res.need ≤ P.length+80 ∧ res.wk ≤ rank a := by
  let base := P++[(⟨i32,(ps.length : Int)⟩ : Cell)]
  let prefixBindings : List CppState.Binding := [counter,⟨P.length,true⟩]
  obtain ⟨res,r,run,ret,reach,rl,root,inv,cost,need,work,saved⟩ :=
    body_exec_find base ps rank forest length a inside fuel enough
  have shifted := VecShift.execution i32 fuel bodyF (stI base a) ps prefixBindings
  rw [run] at shifted
  simp only [Option.map_some] at shifted
  have full := UfBounds.prepend (guard_value P counter ps length a inside) shifted
  have blen : prefixBindings.length = 2 := rfl
  rw [blen,← body_eq] at full
  obtain ⟨sameLength,entries⟩ := inv2_final ps res.vec a r root inv
  have compressed : Compressed ps res.vec a r := ⟨sameLength,reach,root,entries⟩
  obtain ⟨oldVec,z,oldRun,oldCompressed⟩ := recursive_correct ps rank forest (rank a+1) a inside (by omega)
  obtain ⟨sameRoot,sameArray⟩ := unique oldCompressed compressed
  rw [sameRoot,sameArray] at oldRun
  have newForest := find_forest ps res.vec rank forest a r reach rl root sameLength entries
    (Proofs.VectorSumCall.i32_valid _ (by omega) (by omega))
  refine ⟨_,r,full,ret,compressed,newForest,oldRun,?_,?_,?_,work⟩
  · change res.ps.mem.take P.length = P
    calc res.ps.mem.take P.length = (res.ps.mem.take base.length).take P.length := by
          rw [List.take_take,Nat.min_eq_left (by simp [base])]
      _ = base.take P.length := by rw [saved]
      _ = P := by simp [base]
  · change (vwp guardExpr).1+1+res.cost ≤ _
    have wp : vwp guardExpr = (7,7) := rfl
    rw [wp]; dsimp; omega
  · change max ((fields P counter ps.length a).mem.length+(fields P counter ps.length a).bs.length+(vwp guardExpr).2+2)
      (res.need+prefixBindings.length) ≤ _
    have wp : vwp guardExpr = (7,7) := rfl
    simp only [fields,VecShift.pad,stI,List.length_append,List.length_cons,List.length_nil,wp]
    simp only [base,List.length_append,List.length_cons,List.length_nil] at need
    simp [prefixBindings]; omega

theorem prepare_fields (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
    (ok : VOKWF caller vslot vb V vsc vbuf) (countBinding : CppState.Binding) (count : Int)
    (cell : caller.scalarCell cslot i32 = some (countBinding,⟨i32,count⟩)) (writable : countBinding.writable = true)
    (en ea : NExpr) (n a : Int) (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true)
    (nt : en.resultType = i32) (at_ : ea.resultType = i32)
    (nv : en.denote (envOf caller) = some n) (av : ea.denote (envOf caller) = some a)
    (nvalid : i32.valid n = true) (avalid : i32.valid a = true) :
    ∃ q : NState, q.scalars.work ≤ caller.scalars.work+2+en.nodes+ea.nodes ∧
      ∃ Sinit : NState, prepare caller Proofs.UnionFindCandidateInstance.UnionFind_root.parameters
        [.vectorReference vslot,.scalarReference cslot,.value en,.value ea] = some Sinit ∧
      Sinit.slots = [.vector 0,.scalar 0,.scalar 1,.scalar 2] ∧
      Sinit.scalars.memory = callerP caller ++ [⟨i32,n⟩,⟨i32,a⟩] ∧
      Sinit.scalars.bindings = [⟨countBinding.address,true⟩,⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩ ∧
      Sinit.scalars.work = q.scalars.work+5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
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
  have rn : resolve charged (.scalar i32 false true) (.value en) = some (qn,.scalar i32 true n) := by
    simp [resolve,nt,nrun]
  have ra : resolve qn (.scalar i32 false true) (.value ea) = some (qa,.scalar i32 true a) := by
    simp [resolve,at_,arun]
  obtain ⟨cf,_,_,cm,cb,ck⟩ := coreA
  obtain ⟨_,_,_,found,_,cvalid⟩ := scalarCell_facts cell
  have inside : countBinding.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp found).1
  have inPrefix : (callerP caller)[countBinding.address]? = some ⟨i32,count⟩ := by
    rw [callerP,List.getElem?_append_left inside]
    exact found
  have fs : qa.frame.state = caller.frame.state := by rw [cf]
  have fr : qa.frame.rootWritable = caller.frame.rootWritable := by rw [cf]
  have fb : qa.frame.bindings = caller.frame.bindings := by rw [cf]
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩,0) := by
    have obj : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) := object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have rooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have maximum : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths rooted ok.flag
    simp only [Frame.bindRoot,obj,maximum,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  refine ⟨qa,?_,?_⟩
  · have wn := ngood.2.2.1
    have wa := agood.2.2.1
    simp only [charged,NState.charge,NState.observe,CppState.State.observe] at wn
    omega
  · have hp : Proofs.UnionFindCandidateInstance.UnionFind_root.parameters =
        [.vector i32 true,.scalar i32 true true,.scalar i32 false true,.scalar i32 false true] := rfl
    rw [hp]
    simp [prepare,ok.valid,resolveAll,rvec,rcount,rn,ra]
    simp only [callerP] at inPrefix
    simp [fs,fr,fb,cm,cb,ck,bound,bindAll,bindOne,CppState.bindArgument,nvalid,avalid,cvalid,
      inPrefix,NState.observe,CppState.State.observe,callerP]
    have pn := ngood.2.2.2.2.1
    have pa := agood.2.2.2.2.1
    simp only [charged,NState.charge,NState.observe,CppState.State.observe] at pn
    omega

theorem root_call (caller : NState) {vslot vb V vsc cslot : Nat} {vbuf : Buffer Value}
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
      ScalarPost3 caller Sinit out (en.nodes+ea.nodes) (90 * rank a+140) caller.scalars.memory (rank a) V vec := by
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
  obtain ⟨fuel,out,call,post⟩ := call_vecw vc true (fun _ => ⟨rfl,rfl⟩) caller
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
  exact ⟨Sinit,fuel,out,r,res.vec,prep,call,compressed,newForest,oldRun,post.relax (le_refl _) (le_refl _) writes⟩

end Proofs.UfFieldsRoot
