import Proofs.CppConstructorWork
import Proofs.UfConstructionFootprint
import Proofs.UfTraceWork

namespace Proofs.UfConstructionWork
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedEval
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicOwnedState Proofs.MultiVecDynamic
open Proofs.UfConstructionStage Proofs.CppConstructionFootprint Proofs.UfConstructionFootprint
open Proofs.CppConstructorWork
open Proofs.CppRootModel Proofs.UfConstructionExport Proofs.CppConstructorFinish
open Proofs.UfBalancedReceiver (Strong)
open Proofs.DoublingNested (i32)

theorem sized_stage_work (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (small : n < 2147483648) (s : NState)
    (real : Realizes (entry P h params owner binding scope n) s) :
    ∃ t, CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct1.body s =
        .finished ⟨t,none,false⟩ ∧
      Realizes (final P h params owner binding scope n) t ∧
      t.frame = installed s.frame (filledState s.frame.state i32 s.scope n (-1)) i32 true s.scope ∧ t.work ≤ s.work+n+25 := by
  let st := entry P h params owner binding scope n
  let vs := vectorState P h params owner binding scope n
  let cs := countState P h params owner binding scope n
  let fs := final P h params owner binding scope n
  have fill := fill_step P h params owner binding scope n small
  obtain ⟨a,ra,reala⟩ := execute st vs s real (.fillVector i32 true countExpr valueExpr) fill
  have countPure : denote st.params st.core.locals st.core.contents countExpr = some (n : Int) := by
    simpa [st,entry,argLocals] using eval_count P [] (n : Int) [] [] (nat_i32 n small) (nat_u64 n small) st.params st.core.contents
  have countActual : countExpr.denote (Proofs.CppNestedEval.envOf s) = some (n : Int) := by
    rw [← Proofs.DynamicRealizes.scalar_denote _ _ _ s real.data countExpr rfl]
    exact countPure
  have valueActual : valueExpr.denote (Proofs.CppNestedEval.envOf s) = some (-1) := rfl
  have framea := fill_layout s i32 true countExpr valueExpr n (-1) rfl rfl countActual valueActual _ ra
  obtain ⟨b,rb,realb,frameb⟩ := execute_scalar vs cs a reala (.declare i32 true argument) (by trivial)
    (count_step P h params owner binding scope n small)
  obtain ⟨c,rc,realc,framec⟩ := execute_scalar cs fs b realb (.declare i32 true argument) (by trivial)
    (n_step P h params owner binding scope n small)
  obtain ⟨d,rd,reald,framed⟩ := execute_scalar fs fs c realc (.check checkExpr) (by trivial)
    (check_step P h params owner binding scope n small)
  have valuePure : denote st.params st.core.locals st.core.contents valueExpr = some (-1) := by
    rw [denote_scalar _ _ _ _ rfl]
    rfl
  have wa := fill_work st s a real i32 true countExpr valueExpr n (-1) countPure valuePure
    (Int.natCast_nonneg n) (by decide) (by simpa using nat_limit n small) rfl ra
  have wb := scalar_work vs cs a b reala (.declare i32 true argument) (by trivial)
    (count_step P h params owner binding scope n small) rb
  have wc := scalar_work cs fs b c realb (.declare i32 true argument) (by trivial)
    (n_step P h params owner binding scope n small) rc
  have wd := scalar_work fs fs c d realc (.check checkExpr) (by trivial)
    (check_step P h params owner binding scope n small) rd
  simp only [countExpr,valueExpr,argument,checkExpr,NExpr.nodes,Proofs.DynamicScalarSound.workBound,
    Int.toNat_natCast] at wa wb wc wd
  have last : CppNestedProgram.runFuel 4 (.primitive .skip) d = .finished ⟨d,none,false⟩ := rfl
  refine ⟨d,?_,reald,?_,by omega⟩
  · change CppNestedProgram.runFuel 8
      (.sequence (.primitive (.fillVector i32 true countExpr valueExpr))
        (.sequence (.primitive (.declare i32 true argument))
          (.sequence (.primitive (.declare i32 true argument))
            (.sequence (.primitive (.check checkExpr)) (.primitive .skip))))) s = _
    exact cons_actual 6 _ _ _ _ _ ra
      (cons_actual 5 _ _ _ _ _ rb (cons_actual 4 _ _ _ _ _ rc (cons_actual 3 _ _ _ _ _ rd last)))
  · rw [framed,framec,frameb]
    simpa using framea

theorem default_stage_work (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope : Nat) (s : NState)
    (real : Realizes (defaultEntry P h params owner binding scope) s) :
    ∃ t, CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct0.body s =
        .finished ⟨t,none,false⟩ ∧
      Realizes (defaultFinal P h params owner binding scope) t ∧
      t.frame = installed s.frame (emptyState s.frame.state i32 s.scope) i32 true s.scope ∧ t.work ≤ s.work+8 := by
  let st := defaultEntry P h params owner binding scope
  let vs := allocated st (.integer i32) true (.flat i32 scope []) 1
  let cs := {vs with core := ⟨DynamicStmt.declared vs.core.locals i32 true 0,vs.core.contents⟩}
  let fs := defaultFinal P h params owner binding scope
  have alloc : Proofs.DynamicOwnedControl.primitive (.declareVector i32 true) st = some ⟨vs,none,false⟩ := by
    simp [Proofs.DynamicOwnedControl.primitive,runConstruct,Proofs.CppVectorBindings.supported,vs,st,defaultEntry,i32]
  obtain ⟨a,ra,reala⟩ := execute st vs s real (.declareVector i32 true) alloc
  have framea := empty_layout s i32 true _ ra
  have dc : Proofs.DynamicOwnedControl.primitive (.declare i32 true (.literal i32 0)) vs = some ⟨cs,none,false⟩ := by
    apply declare_value vs i32 true (.literal i32 0) 0 0 <;> rfl
  obtain ⟨b,rb,realb,frameb⟩ := execute_scalar vs cs a reala (.declare i32 true (.literal i32 0)) (by trivial) dc
  have dn : Proofs.DynamicOwnedControl.primitive (.declare i32 true (.literal i32 0)) cs = some ⟨fs,none,false⟩ := by
    have step := declare_value cs i32 true (.literal i32 0) 0 0 rfl rfl
    simpa [cs,vs,st,fs,defaultEntry,defaultFinal,allocated,newParameter,
      DynamicConstructCore.appended,DynamicStmt.declared,List.append_assoc] using step
  obtain ⟨c,rc,realc,framec⟩ := execute_scalar cs fs b realb (.declare i32 true (.literal i32 0)) (by trivial) dn
  have wa := empty_work st s a real i32 true (by decide) ra
  have wb := scalar_work vs cs a b reala (.declare i32 true (.literal i32 0)) (by trivial) dc rb
  have wc := scalar_work cs fs b c realb (.declare i32 true (.literal i32 0)) (by trivial) dn rc
  simp only [Proofs.DynamicScalarSound.workBound,NExpr.nodes] at wb wc
  have last : CppNestedProgram.runFuel 5 (.primitive .skip) c = .finished ⟨c,none,false⟩ := rfl
  refine ⟨c,?_,realc,?_,by omega⟩
  · exact cons_actual 6 _ _ _ _ _ ra (cons_actual 5 _ _ _ _ _ rb (cons_actual 4 _ _ _ _ _ rc last))
  · rw [framec,frameb,framea]


theorem profile_vector (caller callee : NState) (h : ContentsHeap) (vec : List Int) (count n : Int)
    (hasArgument : Bool) (real : Realizes (profile caller h vec count n hasArgument) callee) :
    callee.vectorSlot (vectorField hasArgument) = some 0 ∧
    callee.frame.bindings[0]? = some ⟨caller.frame.state.storage.objects.length,.integer i32,true,.root (caller.scope+1)⟩ ∧
    Models callee.frame.state caller.frame.state.storage.objects.length (.flat i32 (caller.scope+1) vec) := by
  obtain ⟨heap,m,family,erased⟩ := real.data.heap
  let root := caller.frame.state.storage.objects.length
  let q : Parameter := ⟨0,root,.integer i32,caller.scope+1,true,true⟩
  have member : q ∈ (profile caller h vec count n hasArgument).params := by simp [profile,q,root]
  have logical : eraseHeap heap root = some (.flat i32 (caller.scope+1) vec) := by
    rw [erased]
    simp [profile,root,putContents]
  have model := family.models root _ (Proofs.DynamicFlatSound.flat_lift heap root i32 (caller.scope+1) vec logical)
  refine ⟨?_,family.bindings q member,model⟩
  have slots := congrArg Locals.slots real.data.locals
  cases hasArgument <;> simp [profile,locals,snapshot] at slots <;>
    simp [NState.vectorSlot,vectorField,slots]

theorem export_work (caller callee out : NState) (h : ContentsHeap) (vec : List Int) (count n : Int)
    (hasArgument : Bool) (cv : i32.valid count = true) (nv : i32.valid n = true)
    (valid : caller.frame.state.wellFormed = true)
    (strict : ∀ owner k, caller.frame.state.forest.context owner = some k → k ≤ caller.scope)
    (real : Realizes (profile caller h vec count n hasArgument) callee)
    (forest : callee.frame.state.forest = caller.frame.state.forest.declareRoot i32 (caller.scope+1))
    (actual : Proofs.CppConstructorFinish.finish caller callee (vectorField hasArgument) (.integer i32)
      (fields hasArgument) = some (out,reference caller 2)) : out.work = callee.work+3 := by
  obtain ⟨slot,binding,model⟩ := profile_vector caller callee h vec count n hasArgument real
  have scopeEq : callee.scope = caller.scope+1 := real.scopedState
  have captured := captureAll_ok callee (fields hasArgument) (payload count n)
    (fields_match callee _ count n hasArgument cv nv real.data.locals)
  have scalarWork := finish_scalar_work caller callee out (vectorField hasArgument) (.integer i32)
    (fields hasArgument) (payload count n) (reference caller 2) captured actual
  simp only [payload,List.length_cons,List.length_nil] at scalarWork
  obtain ⟨frame,_,_⟩ := Proofs.CppConstructionRetire.finish_frame caller callee out (vectorField hasArgument)
    0 (.integer i32) (fields hasArgument) (reference caller 2) _ (.flat i32 (caller.scope+1) vec)
    slot binding model rfl scopeEq.symm actual
  let moved := Proofs.DynamicTransfer.movedFrame callee.frame caller.frame.state.storage.objects.length caller.scope
    (.flat i32 (caller.scope+1) vec)
  have lengths := (Proofs.CppNestedVectorStore.wellFormed_parts caller.frame.state valid).1
  have movedForest : moved.state.forest = caller.frame.state.forest.declareRoot i32 caller.scope := by
    change (callee.frame.state.forest.transferred caller.frame.state.storage.objects.length caller.scope
      (Proofs.CppNestedConstruct.flatTag i32 (caller.scope+1))) = _
    rw [forest,← lengths,declared_transferred]
  have fresh : ∀ owner, moved.state.forest.context owner ≠ some callee.scope := by
    intro owner found
    rw [movedForest] at found
    have bound := declared_scope_bound caller.frame.state.forest i32 caller.scope strict owner callee.scope found
    rw [scopeEq] at bound
    omega
  have retired := Proofs.CppNestedScope.retired_fresh moved.state callee.scope fresh
  have storageWork : out.frame.state.storage.work = callee.frame.state.storage.work := by
    rw [frame]
    change (moved.state.retired callee.scope).storage.work = _
    rw [retired]
    rfl
  unfold NState.work
  rw [scalarWork,storageWork]
  omega

theorem construct_sized_work (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (envOf caller) = some (n : Int)) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
      (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
        .finished (out,Proofs.CppConstructorFinish.reference caller 2) ∧
      Strong out (Proofs.UfReceiverState.layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) ∧ out.work ≤ caller.work+en.nodes+n+30 := by
  obtain ⟨init,prepared,locals,initFrame,initScope,initBase,initWork⟩ :=
    Proofs.UfConstructionPrepare.prepare_sized caller valid en n scalar type value (nat_i32 n small)
  have real := Proofs.UfConstructionPrepare.sized_real caller init heap valid models lengths n locals initFrame initScope
  obtain ⟨callee,ran,after,frame,stageWork⟩ := sized_stage_work _ _ _ _ _ _ n small init real
  have profileReal : Realizes (profile caller (eraseHeap heap) (List.replicate n (-1)) n n true) callee := after
  obtain ⟨out,finished,initialized⟩ := export_fields caller callee (eraseHeap heap) (List.replicate n (-1)) n n true
    (nat_i32 n small) (nat_i32 n small) profileReal
  have forestEq : callee.frame.state.forest = caller.frame.state.forest.declareRoot i32 (caller.scope+1) := by
    rw [frame,initFrame,initScope]
    rfl
  have endWork := export_work caller callee out (eraseHeap heap) (List.replicate n (-1)) n n true
    (nat_i32 n small) (nat_i32 n small) valid strict profileReal forestEq finished
  have executed := construct_of_steps Proofs.UnionFindConstructionInstance.UnionFind_construct1 8 caller init callee out
    [.value en] (vectorField true) (.integer i32) (fields true) (reference caller 2) rfl prepared ran finished
  obtain ⟨other,otherRun,strong⟩ := Proofs.UfBalancedReceiver.construct_sized caller heap valid models lengths strict base en n small scalar type value
  have same : other = out := congrArg Prod.fst (Proofs.CppLoop.Outcome.finished.inj (otherRun.symm.trans executed))
  have prepWork : init.work ≤ caller.work+en.nodes+2 := by
    unfold NState.work
    rw [initFrame]
    change init.scalars.work+caller.frame.state.storage.work ≤
      caller.scalars.work+caller.frame.state.storage.work+en.nodes+2
    omega
  refine ⟨out,executed,by simpa only [same] using strong,?_⟩
  rw [endWork]
  omega

theorem construct_default_work (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
      (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
        .finished (out,Proofs.CppConstructorFinish.reference caller 2) ∧
      Strong out (Proofs.UfReceiverState.layoutOf caller) [] 0 (fun _ => 0) ∧ out.work ≤ caller.work+12 := by
  obtain ⟨init,prepared,locals,initFrame,initScope,initBase,initWork⟩ :=
    Proofs.UfConstructionPrepare.prepare_default caller valid
  have real := Proofs.UfConstructionPrepare.default_real caller init heap valid models lengths locals initFrame initScope
  obtain ⟨callee,ran,after,frame,stageWork⟩ := default_stage_work _ _ _ _ _ _ init real
  have profileReal : Realizes (profile caller (eraseHeap heap) [] 0 0 false) callee := after
  obtain ⟨out,finished,initialized⟩ := export_fields caller callee (eraseHeap heap) [] 0 0 false rfl rfl profileReal
  have forestEq : callee.frame.state.forest = caller.frame.state.forest.declareRoot i32 (caller.scope+1) := by
    rw [frame,initFrame,initScope]
    rfl
  have endWork := export_work caller callee out (eraseHeap heap) [] 0 0 false rfl rfl valid strict profileReal forestEq finished
  have executed := construct_of_steps Proofs.UnionFindConstructionInstance.UnionFind_construct0 8 caller init callee out
    [] (vectorField false) (.integer i32) (fields false) (reference caller 2) rfl prepared ran finished
  obtain ⟨other,otherRun,strong⟩ := Proofs.UfBalancedReceiver.construct_default caller heap valid models lengths strict base
  have same : other = out := congrArg Prod.fst (Proofs.CppLoop.Outcome.finished.inj (otherRun.symm.trans executed))
  have prepWork : init.work = caller.work+1 := by
    unfold NState.work
    rw [initFrame,initWork]
    change caller.scalars.work+1+caller.frame.state.storage.work =
      caller.scalars.work+caller.frame.state.storage.work+1
    omega
  refine ⟨out,executed,by simpa only [same] using strong,?_⟩
  rw [endWork]
  omega

theorem constructed_trace_work (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int))
    (ops : List Proofs.UfReceiverTrace.Operation) (allowed : ∀ op ∈ ops, op.allowed n) :
    ∃ receiver fuels out vec count rank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      Proofs.UfReceiverTrace.runCalls fuels ops receiver (Proofs.UfReceiverState.layoutOf caller) = .finished (out,answers) ∧
      Strong out (Proofs.UfReceiverState.layoutOf caller) vec count rank ∧ vec.length = n ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ caller.work+en.nodes+n+30 + ops.length * Proofs.UfTraceWork.budget n := by
  obtain ⟨receiver,constructed,rep,constructionWork⟩ := construct_sized_work caller heap valid models lengths strict base en n small scalar type value
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalRep,length,fl,al,work⟩ := Proofs.UfTraceWork.calls_work
    ops receiver (Proofs.UfReceiverState.layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) rep (by simpa using allowed)
  simp only [List.length_replicate] at work length
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalRep,length,fl,al,by omega⟩

theorem default_trace_work (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (ops : List Proofs.UfReceiverTrace.Operation) (allowed : ∀ op ∈ ops, op.allowed 0) :
    ∃ receiver fuels out vec count rank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      Proofs.UfReceiverTrace.runCalls fuels ops receiver (Proofs.UfReceiverState.layoutOf caller) = .finished (out,answers) ∧
      Strong out (Proofs.UfReceiverState.layoutOf caller) vec count rank ∧ vec.length = 0 ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ caller.work+12 + ops.length * Proofs.UfTraceWork.budget 0 := by
  obtain ⟨receiver,constructed,rep,constructionWork⟩ := construct_default_work caller heap valid models lengths strict base
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalRep,length,fl,al,work⟩ := Proofs.UfTraceWork.calls_work
    ops receiver (Proofs.UfReceiverState.layoutOf caller) [] 0 (fun _ => 0) rep allowed
  simp only [List.length_nil] at work length
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalRep,length,fl,al,by omega⟩

end Proofs.UfConstructionWork
