import Proofs.UfReadBody
import Proofs.CppMoveReceiverPermissions
import Proofs.UfReceiverLayout

namespace Proofs.UfReadCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMoveContext
open Proofs.CppMoveCallBindings Proofs.CppMovePreparedCall Proofs.CppMoveHeaders
open Proofs.CppMoveFrame Proofs.CppMoveReadReceiver Proofs.CppMoveObjectReceiver Proofs.CppConstructorFinish
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverLayout Proofs.CppMoveReceiverPermissions
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.DoublingNested Proofs.StraightLine Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open Proofs.UfRootCall Proofs.UfReadPrograms
open Proofs.CppState (Cell)

def scalarLimit (caller : Context) (initial : NState) (prefixLength : Nat) : Nat :=
  max (max caller.scalars.peak (UfReadBody.scalarBudget initial prefixLength)) (scalarLive caller)
def totalLimit (caller : Context) (initial : NState) (prefixLength live : Nat) : Nat :=
  max (max caller.peak (max initial.peak (UfReadBody.scalarBudget initial prefixLength+UfReadBody.heapBudget initial live)))
    (scalarLimit caller initial prefixLength+UfReadBody.heapBudget initial live)
structure Resources (caller out : Context) (initial : NState) (prefixLength live : Nat) : Prop where
  scalar : out.scalars.peak ≤ scalarLimit caller initial prefixLength
  heap : out.objects.heap.peak ≤ UfReadBody.heapBudget initial live
  total : out.peak ≤ totalLimit caller initial prefixLength live

theorem finish_call (program : NProgram) (fuel : Nat) (caller prepared : Context) (initial callee : NState)
    (retType : Ty) (args : List NArgument) (value : Int) (prefixLength live : Nat)
    (scalar : program.result = .scalar retType) (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, (project caller i32).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap) (valid : (project caller i32).frame.state.wellFormed = true)
    (preparedRun : prepareArguments caller i32 program.parameters args = some prepared)
    (compacted : compact (project prepared i32) = some initial)
    (ran : runFuel fuel program.body initial = .finished ⟨callee,some (.scalar value),false⟩)
    (saved : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory)
    (valueValid : retType.valid value = true)
    (scalarBound : callee.scalars.peak ≤ UfReadBody.scalarBudget initial prefixLength)
    (heapBound : callee.frame.state.storage.peak ≤ UfReadBody.heapBudget initial live)
    (totalBound : callee.peak ≤ max initial.peak (UfReadBody.scalarBudget initial prefixLength+UfReadBody.heapBudget initial live))
    (liveEq : callee.frame.state.liveSpace = live)
    (baseEq : callee.frame.state.storage.baseSpace = initial.frame.state.storage.baseSpace) :
    ∃ out, callFuel program fuel caller i32 args = .finished (out,.scalar value) ∧
      work out = callee.work+1 ∧ out.scalars.memory = caller.scalars.memory ∧
      (∀ owner, (project out i32).frame.state.storage.lookup owner = callee.frame.state.storage.lookup owner) ∧
      Resources caller out initial prefixLength live := by
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    have sizes := congrArg List.length saved
    simp only [List.length_take] at sizes
    omega
  obtain ⟨out,actual,workEq,memory,lookups,scalarEq,heapEq,peakEq⟩ := call_of_body program fuel caller prepared initial
    i32 retType args callee value scalar allowed contexts covered valid preparedRun compacted ran fits (by rw [saved]) valueValid
  have scalarPeak : out.scalars.peak ≤ scalarLimit caller initial prefixLength := by
    rw [scalarEq]
    exact max_le_max (max_le_max (Nat.le_refl _) scalarBound) (Nat.le_refl _)
  have heapPeak : out.objects.heap.peak ≤ UfReadBody.heapBudget initial live := by
    rw [heapEq]
    apply Nat.max_le.mpr
    refine ⟨heapBound,?_⟩
    rw [liveEq,baseEq]
    exact Nat.le_trans (Nat.sub_le_sub_right (Nat.le_succ _) _) (Nat.le_max_right _ _)
  refine ⟨out,actual,workEq,memory.trans saved,lookups,scalarPeak,heapPeak,?_⟩
  rw [peakEq]
  exact max_le_max (max_le_max (Nat.le_refl _) totalBound) (Nat.add_le_add scalarPeak heapPeak)

theorem size_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (rank : Nat → Nat) (forest : Forest data.items rank) (length : data.items.length < 2147483648)
    (weights : Proofs.UfFieldsSize.Weights data.items) (a : Nat) (inside : a < data.items.length)
    (expression : NExpr) (typed : expression.resultType = i32) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat) (out : Context) (root : Nat) (weight : Int),
      prepareArguments s i32 sizeProgram.parameters (readArguments s object receiver [(expression,(a : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      callFuel sizeProgram fuel s i32 (readArguments s object receiver [(expression,(a : Int))]) = .finished (out,.scalar (-weight)) ∧
      Reach data.items a root ∧ root < data.items.length ∧ data.items[root]? = some weight ∧ weight < 0 ∧
      work out ≤ work prepared+16*rank a+41 ∧ out.scalars.memory = s.scalars.memory ∧ initial.frame.state.liveSpace = vc.L0 ∧ vc.R = data.owner ∧
      Resources s out initial (receiverPrefix s).length vc.L0 ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = data.items.map Value.integer := by
  have ready : Ready s i32 [(expression,(a : Int))] := by
    intro e value member
    rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
    exact ⟨typed,scalar,denotes⟩
  obtain ⟨prepared,initial,vc,buffer,prep,compacted,qs,fw,ty,readonly,flag,sc,actual,base,scope⟩ :=
    prepare_read_frame s object receiver sizeProgram [(expression,(a : Int))] ready rfl
      readable unique covered valid limit contexts
  have same : buffer = data := Option.some.inj (actual.symm.trans current)
  subst buffer
  let P := receiverPrefix s
  let ps := fields P receiver.counter.address [receiver.size.value,(a : Int)]
  have qs' := qs_size initial P receiver.counter.address receiver.size.value a qs
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  obtain ⟨res,root,weight,run,ret,reach,rl,atRoot,negative,valueValid,unchanged,state,cost,need,writes⟩ :=
    Proofs.UfReadQueries.size_correct ps rfl data.items rank forest length weights receiver.size.value receiver.size.valid a inside
      (size_n P receiver.counter.address receiver.size.value a receiver.size.valid)
      (size_a P receiver.counter.address receiver.size.value a av) (rank a+2) (by omega)
  have resident : ps.mem.length+ps.bs.length ≤ P.length+48 := by simp [ps,fields,cells,valueBindings,addresses]
  have need' : res.need ≤ P.length+48 := by
    simp only [ps,fields,cells,valueBindings,addresses,List.map_cons,List.map_nil,List.length_append,
      List.length_cons,List.length_nil] at need
    omega
  obtain ⟨fuel,step,ran,returned,breaking,memory,bodyCost,scalarPeak,heapPeak,totalPeak,live,baseEq,newBuffer,found,items⟩ :=
    Proofs.UfReadBody.execute initial vc sizeProgram.body ps data.items (rank a+2) res P.length (box data)
      ty (by decide +kernel) (by decide +kernel) run unchanged writes qs' fw
      (by rw [base]; simp [ps,fields,P]; omega) resident need' (Nat.le_of_eq sc)
  rw [ret] at returned
  have stepEq : step = ⟨step.state,some (.scalar (-weight)),false⟩ := by
    cases step with
    | mk st rr br => simp_all
  have ran' : runFuel fuel sizeProgram.body initial = .finished ⟨step.state,some (.scalar (-weight)),false⟩ := by
    rw [←stepEq]; exact ran
  have savedP : step.state.scalars.memory.take P.length = P := by
    rw [memory,state]
    simp [Proofs.UfReadInline.inlineState,ps,fields,cells,List.append_assoc]
  have saved : step.state.scalars.memory.take s.scalars.memory.length = s.scalars.memory := by
    calc _ = (step.state.scalars.memory.take P.length).take s.scalars.memory.length := by
           rw [List.take_take,Nat.min_eq_left (Proofs.UfReceiverLayout.prefix_length s)]
         _ = s.scalars.memory := by rw [savedP]; exact Proofs.UfReceiverLayout.prefix_take s
  have compactData := compact_metadata (project prepared i32) initial compacted
  have prepEffects := prepareArguments_effects s prepared i32 sizeProgram.parameters _ prep
  have stateEq : initial.frame.state = (project s i32).frame.state := by
    rw [compactData.1]; simp only [project,materialize,prepEffects.1]
  have sourceValid : (project s i32).frame.state.wellFormed = true := by rw [←stateEq]; exact fw.valid
  obtain ⟨out,call,workEq,scalarMemory,lookups,resources⟩ := finish_call sizeProgram fuel s prepared initial step.state i32
    (readArguments s object receiver [(expression,(a : Int))]) (-weight) P.length vc.L0 rfl (by decide +kernel)
    contexts covered sourceValid prep compacted ran' saved valueValid scalarPeak heapPeak totalPeak live baseEq
  have initialWork : initial.work = work prepared := by
    rw [←project_work prepared i32]
    unfold NState.work
    rw [compactData.1,compactData.2.2.1]
  refine ⟨prepared,initial,vc,fuel,out,root,weight,prep,compacted,call,reach,rl,atRoot,negative,?_,scalarMemory,fw.live,fw.owner.symm,resources,newBuffer,?_,items⟩
  · rw [workEq]
    rw [initialWork] at bodyCost
    omega
  · rw [lookups]; exact found

theorem same_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (rank : Nat → Nat) (forest : Forest data.items rank) (length : data.items.length < 2147483648)
    (a b : Nat) (ha : a < data.items.length) (hb : b < data.items.length)
    (ea eb : NExpr) (ready : Ready s i32 [(ea,(a : Int)),(eb,(b : Int))])
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat) (out : Context) (root1 root2 : Nat),
      prepareArguments s i32 sameProgram.parameters (readArguments s object receiver [(ea,(a : Int)),(eb,(b : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      callFuel sameProgram fuel s i32 (readArguments s object receiver [(ea,(a : Int)),(eb,(b : Int))]) = .finished (out,.scalar (if root1=root2 then 1 else 0)) ∧
      Reach data.items a root1 ∧ Reach data.items b root2 ∧ root1 < data.items.length ∧ root2 < data.items.length ∧
      (∃ w, data.items[root1]? = some w ∧ w < 0) ∧ (∃ w, data.items[root2]? = some w ∧ w < 0) ∧
      work out ≤ work prepared+16*rank a+16*rank b+75 ∧ out.scalars.memory = s.scalars.memory ∧ initial.frame.state.liveSpace = vc.L0 ∧ vc.R = data.owner ∧
      Resources s out initial (receiverPrefix s).length vc.L0 ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = data.items.map Value.integer := by
  obtain ⟨prepared,initial,vc,buffer,prep,compacted,qs,fw,ty,readonly,flag,sc,actual,base,scope⟩ :=
    prepare_read_frame s object receiver sameProgram [(ea,(a : Int)),(eb,(b : Int))] ready rfl
      readable unique covered valid limit contexts
  have same : buffer = data := Option.some.inj (actual.symm.trans current)
  subst buffer
  let P := receiverPrefix s
  let ps := fields P receiver.counter.address [receiver.size.value,(a : Int),(b : Int)]
  have qs' := qs_same initial P receiver.counter.address receiver.size.value a b qs
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by omega)
  have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by omega)
  obtain ⟨res,root1,root2,run,ret,reach1,reach2,rl1,rl2,rootFact1,rootFact2,unchanged,state,cost,need,writes⟩ :=
    Proofs.UfReadQueries.same_correct ps rfl data.items rank forest length receiver.size.value receiver.size.valid a b ha hb
      (same_n P receiver.counter.address receiver.size.value a b receiver.size.valid)
      (same_a P receiver.counter.address receiver.size.value a b av)
      (same_b P receiver.counter.address receiver.size.value a b bv) (rank a+rank b+2) (by omega) (by omega)
  have valueValid : Proofs.PrefixSumsCall.bT.valid (if root1=root2 then 1 else 0) = true := by
    by_cases equal : root1=root2
    · rw [ite_eq_left equal]; rfl
    · rw [ite_eq_right equal]; rfl
  have resident : ps.mem.length+ps.bs.length ≤ P.length+48 := by simp [ps,fields,cells,valueBindings,addresses]
  have need' : res.need ≤ P.length+48 := by
    simp only [ps,fields,cells,valueBindings,addresses,List.map_cons,List.map_nil,List.length_append,
      List.length_cons,List.length_nil] at need
    omega
  obtain ⟨fuel,step,ran,returned,breaking,memory,bodyCost,scalarPeak,heapPeak,totalPeak,live,baseEq,newBuffer,found,items⟩ :=
    Proofs.UfReadBody.execute initial vc sameProgram.body ps data.items (rank a+rank b+2) res P.length (box data)
      ty (by decide +kernel) (by decide +kernel) run unchanged writes qs' fw
      (by rw [base]; simp [ps,fields,P]; omega) resident need' (Nat.le_of_eq sc)
  rw [ret] at returned
  have stepEq : step = ⟨step.state,some (.scalar (if root1=root2 then 1 else 0)),false⟩ := by
    cases step with
    | mk st rr br => simp_all
  have ran' : runFuel fuel sameProgram.body initial = .finished ⟨step.state,some (.scalar (if root1=root2 then 1 else 0)),false⟩ := by
    rw [←stepEq]; exact ran
  have savedP : step.state.scalars.memory.take P.length = P := by
    rw [memory,state]
    simp [Proofs.UfReadQueries.sameState,Proofs.UfReadInline.inlineState,Proofs.VecCapture.appended,ps,fields,cells,List.append_assoc]
  have saved : step.state.scalars.memory.take s.scalars.memory.length = s.scalars.memory := by
    calc _ = (step.state.scalars.memory.take P.length).take s.scalars.memory.length := by
           rw [List.take_take,Nat.min_eq_left (Proofs.UfReceiverLayout.prefix_length s)]
         _ = s.scalars.memory := by rw [savedP]; exact Proofs.UfReceiverLayout.prefix_take s
  have compactData := compact_metadata (project prepared i32) initial compacted
  have prepEffects := prepareArguments_effects s prepared i32 sameProgram.parameters _ prep
  have stateEq : initial.frame.state = (project s i32).frame.state := by
    rw [compactData.1]; simp only [project,materialize,prepEffects.1]
  have sourceValid : (project s i32).frame.state.wellFormed = true := by rw [←stateEq]; exact fw.valid
  obtain ⟨out,call,workEq,scalarMemory,lookups,resources⟩ := finish_call sameProgram fuel s prepared initial step.state Proofs.PrefixSumsCall.bT
    (readArguments s object receiver [(ea,(a : Int)),(eb,(b : Int))]) (if root1=root2 then 1 else 0) P.length vc.L0 rfl (by decide +kernel)
    contexts covered sourceValid prep compacted ran' saved valueValid scalarPeak heapPeak totalPeak live baseEq
  have initialWork : initial.work = work prepared := by
    rw [←project_work prepared i32]
    unfold NState.work
    rw [compactData.1,compactData.2.2.1]
  refine ⟨prepared,initial,vc,fuel,out,root1,root2,prep,compacted,call,reach1,reach2,rl1,rl2,rootFact1,rootFact2,?_,scalarMemory,fw.live,fw.owner.symm,resources,newBuffer,?_,items⟩
  · rw [workEq]
    rw [initialWork] at bodyCost
    omega
  · rw [lookups]; exact found



theorem counter_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (data : Buffer Int) (fuel : Nat) (out : Context),
      prepareArguments s i32 counterProgram.parameters (readArguments s object receiver []) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      currentBuffer s.objects.heap receiver.view.header receiver.header = some data ∧
      callFuel counterProgram fuel s i32 (readArguments s object receiver []) = .finished (out,.scalar receiver.counter.value) ∧
      work out ≤ work prepared+3 ∧ out.scalars.memory = s.scalars.memory ∧ initial.frame.state.liveSpace = vc.L0 ∧ vc.R = data.owner ∧
      Resources s out initial (receiverPrefix s).length vc.L0 ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = data.items.map Value.integer := by
  obtain ⟨prepared,initial,vc,data,prep,compacted,qs,fw,ty,readonly,flag,sc,current,base,scope⟩ :=
    prepare_read_frame s object receiver counterProgram [] (by intro e value member; simp at member) rfl
      readable unique covered valid limit contexts
  let P := receiverPrefix s
  let ps := fields P receiver.counter.address [receiver.size.value]
  have qs' := qs_counter initial P receiver.counter.address receiver.size.value qs
  have value := counter_value P receiver.counter.address receiver.size.value receiver.counter.value
    (Proofs.UfReceiverLayout.prefix_cell s _ _ receiver.counter.found) receiver.counter.valid
  let res : PRW := ⟨ps,data.items,some receiver.counter.value,2,ps.mem.length+ps.bs.length+3,0⟩
  have run : pexecW i32 0 counterProgram.body ps data.items = some res :=
    Proofs.UfReadQueries.counter_correct ps data.items receiver.counter.value value 0
  have resident : ps.mem.length+ps.bs.length ≤ P.length+48 := by simp [ps,fields,cells,valueBindings,addresses]
  have need : res.need ≤ P.length+48 := by simp [res,ps,fields,cells,valueBindings,addresses]
  obtain ⟨fuel,step,ran,returned,breaking,memory,bodyCost,scalarPeak,heapPeak,totalPeak,live,baseEq,newBuffer,found,items⟩ :=
    Proofs.UfReadBody.execute initial vc counterProgram.body ps data.items 0 res P.length (box data)
      ty (by decide +kernel) (by decide +kernel) run rfl rfl qs' fw
      (by rw [base]; simp [ps,fields,P]; omega) resident need (Nat.le_of_eq sc)
  have returned' : step.returned = some (.scalar receiver.counter.value) := by simpa only [res,Option.map_some] using returned
  have stepEq : step = ⟨step.state,some (.scalar receiver.counter.value),false⟩ := by
    cases step with
    | mk st rr br => simp_all
  have ran' : runFuel fuel counterProgram.body initial = .finished ⟨step.state,some (.scalar receiver.counter.value),false⟩ := by
    rw [←stepEq]; exact ran
  have savedP : step.state.scalars.memory.take P.length = P := by
    rw [memory]
    simp [res,ps,fields,cells]
  have saved : step.state.scalars.memory.take s.scalars.memory.length = s.scalars.memory := by
    calc _ = (step.state.scalars.memory.take P.length).take s.scalars.memory.length := by
           rw [List.take_take,Nat.min_eq_left (Proofs.UfReceiverLayout.prefix_length s)]
         _ = s.scalars.memory := by rw [savedP]; exact Proofs.UfReceiverLayout.prefix_take s
  have compactData := compact_metadata (project prepared i32) initial compacted
  have prepEffects := prepareArguments_effects s prepared i32 counterProgram.parameters _ prep
  have stateEq : initial.frame.state = (project s i32).frame.state := by
    rw [compactData.1]; simp only [project,materialize,prepEffects.1]
  have sourceValid : (project s i32).frame.state.wellFormed = true := by rw [←stateEq]; exact fw.valid
  obtain ⟨out,call,workEq,scalarMemory,lookups,resources⟩ := finish_call counterProgram fuel s prepared initial step.state i32
    (readArguments s object receiver []) receiver.counter.value P.length vc.L0 rfl (by decide +kernel)
    contexts covered sourceValid prep compacted ran' saved receiver.counter.valid scalarPeak heapPeak totalPeak live baseEq
  have initialWork : initial.work = work prepared := by
    rw [←project_work prepared i32]
    unfold NState.work
    rw [compactData.1,compactData.2.2.1]
  refine ⟨prepared,initial,vc,data,fuel,out,prep,compacted,current,call,?_,scalarMemory,fw.live,fw.owner.symm,resources,newBuffer,?_,items⟩
  · rw [workEq]
    rw [initialWork] at bodyCost
    change step.state.work ≤ work prepared+2 at bodyCost
    omega
  · rw [lookups]; exact found

end Proofs.UfReadCall
