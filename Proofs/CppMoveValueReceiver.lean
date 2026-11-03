import Proofs.CppMoveReceiverResolve
import Proofs.CppMoveArgumentWork
import Proofs.CppMoveArgumentPeak
import Proofs.ExtremaCall

namespace Proofs.CppMoveValueReceiver
open Proofs.CppScalar Proofs.CppMoveContext Proofs.CppMoveReceiverLayout

-- The order is a vector reference, one captured scalar value, then a scalar reference.
def saved (borrow : Borrow) (ty : Ty) (value : Int) (address : Nat) (writable : Bool) : List SavedArgument :=
  [.vector borrow,.scalar ⟨ty,false,true⟩ (.value value),.scalar ⟨ty,true,writable⟩ (.reference address)]

theorem prepare (s : Context) (borrow : Borrow) (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header borrow.header = some header)
    (permission : borrow.writable = true → header.writable = true)
    (ty : Ty) (value count : Int) (address : Nat) (writable : Bool)
    (cell : s.scalars.memory[address]? = some ⟨ty,count⟩)
    (valueValid : ty.valid value = true) (countValid : ty.valid count = true) :
    ∃ out, prepareSaved s (saved borrow ty value address writable) = some out ∧
      out.objects = ⟨s.objects.heap,s.objects.views++[⟨borrow.header,borrow.writable⟩]⟩ ∧
      out.scalars.memory = receiverPrefix s ++ [⟨ty,value⟩] ∧
      out.scalars.bindings = [⟨(receiverPrefix s).length,true⟩,⟨address,writable⟩] ∧
      out.slots = [.vector s.objects.views.length,.scalar 0,.scalar 1] ∧
      out.scope = s.scope+1 ∧ out.scalars.baseMemory = s.scalars.baseMemory := by
  let initial := prepareBase s 3
  let borrowed : Context := observe {initial with
    objects := ⟨s.objects.heap,s.objects.views++[⟨borrow.header,borrow.writable⟩]⟩,
    slots := [.vector s.objects.views.length],
    scalars := ({initial.scalars with memory := initial.scalars.memory++[⟨⟨1,false,true⟩,0⟩]} : Proofs.CppState.State).observe 0}
  have installed := installBorrow_runs initial borrow header found permission
  have first : bindSaved initial (.vector borrow) = some borrowed := by
    simp only [bindSaved,installed,Bind.bind,Option.bind]
    rfl
  obtain ⟨valued,valuesRun,objects,memory,bindings,slots,scope,baseline⟩ :=
    bind_values borrowed ty [value] (by intro x member; rw [List.mem_singleton] at member; subst x; exact valueValid)
  have second : bindSaved borrowed (.scalar ⟨ty,false,true⟩ (.value value)) = some valued := by
    simpa [valueArguments,bindSavedAll] using valuesRun
  have existing : valued.scalars.memory[address]? = some ⟨ty,count⟩ := by
    have inside := (List.getElem?_eq_some_iff.mp cell).1
    rw [memory]
    simp only [cells,List.map_cons,List.map_nil]
    rw [List.getElem?_append_left (by simp [borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe]; omega)]
    simp only [borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe]
    rw [List.getElem?_append_left (by simp; omega),List.getElem?_append_left inside]
    exact cell
  let scalars : Proofs.CppState.State := ({valued.scalars with bindings := valued.scalars.bindings++[⟨address,writable⟩]} : Proofs.CppState.State).observe 0
  let out : Context := observe {valued with scalars := scalars,slots := valued.slots++[.scalar valued.scalars.bindings.length]}
  have bound : Proofs.CppState.bindArgument valued.scalars ⟨ty,true,writable⟩ (.reference address) = some scalars := by
    simp [Proofs.CppState.bindArgument,existing,countValid,scalars]
  have third : bindSaved valued (.scalar ⟨ty,true,writable⟩ (.reference address)) = some out := by
    exact bindSaved_scalar_runs valued ⟨ty,true,writable⟩ (.reference address) scalars bound
  refine ⟨out,?_,?_,?_,?_,?_,?_,?_⟩
  · change bindSavedAll initial [.vector borrow,.scalar ⟨ty,false,true⟩ (.value value),
        .scalar ⟨ty,true,writable⟩ (.reference address)] = some out
    simp only [bindSavedAll,first,second,third,Bind.bind,Option.bind]
  · exact objects
  · simpa [out,scalars,borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe,receiverPrefix,cells] using memory
  · simp [out,scalars,bindings,borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe,valueBindings,addresses,receiverPrefix]
  · simp [out,slots,bindings,borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe,valueSlots,valueBindings,addresses]
  · exact scope
  · exact baseline

open Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.CppNestedCall
open Proofs.CppMoveArgumentFacts Proofs.CppMoveReceiverResolve

theorem resolve (s : Context) (ty : Ty) (vectorSlot counterSlot : Nat)
    (borrow : Borrow) (binding : Proofs.CppState.Binding) (count : Int)
    (expression : NExpr) (value : Int) (writable : Bool)
    (captured : captureBorrow s vectorSlot borrow.writable = some borrow)
    (counter : (project s ty).scalarCell counterSlot ty = some (binding,⟨ty,count⟩))
    (permission : writable = true → binding.writable = true)
    (typed : expression.resultType = ty) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (envOf (project s ty)) = some value) :
    ∃ last, resolveArguments s ty
      [.vector ty borrow.writable,.scalar ty false true,.scalar ty true writable]
      [.vectorReference vectorSlot,.value expression,.scalarReference counterSlot] =
      some (last,saved borrow ty value binding.address writable) := by
  let first := charge s 1 1
  have vectorRun := resolve_vector_runs s ty vectorSlot borrow.writable borrow captured
  have stable1 := resolveArgument_stable s first ty (.vector ty borrow.writable) (.vectorReference vectorSlot)
    (.vector borrow) vectorRun
  have nextDenotes : expression.denote (envOf (project first ty)) = some value := by
    rw [stable_environment s first ty stable1]
    exact denotes
  obtain ⟨evaluated,eval⟩ := denote_complete expression (project first ty) value scalar nextDenotes
  let valued := resumeExpression first evaluated
  have expressionRun : evalExpression first ty expression = some (valued,value) := by
    simp [evalExpression,eval,valued]
  have valueRun := resolve_value_runs first valued ty ty expression true value typed expressionRun
  have stable2 := resolveArgument_stable first valued ty (.scalar ty false true) (.value expression)
    (.scalar ⟨ty,false,true⟩ (.value value)) valueRun
  have current : (project valued ty).scalarCell counterSlot ty = some (binding,⟨ty,count⟩) := by
    rw [stable_scalarCell s valued ty ty counterSlot (stable1.trans stable2)]
    exact counter
  have reference : captureScalarReference valued ty counterSlot writable =
      some (.scalar ⟨ty,true,writable⟩ (.reference binding.address)) := by
    simp [captureScalarReference,current]
    exact permission
  let last := charge valued 1 1
  have referenceRun : resolveArgument valued ty (.scalar ty true writable) (.scalarReference counterSlot) =
      some (last,.scalar ⟨ty,true,writable⟩ (.reference binding.address)) := by
    simp [resolveArgument,reference,last]
  refine ⟨last,?_⟩
  dsimp only [first,valued,last] at valueRun referenceRun ⊢
  simp only [resolveArguments,vectorRun,valueRun,referenceRun,saved,Bind.bind,Option.bind]

theorem prepare_arguments (s : Context) (ty : Ty) (vectorSlot counterSlot : Nat)
    (borrow : Borrow) (header : Proofs.CppMoveHeaders.Header)
    (binding : Proofs.CppState.Binding) (count : Int) (expression : NExpr) (value : Int) (writable : Bool)
    (captured : captureBorrow s vectorSlot borrow.writable = some borrow)
    (found : s.objects.heap.header borrow.header = some header)
    (vectorPermission : borrow.writable = true → header.writable = true)
    (counter : (project s ty).scalarCell counterSlot ty = some (binding,⟨ty,count⟩))
    (scalarPermission : writable = true → binding.writable = true)
    (typed : expression.resultType = ty) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (envOf (project s ty)) = some value)
    (valueValid : ty.valid value = true) :
    ∃ out, prepareArguments s ty
        [.vector ty borrow.writable,.scalar ty false true,.scalar ty true writable]
        [.vectorReference vectorSlot,.value expression,.scalarReference counterSlot] = some out ∧
      out.objects = ⟨s.objects.heap,s.objects.views++[⟨borrow.header,borrow.writable⟩]⟩ ∧
      out.scalars.memory = receiverPrefix s ++ [⟨ty,value⟩] ∧
      out.scalars.bindings = [⟨(receiverPrefix s).length,true⟩,⟨binding.address,writable⟩] ∧
      out.slots = [.vector s.objects.views.length,.scalar 0,.scalar 1] ∧
      out.scope = s.scope+1 ∧ out.scalars.baseMemory = s.scalars.baseMemory := by
  obtain ⟨last,resolved⟩ := resolve s ty vectorSlot counterSlot borrow binding count expression value writable
    captured counter scalarPermission typed scalar denotes
  have stable := resolveArguments_stable s last ty _ _ _ resolved
  have lastFound : last.objects.heap.header borrow.header = some header := by
    rw [stable.objects]
    exact found
  obtain ⟨_,_,_,cell,_,countValid⟩ := Proofs.ExtremaCall.scalarCell_facts counter
  have lastCell : last.scalars.memory[binding.address]? = some ⟨ty,count⟩ := by
    rw [stable.memory]
    exact cell
  obtain ⟨out,prepared,objects,memory,bindings,slots,scope,base⟩ :=
    prepare last borrow header lastFound vectorPermission ty value count binding.address writable
      lastCell valueValid countValid
  have prefixEq : receiverPrefix last = receiverPrefix s := by
    simp only [receiverPrefix,stable.memory,stable.slots]
  refine ⟨out,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [prepareArguments,resolved,Bind.bind,Option.bind,prepared]
  · simpa only [stable.objects] using objects
  · simpa only [prefixEq] using memory
  · simpa only [prefixEq] using bindings
  · simpa only [stable.objects] using slots
  · simpa only [stable.scope] using scope
  · simpa only [stable.baseline] using base

theorem prepare_compact (s : Context) (ty : Ty) (vectorSlot counterSlot : Nat)
    (borrow : Borrow) (header : Proofs.CppMoveHeaders.Header)
    (binding : Proofs.CppState.Binding) (count : Int) (expression : NExpr) (value : Int) (writable : Bool)
    (captured : captureBorrow s vectorSlot borrow.writable = some borrow)
    (found : s.objects.heap.header borrow.header = some header)
    (vectorPermission : borrow.writable = true → header.writable = true)
    (counter : (project s ty).scalarCell counterSlot ty = some (binding,⟨ty,count⟩))
    (scalarPermission : writable = true → binding.writable = true)
    (typed : expression.resultType = ty) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (envOf (project s ty)) = some value)
    (valueValid : ty.valid value = true) :
    ∃ prepared initial,
      prepareArguments s ty [.vector ty borrow.writable,.scalar ty false true,.scalar ty true writable]
        [.vectorReference vectorSlot,.value expression,.scalarReference counterSlot] = some prepared ∧
      Proofs.CppMoveCallBindings.compact (project prepared ty) = some initial ∧
      initial.scalars.memory.take s.scalars.memory.length = s.scalars.memory ∧
      (.variable ty 2 : NExpr).denote (envOf initial) = some count ∧
      initial.frame.state = (project s ty).frame.state ∧
      initial.work ≤ work s+expression.nodes+6 ∧
      initial.scalars.memory.length = s.scalars.memory.length+s.slots.length+2 ∧
      initial.scalars.bindings.length = 2 ∧ initial.scalars.baseMemory = s.scalars.baseMemory ∧
      initial.scalars.peak ≤ max (max s.scalars.peak (scalarLive s+expression.nodes+2))
        ((s.scalars.memory.length+s.slots.length+6-s.scalars.baseMemory)+6) := by
  obtain ⟨prepared,run,objects,memory,bindings,slots,scope,base⟩ :=
    prepare_arguments s ty vectorSlot counterSlot borrow header binding count expression value writable
      captured found vectorPermission counter scalarPermission typed scalar denotes valueValid
  have viewFound : prepared.objects.views[s.objects.views.length]? = some ⟨borrow.header,borrow.writable⟩ := by
    simp [objects]
  obtain ⟨initial,compacted,qs,state,viewBindings⟩ := compact_receiver prepared ty s.objects.views.length 1
    ⟨borrow.header,borrow.writable⟩ viewFound (by simpa [valueSlots,addresses] using slots)
  have initialMemory : initial.scalars.memory = s.scalars.memory ++
      (List.replicate s.slots.length ⟨⟨1,false,true⟩,0⟩ ++ [⟨⟨1,false,true⟩,0⟩,⟨ty,value⟩]) := by
    rw [qs.memory,List.nil_append]
    simpa [receiverPrefix,List.append_assoc] using memory
  have initialBindings : initial.scalars.bindings = [⟨(receiverPrefix s).length,true⟩,⟨binding.address,writable⟩] := by
    rw [qs.bindings]
    exact bindings
  have initialSlots : initial.slots = [.vector 0,.scalar 0,.scalar 1] := by
    simpa [valueSlots,addresses] using qs.slots
  obtain ⟨_,_,_,cell,_,countValid⟩ := Proofs.ExtremaCall.scalarCell_facts counter
  have cellSource : s.scalars.memory[binding.address]? = some ⟨ty,count⟩ := cell
  have inside := (List.getElem?_eq_some_iff.mp cellSource).1
  have cellInitial : initial.scalarCell 2 ty = some (⟨binding.address,writable⟩,⟨ty,count⟩) := by
    simp [NState.scalarCell,NState.scalarSlot,initialSlots,initialBindings,initialMemory,
      List.getElem?_append_left inside,cellSource,countValid]
  have pureArguments : ∀ argument ∈ [.vectorReference vectorSlot,.value expression,.scalarReference counterSlot],
      Proofs.CppMoveArgumentWork.argumentPure argument := by
    intro argument member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · trivial
    · exact scalar
    · trivial
  have cost := Proofs.CppMoveArgumentWork.prepare_work s prepared ty _ _ pureArguments run
  have peak := Proofs.CppMoveArgumentPeak.prepare_peak s prepared ty _ _ pureArguments run
  have metadata := Proofs.CppMoveCallBindings.compact_metadata (project prepared ty) initial compacted
  have workEq : initial.work = work prepared := by
    simp only [NState.work,metadata.1,metadata.2.2.1]
    exact project_work prepared ty
  refine ⟨prepared,initial,run,compacted,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [initialMemory]
  · simp [NExpr.denote,envOf,cellInitial]
  · rw [state]
    simp [project,Proofs.CppMoveFrame.materialize,objects]
  · rw [workEq]
    simp only [Proofs.CppMoveArgumentWork.argumentsWork,Proofs.CppMoveArgumentWork.argumentWork,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at cost
    omega
  · simp [initialMemory]
    omega
  · simp [initialBindings]
  · rw [qs.base]
    exact base
  · rw [metadata.2.2.1]
    change prepared.scalars.peak ≤ _
    simp only [Proofs.CppMoveArgumentWork.argumentsWork,Proofs.CppMoveArgumentWork.argumentWork,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at peak
    omega

def charged (s : Context) : Context := charge (charge (charge s 1 1) 1 1) 1 1

theorem charged_peaks (s : Context) :
    (charged s).scalars.peak = max s.scalars.peak (scalarLive s+1) ∧
    (charged s).peak = max s.peak (max s.scalars.peak (scalarLive s+1)+s.objects.heap.peak) := by
  simp [charged,charge,scalarLive,Proofs.CppState.State.observe]

theorem eval_field (s : Context) (ty : Ty) (slot : Nat) (binding : Proofs.CppState.Binding) (value : Int)
    (cell : (project s ty).scalarCell slot ty = some (binding,⟨ty,value⟩)) :
    evalExpression s ty (.variable ty slot) = some (charge s 1 1,value) := by
  simp only [evalExpression,NExpr.eval,cell,Bind.bind,Option.bind]
  rfl

theorem resolve_fields (s : Context) (ty : Ty) (vectorSlot sizeSlot counterSlot : Nat)
    (borrow : Borrow) (counterBinding sizeBinding : Proofs.CppState.Binding) (count size : Int) (writable : Bool)
    (captured : captureBorrow s vectorSlot borrow.writable = some borrow)
    (counter : (project s ty).scalarCell counterSlot ty = some (counterBinding,⟨ty,count⟩))
    (sizeCell : (project s ty).scalarCell sizeSlot ty = some (sizeBinding,⟨ty,size⟩))
    (permission : writable = true → counterBinding.writable = true) :
    resolveArguments s ty [.vector ty borrow.writable,.scalar ty false true,.scalar ty true writable]
      [.vectorReference vectorSlot,.value (.variable ty sizeSlot),.scalarReference counterSlot] =
      some (charged s,saved borrow ty size counterBinding.address writable) := by
  let first := charge s 1 1
  let second := charge first 1 1
  have vectorRun := resolve_vector_runs s ty vectorSlot borrow.writable borrow captured
  have stable1 := resolveArgument_stable s first ty (.vector ty borrow.writable) (.vectorReference vectorSlot)
    (.vector borrow) vectorRun
  have sizeCurrent : (project first ty).scalarCell sizeSlot ty = some (sizeBinding,⟨ty,size⟩) := by
    rw [stable_scalarCell s first ty ty sizeSlot stable1]
    exact sizeCell
  have valueRun := resolve_value_runs first second ty ty (.variable ty sizeSlot) true size rfl
    (eval_field first ty sizeSlot sizeBinding size sizeCurrent)
  have stable2 := resolveArgument_stable first second ty (.scalar ty false true) (.value (.variable ty sizeSlot))
    (.scalar ⟨ty,false,true⟩ (.value size)) valueRun
  have counterCurrent : (project second ty).scalarCell counterSlot ty = some (counterBinding,⟨ty,count⟩) := by
    rw [stable_scalarCell s second ty ty counterSlot (stable1.trans stable2)]
    exact counter
  have reference : captureScalarReference second ty counterSlot writable =
      some (.scalar ⟨ty,true,writable⟩ (.reference counterBinding.address)) := by
    simp [captureScalarReference,counterCurrent]
    exact permission
  have referenceRun : resolveArgument second ty (.scalar ty true writable) (.scalarReference counterSlot) =
      some (charge second 1 1,.scalar ⟨ty,true,writable⟩ (.reference counterBinding.address)) := by
    simp [resolveArgument,reference]
  dsimp only [first,second] at valueRun referenceRun
  simp only [resolveArguments,vectorRun,valueRun,referenceRun,saved,charged,Bind.bind,Option.bind]

-- A caller-only bound; the stored size/count values do not occur in it.
def fieldScalarBudget (s : Context) : Nat :=
  max s.scalars.peak (max (scalarLive s+3)
    ((s.scalars.memory.length+s.slots.length+6-s.scalars.baseMemory)+6))

theorem prepare_fields_compact (s : Context) (ty : Ty) (vectorSlot sizeSlot counterSlot : Nat)
    (borrow : Borrow) (header : Proofs.CppMoveHeaders.Header)
    (counterBinding sizeBinding : Proofs.CppState.Binding) (count size : Int) (writable : Bool)
    (captured : captureBorrow s vectorSlot borrow.writable = some borrow)
    (found : s.objects.heap.header borrow.header = some header)
    (vectorPermission : borrow.writable = true → header.writable = true)
    (counter : (project s ty).scalarCell counterSlot ty = some (counterBinding,⟨ty,count⟩))
    (sizeCell : (project s ty).scalarCell sizeSlot ty = some (sizeBinding,⟨ty,size⟩))
    (scalarPermission : writable = true → counterBinding.writable = true) :
    ∃ prepared initial,
      prepareArguments s ty [.vector ty borrow.writable,.scalar ty false true,.scalar ty true writable]
        [.vectorReference vectorSlot,.value (.variable ty sizeSlot),.scalarReference counterSlot] = some prepared ∧
      Proofs.CppMoveCallBindings.compact (project prepared ty) = some initial ∧
      initial.scalars.memory.take s.scalars.memory.length = s.scalars.memory ∧
      (.variable ty 2 : NExpr).denote (envOf initial) = some count ∧
      initial.frame.state = (project s ty).frame.state ∧ initial.work ≤ work s+7 ∧
      initial.scalars.peak ≤ fieldScalarBudget s ∧ liveS initial+1 ≤ fieldScalarBudget s ∧
      initial.peak ≤ max s.peak (fieldScalarBudget s+s.objects.heap.peak) := by
  obtain ⟨_,_,_,_,_,sizeValid⟩ := Proofs.ExtremaCall.scalarCell_facts sizeCell
  have denotes : (.variable ty sizeSlot : NExpr).denote (envOf (project s ty)) = some size := by
    simp [NExpr.denote,envOf,sizeCell]
  obtain ⟨prepared,initial,run,compacted,memoryPrefix,counterValue,state,cost,memoryLength,bindingLength,base,scalarPeak⟩ :=
    prepare_compact s ty vectorSlot counterSlot borrow header counterBinding count (.variable ty sizeSlot)
      size writable captured found vectorPermission counter scalarPermission rfl rfl denotes sizeValid
  have metadata := Proofs.CppMoveCallBindings.compact_metadata (project prepared ty) initial compacted
  have scalarBound : initial.scalars.peak ≤ fieldScalarBudget s := by
    simp only [NExpr.nodes] at scalarPeak
    simp only [fieldScalarBudget]
    omega
  have liveBound : liveS initial+1 ≤ fieldScalarBudget s := by
    simp only [liveS,memoryLength,bindingLength,base,fieldScalarBudget]
    omega
  have resolved := resolve_fields s ty vectorSlot sizeSlot counterSlot borrow counterBinding sizeBinding
    count size writable captured counter sizeCell scalarPermission
  have savedRun : prepareSaved (charged s) (saved borrow ty size counterBinding.address writable) = some prepared := by
    simpa only [prepareArguments,resolved,Bind.bind,Option.bind] using run
  have peak := (prepareSaved_peak (charged s) prepared _ savedRun).2
  have preparedLive : scalarLive prepared = liveS initial := by
    simp only [liveS,metadata.2.2.1]
    rfl
  have chargedScalar : (charged s).scalars.peak ≤ fieldScalarBudget s := by
    rw [(charged_peaks s).1]
    simp only [fieldScalarBudget]
    omega
  have total : initial.peak ≤ max s.peak (fieldScalarBudget s+s.objects.heap.peak) := by
    rw [metadata.2.2.2.2.1]
    change prepared.peak ≤ _
    change prepared.peak ≤ max (charged s).peak
      (max (charged s).scalars.peak (scalarLive prepared)+s.objects.heap.peak) at peak
    rw [(charged_peaks s).2,preparedLive] at peak
    have oldScalar : max s.scalars.peak (scalarLive s+1) ≤ fieldScalarBudget s := by
      simp only [fieldScalarBudget]
      omega
    omega
  exact ⟨prepared,initial,run,compacted,memoryPrefix,counterValue,state,
    by simpa only [NExpr.nodes,Nat.reduceAdd,Nat.add_assoc] using cost,scalarBound,liveBound,total⟩

theorem fieldScalarBudget_bound (s : Context) :
    fieldScalarBudget s ≤ max s.scalars.peak (scalarLive s+s.slots.length+12) := by
  simp only [fieldScalarBudget,scalarLive]
  omega

end Proofs.CppMoveValueReceiver
