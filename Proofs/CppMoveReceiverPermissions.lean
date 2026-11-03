import Proofs.CppMoveReadReceiver
import Proofs.CppMoveReceiverFrame

namespace Proofs.CppMoveReceiverPermissions
open Proofs.CppScalar Proofs.CppMoveContext Proofs.CppMoveArgumentFacts Proofs.CppMoveReceiverLayout
open Proofs.CppMoveReceiverResolve Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.CppNestedCall
open Proofs.CppMoveReadReceiver Proofs.CppMoveObjectReceiver Proofs.CppConstructorFinish
open Proofs.DoublingNested Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open Proofs.CppMoveCallBindings Proofs.CppMoveReceiverFrame Proofs.CppMoveFrame Proofs.CppMoveHeaders
open Proofs.CppVector Proofs.CppNestedVectorStore

theorem resolve_receiver (s : Context) (ty : Ty) (vectorSlot counterSlot : Nat)
    (borrow : Borrow) (binding : Proofs.CppState.Binding) (count : Int)
    (captured : captureBorrow s vectorSlot borrow.writable = some borrow)
    (counter : (project s ty).scalarCell counterSlot ty = some (binding,⟨ty,count⟩))
    (counterWritable : Bool) (permission : counterWritable = true → binding.writable = true) (expressions : List (NExpr × Int))
    (ready : Ready s ty expressions) :
    ∃ last, resolveArguments s ty
      (.vector ty borrow.writable :: .scalar ty true counterWritable :: parameters ty expressions)
      (.vectorReference vectorSlot :: .scalarReference counterSlot :: arguments expressions) =
      some (last,receiverArguments borrow ty binding.address counterWritable (values expressions)) := by
  let first := charge s 1 1
  have vectorRun := resolve_vector_runs s ty vectorSlot borrow.writable borrow captured
  have stable1 := resolveArgument_stable s first ty (.vector ty borrow.writable) (.vectorReference vectorSlot)
    (.vector borrow) vectorRun
  have cell : (project first ty).scalarCell counterSlot ty = some (binding,⟨ty,count⟩) := by
    rw [stable_scalarCell s first ty ty counterSlot stable1]
    exact counter
  have reference : captureScalarReference first ty counterSlot counterWritable =
      some (.scalar ⟨ty,true,counterWritable⟩ (.reference binding.address)) := by
    simp [captureScalarReference,cell]
    exact permission
  let second := charge first 1 1
  have scalarRun : resolveArgument first ty (.scalar ty true counterWritable) (.scalarReference counterSlot) =
      some (second,.scalar ⟨ty,true,counterWritable⟩ (.reference binding.address)) := by
    simp [resolveArgument,reference,second]
  have stable2 := resolveArgument_stable first second ty (.scalar ty true counterWritable) (.scalarReference counterSlot)
    (.scalar ⟨ty,true,counterWritable⟩ (.reference binding.address)) scalarRun
  obtain ⟨last,rest⟩ := resolve_values second ty expressions
    (ready_stable s second ty expressions (stable1.trans stable2) ready)
  refine ⟨last,?_⟩
  dsimp only [first,second] at scalarRun rest
  simp only [resolveArguments,vectorRun,scalarRun,receiverArguments,Bind.bind,Option.bind,rest]


theorem resolve_fields (s : Context) (ty : Ty) (vectorSlot counterSlot sizeSlot : Nat)
    (borrow : Borrow) (counterBinding sizeBinding : Proofs.CppState.Binding) (count size : Int)
    (captured : captureBorrow s vectorSlot borrow.writable = some borrow)
    (counter : (project s ty).scalarCell counterSlot ty = some (counterBinding,⟨ty,count⟩))
    (sizeCell : (project s ty).scalarCell sizeSlot ty = some (sizeBinding,⟨ty,size⟩))
    (counterWritable : Bool) (permission : counterWritable = true → counterBinding.writable = true) (expressions : List (NExpr × Int))
    (ready : Ready s ty expressions) :
    ∃ last, resolveArguments s ty
      (.vector ty borrow.writable :: .scalar ty true counterWritable :: .scalar ty false true :: parameters ty expressions)
      (.vectorReference vectorSlot :: .scalarReference counterSlot ::
        .value (.variable ty sizeSlot) :: arguments expressions) =
      some (last,receiverArguments borrow ty counterBinding.address counterWritable (size::values expressions)) := by
  exact resolve_receiver s ty vectorSlot counterSlot borrow counterBinding count captured counter counterWritable permission
    ((.variable ty sizeSlot,size)::expressions) (ready_field s ty sizeSlot sizeBinding size sizeCell expressions ready)


theorem capture_read (s : Context) (object : ObjectRef) (ty : Ty) (receiver : ReadReceiver s object ty) :
    captureBorrow s object.vectorSlot false = some ⟨receiver.view.header,false⟩ := by
  exact captureBorrow_runs s object.vectorSlot receiver.viewSlot false receiver.view receiver.header
    receiver.located receiver.resolved (by intro impossible; contradiction)

theorem resolve_read (s : Context) (object : ObjectRef) (ty : Ty) (receiver : ReadReceiver s object ty)
    (expressions : List (NExpr × Int)) (ready : Ready s ty expressions) :
    ∃ last, resolveArguments s ty
      (.vector ty false :: .scalar ty true false :: .scalar ty false true :: parameters ty expressions)
      (.vectorReference object.vectorSlot :: .scalarReference receiver.counter.slot ::
        .value (.variable ty receiver.size.slot) :: arguments expressions) =
      some (last,receiverArguments ⟨receiver.view.header,false⟩ ty
        receiver.counter.address false (receiver.size.value::values expressions)) := by
  exact resolve_fields s ty object.vectorSlot receiver.counter.slot receiver.size.slot ⟨receiver.view.header,false⟩
    ⟨receiver.counter.address,receiver.counter.writable⟩ ⟨receiver.size.address,receiver.size.writable⟩
    receiver.counter.value receiver.size.value (capture_read s object ty receiver) (Field.cell s ty receiver.counter)
    (Field.cell s ty receiver.size) false (by intro impossible; contradiction) expressions ready

theorem prepare_read (s : Context) (object : ObjectRef) (ty : Ty) (receiver : ReadReceiver s object ty)
    (expressions : List (NExpr × Int)) (ready : Ready s ty expressions) :
    ∃ out, prepareArguments s ty
      (.vector ty false :: .scalar ty true false :: .scalar ty false true :: parameters ty expressions)
      (.vectorReference object.vectorSlot :: .scalarReference receiver.counter.slot ::
        .value (.variable ty receiver.size.slot) :: arguments expressions) = some out ∧
      out.objects = ⟨s.objects.heap,s.objects.views++[⟨receiver.view.header,false⟩]⟩ ∧
      out.scalars.memory = receiverPrefix s ++ cells ty (receiver.size.value::values expressions) ∧
      out.scalars.bindings = ⟨receiver.counter.address,false⟩ ::
        valueBindings (receiverPrefix s).length (expressions.length+1) ∧
      out.slots = .vector s.objects.views.length :: .scalar 0 :: valueSlots 1 (expressions.length+1) ∧
      out.scope = s.scope+1 ∧ out.scalars.baseMemory = s.scalars.baseMemory := by
  obtain ⟨last,resolved⟩ := resolve_read s object ty receiver expressions ready
  have found := (Proofs.CppMoveViews.resolve_parts s.objects receiver.viewSlot receiver.view receiver.header receiver.resolved).2.1
  have allReady := ready_field s ty receiver.size.slot ⟨receiver.size.address,receiver.size.writable⟩
    receiver.size.value (Field.cell s ty receiver.size) expressions ready
  have valid := ready_values_valid s ty _ allReady
  have valid' : ∀ value ∈ receiver.size.value::values expressions, ty.valid value = true := by
    simpa [values] using valid
  obtain ⟨out,run,objects,memory,bindings,slots,scope,base⟩ :=
    prepareArguments_receiver s last ⟨receiver.view.header,false⟩ receiver.header found
      (by intro impossible; contradiction) ty receiver.counter.address false receiver.counter.value
      receiver.counter.found receiver.counter.valid (receiver.size.value::values expressions) valid' _ _ resolved
  exact ⟨out,run,objects,memory,by simpa [values] using bindings,
    by simpa [values] using slots,scope,base⟩

theorem prepare_qs (s last : Context) (borrow : Borrow)
    (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header borrow.header = some header)
    (permission : borrow.writable = true → header.writable = true)
    (address : Nat) (counterWritable : Bool) (count : Int)
    (counter : s.scalars.memory[address]? = some ⟨i32,count⟩)
    (countValid : i32.valid count = true) (values : List Int)
    (valid : ∀ value ∈ values, i32.valid value = true)
    (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument)
    (resolved : resolveArguments s i32 parameters arguments =
      some (last,receiverArguments borrow i32 address counterWritable values)) :
    ∃ prepared initial,
      prepareArguments s i32 parameters arguments = some prepared ∧
      compact (project prepared i32) = some initial ∧
      QS initial [] initial.scalars.baseMemory initial.scope
        (receiverPrefix s ++ cells i32 values)
        (⟨address,counterWritable⟩ :: valueBindings (receiverPrefix s).length values.length)
        (.vector 0 :: .scalar 0 :: valueSlots 1 values.length) ∧
      initial.scalars.baseMemory = s.scalars.baseMemory ∧
      initial.scope = s.scope+1 ∧
      initial.frame.state = (project s i32).frame.state ∧
      initial.frame.rootWritable = (project s i32).frame.rootWritable ∧
      initial.frame.bindings = [Proofs.CppMoveFrame.viewBinding s.objects i32 ⟨borrow.header,borrow.writable⟩] := by
  obtain ⟨prepared,run,objects,memory,bindings,slots,scope,base⟩ :=
    prepareArguments_receiver s last borrow header found permission i32 address counterWritable count
      counter countValid values valid parameters arguments resolved
  have view : prepared.objects.views[s.objects.views.length]? = some ⟨borrow.header,borrow.writable⟩ := by
    simp [objects]
  obtain ⟨initial,compacted,qs,state,oneBinding⟩ := compact_receiver prepared i32 _ values.length _ view slots
  have data := compact_metadata (project prepared i32) initial compacted
  refine ⟨prepared,initial,run,compacted,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨qs.slots,by simpa only [List.nil_append,memory] using qs.memory,
      qs.bindings.trans bindings,rfl,rfl⟩
  · rw [data.2.2.1]
    exact base
  · rw [data.2.2.2.1]
    exact scope
  · rw [state]
    simp only [project,Proofs.CppMoveFrame.materialize,objects]
  · rw [data.2.1]
    simp only [project,Proofs.CppMoveFrame.materialize,objects]
  · simpa only [Proofs.CppMoveFrame.viewBinding,objects] using oneBinding


theorem prepare_qs_fw (s last : Context) (borrow : Borrow)
    (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header borrow.header = some header)
    (permission : borrow.writable = true → header.writable = true)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (validAllocations : AllocationsValid s.objects.heap i32)
    (limit : header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (address : Nat) (counterWritable : Bool) (count : Int)
    (counter : s.scalars.memory[address]? = some ⟨i32,count⟩)
    (countValid : i32.valid count = true) (values : List Int)
    (valid : ∀ value ∈ values, i32.valid value = true)
    (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument)
    (resolved : resolveArguments s i32 parameters arguments =
      some (last,receiverArguments borrow i32 address counterWritable values))
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (buffer : Buffer Int),
      prepareArguments s i32 parameters arguments = some prepared ∧
      compact (project prepared i32) = some initial ∧
      QS initial [] initial.scalars.baseMemory initial.scope
        (receiverPrefix s ++ cells i32 values)
        (⟨address,counterWritable⟩ :: valueBindings (receiverPrefix s).length values.length)
        (.vector 0 :: .scalar 0 :: valueSlots 1 values.length) ∧
      FW vc buffer.items (box buffer) 0 initial.frame ∧
      vc.ty = i32 ∧ vc.wV = borrow.writable ∧ vc.flag = true ∧ vc.sc = initial.scope ∧
      currentBuffer s.objects.heap borrow.header header = some buffer ∧
      initial.scalars.baseMemory = s.scalars.baseMemory ∧ initial.scope = s.scope+1 := by
  obtain ⟨prepared,initial,run,compacted,qs,base,scope,state,roots,bindings⟩ :=
    prepare_qs s last borrow header found permission address counterWritable count counter countValid values valid parameters arguments resolved
  obtain ⟨buffer,current,entry,bufferValid,bufferLimit,owner⟩ :=
    current_entry s.objects.heap i32 borrow.header header found readable unique covered
  have small : buffer.items.length < 18446744073709551616 := by
    have lengths := bufferValid.1
    have capacity := bufferValid.2.1
    have limitBound : Proofs.CppVectorBindings.sizeLimit i32 < 18446744073709551616 := by decide +kernel
    rw [bufferLimit,limit] at capacity
    omega
  have fw := fw_from_entry s initial i32 borrow.header header borrow.writable buffer found permission entry
    bufferValid (bufferLimit.trans limit) small owner (by decide +kernel) validAllocations state roots bindings scope contexts
  exact ⟨prepared,initial,Proofs.CppMoveReceiverFrame.context initial i32 header borrow.writable buffer small,
    buffer,run,compacted,qs,fw,rfl,rfl,rfl,rfl,current,base,scope⟩

def readArguments (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (expressions : List (NExpr × Int)) : List NArgument :=
  [.vectorReference object.vectorSlot,.scalarReference receiver.counter.slot,
    .value (.variable i32 receiver.size.slot)] ++ arguments expressions

theorem prepare_read_frame (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (method : NProgram) (expressions : List (NExpr × Int)) (ready : Ready s i32 expressions)
    (params : method.parameters = .vector i32 false :: .scalar i32 true false :: .scalar i32 false true ::
      parameters i32 expressions)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (buffer : Buffer Int),
      prepareArguments s i32 method.parameters (readArguments s object receiver expressions) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      QS initial [] initial.scalars.baseMemory initial.scope
        (receiverPrefix s ++ cells i32 (receiver.size.value::values expressions))
        (⟨receiver.counter.address,false⟩ :: valueBindings (receiverPrefix s).length (expressions.length+1))
        (.vector 0 :: .scalar 0 :: valueSlots 1 (expressions.length+1)) ∧
      FW vc buffer.items (box buffer) 0 initial.frame ∧
      vc.ty = i32 ∧ vc.wV = false ∧ vc.flag = true ∧ vc.sc = initial.scope ∧
      currentBuffer s.objects.heap receiver.view.header receiver.header = some buffer ∧
      initial.scalars.baseMemory = s.scalars.baseMemory ∧ initial.scope = s.scope+1 := by
  obtain ⟨last,resolved⟩ := resolve_read s object i32 receiver expressions ready
  have fullReady := ready_field s i32 receiver.size.slot ⟨receiver.size.address,receiver.size.writable⟩
    receiver.size.value (Field.cell s i32 receiver.size) expressions ready
  have valuesValid := ready_values_valid s i32 _ fullReady
  have parts := Proofs.CppMoveViews.resolve_parts s.objects receiver.viewSlot receiver.view receiver.header receiver.resolved
  rw [←params] at resolved
  obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,current,base,scope⟩ :=
    prepare_qs_fw s last ⟨receiver.view.header,false⟩ receiver.header parts.2.1
      (by intro impossible; contradiction) readable unique covered valid limit receiver.counter.address false
      receiver.counter.value receiver.counter.found receiver.counter.valid (receiver.size.value::values expressions)
      valuesValid method.parameters (readArguments s object receiver expressions) resolved contexts
  exact ⟨prepared,initial,vc,buffer,run,compacted,by simpa [values] using qs,fw,
    tyEq,writable,flag,sc,current,base,scope⟩

end Proofs.CppMoveReceiverPermissions
