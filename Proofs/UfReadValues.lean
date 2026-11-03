import Proofs.UfReadPrepareBudget
import Proofs.CppCompactValues

namespace Proofs.UfReadValues
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMoveContext Proofs.CppScalar
open Proofs.CppMoveCallLayout Proofs.CppMoveRestore Proofs.CppMoveFrame Proofs.CppMoveHeaders
open Proofs.CppMoveReadReceiver Proofs.CppConstructorFinish Proofs.CppMoveReceiverPermissions
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverLayout Proofs.CppMoveReceiverFrame
open Proofs.CppMoveCallBindings Proofs.CppVector Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppBufferHeaders Proofs.DoublingNested

theorem call_frame (program : NProgram) (fuel : Nat) (s out : Context) (args : List NArgument) (result : Ret)
    (covered : OwnsAll s.objects.heap)
    (actual : callFuel program fuel s i32 args = .finished (out,result)) :
    SameHeaders (project s i32).frame.state (project out i32).frame.state ∧
      (project out i32).frame.rootWritable = (project s i32).frame.rootWritable := by
  obtain ⟨after,restored⟩ := call_restored program fuel s out i32 args result actual
  have objectRun := restore_objects s out i32 after restored
  have shapes := (restore_metadata s.objects out.objects i32 after.frame objectRun).2.2.2.2.2.2.2
  rw [restoreContext_project s out i32 after restored covered]
  exact sameHeaders_of_shape (project s i32).frame after.frame shapes

theorem call_headers (program : NProgram) (fuel : Nat) (s out : Context) (args : List NArgument) (result : Ret)
    (covered : OwnsAll s.objects.heap)
    (actual : callFuel program fuel s i32 args = .finished (out,result)) :
    SameHeaders (project s i32).frame.state (project out i32).frame.state :=
  (call_frame program fuel s out args result covered actual).1

theorem buffer_eq (before after : Buffer Value) (headers : signature after = signature before)
    (items : after.items = before.items) : after = before := by
  cases before with
  | mk bo bi bc bl be =>
    cases after with
    | mk ao ai ac al ae =>
      simp only [signature,Signature.mk.injEq] at headers
      rcases headers with ⟨owner,capacity,limit,epoch,_⟩
      cases owner
      cases capacity
      cases limit
      cases epoch
      cases items
      rfl

theorem source_payload (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) :
    (project s i32).frame.state.storage.lookup data.owner = some (box data) := by
  have parts := Proofs.CppMoveViews.resolve_parts s.objects receiver.viewSlot receiver.view receiver.header receiver.resolved
  obtain ⟨buffer,found,entry,valid,limit,owner⟩ :=
    current_entry s.objects.heap i32 receiver.view.header receiver.header parts.2.1 readable unique covered
  have eq := Option.some.inj (found.symm.trans current)
  subst buffer
  exact (materialize_entry s.objects i32 data.owner (box data) _ entry).1

theorem other_payload (s out : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (program : NProgram) (expressions : List (NExpr × Int)) (ready : Ready s i32 expressions)
    (params : program.parameters = .vector i32 false :: .scalar i32 true false :: .scalar i32 false true :: parameters i32 expressions)
    (retType : Ty) (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppFixedRun.Allowed program.body = true)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (contexts : ∀ owner scope, (project s i32).frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (fuel : Nat) (result : Ret)
    (actual : callFuel program fuel s i32 (readArguments s object receiver expressions) = .finished (out,result)) :
    ∀ owner, owner ≠ data.owner →
      (project out i32).frame.state.storage.lookup owner = (project s i32).frame.state.storage.lookup owner := by
  obtain ⟨prepared,initial,vc,buffer,prep,compacted,qs,fw,ty,readonly,flag,scope,found,base,initialScope⟩ :=
    prepare_read_frame s object receiver program expressions ready params readable unique covered valid limit contexts
  have eq := Option.some.inj (found.symm.trans current)
  subst buffer
  have target : Proofs.CppFixedWrite.Target initial vc.R := by
    refine ⟨0,⟨vc.R,.integer vc.ty,vc.wV,.root vc.vsc⟩,?_,?_,rfl⟩
    · simp only [NState.vectorSlot,qs.slots]
      rfl
    · rw [fw.bindings]
      rfl
  have kept := Proofs.CppCompactValues.call_other program fuel s out prepared initial i32 retType
    (readArguments s object receiver expressions) result vc.R scalar allowed prep compacted target contexts covered actual
  have ownerEq : data.owner = vc.R := fw.owner
  rw [←ownerEq] at kept
  exact kept

theorem all_payload (s out : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (program : NProgram) (expressions : List (NExpr × Int)) (ready : Ready s i32 expressions)
    (params : program.parameters = .vector i32 false :: .scalar i32 true false :: .scalar i32 false true :: parameters i32 expressions)
    (retType : Ty) (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppFixedRun.Allowed program.body = true)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (contexts : ∀ owner scope, (project s i32).frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (fuel : Nat) (result : Ret)
    (actual : callFuel program fuel s i32 (readArguments s object receiver expressions) = .finished (out,result))
    (payload : ∃ buffer, (project out i32).frame.state.storage.lookup data.owner = some buffer ∧ buffer.items = data.items.map Value.integer) :
    ∀ owner, (project out i32).frame.state.storage.lookup owner = (project s i32).frame.state.storage.lookup owner := by
  have others := other_payload s out object receiver program expressions ready params retType scalar allowed data current
    readable unique covered valid limit contexts fuel result actual
  have old := source_payload s object receiver data current readable unique covered
  obtain ⟨buffer,found,items⟩ := payload
  have headers := (call_headers program fuel s out _ result covered actual).buffers data.owner
  rw [found,old] at headers
  simp only [Option.map_some,Option.some.injEq] at headers
  have eq := buffer_eq (box data) buffer headers items
  intro owner
  by_cases same : owner = data.owner
  · subst owner
    rw [found,eq,old]
  · exact others owner same


open Proofs.CppNestedEval

theorem effects (program : NProgram) (fuel : Nat) (s out : Context) (args : List NArgument) (result : Ret)
    (covered : OwnsAll s.objects.heap)
    (actual : callFuel program fuel s i32 args = .finished (out,result)) :
    Proofs.CppCallFrame.CallEffects (project s i32) (project out i32) := by
  have layout := call_layout program fuel s out i32 args result actual
  have frames := call_frame program fuel s out args result covered actual
  have bindings : (project out i32).frame.bindings = (project s i32).frame.bindings := by
    have views : List.map (viewBinding out.objects i32) s.objects.views =
        List.map (viewBinding s.objects i32) s.objects.views := by
      apply List.map_congr_left
      intro view _
      simp only [viewBinding,Heap.header,layout.headers,layout.allocations]
    simp only [project,materialize,layout.grants,layout.views,views]
  have slots : (project out i32).slots = (project s i32).slots := by
    simp only [project,layout.slots,layout.grants]
  exact ⟨frames.1,frames.2,bindings,layout.scope,slots,layout.bindings,layout.baseline,layout.memoryLength,
    by simp only [Proofs.CppNestedEval.liveS,project,layout.memoryLength,layout.bindings,layout.baseline]⟩

theorem reads (s out : Context) (program : NProgram) (fuel : Nat) (args : List NArgument) (result : Ret)
    (covered : OwnsAll s.objects.heap)
    (valid : (project s i32).frame.state.wellFormed = true)
    (actual : callFuel program fuel s i32 args = .finished (out,result))
    (lookups : ∀ owner, (project out i32).frame.state.storage.lookup owner = (project s i32).frame.state.storage.lookup owner) :
    ∀ reference, (project out i32).frame.read reference = (project s i32).frame.read reference := by
  have effect := effects program fuel s out args result covered actual
  have afterValid : (project out i32).frame.state.wellFormed = true :=
    materialize_ready out.objects i32 (by decide +kernel) (call_allocationsValid program fuel s out i32 args result actual)
  intro reference
  have objectEq : (project out i32).frame.object reference.address.owner (.integer reference.element) =
      (project s i32).frame.object reference.address.owner (.integer reference.element) := by
    simp only [Frame.object,valid,afterValid,lookups,effect.headers.forest]
  simp only [Frame.read,effect.grant reference,objectEq]

def receiver_after (s out : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (layout : Layout s out) (memory : out.scalars.memory = s.scalars.memory) : ReadReceiver out object i32 :=
  ⟨Field.update s out i32 receiver.counter layout receiver.counter.value
      (by rw [memory]; exact receiver.counter.found) receiver.counter.valid,
   Field.update s out i32 receiver.size layout receiver.size.value
      (by rw [memory]; exact receiver.size.found) receiver.size.valid,
   receiver.fields,receiver.viewSlot,receiver.view,receiver.header,
   by simpa only [vectorView,layout.slots] using receiver.located,
   by simpa only [Proofs.CppMoveViews.resolve,Heap.header,layout.views,layout.headers] using receiver.resolved⟩


structure Preserved (before after : Context) (object : ObjectRef) (receiver : ReadReceiver before object i32) : Prop where
  memory : after.scalars.memory = before.scalars.memory
  layout : Layout before after
  payload : ∀ owner, (project after i32).frame.state.storage.lookup owner = (project before i32).frame.state.storage.lookup owner
  references : ∀ reference, (project after i32).frame.read reference = (project before i32).frame.read reference
  receiver : ∃ next : ReadReceiver after object i32,
    next.counter.value = receiver.counter.value ∧ next.size.value = receiver.size.value

theorem preserved (s out : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (program : NProgram) (expressions : List (NExpr × Int)) (ready : Ready s i32 expressions)
    (params : program.parameters = .vector i32 false :: .scalar i32 true false :: .scalar i32 false true :: parameters i32 expressions)
    (retType : Ty) (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppFixedRun.Allowed program.body = true)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (contexts : ∀ owner scope, (project s i32).frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (fuel : Nat) (result : Ret)
    (actual : callFuel program fuel s i32 (readArguments s object receiver expressions) = .finished (out,result))
    (payload : ∃ buffer, (project out i32).frame.state.storage.lookup data.owner = some buffer ∧ buffer.items = data.items.map Value.integer)
    (memory : out.scalars.memory = s.scalars.memory) : Preserved s out object receiver := by
  have all := all_payload s out object receiver program expressions ready params retType scalar allowed data current
    readable unique covered valid limit contexts fuel result actual payload
  have sourceValid := materialize_ready s.objects i32 (by decide +kernel) valid
  have readEq := reads s out program fuel _ result covered sourceValid actual all
  have layout := call_layout program fuel s out i32 _ result actual
  exact ⟨memory,layout,all,readEq,receiver_after s out object receiver layout memory,rfl,rfl⟩

open Proofs.UfReadPrograms Proofs.UfRootCall
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
    ∃ (fuel : Nat) (out : Context) (root : Nat) (weight : Int),
      callFuel sizeProgram fuel s i32 (readArguments s object receiver [(expression,(a : Int))]) = .finished (out,.scalar (-weight)) ∧
      Reach data.items a root ∧ root < data.items.length ∧ data.items[root]? = some weight ∧ weight < 0 ∧
      (∀ groups, Proofs.UfClassInvariant.Valid data.items groups rank →
        -weight = ((Proofs.UfClassInvariant.component data.items a).length : Int)) ∧
      work out ≤ work s+expression.nodes+16*rank a+49 ∧ Proofs.UfReadPrepareBudget.Resources s out expression.nodes ∧ Preserved s out object receiver := by
  have ready : Ready s i32 [(expression,(a : Int))] := by
    intro e value member
    rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
    exact ⟨typed,scalar,denotes⟩
  obtain ⟨fuel,out,root,weight,call,reach,insideRoot,found,negative,meaning,cost,memory,resources,payload⟩ :=
    Proofs.UfReadPrepareBudget.size_call s object receiver data current rank forest length weights a inside expression typed scalar denotes
      readable unique covered valid limit baseline contexts
  have keep := preserved s out object receiver sizeProgram [(expression,(a : Int))] ready rfl i32 rfl (by decide +kernel)
    data current readable unique covered valid limit contexts fuel (.scalar (-weight)) call payload memory
  exact ⟨fuel,out,root,weight,call,reach,insideRoot,found,negative,meaning,cost,resources,keep⟩

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
    ∃ (fuel : Nat) (out : Context) (root1 root2 : Nat),
      callFuel sameProgram fuel s i32 (readArguments s object receiver [(ea,(a : Int)),(eb,(b : Int))]) =
        .finished (out,.scalar (if root1=root2 then 1 else 0)) ∧
      Reach data.items a root1 ∧ Reach data.items b root2 ∧
      (root1=root2 ↔ Proofs.UfFieldsSame.Connected data.items a b) ∧
      work out ≤ work s+ea.nodes+eb.nodes+16*rank a+16*rank b+84 ∧ Proofs.UfReadPrepareBudget.Resources s out (ea.nodes+eb.nodes) ∧ Preserved s out object receiver := by
  obtain ⟨fuel,out,r1,r2,call,reach1,reach2,connected,cost,memory,resources,payload⟩ :=
    Proofs.UfReadPrepareBudget.same_call s object receiver data current rank forest length a b ha hb ea eb ready
      readable unique covered valid limit baseline contexts
  have keep := preserved s out object receiver sameProgram [(ea,(a : Int)),(eb,(b : Int))] ready rfl
    Proofs.PrefixSumsCall.bT rfl (by decide +kernel) data current readable unique covered valid limit contexts fuel _ call payload memory
  exact ⟨fuel,out,r1,r2,call,reach1,reach2,connected,cost,resources,keep⟩

theorem counter_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (data : Buffer Int) (fuel : Nat) (out : Context),
      currentBuffer s.objects.heap receiver.view.header receiver.header = some data ∧
      callFuel counterProgram fuel s i32 (readArguments s object receiver []) = .finished (out,.scalar receiver.counter.value) ∧
      work out ≤ work s+10 ∧ Proofs.UfReadPrepareBudget.Resources s out 0 ∧ Preserved s out object receiver := by
  obtain ⟨data,fuel,out,current,call,cost,memory,resources,payload⟩ :=
    Proofs.UfReadPrepareBudget.counter_call s object receiver readable unique covered valid limit baseline contexts
  have ready : Ready s i32 [] := by intro e value member; simp at member
  have keep := preserved s out object receiver counterProgram [] ready rfl i32 rfl (by decide +kernel)
    data current readable unique covered valid limit contexts fuel _ call payload memory
  exact ⟨data,fuel,out,current,call,cost,resources,keep⟩


end Proofs.UfReadValues
