import Proofs.CppMoveCallPayload
import Proofs.UfObjectMethods

namespace Proofs.UfObjectState
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppMoveCallLayout
open Proofs.CppMoveCallPayload Proofs.CppMoveFrame Proofs.CppScalar Proofs.CppVector
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish
open Proofs.CppMoveHeaders Proofs.CppMoveReceiverLayout Proofs.CppNestedVectorStore
open Proofs.CppMoveCallBindings Proofs.VecExpr Proofs.VecWrite Proofs.UfObjectCall
open Proofs.UfCompactCounterBody
open Proofs.UfCompactRootBody
open Proofs.UfRootCall Proofs.UfClassInvariant Proofs.UfCompression Proofs.DoublingNested

-- A normal UF object: moved-from getter states remain covered by the weak call API.
structure State (s : Context) (object : ObjectRef) where
  receiver : Receiver s object i32
  data : Buffer Int
  current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data
  rank : Nat → Nat
  math : Valid data.items receiver.counter.value rank
  size : receiver.size.value = (data.items.length : Int)
  separated : receiver.counter.address ≠ receiver.size.address
  readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true
  unique : Unique s.objects.heap
  covered : OwnsAll s.objects.heap
  allocations : AllocationsValid s.objects.heap i32
  limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32
  baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length
  contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope

theorem transition (s out : Context) (object : ObjectRef) (state : State s object)
    (program : NProgram) (fuel : Nat) (args : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s i32 args = .finished (out,result))
    (count : Int) (countValid : i32.valid count = true)
    (counter : out.scalars.memory[state.receiver.counter.address]? = some ⟨i32,count⟩)
    (sizeCell : out.scalars.memory[state.receiver.size.address]? = some ⟨i32,state.receiver.size.value⟩)
    (final : List Int) (rank : Nat → Nat) (math : Valid final count rank)
    (length : final.length = state.data.items.length)
    (buffer : Buffer Value)
    (lookup : (project out i32).frame.state.storage.lookup state.data.owner = some buffer)
    (items : buffer.items = final.map Value.integer) :
    ∃ next : State out object, next.rank = rank ∧ next.receiver.counter.value = count ∧
      next.receiver.size.value = state.receiver.size.value ∧ next.data.items = final := by
  have layout := call_layout program fuel s out i32 args result run
  let receiver := Receiver.update s out object i32 state.receiver layout count state.receiver.size.value
    counter countValid sizeCell state.receiver.size.valid
  have parts := Proofs.CppMoveViews.resolve_parts s.objects state.receiver.viewSlot
    state.receiver.view state.receiver.header state.receiver.resolved
  obtain ⟨data,current,dataItems⟩ := call_payload program fuel s out i32 args result run
    state.receiver.view.header state.receiver.header parts.2.1 state.readable state.unique state.covered
    state.data state.current final buffer lookup items
  have nextMath : Valid data.items receiver.counter.value rank := by
    change Valid data.items count rank
    rw [dataItems]
    exact math
  have nextSize : receiver.size.value = (data.items.length : Int) := by
    change state.receiver.size.value = _
    rw [dataItems,length]
    exact state.size
  let next : State out object := ⟨receiver,data,current,rank,nextMath,nextSize,state.separated,
    call_readable program fuel s out i32 args result run state.receiver.header state.readable,
    call_unique program fuel s out i32 args result run state.unique,
    call_ownsAll program fuel s out i32 args result run state.covered,
    call_allocationsValid program fuel s out i32 args result run,state.limit,
    Layout.baseline_fits s out layout state.baseline,
    call_contexts program fuel s out i32 args result run state.covered state.contexts⟩
  exact ⟨next,rfl,rfl,rfl,dataItems⟩

-- Retain the complete normal-call resource post and add closure of State.
theorem root_step (s : Context) (object : ObjectRef) (state : State s object)
    (a : Nat) (inside : a < state.data.items.length) (expression : NExpr)
    (typed : expression.resultType = i32) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int)) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat)
      (out : Context) (root : Nat) (final : List Int),
      (prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_root.parameters
        (arguments s object state.receiver [(expression,(a : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc state.data.items (box state.data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_root fuel s i32 (arguments s object state.receiver [(expression,(a : Int))]) = .finished (out,.scalar (root : Int)) ∧
      Compressed state.data.items final a root ∧ Forest final state.rank ∧
      work out ≤ work prepared+91*state.rank a+81 ∧
      out.scalars.memory = s.scalars.memory ∧
      out.scalars.peak ≤ max (max s.scalars.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max s.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max s.scalars.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
          (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer) ∧ ∃ next : State out object, next.rank = state.rank ∧
        next.receiver.counter.value = state.receiver.counter.value ∧
        next.receiver.size.value = state.receiver.size.value ∧ next.data.items = final := by

  obtain ⟨prepared,initial,vc,fuel,out,root,final,post⟩ :=
    Proofs.UfObjectCall.root_call s object state.receiver state.data state.current state.size
      state.rank state.math.forest state.math.length a inside expression typed scalar denotes
      state.readable state.unique state.covered state.allocations state.limit state.baseline state.contexts
  have complete := post
  obtain ⟨prep,compacted,fw,actual,compressed,forest,cost,memory,scalarPeak,heapPeak,peak,buffer,lookup,items⟩ := post
  have counter : out.scalars.memory[state.receiver.counter.address]? = some ⟨i32,state.receiver.counter.value⟩ := by
    rw [memory]
    exact state.receiver.counter.found
  have sizeCell : out.scalars.memory[state.receiver.size.address]? = some ⟨i32,state.receiver.size.value⟩ := by
    rw [memory]
    exact state.receiver.size.found
  have lookupOwner : (project out i32).frame.state.storage.lookup state.data.owner = some buffer := by
    change (project out i32).frame.state.storage.lookup (box state.data).owner = some buffer
    rw [fw.owner]
    exact lookup
  have next := transition s out object state Proofs.UnionFindCandidateInstance.UnionFind_root fuel
    (Proofs.UfObjectCall.arguments s object state.receiver [(expression,(a : Int))]) (.scalar (root : Int)) actual
    state.receiver.counter.value state.receiver.counter.valid counter sizeCell final state.rank
    (state.math.compressed compressed) compressed.length buffer lookupOwner items
  exact ⟨prepared,initial,vc,fuel,out,root,final,complete,next⟩

-- The complete getter post is retained together with normal-state closure.
theorem counter_step (s : Context) (object : ObjectRef) (state : State s object) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat) (out : Context),
      (prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters
        (arguments s object state.receiver []) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      currentBuffer s.objects.heap state.receiver.view.header state.receiver.header = some state.data ∧
      FW vc state.data.items (box state.data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel s i32 (arguments s object state.receiver []) = .finished (out,.scalar state.receiver.counter.value) ∧
      work out ≤ work prepared+3 ∧
      out.scalars.memory = s.scalars.memory ∧
      out.scalars.peak ≤ max (max s.scalars.peak (counterScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max s.peak (counterScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max s.scalars.peak (counterScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
          (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = state.data.items.map Value.integer) ∧ ∃ next : State out object, next.rank = state.rank ∧
        next.receiver.counter.value = state.receiver.counter.value ∧
        next.receiver.size.value = state.receiver.size.value ∧ next.data.items = state.data.items := by
  obtain ⟨prepared,initial,vc,data,fuel,out,post⟩ :=
    Proofs.UfObjectCall.counter_call s object state.receiver state.readable state.unique state.covered
      state.allocations state.limit state.baseline state.contexts
  have current := post.2.2.1
  have same : data = state.data := Option.some.inj (current.symm.trans state.current)
  subst data
  have complete := post
  obtain ⟨prep,compacted,current,fw,actual,cost,memory,scalarPeak,heapPeak,peak,buffer,lookup,items⟩ := post
  have counter : out.scalars.memory[state.receiver.counter.address]? = some ⟨i32,state.receiver.counter.value⟩ := by
    rw [memory]
    exact state.receiver.counter.found
  have sizeCell : out.scalars.memory[state.receiver.size.address]? = some ⟨i32,state.receiver.size.value⟩ := by
    rw [memory]
    exact state.receiver.size.found
  have lookupOwner : (project out i32).frame.state.storage.lookup state.data.owner = some buffer := by
    change (project out i32).frame.state.storage.lookup (box state.data).owner = some buffer
    rw [fw.owner]
    exact lookup
  have next := transition s out object state Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel
    (Proofs.UfObjectCall.arguments s object state.receiver []) (.scalar state.receiver.counter.value) actual
    state.receiver.counter.value state.receiver.counter.valid counter sizeCell state.data.items state.rank
    state.math rfl buffer lookupOwner items
  exact ⟨prepared,initial,vc,fuel,out,complete,next⟩

end Proofs.UfObjectState
