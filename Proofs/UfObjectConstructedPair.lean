import Proofs.UfObjectPairTrace
import Proofs.UfObjectConstructionPreserve

namespace Proofs.UfObjectConstructedPair
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppMoveCallLayout Proofs.CppConstructorFinish
open Proofs.CppNestedProgram Proofs.CppMoveFrame Proofs.CppMoveHeaders Proofs.CppMoveSpace Proofs.DoublingNested
open Proofs.UfObjectState Proofs.UfObjectConstructionContext Proofs.UfObjectConstructionExport Proofs.UfObjectPair

-- Any two receivers of the same object in the same Context have identical identifying metadata.
theorem receiver_same (s : Context) (object : ObjectRef) (a b : Receiver s object i32) :
    b.counter.address = a.counter.address ∧ b.size.address = a.size.address ∧ b.view = a.view ∧ b.header = a.header :=
  Proofs.UfObjectIdentity.receiver s s object i32 a b (by constructor <;> rfl)

theorem state_owner (s : Context) (object : ObjectRef) (state : State s object) :
    state.data.owner = state.receiver.header.allocation.getD (s.objects.heap.allocations.length+state.receiver.view.header) := by
  have headerFound := (Proofs.CppMoveViews.resolve_parts s.objects state.receiver.viewSlot state.receiver.view state.receiver.header state.receiver.resolved).2.1
  obtain ⟨buffer,current,entry,valid,limit,owner⟩ := Proofs.CppMoveReceiverFrame.current_entry s.objects.heap i32
    state.receiver.view.header state.receiver.header headerFound state.readable state.unique state.covered
  have same := Option.some.inj (current.symm.trans state.current)
  subst buffer
  exact owner

theorem header_bound (s : Heap Int) (id : Nat) (header : Header) (owner : Nat)
    (live : HeadersLive s) (found : s.header id = some header) (owns : header.allocation = some owner) :
    owner < s.allocations.length := by
  have present := live id header owner found owns
  cases allocation : s.allocation owner with
  | none => simp [allocation] at present
  | some tracked => exact Proofs.CppMoveAssign.allocation_inside s owner tracked allocation

theorem apart_initialized (s : Context) (after : NState) (n : Nat) (object : ObjectRef)
    (state : State s object) (old : State (exported s after n) object)
    (new : State (exported s after n) (reference (project s i32) 2))
    (live : HeadersLive s.objects.heap)
    (initialized : Proofs.UfConstructionExport.Initialized (project s i32) after (List.replicate n (-1)) n n)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (reference (project s i32) 2)) : Apart old new := by
  obtain ⟨knownOld,oldCounter,oldSize,oldCount,oldN,oldView,oldHeader⟩ :=
    Proofs.UfObjectConstructionPreserve.old_receiver s after n object state.receiver initialized layout
  obtain ⟨knownNew,newCounter,newSize,newCount,newN,newHeader,newView⟩ :=
    Proofs.UfObjectConstructionContext.receiver s after n initialized layout
  have oldIdentity := receiver_same (exported s after n) object knownOld old.receiver
  have newIdentity := receiver_same (exported s after n) (reference (project s i32) 2) knownNew new.receiver
  have oldCounterEq := oldIdentity.1.trans oldCounter
  have oldSizeEq := oldIdentity.2.1.trans oldSize
  have oldViewEq := oldIdentity.2.2.1.trans oldView
  have oldHeaderEq := oldIdentity.2.2.2.trans oldHeader
  have newCounterEq := newIdentity.1.trans newCounter
  have newSizeEq := newIdentity.2.1.trans newSize
  have newHeaderEq := newIdentity.2.2.2.trans newHeader
  have allocationLength : (exported s after n).objects.heap.allocations.length = s.objects.heap.allocations.length+1 := by
    simp [exported,exportedHeap,Proofs.CppMoveAppendOwned.appended]
  have oldOwner := state_owner (exported s after n) object old
  rw [oldViewEq,oldHeaderEq,allocationLength] at oldOwner
  have newOwner := state_owner (exported s after n) (reference (project s i32) 2) new
  rw [newHeaderEq] at newOwner
  change new.data.owner = s.objects.heap.allocations.length at newOwner
  have different : old.data.owner ≠ new.data.owner := by
    cases owns : state.receiver.header.allocation with
    | none =>
      rw [owns] at oldOwner
      change old.data.owner = s.objects.heap.allocations.length+1+state.receiver.view.header at oldOwner
      rw [oldOwner,newOwner]
      omega
    | some owner =>
      have headerFound := (Proofs.CppMoveViews.resolve_parts s.objects state.receiver.viewSlot state.receiver.view state.receiver.header state.receiver.resolved).2.1
      have inside := header_bound s.objects.heap state.receiver.view.header state.receiver.header owner live headerFound owns
      rw [owns] at oldOwner
      change old.data.owner = owner at oldOwner
      rw [oldOwner,newOwner]
      omega
  have counterInside := (List.getElem?_eq_some_iff.mp state.receiver.counter.found).1
  have sizeInside := (List.getElem?_eq_some_iff.mp state.receiver.size.found).1
  refine ⟨different,?_,?_,?_⟩
  · rw [oldCounterEq,newCounterEq]
    omega
  · rw [oldCounterEq,newSizeEq]
    omega
  · rw [oldSizeEq,newCounterEq]
    omega

theorem construct_sized (s : Context) (heap : Proofs.CppRootModel.Heap) (object : ObjectRef)
    (state : Proofs.UfObjectState.State s object)
    (models : Proofs.CppRootModel.HeapModels (project s i32).frame.state heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (typed : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (n : Int)) :
    ∃ (after : NState) (pair : Pair (exported s after n) object (reference (project s i32) 2)),
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 (project s i32) [.value en]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (after,(reference (project s i32) 2)) ∧
      pair.left.data.items = state.data.items ∧ pair.left.rank = state.rank ∧
      pair.left.receiver.counter.value = state.receiver.counter.value ∧ pair.left.receiver.size.value = state.receiver.size.value ∧
      pair.right.data.items = List.replicate n (-1) ∧ Proofs.CppMoveSpace.HeadersLive (exported s after n).objects.heap := by
  have wf := Proofs.CppMoveFrame.materialize_ready s.objects i32 (by decide +kernel) state.allocations
  have lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length := by
    simp [project,Proofs.CppMoveFrame.materialize]
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ :=
    Proofs.UfObjectConstructionExport.sized_export s heap wf models lengths state.contexts base
      state.unique state.covered live state.allocations en n small scalar typed value
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8 (project s i32) after [.value en]
    (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) (reference (project s i32) 2) rfl ran
  obtain ⟨old,items,rank,count,size⟩ := Proofs.UfObjectConstructionPreserve.old_state s after n small object state live base initialized layout
  obtain ⟨new,newItems,liveAfter⟩ := Proofs.UfObjectConstructedState.initialized_state s after n small
    initialized layout state.unique state.covered live state.allocations base state.contexts
  have apart := apart_initialized s after n object state old new live initialized layout
  let pair : Pair (exported s after n) object (reference (project s i32) 2) := ⟨old,new,apart⟩
  exact ⟨after,pair,ran,items,rank,count,size,newItems,liveAfter⟩

theorem construct_default (s : Context) (heap : Proofs.CppRootModel.Heap) (object : ObjectRef)
    (state : Proofs.UfObjectState.State s object)
    (models : Proofs.CppRootModel.HeapModels (project s i32).frame.state heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length) :
    ∃ (after : NState) (pair : Pair (exported s after 0) object (reference (project s i32) 2)),
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 (project s i32) []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (after,(reference (project s i32) 2)) ∧
      pair.left.data.items = state.data.items ∧ pair.left.rank = state.rank ∧
      pair.left.receiver.counter.value = state.receiver.counter.value ∧ pair.left.receiver.size.value = state.receiver.size.value ∧
      pair.right.data.items = List.replicate 0 (-1) ∧ Proofs.CppMoveSpace.HeadersLive (exported s after 0).objects.heap := by
  have wf := Proofs.CppMoveFrame.materialize_ready s.objects i32 (by decide +kernel) state.allocations
  have lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length := by
    simp [project,Proofs.CppMoveFrame.materialize]
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ :=
    Proofs.UfObjectConstructionExport.default_export s heap wf models lengths state.contexts base
      state.unique state.covered live state.allocations
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct0 8 (project s i32) after []
    (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) (reference (project s i32) 2) rfl ran
  obtain ⟨old,items,rank,count,size⟩ := Proofs.UfObjectConstructionPreserve.old_state s after 0 (by decide +kernel) object state live base initialized layout
  obtain ⟨new,newItems,liveAfter⟩ := Proofs.UfObjectConstructedState.initialized_state s after 0 (by decide +kernel)
    initialized layout state.unique state.covered live state.allocations base state.contexts
  have apart := apart_initialized s after 0 object state old new live initialized layout
  let pair : Pair (exported s after 0) object (reference (project s i32) 2) := ⟨old,new,apart⟩
  exact ⟨after,pair,ran,items,rank,count,size,newItems,liveAfter⟩

theorem construct_sized_trace (s : Context) (heap : Proofs.CppRootModel.Heap) (object : ObjectRef)
    (state : Proofs.UfObjectState.State s object)
    (models : Proofs.CppRootModel.HeapModels (project s i32).frame.state heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (typed : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (n : Int))
    (actions : List Proofs.UfObjectPairTrace.Action)
    (ready : ∀ action ∈ actions, action.Valid state.data.items.length n) :
    ∃ (after : NState) (pair : Pair (exported s after n) object (reference (project s i32) 2))
      (script : List (Nat × Proofs.UfObjectPairTrace.Action)) (out : Context) (results : List Ret)
      (final : Pair out object (reference (project s i32) 2)),
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 (project s i32) [.value en]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (after,(reference (project s i32) 2)) ∧
      pair.left.data.items = state.data.items ∧ pair.left.rank = state.rank ∧
      pair.left.receiver.counter.value = state.receiver.counter.value ∧ pair.left.receiver.size.value = state.receiver.size.value ∧
      pair.right.data.items = List.replicate n (-1) ∧ HeadersLive (exported s after n).objects.heap ∧
      script.map Prod.snd = actions ∧
      Proofs.UfObjectPairTrace.run (exported s after n) object (reference (project s i32) 2) script = .finished (out,results) ∧
      results.length = actions.length ∧ final.left.receiver.size.value = state.receiver.size.value ∧
      final.right.receiver.size.value = (n : Int) ∧
      Proofs.UfObjectPairTrace.History object (reference (project s i32) 2) (exported s after n) pair actions out results final := by
  obtain ⟨after,pair,constructed,oldItems,oldRank,oldCount,oldSize,newItems,liveAfter⟩ :=
    construct_sized s heap object state models live base en n small scalar typed value
  have readyPair : ∀ action ∈ actions, action.Valid pair.left.data.items.length pair.right.data.items.length := by
    intro action member
    rw [oldItems,newItems,List.length_replicate]
    exact ready action member
  obtain ⟨script,out,results,final,mapped,ran,count,leftSize,rightSize,history⟩ :=
    Proofs.UfObjectPairTrace.execute (exported s after n) object (reference (project s i32) 2) pair actions readyPair
  have initialRightSize : pair.right.receiver.size.value = (n : Int) := by
    simpa only [newItems,List.length_replicate,Nat.cast_zero] using pair.right.size
  exact ⟨after,pair,script,out,results,final,constructed,oldItems,oldRank,oldCount,oldSize,newItems,liveAfter,
    mapped,ran,count,leftSize.trans oldSize,rightSize.trans initialRightSize,history⟩

theorem construct_default_trace (s : Context) (heap : Proofs.CppRootModel.Heap) (object : ObjectRef)
    (state : Proofs.UfObjectState.State s object)
    (models : Proofs.CppRootModel.HeapModels (project s i32).frame.state heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (actions : List Proofs.UfObjectPairTrace.Action)
    (ready : ∀ action ∈ actions, action.Valid state.data.items.length 0) :
    ∃ (after : NState) (pair : Pair (exported s after 0) object (reference (project s i32) 2))
      (script : List (Nat × Proofs.UfObjectPairTrace.Action)) (out : Context) (results : List Ret)
      (final : Pair out object (reference (project s i32) 2)),
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 (project s i32) []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (after,(reference (project s i32) 2)) ∧
      pair.left.data.items = state.data.items ∧ pair.left.rank = state.rank ∧
      pair.left.receiver.counter.value = state.receiver.counter.value ∧ pair.left.receiver.size.value = state.receiver.size.value ∧
      pair.right.data.items = List.replicate 0 (-1) ∧ HeadersLive (exported s after 0).objects.heap ∧
      script.map Prod.snd = actions ∧
      Proofs.UfObjectPairTrace.run (exported s after 0) object (reference (project s i32) 2) script = .finished (out,results) ∧
      results.length = actions.length ∧ final.left.receiver.size.value = state.receiver.size.value ∧
      final.right.receiver.size.value = (0 : Int) ∧
      Proofs.UfObjectPairTrace.History object (reference (project s i32) 2) (exported s after 0) pair actions out results final := by
  obtain ⟨after,pair,constructed,oldItems,oldRank,oldCount,oldSize,newItems,liveAfter⟩ :=
    construct_default s heap object state models live base
  have readyPair : ∀ action ∈ actions, action.Valid pair.left.data.items.length pair.right.data.items.length := by
    intro action member
    rw [oldItems,newItems,List.length_replicate]
    exact ready action member
  obtain ⟨script,out,results,final,mapped,ran,count,leftSize,rightSize,history⟩ :=
    Proofs.UfObjectPairTrace.execute (exported s after 0) object (reference (project s i32) 2) pair actions readyPair
  have initialRightSize : pair.right.receiver.size.value = (0 : Int) := by
    simpa only [newItems,List.length_replicate,Nat.cast_zero] using pair.right.size
  exact ⟨after,pair,script,out,results,final,constructed,oldItems,oldRank,oldCount,oldSize,newItems,liveAfter,
    mapped,ran,count,leftSize.trans oldSize,rightSize.trans initialRightSize,history⟩

end Proofs.UfObjectConstructedPair
