import Proofs.UfObjectConstructedState

namespace Proofs.UfObjectConstructionPreserve
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.DoublingNested
open Proofs.UfObjectConstructionContext Proofs.UfObjectConstructionExport Proofs.CppMoveObjectReceiver
open Proofs.DynamicResultValid

theorem inverse_location (grants : Nat) (loc : Proofs.CppMixedInvoke.Location) :
    unlocation grants (location grants loc) = loc := by
  cases loc <;> simp [unlocation,location]

theorem map_project_slots (s : Context) :
    (project s i32).slots.map (unlocation s.objects.heap.grants.length) = s.slots := by
  change (s.slots.map (location s.objects.heap.grants.length)).map (unlocation s.objects.heap.grants.length) = _
  rw [List.map_map]
  have same : (unlocation s.objects.heap.grants.length) ∘ (location s.objects.heap.grants.length) = id :=
    funext (inverse_location s.objects.heap.grants.length)
  rw [same,List.map_id]

theorem exported_slots (s : Context) (after : NState) (n : Nat)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (reference (project s i32) 2)) :
    (exported s after n).slots = s.slots++[.vector s.objects.views.length]++scalarLocations s.scalars.bindings.length 2 := by
  obtain ⟨oldCells,values,oldLength,oldTypes,memory,bindings,slots,scope,base,objectEq⟩ := layout
  have countSame := congrArg (fun object : ObjectRef => object.scalarSlots.length) objectEq
  have fieldCount : values.length = 2 := by simpa [reference] using countSame.symm
  change after.slots.map (unlocation s.objects.heap.grants.length) = _
  rw [slots,List.map_append,List.map_append,map_project_slots]
  simp [scalarLocations,List.map_map,Function.comp_def,unlocation,project,Proofs.CppMoveFrame.materialize,fieldCount]

theorem old_slot (s : Context) (after : NState) (n slot : Nat)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (reference (project s i32) 2))
    (inside : slot < s.slots.length) : (exported s after n).slots[slot]? = s.slots[slot]? := by
  rw [exported_slots s after n layout,List.append_assoc,List.getElem?_append_left inside]

theorem old_scalar_slot (s : Context) (after : NState) (n slot : Nat)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (reference (project s i32) 2))
    (inside : slot < s.slots.length) :
    Proofs.CppMoveContext.scalarSlot (exported s after n) slot = Proofs.CppMoveContext.scalarSlot s slot := by
  unfold Proofs.CppMoveContext.scalarSlot
  rw [old_slot s after n slot layout inside]

theorem old_binding (s : Context) (after : NState) (n index : Nat)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (reference (project s i32) 2))
    (inside : index < s.scalars.bindings.length) :
    (exported s after n).scalars.bindings[index]? = s.scalars.bindings[index]? := by
  obtain ⟨oldCells,values,oldLength,oldTypes,memory,bindings,slots,scope,base,objectEq⟩ := layout
  change after.scalars.bindings[index]? = _
  rw [bindings]
  change (s.scalars.bindings++scalarBindings s.scalars.memory.length values)[index]? = _
  rw [List.getElem?_append_left inside]

theorem old_memory (s : Context) (after : NState) (n address : Nat)
    (initialized : Proofs.UfConstructionExport.Initialized (project s i32) after (List.replicate n (-1)) n n)
    (inside : address < s.scalars.memory.length) :
    (exported s after n).scalars.memory[address]? = s.scalars.memory[address]? := by
  change after.scalars.memory[address]? = _
  rw [initialized.2.1]
  change (s.scalars.memory++[⟨i32,(n : Int)⟩,⟨i32,(n : Int)⟩])[address]? = _
  rw [List.getElem?_append_left inside]

theorem old_field (s : Context) (after : NState) (n : Nat) (ty : Proofs.CppScalar.Ty) (field : Field s ty)
    (initialized : Proofs.UfConstructionExport.Initialized (project s i32) after (List.replicate n (-1)) n n)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (reference (project s i32) 2)) :
    ∃ next : Field (exported s after n) ty,
      next.slot = field.slot ∧ next.index = field.index ∧ next.address = field.address ∧
      next.writable = field.writable ∧ next.value = field.value := by
  have located := field.located
  unfold Proofs.CppMoveContext.scalarSlot at located
  obtain ⟨loc,slotFound,rest⟩ := bind_some _ _ _ located
  have slotInside := (List.getElem?_eq_some_iff.mp slotFound).1
  have indexInside := (List.getElem?_eq_some_iff.mp field.bound).1
  have addressInside := (List.getElem?_eq_some_iff.mp field.found).1
  refine ⟨⟨field.slot,field.index,field.address,field.writable,field.value,?_,?_,?_,field.valid⟩,rfl,rfl,rfl,rfl,rfl⟩
  · rw [old_scalar_slot s after n field.slot layout slotInside]
    exact field.located
  · rw [old_binding s after n field.index layout indexInside]
    exact field.bound
  · rw [old_memory s after n field.address initialized addressInside]
    exact field.found

theorem old_resolve (s : Context) (after : NState) (n slot : Nat) (view : Proofs.CppMoveViews.View)
    (header : Proofs.CppMoveHeaders.Header) (resolved : Proofs.CppMoveViews.resolve s.objects slot = some (view,header)) :
    Proofs.CppMoveViews.resolve (exported s after n).objects slot = some (view,header) := by
  unfold Proofs.CppMoveViews.resolve at resolved
  obtain ⟨actualView,viewFound,rest⟩ := bind_some _ _ _ resolved
  obtain ⟨actualHeader,headerFound,final⟩ := bind_some _ _ _ rest
  have viewInside := (List.getElem?_eq_some_iff.mp viewFound).1
  have headerInside := (List.getElem?_eq_some_iff.mp (Proofs.CppMoveHeaders.header_lookup _ _ _ headerFound)).1
  have kept : (exported s after n).objects.heap.header actualView.header = s.objects.heap.header actualView.header :=
    Proofs.CppMoveAppendOwned.old_header s.objects.heap (payload n) s.scope true actualView.header headerInside
  unfold Proofs.CppMoveViews.resolve
  change (do let v ← (s.objects.views++([⟨s.objects.heap.headers.length,true⟩] : List Proofs.CppMoveViews.View))[slot]?; let h ← (exported s after n).objects.heap.header v.header; if v.writable = true → h.writable = true then some (v,h) else none) = _
  rw [List.getElem?_append_left viewInside,viewFound]
  change (do let h ← (exported s after n).objects.heap.header actualView.header; if actualView.writable = true → h.writable = true then some (actualView,h) else none) = _
  rw [kept]
  exact rest


theorem old_receiver (s : Context) (after : NState) (n : Nat) (object : ObjectRef) (r : Receiver s object i32)
    (initialized : Proofs.UfConstructionExport.Initialized (project s i32) after (List.replicate n (-1)) n n)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (reference (project s i32) 2)) :
    ∃ next : Receiver (exported s after n) object i32,
      next.counter.address = r.counter.address ∧ next.size.address = r.size.address ∧
      next.counter.value = r.counter.value ∧ next.size.value = r.size.value ∧ next.view = r.view ∧ next.header = r.header := by
  obtain ⟨counter,slotC,indexC,addressC,writableC,valueC⟩ := old_field s after n i32 r.counter initialized layout
  obtain ⟨size,slotS,indexS,addressS,writableS,valueS⟩ := old_field s after n i32 r.size initialized layout
  have located := r.located
  unfold vectorView at located
  obtain ⟨loc,slotFound,rest⟩ := bind_some _ _ _ located
  have slotInside := (List.getElem?_eq_some_iff.mp slotFound).1
  refine ⟨⟨counter,size,?_,?_,r.viewSlot,r.view,r.header,?_,old_resolve s after n r.viewSlot r.view r.header r.resolved,r.writable⟩,
    addressC,addressS,valueC,valueS,rfl,rfl⟩
  · rw [slotC,slotS]
    exact r.fields
  · rw [writableC]
    exact r.counterWritable
  · unfold vectorView
    rw [old_slot s after n object.vectorSlot layout slotInside]
    exact r.located

theorem old_allocation (s : Context) (after : NState) (n owner : Nat) (inside : owner < s.objects.heap.allocations.length) :
    (exported s after n).objects.heap.allocation owner = s.objects.heap.allocation owner :=
  Proofs.CppMoveAppendOwned.old_allocation s.objects.heap (payload n) s.scope true owner inside

theorem current_payload (s : Context) (after : NState) (n id : Nat) (header : Proofs.CppMoveHeaders.Header)
    (data : Proofs.CppVector.Buffer Int) (current : Proofs.CppMoveFrame.currentBuffer s.objects.heap id header = some data) :
    ∃ next : Proofs.CppVector.Buffer Int,
      Proofs.CppMoveFrame.currentBuffer (exported s after n).objects.heap id header = some next ∧
      next.items = data.items ∧ next.capacity = data.capacity ∧ next.limit = data.limit ∧ next.epoch = data.epoch := by
  cases owns : header.allocation with
  | none =>
    have same : (⟨s.objects.heap.allocations.length+id,[],0,header.limit,0⟩ : Proofs.CppVector.Buffer Int) = data := by
      simpa only [Proofs.CppMoveFrame.currentBuffer,owns,Option.some.injEq] using current
    subst data
    exact ⟨⟨(exported s after n).objects.heap.allocations.length+id,[],0,header.limit,0⟩,
      by simp only [Proofs.CppMoveFrame.currentBuffer,owns],rfl,rfl,rfl,rfl⟩
  | some owner =>
    cases allocation : s.objects.heap.allocation owner with
    | none => simp [Proofs.CppMoveFrame.currentBuffer,owns,allocation] at current
    | some tracked =>
      have same : tracked.buffer = data := by simpa only [Proofs.CppMoveFrame.currentBuffer,owns,allocation,Option.map_some,Option.some.injEq] using current
      subst data
      have inside := Proofs.CppMoveAssign.allocation_inside s.objects.heap owner tracked allocation
      refine ⟨tracked.buffer,?_,rfl,rfl,rfl,rfl⟩
      simp only [Proofs.CppMoveFrame.currentBuffer,owns]
      rw [old_allocation s after n owner inside,allocation]
      rfl

theorem old_readable (s : Context) (after : NState) (n id : Nat) (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header id = some header) (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (accept : Int → Bool) :
    Proofs.CppMoveHeaders.readable (exported s after n).objects.heap header accept = Proofs.CppMoveHeaders.readable s.objects.heap header accept := by
  cases owns : header.allocation with
  | none => simp only [Proofs.CppMoveHeaders.readable,owns]
  | some owner =>
    have inside := Proofs.CppMoveAppendOwned.header_owner_bound s.objects.heap live id header owner found owns
    simp only [Proofs.CppMoveHeaders.readable,owns]
    rw [old_allocation s after n owner inside]


theorem old_state (s : Context) (after : NState) (n : Nat) (small : n < 2147483648) (object : ObjectRef)
    (state : Proofs.UfObjectState.State s object) (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (initialized : Proofs.UfConstructionExport.Initialized (project s i32) after (List.replicate n (-1)) n n)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (reference (project s i32) 2)) :
    ∃ next : Proofs.UfObjectState.State (exported s after n) object,
      next.data.items = state.data.items ∧ next.rank = state.rank ∧
      next.receiver.counter.value = state.receiver.counter.value ∧ next.receiver.size.value = state.receiver.size.value := by
  obtain ⟨r,addressC,addressS,valueC,valueS,viewEq,headerEq⟩ := old_receiver s after n object state.receiver initialized layout
  obtain ⟨data,current,items,capacity,limit,epoch⟩ := current_payload s after n state.receiver.view.header state.receiver.header state.data state.current
  have newCurrent : Proofs.CppMoveFrame.currentBuffer (exported s after n).objects.heap r.view.header r.header = some data := by
    rw [viewEq,headerEq]
    exact current
  have headerFound := (Proofs.CppMoveViews.resolve_parts s.objects state.receiver.viewSlot state.receiver.view state.receiver.header state.receiver.resolved).2.1
  have readable : Proofs.CppMoveHeaders.readable (exported s after n).objects.heap r.header i32.valid = true := by
    rw [headerEq,old_readable s after n state.receiver.view.header state.receiver.header headerFound live i32.valid]
    exact state.readable
  have inv := heap_invariants s after n small state.unique state.covered live state.allocations
  have oldScopes := Proofs.CppMoveFrameScopes.headers_of_contexts s.objects i32 s.scope state.unique state.covered live state.contexts
  have newScopes : Proofs.CppMoveFrameScopes.HeaderScopes (exported s after n).objects.heap s.scope :=
    Proofs.CppMoveFrameScopes.appended_scopes s.objects.heap (payload n) s.scope s.scope true oldScopes (Nat.le_refl _)
  have contexts := Proofs.CppMoveFrameScopes.contexts_of_headers (exported s after n).objects i32 s.scope newScopes
  obtain ⟨oldCells,values,oldLength,oldTypes,memory,bindings,slots,scope,scalarBase,objectEq⟩ := layout
  have afterBase : after.scalars.baseMemory = s.scalars.baseMemory := scalarBase
  have length := congrArg List.length initialized.2.1
  simp only [List.length_append,List.length_cons,List.length_nil] at length
  change after.scalars.memory.length = s.scalars.memory.length+2 at length
  refine ⟨⟨r,data,newCurrent,state.rank,?_,?_,?_,readable,inv.1,inv.2.1,inv.2.2.2,?_,?_,?_⟩,items,rfl,valueC,valueS⟩
  · rw [items,valueC]
    exact state.math
  · rw [items,valueS]
    exact state.size
  · rw [addressC,addressS]
    exact state.separated
  · rw [headerEq]
    exact state.limit
  · simp only [Proofs.CppMoveReceiverLayout.receiverPrefix,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
    change after.scalars.baseMemory ≤ after.scalars.memory.length+(exported s after n).slots.length+1
    omega
  · intro owner sc found
    have bound := contexts owner sc found
    change sc ≤ after.scope
    rw [scope]
    exact bound


theorem construct_sized_pair (s : Context) (heap : Proofs.CppRootModel.Heap) (object : ObjectRef)
    (state : Proofs.UfObjectState.State s object)
    (models : Proofs.CppRootModel.HeapModels (project s i32).frame.state heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (typed : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (n : Int)) :
    ∃ (after : NState) (old : Proofs.UfObjectState.State (exported s after n) object)
      (new : Proofs.UfObjectState.State (exported s after n) (reference (project s i32) 2)),
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 (project s i32) [.value en]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (after,(reference (project s i32) 2)) ∧
      old.data.items = state.data.items ∧ old.rank = state.rank ∧
      old.receiver.counter.value = state.receiver.counter.value ∧ old.receiver.size.value = state.receiver.size.value ∧
      new.data.items = List.replicate n (-1) ∧ Proofs.CppMoveSpace.HeadersLive (exported s after n).objects.heap := by
  have wf := Proofs.CppMoveFrame.materialize_ready s.objects i32 (by decide +kernel) state.allocations
  have lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length := by
    simp [project,Proofs.CppMoveFrame.materialize]
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ :=
    Proofs.UfObjectConstructionExport.sized_export s heap wf models lengths state.contexts base
      state.unique state.covered live state.allocations en n small scalar typed value
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8 (project s i32) after [.value en]
    (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) (reference (project s i32) 2) rfl ran
  obtain ⟨old,items,rank,count,size⟩ := old_state s after n small object state live base initialized layout
  obtain ⟨new,newItems,liveAfter⟩ := Proofs.UfObjectConstructedState.initialized_state s after n small
    initialized layout state.unique state.covered live state.allocations base state.contexts
  exact ⟨after,old,new,ran,items,rank,count,size,newItems,liveAfter⟩


theorem construct_default_pair (s : Context) (heap : Proofs.CppRootModel.Heap) (object : ObjectRef)
    (state : Proofs.UfObjectState.State s object)
    (models : Proofs.CppRootModel.HeapModels (project s i32).frame.state heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length) :
    ∃ (after : NState) (old : Proofs.UfObjectState.State (exported s after 0) object)
      (new : Proofs.UfObjectState.State (exported s after 0) (reference (project s i32) 2)),
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 (project s i32) []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (after,(reference (project s i32) 2)) ∧
      old.data.items = state.data.items ∧ old.rank = state.rank ∧
      old.receiver.counter.value = state.receiver.counter.value ∧ old.receiver.size.value = state.receiver.size.value ∧
      new.data.items = List.replicate 0 (-1) ∧ Proofs.CppMoveSpace.HeadersLive (exported s after 0).objects.heap := by
  have wf := Proofs.CppMoveFrame.materialize_ready s.objects i32 (by decide +kernel) state.allocations
  have lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length := by
    simp [project,Proofs.CppMoveFrame.materialize]
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ :=
    Proofs.UfObjectConstructionExport.default_export s heap wf models lengths state.contexts base
      state.unique state.covered live state.allocations
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct0 8 (project s i32) after []
    (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) (reference (project s i32) 2) rfl ran
  obtain ⟨old,items,rank,count,size⟩ := old_state s after 0 (by decide +kernel) object state live base initialized layout
  obtain ⟨new,newItems,liveAfter⟩ := Proofs.UfObjectConstructedState.initialized_state s after 0 (by decide +kernel)
    initialized layout state.unique state.covered live state.allocations base state.contexts
  exact ⟨after,old,new,ran,items,rank,count,size,newItems,liveAfter⟩

end Proofs.UfObjectConstructionPreserve
