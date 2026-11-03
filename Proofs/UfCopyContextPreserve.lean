import Proofs.UfCopyContext
import Proofs.UfObjectConstructionPreserve

namespace Proofs.UfCopyContextPreserve
open Proofs.UfCopyContext Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.CppMoveObjectReceiver Proofs.CppMoveReadReceiver Proofs.DoublingNested

theorem old_field (s : Context) (data : Proofs.CppVector.Buffer Int) (count n : Int) (w : Bool)
    (ty : Proofs.CppScalar.Ty) (field : Field s ty) :
    let after := Proofs.UfCopyContext.state (project s i32) data count n w
    ∃ next : Field (exported s after data w) ty,
      next.slot = field.slot ∧ next.index = field.index ∧ next.address = field.address ∧
      next.writable = field.writable ∧ next.value = field.value := by
  dsimp only
  let after := Proofs.UfCopyContext.state (project s i32) data count n w
  have shape := Proofs.UfCopyContext.layout (project s i32) data count n w
  have located := field.located
  unfold Proofs.CppMoveContext.scalarSlot at located
  obtain ⟨loc,slotFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ located
  have slotInside := (List.getElem?_eq_some_iff.mp slotFound).1
  have indexInside := (List.getElem?_eq_some_iff.mp field.bound).1
  have addressInside := (List.getElem?_eq_some_iff.mp field.found).1
  refine ⟨⟨field.slot,field.index,field.address,field.writable,field.value,?_,?_,?_,field.valid⟩,rfl,rfl,rfl,rfl,rfl⟩
  · have kept := Proofs.UfObjectConstructionPreserve.old_scalar_slot s after 0 field.slot shape slotInside
    change Proofs.CppMoveContext.scalarSlot (exported s after data w) field.slot = _ at kept
    rw [kept]
    exact field.located
  · have kept := Proofs.UfObjectConstructionPreserve.old_binding s after 0 field.index shape indexInside
    exact kept.trans field.bound
  · change (s.scalars.memory++[⟨i32,count⟩,⟨i32,n⟩])[field.address]? = _
    rw [List.getElem?_append_left addressInside]
    exact field.found

theorem old_resolve (s : Context) (after : NState) (data : Proofs.CppVector.Buffer Int) (w : Bool)
    (slot : Nat) (view : Proofs.CppMoveViews.View) (header : Proofs.CppMoveHeaders.Header)
    (resolved : Proofs.CppMoveViews.resolve s.objects slot = some (view,header)) :
    Proofs.CppMoveViews.resolve (exported s after data w).objects slot = some (view,header) := by
  unfold Proofs.CppMoveViews.resolve at resolved
  obtain ⟨actualView,viewFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ resolved
  obtain ⟨actualHeader,headerFound,final⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  have viewInside := (List.getElem?_eq_some_iff.mp viewFound).1
  have headerInside := (List.getElem?_eq_some_iff.mp (Proofs.CppMoveHeaders.header_lookup _ _ _ headerFound)).1
  have kept : (exported s after data w).objects.heap.header actualView.header = s.objects.heap.header actualView.header :=
    Proofs.CppMoveAppendOwned.old_header s.objects.heap (payload data) s.scope w actualView.header headerInside
  unfold Proofs.CppMoveViews.resolve
  change (do let v ← (s.objects.views++([⟨s.objects.heap.headers.length,w⟩] : List Proofs.CppMoveViews.View))[slot]?; let h ← (exported s after data w).objects.heap.header v.header; if v.writable = true → h.writable = true then some (v,h) else none) = _
  rw [List.getElem?_append_left viewInside,viewFound]
  change (do let h ← (exported s after data w).objects.heap.header actualView.header; if actualView.writable = true → h.writable = true then some (actualView,h) else none) = _
  rw [kept]
  exact rest

theorem old_read_receiver (s : Context) (data : Proofs.CppVector.Buffer Int) (count n : Int) (w : Bool)
    (object : ObjectRef) (r : ReadReceiver s object i32) :
    let after := Proofs.UfCopyContext.state (project s i32) data count n w
    ∃ next : ReadReceiver (exported s after data w) object i32,
      next.counter.address = r.counter.address ∧ next.size.address = r.size.address ∧
      next.counter.value = r.counter.value ∧ next.size.value = r.size.value ∧
      next.counter.writable = r.counter.writable ∧ next.size.writable = r.size.writable ∧
      next.view = r.view ∧ next.header = r.header := by
  dsimp only
  let after := Proofs.UfCopyContext.state (project s i32) data count n w
  obtain ⟨counter,slotC,indexC,addressC,writableC,valueC⟩ := old_field s data count n w i32 r.counter
  obtain ⟨size,slotS,indexS,addressS,writableS,valueS⟩ := old_field s data count n w i32 r.size
  have located := r.located
  unfold vectorView at located
  obtain ⟨loc,slotFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ located
  have slotInside := (List.getElem?_eq_some_iff.mp slotFound).1
  have shape := Proofs.UfCopyContext.layout (project s i32) data count n w
  refine ⟨⟨counter,size,?_,r.viewSlot,r.view,r.header,?_,old_resolve s after data w r.viewSlot r.view r.header r.resolved⟩,
    addressC,addressS,valueC,valueS,writableC,writableS,rfl,rfl⟩
  · rw [slotC,slotS]
    exact r.fields
  · unfold vectorView
    have kept := Proofs.UfObjectConstructionPreserve.old_slot s after 0 object.vectorSlot shape slotInside
    change (exported s after data w).slots[object.vectorSlot]? = _ at kept
    rw [kept]
    exact r.located

theorem old_allocation (s : Context) (after : NState) (data : Proofs.CppVector.Buffer Int) (w : Bool)
    (owner : Nat) (inside : owner < s.objects.heap.allocations.length) :
    (exported s after data w).objects.heap.allocation owner = s.objects.heap.allocation owner :=
  Proofs.CppMoveAppendOwned.old_allocation s.objects.heap (payload data) s.scope w owner inside

theorem current_payload (s : Context) (after : NState) (cloned : Proofs.CppVector.Buffer Int) (w : Bool)
    (id : Nat) (header : Proofs.CppMoveHeaders.Header) (data : Proofs.CppVector.Buffer Int)
    (current : Proofs.CppMoveFrame.currentBuffer s.objects.heap id header = some data) :
    ∃ next : Proofs.CppVector.Buffer Int,
      Proofs.CppMoveFrame.currentBuffer (exported s after cloned w).objects.heap id header = some next ∧
      next.items = data.items ∧ next.capacity = data.capacity ∧ next.limit = data.limit ∧ next.epoch = data.epoch := by
  cases owns : header.allocation with
  | none =>
    have same : (⟨s.objects.heap.allocations.length+id,[],0,header.limit,0⟩ : Proofs.CppVector.Buffer Int) = data := by
      simpa only [Proofs.CppMoveFrame.currentBuffer,owns,Option.some.injEq] using current
    subst data
    exact ⟨⟨(exported s after cloned w).objects.heap.allocations.length+id,[],0,header.limit,0⟩,
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
      rw [old_allocation s after cloned w owner inside,allocation]
      rfl

theorem old_receiver (s : Context) (data : Proofs.CppVector.Buffer Int) (count n : Int) (w : Bool)
    (object : ObjectRef) (r : Receiver s object i32) :
    let after := Proofs.UfCopyContext.state (project s i32) data count n w
    ∃ next : Receiver (exported s after data w) object i32,
      next.counter.address = r.counter.address ∧ next.size.address = r.size.address ∧
      next.counter.value = r.counter.value ∧ next.size.value = r.size.value ∧
      next.view = r.view ∧ next.header = r.header := by
  dsimp only
  obtain ⟨next,addrC,addrS,valueC,valueS,writableC,writableS,view,header⟩ :=
    old_read_receiver s data count n w object (of_mutable s object i32 r)
  refine ⟨⟨next.counter,next.size,next.fields,?_,next.viewSlot,next.view,next.header,
    next.located,next.resolved,?_⟩,addrC,addrS,valueC,valueS,view,header⟩
  · exact writableC.trans r.counterWritable
  · rw [view]
    exact r.writable

theorem old_readable (s : Context) (after : NState) (data : Proofs.CppVector.Buffer Int) (w : Bool)
    (id : Nat) (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header id = some header) (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (accept : Int → Bool) :
    Proofs.CppMoveHeaders.readable (exported s after data w).objects.heap header accept =
      Proofs.CppMoveHeaders.readable s.objects.heap header accept := by
  cases owns : header.allocation with
  | none => simp only [Proofs.CppMoveHeaders.readable,owns]
  | some owner =>
    have inside := Proofs.CppMoveAppendOwned.header_owner_bound s.objects.heap live id header owner found owns
    simp only [Proofs.CppMoveHeaders.readable,owns]
    rw [old_allocation s after data w owner inside]

theorem old_state (s : Context) (data : Proofs.CppVector.Buffer Int) (count n : Int) (w : Bool)
    (object : ObjectRef) (original : Proofs.UfObjectState.State s object)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap) (valid : data.Valid i32.valid) :
    let after := Proofs.UfCopyContext.state (project s i32) data count n w
    ∃ next : Proofs.UfObjectState.State (exported s after data w) object,
      next.data.items = original.data.items ∧ next.rank = original.rank ∧
      next.receiver.counter.value = original.receiver.counter.value ∧
      next.receiver.size.value = original.receiver.size.value := by
  dsimp only
  let after := Proofs.UfCopyContext.state (project s i32) data count n w
  obtain ⟨r,addressC,addressS,valueC,valueS,viewEq,headerEq⟩ :=
    old_receiver s data count n w object original.receiver
  obtain ⟨nextData,current,items,capacity,limit,epoch⟩ :=
    current_payload s after data w original.receiver.view.header original.receiver.header original.data original.current
  have newCurrent : Proofs.CppMoveFrame.currentBuffer (exported s after data w).objects.heap r.view.header r.header = some nextData := by
    rw [viewEq,headerEq]
    exact current
  have headerFound := (Proofs.CppMoveViews.resolve_parts s.objects original.receiver.viewSlot
    original.receiver.view original.receiver.header original.receiver.resolved).2.1
  have readable : Proofs.CppMoveHeaders.readable (exported s after data w).objects.heap r.header i32.valid = true := by
    rw [headerEq,old_readable s after data w original.receiver.view.header original.receiver.header headerFound live i32.valid]
    exact original.readable
  have inv := heap_invariants s after data w original.unique original.covered live original.allocations valid
  have oldScopes := Proofs.CppMoveFrameScopes.headers_of_contexts s.objects i32 s.scope
    original.unique original.covered live original.contexts
  have newScopes : Proofs.CppMoveFrameScopes.HeaderScopes (exported s after data w).objects.heap s.scope :=
    Proofs.CppMoveFrameScopes.appended_scopes s.objects.heap (payload data) s.scope s.scope w oldScopes (Nat.le_refl _)
  have contexts := Proofs.CppMoveFrameScopes.contexts_of_headers (exported s after data w).objects i32 s.scope newScopes
  refine ⟨⟨r,nextData,newCurrent,original.rank,?_,?_,?_,readable,inv.1,inv.2.1,inv.2.2.2,?_,?_,?_⟩,
    items,rfl,valueC,valueS⟩
  · rw [items,valueC]
    exact original.math
  · rw [items,valueS]
    exact original.size
  · rw [addressC,addressS]
    exact original.separated
  · rw [headerEq]
    exact original.limit
  · have before := original.baseline
    change s.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix s).length at before
    simp only [Proofs.CppMoveReceiverLayout.receiverPrefix,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil] at before ⊢
    have shape := Proofs.UfCopyContext.layout (project s i32) data count n w
    have slots := Proofs.UfObjectConstructionPreserve.exported_slots s after 0 shape
    change (exported s after data w).slots = _ at slots
    rw [slots]
    simp only [scalarLocations,List.length_append,List.length_cons,List.length_nil,List.length_map,List.length_range]
    have scalarFacts := scalar_metadata s data count n w
    rw [scalarFacts.2.2,scalarFacts.1]
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  · intro owner sc found
    exact contexts owner sc found

end Proofs.UfCopyContextPreserve
