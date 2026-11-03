import Proofs.UfCopyContext
import Proofs.UfObjectConstructionPreserve

namespace Proofs.UfCopyNewState
open Proofs.UfCopyContext Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.CppMoveObjectReceiver Proofs.CppMoveReadReceiver Proofs.CppMoveFrame
open Proofs.CppMoveHeaders Proofs.CppMoveSpace Proofs.CppMoveFrameScopes Proofs.DoublingNested
open Proofs.CppVector

theorem new_state (s : Context) (data : Buffer Int) (count n : Int) (rank : Nat → Nat)
    (cv : i32.valid count = true) (nv : i32.valid n = true)
    (math : Proofs.UfClassInvariant.Valid data.items count rank) (size : n = (data.items.length : Int))
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (valid : data.Valid i32.valid) (limit : data.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    let after := Proofs.UfCopyContext.state (project s i32) data count n true
    ∃ next : Proofs.UfObjectState.State (exported s after data true) (reference (project s i32) 2),
      next.data.items = data.items ∧ next.rank = rank ∧
      next.receiver.counter.value = count ∧ next.receiver.size.value = n := by
  dsimp only
  let after := Proofs.UfCopyContext.state (project s i32) data count n true
  obtain ⟨r,addrC,addrS,valueC,valueS,writableC,writableS,headerEq,viewEq⟩ :=
    receiver s data count n true cv nv
  let mutableReceiver : Receiver (exported s after data true) (reference (project s i32) 2) i32 :=
    ⟨r.counter,r.size,r.fields,writableC,r.viewSlot,r.view,r.header,r.located,r.resolved,
      by rw [viewEq]⟩
  let newData : Buffer Int := {(payload data) with owner := s.objects.heap.allocations.length}
  have current : currentBuffer (exported s after data true).objects.heap mutableReceiver.view.header mutableReceiver.header = some newData := by
    change currentBuffer (heap s after data true) r.view.header r.header = _
    rw [viewEq,headerEq]
    exact current_buffer s after data true
  have inv := heap_invariants s after data true unique covered live allocations valid
  have allocated : (exported s after data true).objects.heap.allocation s.objects.heap.allocations.length =
      some ⟨newData,fun _ => 0⟩ := by
    change (Proofs.CppMoveAppendOwned.appended s.objects.heap (payload data) s.scope true).allocation s.objects.heap.allocations.length = _
    rw [Proofs.CppMoveAppendOwned.allocation_lookup,ite_eq_left rfl]
  have readable : Proofs.CppMoveHeaders.readable (exported s after data true).objects.heap mutableReceiver.header i32.valid = true := by
    change Proofs.CppMoveHeaders.readable (exported s after data true).objects.heap r.header i32.valid = true
    rw [headerEq]
    simp only [Proofs.CppMoveHeaders.readable,allocated,decide_eq_true_eq]
    exact ⟨rfl,rfl,payload_valid data valid⟩
  have oldScopes := headers_of_contexts s.objects i32 s.scope unique covered live contexts
  have newScopes : HeaderScopes (exported s after data true).objects.heap s.scope :=
    appended_scopes s.objects.heap (payload data) s.scope s.scope true oldScopes (Nat.le_refl _)
  have nextContexts := contexts_of_headers (exported s after data true).objects i32 s.scope newScopes
  refine ⟨⟨mutableReceiver,newData,current,rank,?_,?_,?_,readable,inv.1,inv.2.1,inv.2.2.2,?_,?_,?_⟩,
    rfl,rfl,valueC,valueS⟩
  · change Proofs.UfClassInvariant.Valid data.items r.counter.value rank
    rw [valueC]
    exact math
  · change r.size.value = (data.items.length : Int)
    exact valueS.trans size
  · change r.counter.address ≠ r.size.address
    rw [addrC,addrS]
    omega
  · change r.header.limit = _
    rw [headerEq]
    exact limit
  · have slots := Proofs.UfObjectConstructionPreserve.exported_slots s after 0
      (Proofs.UfCopyContext.layout (project s i32) data count n true)
    change (exported s after data true).slots = _ at slots
    simp only [Proofs.CppMoveReceiverLayout.receiverPrefix,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil] at baseline ⊢
    rw [slots]
    simp only [scalarLocations,List.length_append,List.length_cons,List.length_nil,List.length_map,List.length_range]
    have scalarFacts := scalar_metadata s data count n true
    rw [scalarFacts.2.2,scalarFacts.1]
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  · intro owner sc found
    exact nextContexts owner sc found

end Proofs.UfCopyNewState
