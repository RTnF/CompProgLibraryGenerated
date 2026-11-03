import Proofs.UfCopyContext
import Proofs.CppMoveFrameScopes

namespace Proofs.UfCopyReadReady
open Proofs.UfCopyContext Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.CppMoveReadReceiver Proofs.CppMoveFrame Proofs.CppMoveHeaders
open Proofs.CppMoveSpace Proofs.CppMoveFrameScopes Proofs.DoublingNested Proofs.CppVector

theorem ready (s : Context) (data : Buffer Int) (count n : Int) (w : Bool)
    (cv : i32.valid count = true) (nv : i32.valid n = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (valid : data.Valid i32.valid) (limit : data.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    let after := state (project s i32) data count n w
    let out := exported s after data w
    ∃ r : ReadReceiver out (reference (project s i32) 2) i32,
      r.counter.value = count ∧ r.size.value = n ∧
      r.counter.writable = w ∧ r.size.writable = w ∧
      currentBuffer out.objects.heap r.view.header r.header =
        some {(payload data) with owner := s.objects.heap.allocations.length} ∧
      Proofs.CppMoveHeaders.readable out.objects.heap r.header i32.valid = true ∧
      Unique out.objects.heap ∧ OwnsAll out.objects.heap ∧ HeadersLive out.objects.heap ∧
      AllocationsValid out.objects.heap i32 ∧
      r.header.limit = Proofs.CppVectorBindings.sizeLimit i32 ∧
      out.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix out).length ∧
      (∀ owner sc, (project out i32).frame.state.forest.context owner = some sc → sc ≤ out.scope) := by
  dsimp only
  let after := state (project s i32) data count n w
  let out := exported s after data w
  obtain ⟨r,addrC,addrS,valueC,valueS,writableC,writableS,headerEq,viewEq⟩ := receiver s data count n w cv nv
  have current : currentBuffer out.objects.heap r.view.header r.header =
      some {(payload data) with owner := s.objects.heap.allocations.length} := by
    rw [viewEq,headerEq]
    exact current_buffer s after data w
  have allocated : out.objects.heap.allocation s.objects.heap.allocations.length =
      some ⟨{(payload data) with owner := s.objects.heap.allocations.length},fun _ => 0⟩ := by
    change (Proofs.CppMoveAppendOwned.appended s.objects.heap (payload data) s.scope w).allocation s.objects.heap.allocations.length = _
    rw [Proofs.CppMoveAppendOwned.allocation_lookup,ite_eq_left rfl]
  have readable : Proofs.CppMoveHeaders.readable out.objects.heap r.header i32.valid = true := by
    rw [headerEq]
    simp only [Proofs.CppMoveHeaders.readable,allocated,decide_eq_true_eq]
    exact ⟨True.intro,rfl,payload_valid data valid⟩
  have inv := heap_invariants s after data w unique covered live allocations valid
  have oldScopes := headers_of_contexts s.objects i32 s.scope unique covered live contexts
  have newScopes : HeaderScopes out.objects.heap s.scope :=
    appended_scopes s.objects.heap (payload data) s.scope s.scope w oldScopes (Nat.le_refl _)
  have nextContexts := contexts_of_headers out.objects i32 s.scope newScopes
  refine ⟨r,valueC,valueS,writableC,writableS,current,readable,inv.1,inv.2.1,inv.2.2.1,inv.2.2.2,?_,?_,?_⟩
  · rw [headerEq]
    exact limit
  · have slots := Proofs.UfObjectConstructionPreserve.exported_slots s after 0
      (Proofs.UfCopyContext.layout (project s i32) data count n w)
    change out.slots = _ at slots
    simp only [Proofs.CppMoveReceiverLayout.receiverPrefix,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil] at baseline ⊢
    rw [slots]
    simp only [scalarLocations,List.length_append,List.length_cons,List.length_nil,List.length_map,List.length_range]
    have scalarFacts := scalar_metadata s data count n w
    rw [scalarFacts.2.2,scalarFacts.1]
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  · intro owner sc found
    exact nextContexts owner sc found

end Proofs.UfCopyReadReady
