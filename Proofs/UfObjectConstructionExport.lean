import Proofs.CppMoveAppendOwned
import Proofs.CppMoveContext
import Proofs.UfConstructedReceiver

namespace Proofs.UfObjectConstructionExport
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveSpace
open Proofs.UfConstructionExport Proofs.DoublingNested Proofs.CppRootModel

-- Payload already produced by the audited sized/default source constructor.
def payload (n : Nat) : Proofs.CppVector.Buffer Int :=
  ⟨0,List.replicate n (-1),n,Proofs.CppVectorBindings.sizeLimit i32,0⟩

def exportedHeap (s : Context) (after : NState) (n : Nat) : Proofs.CppMoveHeaders.Heap Int :=
  {Proofs.CppMoveAppendOwned.appended s.objects.heap (payload n) s.scope true with
    work := after.frame.state.storage.work,
    peak := after.frame.state.storage.peak,
    baseSpace := after.frame.state.storage.baseSpace}

theorem payload_valid (n : Nat) (small : n < 2147483648) : (payload n).Valid i32.valid := by
  refine ⟨by simp [payload],Proofs.UfConstructionStage.nat_limit n small,?_⟩
  have negative : i32.valid (-1) = true := by decide +kernel
  simp [payload,negative]

theorem heap_invariants (s : Context) (after : NState) (n : Nat) (small : n < 2147483648)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (valid : AllocationsValid s.objects.heap i32) :
    Unique (exportedHeap s after n) ∧ OwnsAll (exportedHeap s after n) ∧
      HeadersLive (exportedHeap s after n) ∧ AllocationsValid (exportedHeap s after n) i32 := by
  exact ⟨Proofs.CppMoveAppendOwned.appended_unique s.objects.heap (payload n) s.scope true unique live,
    Proofs.CppMoveAppendOwned.appended_ownsAll s.objects.heap (payload n) s.scope true covered,
    Proofs.CppMoveAppendOwned.appended_headersLive s.objects.heap (payload n) s.scope true live,
    Proofs.CppMoveAppendOwned.appended_valid s.objects.heap (payload n) s.scope true i32 valid (payload_valid n small)⟩

theorem current_buffer (s : Context) (after : NState) (n : Nat) :
    currentBuffer (exportedHeap s after n) s.objects.heap.headers.length
      ⟨some s.objects.heap.allocations.length,s.scope,true,Proofs.CppVectorBindings.sizeLimit i32⟩ =
      some {(payload n) with owner := s.objects.heap.allocations.length} :=
  Proofs.CppMoveAppendOwned.current_buffer s.objects.heap (payload n) s.scope true

theorem sized_export (s : Context) (heap : Proofs.CppRootModel.Heap)
    (valid : (project s i32).frame.state.wellFormed = true)
    (models : HeapModels (project s i32).frame.state heap)
    (lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length)
    (strict : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ (project s i32).scope)
    (base : (project s i32).scalars.baseMemory ≤ (project s i32).scalars.memory.length)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (n : Int)) :
    ∃ after : NState,
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 (project s i32) [.value en]
        (vectorField true) (.integer i32) (fields true) = .finished (after,Proofs.CppConstructorFinish.reference (project s i32) 2) ∧
      Initialized (project s i32) after (List.replicate n (-1)) n n ∧
      Proofs.CppFrameExtension.Extends (project s i32).frame after.frame ∧
      (∀ ref v, (project s i32).frame.read ref = some v → after.frame.read ref = some v) ∧
      after.frame.state.storage.lookup (project s i32).frame.state.storage.objects.length =
        some {(box (payload n)) with owner := (project s i32).frame.state.storage.objects.length} ∧
      currentBuffer (exportedHeap s after n) s.objects.heap.headers.length
        ⟨some s.objects.heap.allocations.length,s.scope,true,Proofs.CppVectorBindings.sizeLimit i32⟩ =
        some {(payload n) with owner := s.objects.heap.allocations.length} ∧
      Unique (exportedHeap s after n) ∧ OwnsAll (exportedHeap s after n) ∧
      HeadersLive (exportedHeap s after n) ∧ AllocationsValid (exportedHeap s after n) i32 := by
  obtain ⟨after,ran,initialized,ready,math⟩ :=
    Proofs.UfConstructedReceiver.sized_ready (project s i32) heap valid models lengths strict base en n small scalar type value
  obtain ⟨other,otherRun,otherInitialized,extension,reads⟩ :=
    Proofs.UfConstructionReferences.construct_sized (project s i32) heap valid models lengths
      (Proofs.UfConstructionReferences.oldScopes_of_bound (project s i32) strict) en n small scalar type value
  have same : after = other := (Prod.mk.inj (Proofs.CppLoop.Outcome.finished.inj (ran.symm.trans otherRun))).1
  subst other
  refine ⟨after,ran,initialized,extension,reads,?_,current_buffer s after n,heap_invariants s after n small unique covered live allocations⟩
  simpa [Proofs.UfConstructedReceiver.buffer,box,payload] using ready.vfound

theorem default_export (s : Context) (heap : Proofs.CppRootModel.Heap)
    (valid : (project s i32).frame.state.wellFormed = true)
    (models : HeapModels (project s i32).frame.state heap)
    (lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length)
    (strict : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ (project s i32).scope)
    (base : (project s i32).scalars.baseMemory ≤ (project s i32).scalars.memory.length)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (allocations : AllocationsValid s.objects.heap i32) :
    ∃ after : NState,
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 (project s i32) []
        (vectorField false) (.integer i32) (fields false) = .finished (after,Proofs.CppConstructorFinish.reference (project s i32) 2) ∧
      Initialized (project s i32) after [] 0 0 ∧
      Proofs.CppFrameExtension.Extends (project s i32).frame after.frame ∧
      (∀ ref v, (project s i32).frame.read ref = some v → after.frame.read ref = some v) ∧
      after.frame.state.storage.lookup (project s i32).frame.state.storage.objects.length =
        some {(box (payload 0)) with owner := (project s i32).frame.state.storage.objects.length} ∧
      currentBuffer (exportedHeap s after 0) s.objects.heap.headers.length
        ⟨some s.objects.heap.allocations.length,s.scope,true,Proofs.CppVectorBindings.sizeLimit i32⟩ =
        some {(payload 0) with owner := s.objects.heap.allocations.length} ∧
      Unique (exportedHeap s after 0) ∧ OwnsAll (exportedHeap s after 0) ∧
      HeadersLive (exportedHeap s after 0) ∧ AllocationsValid (exportedHeap s after 0) i32 := by
  obtain ⟨after,ran,initialized,ready,math⟩ :=
    Proofs.UfConstructedReceiver.default_ready (project s i32) heap valid models lengths strict base
  obtain ⟨other,otherRun,otherInitialized,extension,reads⟩ :=
    Proofs.UfConstructionReferences.construct_default (project s i32) heap valid models lengths
      (Proofs.UfConstructionReferences.oldScopes_of_bound (project s i32) strict)
  have same : after = other := (Prod.mk.inj (Proofs.CppLoop.Outcome.finished.inj (ran.symm.trans otherRun))).1
  subst other
  refine ⟨after,ran,initialized,extension,reads,?_,current_buffer s after 0,heap_invariants s after 0 (by decide) unique covered live allocations⟩
  simpa [Proofs.UfConstructedReceiver.buffer,box,payload] using ready.vfound

theorem exported_counters (s : Context) (after : NState) (n : Nat) :
    (exportedHeap s after n).work = after.frame.state.storage.work ∧
    (exportedHeap s after n).peak = after.frame.state.storage.peak ∧
    (exportedHeap s after n).baseSpace = after.frame.state.storage.baseSpace := ⟨rfl,rfl,rfl⟩

theorem old_read (s : Context) (after : NState) (n : Nat) (id : Nat) (grant : Proofs.CppMoveHeaders.Grant)
    (found : s.objects.heap.grants[id]? = some grant)
    (inside : grant.reference.element.owner < s.objects.heap.allocations.length) :
    Proofs.CppMoveHeaders.read (exportedHeap s after n) i32.valid id =
      Proofs.CppMoveHeaders.read s.objects.heap i32.valid id :=
  Proofs.CppMoveAppendOwned.old_read s.objects.heap (payload n) s.scope true i32.valid id grant found inside

theorem liveSpace (s : Context) (after : NState) (n : Nat) :
    (exportedHeap s after n).liveSpace = s.objects.heap.liveSpace+1+n :=
  Proofs.CppMoveAppendOwned.liveSpace s.objects.heap (payload n) s.scope true

end Proofs.UfObjectConstructionExport
