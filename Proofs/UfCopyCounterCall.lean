import Proofs.UfCopyReadReady
import Proofs.UfPublicSource

namespace Proofs.UfCopyCounterCall
open Proofs.UfCopyContext Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.CppMoveReadReceiver Proofs.CppMoveFrame Proofs.CppMoveHeaders
open Proofs.CppMoveSpace Proofs.DoublingNested Proofs.CppMoveCallBindings Proofs.CppVector

theorem counter (s : Context) (object : ObjectRef) (source : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap source.view.header source.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap source.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : source.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope)
    (w : Bool) :
    let after := state (project s i32) data source.counter.value source.size.value w
    let copiedContext := exported s after data w
    let copiedObject := reference (project s i32) 2
    copy s object w = some (copiedContext,copiedObject) ∧
      ∃ (r : ReadReceiver copiedContext copiedObject i32) (fuel : Nat) (out : Context),
        r.counter.value = source.counter.value ∧ r.size.value = source.size.value ∧
        Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_2_callFuel
          fuel copiedContext copiedObject [] = .finished (out,.scalar source.counter.value) ∧
        work out ≤ work s+data.items.length+14 ∧
        Proofs.UfReadPrepareBudget.Resources copiedContext out 0 ∧
        Proofs.UfReadValues.Preserved copiedContext out copiedObject r := by
  dsimp only
  let after := state (project s i32) data source.counter.value source.size.value w
  let copiedContext := exported s after data w
  let copiedObject := reference (project s i32) 2
  have found := (Proofs.CppMoveViews.resolve_parts s.objects source.viewSlot source.view source.header source.resolved).2.1
  obtain ⟨actual,actualCurrent,entry,dataValid,dataLimit,owner⟩ :=
    Proofs.CppMoveReceiverFrame.current_entry s.objects.heap i32 source.view.header source.header
      found readable unique covered
  have same := Option.some.inj (actualCurrent.symm.trans current)
  subst actual
  obtain ⟨r,valueC,valueS,writableC,writableS,newCurrent,newReadable,newUnique,newCovered,newLive,newValid,newLimit,newBase,newContexts⟩ :=
    Proofs.UfCopyReadReady.ready s data source.counter.value source.size.value w source.counter.valid source.size.valid
      unique covered live valid dataValid (dataLimit.trans limit) baseline contexts
  obtain ⟨buffer,fuel,out,cur,called,cost,resources,keep⟩ :=
    Proofs.UfPublicSource.Readonly.counter_call copiedContext copiedObject r
      newReadable newUnique newCovered newValid newLimit newBase newContexts
  have calledSource : Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_2_callFuel
      fuel copiedContext copiedObject [] = .finished (out,.scalar source.counter.value) := by
    rw [valueC] at called
    exact called
  have copyWork := work_eq s data source.counter.value source.size.value w
  refine ⟨copied s object source data current readable unique covered valid w,r,fuel,out,
    valueC,valueS,calledSource,?_,resources,keep⟩
  change work out ≤ work copiedContext+10 at cost
  change work copiedContext = work s+data.items.length+4 at copyWork
  omega

end Proofs.UfCopyCounterCall
