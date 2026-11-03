import Proofs.UfCopyCounterCall

namespace Proofs.UfCopyReadQueries
open Proofs.UfCopyContext Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.CppMoveReadReceiver Proofs.CppMoveFrame Proofs.CppMoveHeaders
open Proofs.CppMoveSpace Proofs.DoublingNested Proofs.CppMoveCallBindings Proofs.CppVector

theorem size (s : Context) (object : ObjectRef) (source : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap source.view.header source.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap source.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : source.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope)
    (w : Bool)
    (rank : Nat → Nat) (forest : Proofs.UfRootCall.Forest data.items rank)
    (length : data.items.length < 2147483648) (weights : Proofs.UfFieldsSize.Weights data.items)
    (a : Nat) (inside : a < data.items.length)
    (expression : NExpr) (typed : expression.resultType = i32) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (Proofs.CppNestedEval.envOf (project
      (exported s (state (project s i32) data source.counter.value source.size.value w) data w) i32)) = some (a : Int)) :
    let after := state (project s i32) data source.counter.value source.size.value w
    let copiedContext := exported s after data w
    let copiedObject := reference (project s i32) 2
    copy s object w = some (copiedContext,copiedObject) ∧
      ∃ (r : ReadReceiver copiedContext copiedObject i32) (fuel : Nat) (out : Context) (root : Nat) (weight : Int),
        r.counter.value = source.counter.value ∧ r.size.value = source.size.value ∧
        Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_2_callFuel
          fuel copiedContext copiedObject (Proofs.CppMoveReceiverResolve.arguments [(expression,(a : Int))]) = .finished (out,.scalar (-weight)) ∧
        Proofs.UfRootCall.Reach data.items a root ∧ root < data.items.length ∧
        data.items[root]? = some weight ∧ weight < 0 ∧
        (∀ groups, Proofs.UfClassInvariant.Valid data.items groups rank →
          -weight = ((Proofs.UfClassInvariant.component data.items a).length : Int)) ∧
        work out ≤ work s+data.items.length+expression.nodes+16*rank a+53 ∧
        Proofs.UfReadPrepareBudget.Resources copiedContext out expression.nodes ∧
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
  obtain ⟨fuel,out,root,weight,called,reach,insideRoot,rootWeight,negative,meaning,cost,resources,keep⟩ :=
    Proofs.UfPublicSource.Readonly.size_call copiedContext copiedObject r
      {(payload data) with owner := s.objects.heap.allocations.length} newCurrent
      rank forest length weights a inside expression typed scalar denotes
      newReadable newUnique newCovered newValid newLimit newBase newContexts
  have copyWork := work_eq s data source.counter.value source.size.value w
  refine ⟨copied s object source data current readable unique covered valid w,r,fuel,out,root,weight,
    valueC,valueS,called,reach,insideRoot,rootWeight,negative,meaning,?_,resources,keep⟩
  change work out ≤ work copiedContext+expression.nodes+16*rank a+49 at cost
  change work copiedContext = work s+data.items.length+4 at copyWork
  omega


theorem same (s : Context) (object : ObjectRef) (source : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap source.view.header source.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap source.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : source.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope)
    (w : Bool)
    (rank : Nat → Nat) (forest : Proofs.UfRootCall.Forest data.items rank)
    (length : data.items.length < 2147483648)
    (a b : Nat) (ha : a < data.items.length) (hb : b < data.items.length)
    (ea eb : NExpr) (ready : Proofs.CppMoveReceiverResolve.Ready
      (exported s (state (project s i32) data source.counter.value source.size.value w) data w)
      i32 [(ea,(a : Int)),(eb,(b : Int))]) :
    let after := state (project s i32) data source.counter.value source.size.value w
    let copiedContext := exported s after data w
    let copiedObject := reference (project s i32) 2
    copy s object w = some (copiedContext,copiedObject) ∧
      ∃ (r : ReadReceiver copiedContext copiedObject i32) (fuel : Nat) (out : Context) (root1 root2 : Nat),
        r.counter.value = source.counter.value ∧ r.size.value = source.size.value ∧
        Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_2_callFuel
          fuel copiedContext copiedObject (Proofs.CppMoveReceiverResolve.arguments [(ea,(a : Int)),(eb,(b : Int))]) =
            .finished (out,.scalar (if root1=root2 then 1 else 0)) ∧
        Proofs.UfRootCall.Reach data.items a root1 ∧ Proofs.UfRootCall.Reach data.items b root2 ∧
        (root1=root2 ↔ Proofs.UfFieldsSame.Connected data.items a b) ∧
        work out ≤ work s+data.items.length+ea.nodes+eb.nodes+16*rank a+16*rank b+88 ∧
        Proofs.UfReadPrepareBudget.Resources copiedContext out (ea.nodes+eb.nodes) ∧
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
  obtain ⟨fuel,out,root1,root2,called,reach1,reach2,meaning,cost,resources,keep⟩ :=
    Proofs.UfPublicSource.Readonly.same_call copiedContext copiedObject r
      {(payload data) with owner := s.objects.heap.allocations.length} newCurrent
      rank forest length a b ha hb ea eb ready
      newReadable newUnique newCovered newValid newLimit newBase newContexts
  have copyWork := work_eq s data source.counter.value source.size.value w
  refine ⟨copied s object source data current readable unique covered valid w,r,fuel,out,root1,root2,
    valueC,valueS,called,reach1,reach2,meaning,?_,resources,keep⟩
  change work out ≤ work copiedContext+ea.nodes+eb.nodes+16*rank a+16*rank b+84 at cost
  change work copiedContext = work s+data.items.length+4 at copyWork
  omega

theorem size_log (s : Context) (object : ObjectRef) (source : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap source.view.header source.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap source.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : source.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope)
    (w : Bool)
    (rank rho : Nat → Nat)
    (math : Proofs.UfClassInvariant.Valid data.items source.counter.value rank)
    (history : Proofs.UfHistoricalRank.History data.items rho)
    (a : Nat) (inside : a < data.items.length)
    (expression : NExpr) (typed : expression.resultType = i32) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (Proofs.CppNestedEval.envOf (project
      (exported s (state (project s i32) data source.counter.value source.size.value w) data w) i32)) = some (a : Int)) :
    let after := state (project s i32) data source.counter.value source.size.value w
    let copiedContext := exported s after data w
    let copiedObject := reference (project s i32) 2
    copy s object w = some (copiedContext,copiedObject) ∧
      ∃ (r : ReadReceiver copiedContext copiedObject i32) (fuel : Nat) (out : Context) (root : Nat) (weight : Int),
        r.counter.value = source.counter.value ∧ r.size.value = source.size.value ∧
        Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_2_callFuel
          fuel copiedContext copiedObject (Proofs.CppMoveReceiverResolve.arguments [(expression,(a : Int))]) = .finished (out,.scalar (-weight)) ∧
        Proofs.UfRootCall.Reach data.items a root ∧ root < data.items.length ∧
        data.items[root]? = some weight ∧ weight < 0 ∧
        -weight = ((Proofs.UfClassInvariant.component data.items a).length : Int) ∧
        work out ≤ work s+data.items.length+expression.nodes+16*Nat.log2 data.items.length+53 ∧
        Proofs.UfReadPrepareBudget.Resources copiedContext out expression.nodes ∧
        Proofs.UfReadValues.Preserved copiedContext out copiedObject r := by
  dsimp only
  have forest := Proofs.UfPublicSource.Historical.descent_forest data.items source.counter.value rank rho math history
  have descended : Proofs.UfClassInvariant.Valid data.items source.counter.value
      (Proofs.UfPublicSource.Historical.descent data.items rho) :=
    ⟨forest,math.length,math.sizes,math.count⟩
  obtain ⟨copied,r,fuel,out,root,weight,valueC,valueS,called,reach,insideRoot,found,negative,meaning,cost,resources,keep⟩ :=
    size s object source data current readable unique covered live valid limit baseline contexts w
      _ forest math.length math.weights a inside expression typed scalar denotes
  have upper := Proofs.UfPublicSource.Historical.descent_bound data.items rho a
  refine ⟨copied,r,fuel,out,root,weight,valueC,valueS,called,reach,insideRoot,found,negative,
    meaning source.counter.value descended,?_,resources,keep⟩
  omega

theorem same_log (s : Context) (object : ObjectRef) (source : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap source.view.header source.header = some data)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap source.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : source.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (Proofs.CppMoveReceiverLayout.receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope)
    (w : Bool)
    (rank rho : Nat → Nat)
    (math : Proofs.UfClassInvariant.Valid data.items source.counter.value rank)
    (history : Proofs.UfHistoricalRank.History data.items rho)
    (a b : Nat) (ha : a < data.items.length) (hb : b < data.items.length)
    (ea eb : NExpr) (ready : Proofs.CppMoveReceiverResolve.Ready
      (exported s (state (project s i32) data source.counter.value source.size.value w) data w)
      i32 [(ea,(a : Int)),(eb,(b : Int))]) :
    let after := state (project s i32) data source.counter.value source.size.value w
    let copiedContext := exported s after data w
    let copiedObject := reference (project s i32) 2
    copy s object w = some (copiedContext,copiedObject) ∧
      ∃ (r : ReadReceiver copiedContext copiedObject i32) (fuel : Nat) (out : Context) (root1 root2 : Nat),
        r.counter.value = source.counter.value ∧ r.size.value = source.size.value ∧
        Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_2_callFuel
          fuel copiedContext copiedObject (Proofs.CppMoveReceiverResolve.arguments [(ea,(a : Int)),(eb,(b : Int))]) =
            .finished (out,.scalar (if root1=root2 then 1 else 0)) ∧
        Proofs.UfRootCall.Reach data.items a root1 ∧ Proofs.UfRootCall.Reach data.items b root2 ∧
        (root1=root2 ↔ Proofs.UfFieldsSame.Connected data.items a b) ∧
        work out ≤ work s+data.items.length+ea.nodes+eb.nodes+32*Nat.log2 data.items.length+88 ∧
        Proofs.UfReadPrepareBudget.Resources copiedContext out (ea.nodes+eb.nodes) ∧
        Proofs.UfReadValues.Preserved copiedContext out copiedObject r := by
  dsimp only
  have forest := Proofs.UfPublicSource.Historical.descent_forest data.items source.counter.value rank rho math history
  obtain ⟨copied,r,fuel,out,root1,root2,valueC,valueS,called,reach1,reach2,meaning,cost,resources,keep⟩ :=
    same s object source data current readable unique covered live valid limit baseline contexts w
      _ forest math.length a b ha hb ea eb ready
  have upperA := Proofs.UfPublicSource.Historical.descent_bound data.items rho a
  have upperB := Proofs.UfPublicSource.Historical.descent_bound data.items rho b
  refine ⟨copied,r,fuel,out,root1,root2,valueC,valueS,called,reach1,reach2,meaning,?_,resources,keep⟩
  omega

end Proofs.UfCopyReadQueries
