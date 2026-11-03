import Proofs.UfObjectInitialAmortized
import Proofs.UfObjectConstructionExport
import Proofs.CppConstructorLayout
import Proofs.CppMoveFrameScopes
import Proofs.UfObjectConstructionContext
import Proofs.UfConstructionWork

namespace Proofs.UfObjectConstructedState
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.DoublingNested
open Proofs.UfObjectState Proofs.UfObjectConstructionExport Proofs.CppMoveFrame
open Proofs.CppMoveHeaders Proofs.CppMoveSpace Proofs.CppRootModel
open Proofs.UfObjectConstructionContext Proofs.CppMoveFrameScopes

theorem initialized_state (s : Context) (after : NState) (n : Nat) (small : n < 2147483648)
    (initialized : Proofs.UfConstructionExport.Initialized (project s i32) after (List.replicate n (-1)) n n)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (reference (project s i32) 2))
    (unique : Proofs.CppMoveHeaders.Unique s.objects.heap) (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ state : State (exported s after n) (reference (project s i32) 2),
      state.data.items = List.replicate n (-1) ∧ Proofs.CppMoveSpace.HeadersLive (exported s after n).objects.heap := by
  obtain ⟨r,addressC,addressS,valueC,valueS,headerEq,viewEq⟩ :=
    Proofs.UfObjectConstructionContext.receiver s after n initialized layout
  let data : Proofs.CppVector.Buffer Int := {payload n with owner := s.objects.heap.allocations.length}
  have current : currentBuffer (exported s after n).objects.heap r.view.header r.header = some data := by
    rw [viewEq,headerEq]
    exact current_buffer s after n
  have inv := heap_invariants s after n small unique covered live allocations
  have validData : data.Valid i32.valid := payload_valid n small
  have allocated : (exported s after n).objects.heap.allocation s.objects.heap.allocations.length =
      some ⟨data,fun _ => 0⟩ := by
    change (Proofs.CppMoveAppendOwned.appended s.objects.heap (payload n) s.scope true).allocation s.objects.heap.allocations.length = _
    rw [Proofs.CppMoveAppendOwned.allocation_lookup,ite_eq_left rfl]
  have readable : Proofs.CppMoveHeaders.readable (exported s after n).objects.heap r.header i32.valid = true := by
    rw [headerEq]
    simp only [Proofs.CppMoveHeaders.readable,allocated,decide_eq_true_eq]
    exact ⟨rfl,rfl,validData⟩
  have oldHeaders := headers_of_contexts s.objects i32 s.scope unique covered live contexts
  have newHeaders : HeaderScopes (exported s after n).objects.heap s.scope :=
    appended_scopes s.objects.heap (payload n) s.scope s.scope true oldHeaders (Nat.le_refl _)
  have newContexts := contexts_of_headers (exported s after n).objects i32 s.scope newHeaders
  obtain ⟨oldCells,values,oldLength,oldTypes,memory,bindings,slots,scope,scalarBase,objectEq⟩ := layout
  have afterBase : after.scalars.baseMemory = s.scalars.baseMemory := scalarBase
  have length := congrArg List.length initialized.2.1
  simp only [List.length_append,List.length_cons,List.length_nil] at length
  change after.scalars.memory.length = s.scalars.memory.length+2 at length
  refine ⟨⟨r,data,current,(fun _ => 0),?_,?_,?_,readable,inv.1,inv.2.1,inv.2.2.2,?_,?_,?_⟩,rfl,inv.2.2.1⟩
  · rw [valueC]
    exact Proofs.UfClassInvariant.initial_valid n small
  · rw [valueS]
    simp [data,payload]
  · rw [addressC,addressS]
    omega
  · rw [headerEq]
  · simp only [Proofs.CppMoveReceiverLayout.receiverPrefix,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
    change after.scalars.baseMemory ≤ after.scalars.memory.length+(exported s after n).slots.length+1
    omega
  · intro owner sc found
    have bound := newContexts owner sc found
    change sc ≤ after.scope
    rw [scope]
    exact bound

theorem construct_sized_resources (s : Context) (heap : Proofs.CppRootModel.Heap)
    (valid : (project s i32).frame.state.wellFormed = true)
    (models : HeapModels (project s i32).frame.state heap)
    (lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length)
    (strict : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ (project s i32).scope)
    (base : (project s i32).scalars.baseMemory ≤ (project s i32).scalars.memory.length)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (n : Int))
    (ops : List Proofs.UfObjectTrace.Operation) (ready : ∀ op ∈ ops, op.Valid n) :
    ∃ (after : NState) (script : List (Nat × Proofs.UfObjectTrace.Operation)) (out : Context) (results : List Ret)
      (initial : State (exported s after n) (Proofs.CppConstructorFinish.reference (project s i32) 2)) (next : State out (Proofs.CppConstructorFinish.reference (project s i32) 2)) (nextRho : Nat → Nat),
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 (project s i32) [.value en]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (after,(Proofs.CppConstructorFinish.reference (project s i32) 2)) ∧
      initial.data.items = List.replicate n (-1) ∧ script.map Prod.snd = ops ∧
      Proofs.UfObjectTrace.run (exported s after n) (Proofs.CppConstructorFinish.reference (project s i32) 2) script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = initial.receiver.size.value ∧
      Proofs.UfObjectTrace.History (Proofs.CppConstructorFinish.reference (project s i32) 2) (exported s after n) initial ops out results next ∧
      Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out ≤ work s+en.nodes+n+30+718*ops.length*(Proofs.UfPotential.alpha n+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget (exported s after n) ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget (exported s after n) ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget (exported s after n) := by
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,allocationValid⟩ :=
    Proofs.UfObjectConstructionExport.sized_export s heap valid models lengths strict base unique covered live allocations en n small scalar type value
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8 (project s i32) after [.value en]
    (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) (Proofs.CppConstructorFinish.reference (project s i32) 2) rfl ran
  obtain ⟨initial,items,liveAfter⟩ := initialized_state s after n small initialized layout unique covered live allocations base strict
  obtain ⟨script,out,results,next,nextRho,mapped,called,count,size,history,mathNext,bound,scalarPeak,heapPeak,totalPeak⟩ :=
    Proofs.UfObjectInitialAmortized.initialized_resources (exported s after n) (Proofs.CppConstructorFinish.reference (project s i32) 2) initial liveAfter n items ops ready
  obtain ⟨other,otherRun,strong,constructionWork⟩ := Proofs.UfConstructionWork.construct_sized_work (project s i32) heap valid models lengths strict base en n small scalar type value
  have same : other = after := congrArg Prod.fst (Proofs.CppLoop.Outcome.finished.inj (otherRun.symm.trans ran))
  subst other
  change after.work ≤ work s+en.nodes+n+30 at constructionWork
  change work out ≤ after.work+718*ops.length*(Proofs.UfPotential.alpha n+1) at bound
  exact ⟨after,script,out,results,initial,next,nextRho,ran,items,mapped,called,count,size,history,mathNext,
    bound.trans (Nat.add_le_add_right constructionWork _),scalarPeak,heapPeak,totalPeak⟩

theorem construct_default_resources (s : Context) (heap : Proofs.CppRootModel.Heap)
    (valid : (project s i32).frame.state.wellFormed = true)
    (models : HeapModels (project s i32).frame.state heap)
    (lengths : (project s i32).frame.rootWritable.length = (project s i32).frame.state.forest.objects.length)
    (strict : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ (project s i32).scope)
    (base : (project s i32).scalars.baseMemory ≤ (project s i32).scalars.memory.length)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (live : HeadersLive s.objects.heap) (allocations : AllocationsValid s.objects.heap i32)
    (ops : List Proofs.UfObjectTrace.Operation) (ready : ∀ op ∈ ops, op.Valid 0) :
    ∃ (after : NState) (script : List (Nat × Proofs.UfObjectTrace.Operation)) (out : Context) (results : List Ret)
      (initial : State (exported s after 0) (Proofs.CppConstructorFinish.reference (project s i32) 2)) (next : State out (Proofs.CppConstructorFinish.reference (project s i32) 2)) (nextRho : Nat → Nat),
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 (project s i32) []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (after,(Proofs.CppConstructorFinish.reference (project s i32) 2)) ∧
      initial.data.items = List.replicate 0 (-1) ∧ script.map Prod.snd = ops ∧
      Proofs.UfObjectTrace.run (exported s after 0) (Proofs.CppConstructorFinish.reference (project s i32) 2) script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = initial.receiver.size.value ∧
      Proofs.UfObjectTrace.History (Proofs.CppConstructorFinish.reference (project s i32) 2) (exported s after 0) initial ops out results next ∧
      Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out ≤ work s+12+718*ops.length*(Proofs.UfPotential.alpha 0+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget (exported s after 0) ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget (exported s after 0) ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget (exported s after 0) := by
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,allocationValid⟩ :=
    Proofs.UfObjectConstructionExport.default_export s heap valid models lengths strict base unique covered live allocations
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct0 8 (project s i32) after []
    (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) (Proofs.CppConstructorFinish.reference (project s i32) 2) rfl ran
  obtain ⟨initial,items,liveAfter⟩ := initialized_state s after 0 (by decide +kernel) initialized layout unique covered live allocations base strict
  obtain ⟨script,out,results,next,nextRho,mapped,called,count,size,history,mathNext,bound,scalarPeak,heapPeak,totalPeak⟩ :=
    Proofs.UfObjectInitialAmortized.initialized_resources (exported s after 0) (Proofs.CppConstructorFinish.reference (project s i32) 2) initial liveAfter 0 items ops ready
  obtain ⟨other,otherRun,strong,constructionWork⟩ := Proofs.UfConstructionWork.construct_default_work (project s i32) heap valid models lengths strict base
  have same : other = after := congrArg Prod.fst (Proofs.CppLoop.Outcome.finished.inj (otherRun.symm.trans ran))
  subst other
  change after.work ≤ work s+12 at constructionWork
  change work out ≤ after.work+718*ops.length*(Proofs.UfPotential.alpha 0+1) at bound
  exact ⟨after,script,out,results,initial,next,nextRho,ran,items,mapped,called,count,size,history,mathNext,
    bound.trans (Nat.add_le_add_right constructionWork _),scalarPeak,heapPeak,totalPeak⟩

end Proofs.UfObjectConstructedState
