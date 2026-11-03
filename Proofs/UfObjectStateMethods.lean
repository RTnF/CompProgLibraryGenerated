import Proofs.UfObjectState

namespace Proofs.UfObjectStateMethods
open Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppMoveObjectReceiver
open Proofs.CppMoveCallLayout Proofs.CppMoveCallPayload Proofs.CppMoveFrame
open Proofs.CppScalar Proofs.CppVector Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppConstructorFinish Proofs.CppMoveReceiverLayout Proofs.CppNestedVectorStore
open Proofs.CppMoveCallBindings Proofs.VecExpr Proofs.VecWrite Proofs.UfObjectCall
open Proofs.UfCompactRootBody Proofs.UfCompactUniteBody
open Proofs.UfRootCall Proofs.UfClassInvariant Proofs.UfCompression Proofs.DoublingNested

theorem updated_counter (memory : List Proofs.CppState.Cell) (address : Nat) (groups : Int) (r1 r2 : Nat)
    (found : memory[address]? = some ⟨i32,groups⟩) :
    (Proofs.UfFieldsUnite.updatedMemory memory address groups r1 r2)[address]? =
      some ⟨i32,Proofs.UfFieldsUnite.countAfter groups r1 r2⟩ := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  by_cases same : r1=r2
  · simpa only [Proofs.UfFieldsUnite.updatedMemory,Proofs.UfFieldsUnite.countAfter,ite_eq_left same] using found
  · simpa only [Proofs.UfFieldsUnite.updatedMemory,Proofs.UfFieldsUnite.countAfter,ite_eq_right same] using
      (List.getElem?_set_self (l := memory) (i := address) (a := (⟨i32,groups-1⟩ : Proofs.CppState.Cell)) inside)

theorem same_step (s : Context) (object : ObjectRef) (state : State s object)
    (a : Nat) (ha : a < state.data.items.length) (b : Nat) (hb : b < state.data.items.length)
    (expressionA : NExpr) (typedA : expressionA.resultType = i32) (scalarA : expressionA.scalarOnly = true)
    (denotesA : expressionA.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (expressionB : NExpr) (typedB : expressionB.resultType = i32) (scalarB : expressionB.scalarOnly = true)
    (denotesB : expressionB.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (b : Int)) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat) (out : Context) (r1 r2 : Nat) (middle final : List Int),
      (prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_same.parameters
        (arguments s object state.receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc state.data.items (box state.data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_same fuel s i32 (arguments s object state.receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = .finished (out,.scalar (if r1=r2 then 1 else 0)) ∧
      Compressed state.data.items middle a r1 ∧ Compressed middle final b r2 ∧ Forest final state.rank ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected state.data.items a b) ∧
      work out ≤ work prepared+91*state.rank a+91*state.rank b+181 ∧
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
  obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,final,post⟩ :=
    Proofs.UfObjectMethods.same_call s object state.receiver state.data state.current state.size state.rank state.math.forest state.math.length a ha b hb
      expressionA typedA scalarA denotesA expressionB typedB scalarB denotesB
      state.readable state.unique state.covered state.allocations state.limit state.baseline state.contexts
  have complete := post
  obtain ⟨prep,compacted,fw,actual,c1,c2,forest,connected,cost,memory,scalarPeak,heapPeak,peak,buffer,lookup,items⟩ := post
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
  have next := transition s out object state Proofs.UnionFindCandidateInstance.UnionFind_same fuel
    (Proofs.UfObjectCall.arguments s object state.receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) (.scalar (if r1=r2 then 1 else 0)) actual
    state.receiver.counter.value state.receiver.counter.valid counter sizeCell final state.rank
    ((state.math.compressed c1).compressed c2) (c2.length.trans c1.length) buffer lookupOwner items
  exact ⟨prepared,initial,vc,fuel,out,r1,r2,middle,final,complete,next⟩

theorem size_step (s : Context) (object : ObjectRef) (state : State s object)
    (a : Nat) (ha : a < state.data.items.length)
    (expressionA : NExpr) (typedA : expressionA.resultType = i32) (scalarA : expressionA.scalarOnly = true)
    (denotesA : expressionA.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int)) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat) (out : Context) (root : Nat) (weight : Int) (final : List Int),
      (prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_size.parameters
        (arguments s object state.receiver [(expressionA,(a : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc state.data.items (box state.data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_size fuel s i32 (arguments s object state.receiver [(expressionA,(a : Int))]) = .finished (out,.scalar (-weight)) ∧
      state.data.items[root]? = some weight ∧ weight < 0 ∧
      Compressed state.data.items final a root ∧ Forest final state.rank ∧ Proofs.UfFieldsSize.Weights final ∧
      (∀ groups, Proofs.UfClassInvariant.Valid state.data.items groups state.rank →
        -weight = ((Proofs.UfClassInvariant.component state.data.items a).length : Int) ∧ Proofs.UfClassInvariant.Valid final groups state.rank) ∧
      work out ≤ work prepared+91*state.rank a+101 ∧
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
  obtain ⟨prepared,initial,vc,fuel,out,root,weight,final,post⟩ :=
    Proofs.UfObjectMethods.size_call s object state.receiver state.data state.current state.size state.rank state.math.forest state.math.length state.math.weights a ha
      expressionA typedA scalarA denotesA
      state.readable state.unique state.covered state.allocations state.limit state.baseline state.contexts
  have complete := post
  obtain ⟨prep,compacted,fw,actual,atRoot,negative,compressed,forest,weights,meaning,cost,memory,scalarPeak,heapPeak,peak,buffer,lookup,items⟩ := post
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
  have next := transition s out object state Proofs.UnionFindCandidateInstance.UnionFind_size fuel
    (Proofs.UfObjectCall.arguments s object state.receiver [(expressionA,(a : Int))]) (.scalar (-weight)) actual
    state.receiver.counter.value state.receiver.counter.valid counter sizeCell final state.rank
    (state.math.compressed compressed) compressed.length buffer lookupOwner items
  exact ⟨prepared,initial,vc,fuel,out,root,weight,final,complete,next⟩

theorem unite_step (s : Context) (object : ObjectRef) (state : State s object)
    (a : Nat) (ha : a < state.data.items.length) (b : Nat) (hb : b < state.data.items.length)
    (expressionA : NExpr) (typedA : expressionA.resultType = i32) (scalarA : expressionA.scalarOnly = true)
    (denotesA : expressionA.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (expressionB : NExpr) (typedB : expressionB.resultType = i32) (scalarB : expressionB.scalarOnly = true)
    (denotesB : expressionB.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (b : Int)) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat) (out : Context) (r1 r2 : Nat) (middle two final : List Int),
      (prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters
        (arguments s object state.receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc state.data.items (box state.data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite fuel s i32 (arguments s object state.receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = .finished (out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧
      Compressed state.data.items middle a r1 ∧ Compressed middle two b r2 ∧
      final = Proofs.UfUniteCall.uniteVec two r1 r2 ∧
      (∃ rank', Proofs.UfClassInvariant.Valid final (Proofs.UfFieldsUnite.countAfter state.receiver.counter.value r1 r2) rank') ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected state.data.items a b) ∧
      work out ≤ work prepared+91*state.rank a+91*state.rank b+343 ∧
      out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory s.scalars.memory state.receiver.counter.address state.receiver.counter.value r1 r2 ∧
      out.scalars.peak ≤ max (max s.scalars.peak (uniteScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max s.peak (uniteScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max s.scalars.peak (uniteScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
          (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer) ∧ ∃ next : State out object, next.receiver.counter.value = (Proofs.UfFieldsUnite.countAfter state.receiver.counter.value r1 r2) ∧
        next.receiver.size.value = state.receiver.size.value ∧ next.data.items = final := by
  obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,post⟩ :=
    Proofs.UfObjectMethods.unite_call s object state.receiver state.data state.current state.size state.rank state.math a ha b hb
      expressionA typedA scalarA denotesA expressionB typedB scalarB denotesB
      state.readable state.unique state.covered state.allocations state.limit state.baseline state.contexts
  have complete := post
  obtain ⟨prep,compacted,fw,actual,c1,c2,finalEq,newValid,connected,cost,memory,scalarPeak,heapPeak,peak,buffer,lookup,items⟩ := post
  obtain ⟨nextRank,nextMath⟩ := newValid
  let count := Proofs.UfFieldsUnite.countAfter state.receiver.counter.value r1 r2
  have countValid : i32.valid count = true := nextMath.count_range.2.2
  have counter : out.scalars.memory[state.receiver.counter.address]? = some ⟨i32,count⟩ := by
    rw [memory]
    exact updated_counter s.scalars.memory state.receiver.counter.address state.receiver.counter.value r1 r2 state.receiver.counter.found
  have sizeCell : out.scalars.memory[state.receiver.size.address]? = some ⟨i32,state.receiver.size.value⟩ := by
    rw [memory]
    by_cases same : r1=r2
    · simpa [Proofs.UfFieldsUnite.updatedMemory,same] using state.receiver.size.found
    · simpa only [Proofs.UfFieldsUnite.updatedMemory,ite_eq_right same,List.getElem?_set_ne state.separated]
        using state.receiver.size.found
  have length : final.length = state.data.items.length := by
    rw [finalEq]
    unfold Proofs.UfUniteCall.uniteVec
    split <;> simp [c2.length,c1.length]
  have lookupOwner : (project out i32).frame.state.storage.lookup state.data.owner = some buffer := by
    change (project out i32).frame.state.storage.lookup (box state.data).owner = some buffer
    rw [fw.owner]
    exact lookup
  have next := transition s out object state Proofs.UnionFindCandidateInstance.UnionFind_unite fuel
    (Proofs.UfObjectCall.arguments s object state.receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) (.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) actual
    count countValid counter sizeCell final nextRank nextMath length buffer lookupOwner items
  obtain ⟨next,rankEq,countEq,sizeEq,itemsEq⟩ := next
  exact ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,complete,⟨next,countEq,sizeEq,itemsEq⟩⟩

end Proofs.UfObjectStateMethods
