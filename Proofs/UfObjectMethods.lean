import Proofs.UfObjectCall
import Proofs.UfCompactSameCall
import Proofs.UfCompactSizeCall
import Proofs.UfCompactUniteCall

namespace Proofs.UfObjectMethods
open Proofs.CppScalar Proofs.CppMoveContext Proofs.CppMoveObjectReceiver
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverLayout Proofs.CppMoveFrame
open Proofs.CppMoveCallBindings Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppMoveHeaders Proofs.CppVector Proofs.CppNestedVectorStore
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame Proofs.DoublingNested
open Proofs.UfReceiverLayout Proofs.UfRootCall Proofs.UfCompression Proofs.UfCompactRootBody
open Proofs.UfCompactUniteBody Proofs.UfObjectCall

theorem same_call (s : Context) (object : ObjectRef) (receiver : Receiver s object i32)
    (data : Buffer Int)
    (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (size : receiver.size.value = (data.items.length : Int))
    (rank : Nat → Nat) (forest : Forest data.items rank) (length : data.items.length < 2147483648)
    (a : Nat) (ha : a < data.items.length) (b : Nat) (hb : b < data.items.length)
    (expressionA : NExpr) (typedA : expressionA.resultType = i32) (scalarA : expressionA.scalarOnly = true)
    (denotesA : expressionA.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (expressionB : NExpr) (typedB : expressionB.resultType = i32) (scalarB : expressionB.scalarOnly = true)
    (denotesB : expressionB.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (b : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (validAllocations : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat) (out : Context) (r1 r2 : Nat) (middle final : List Int),
      prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_same.parameters
        (arguments s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc data.items (box data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_same fuel s i32 (arguments s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = .finished (out,.scalar (if r1=r2 then 1 else 0)) ∧
      Compressed data.items middle a r1 ∧ Compressed middle final b r2 ∧ Forest final rank ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected data.items a b) ∧
      work out ≤ work prepared+91*rank a+91*rank b+181 ∧
      out.scalars.memory = s.scalars.memory ∧
      out.scalars.peak ≤ max (max s.scalars.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max s.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max s.scalars.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
          (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer := by
  have ready : Ready s i32 [(expressionA,(a : Int)),(expressionB,(b : Int))] := by
    intro e value member
    rcases List.mem_cons.mp member with equal | member
    · rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
      exact ⟨typedA,scalarA,denotesA⟩
    · rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
      exact ⟨typedB,scalarB,denotesB⟩
  obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,actual,base,scope⟩ :=
    prepare s object receiver Proofs.UnionFindCandidateInstance.UnionFind_same [(expressionA,(a : Int)),(expressionB,(b : Int))]
      ready rfl readable unique covered validAllocations limit contexts
  have same : buffer = data := Option.some.inj (actual.symm.trans current)
  subst buffer
  have fields := qs_three initial (receiverPrefix s) receiver.counter.address receiver.size.value (a : Int) (b : Int) qs
  rw [size] at fields
  obtain ⟨fuel,out,r1,r2,middle,final,post⟩ := Proofs.UfCompactSameCall.same_call s prepared initial
    (arguments s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) vc data.items rank forest length a b ha hb
    (receiverPrefix s) ⟨receiver.counter.address,true⟩ (box data) tyEq ⟨writable,flag⟩ run compacted
    fields fw (by rw [base]; exact baseline) (Nat.le_of_eq sc) (prefix_length s) (prefix_take s) contexts covered
  exact ⟨prepared,initial,vc,fuel,out,r1,r2,middle,final,run,compacted,fw,post⟩

theorem size_call (s : Context) (object : ObjectRef) (receiver : Receiver s object i32)
    (data : Buffer Int)
    (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (size : receiver.size.value = (data.items.length : Int))
    (rank : Nat → Nat) (forest : Forest data.items rank) (length : data.items.length < 2147483648)
    (weights : Proofs.UfFieldsSize.Weights data.items)
    (a : Nat) (ha : a < data.items.length)
    (expressionA : NExpr) (typedA : expressionA.resultType = i32) (scalarA : expressionA.scalarOnly = true)
    (denotesA : expressionA.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (validAllocations : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat) (out : Context) (root : Nat) (weight : Int) (final : List Int),
      prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_size.parameters
        (arguments s object receiver [(expressionA,(a : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc data.items (box data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_size fuel s i32 (arguments s object receiver [(expressionA,(a : Int))]) = .finished (out,.scalar (-weight)) ∧
      data.items[root]? = some weight ∧ weight < 0 ∧
      Compressed data.items final a root ∧ Forest final rank ∧ Proofs.UfFieldsSize.Weights final ∧
      (∀ groups, Proofs.UfClassInvariant.Valid data.items groups rank →
        -weight = ((Proofs.UfClassInvariant.component data.items a).length : Int) ∧ Proofs.UfClassInvariant.Valid final groups rank) ∧
      work out ≤ work prepared+91*rank a+101 ∧
      out.scalars.memory = s.scalars.memory ∧
      out.scalars.peak ≤ max (max s.scalars.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max s.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max s.scalars.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
          (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer := by
  have ready : Ready s i32 [(expressionA,(a : Int))] := by
    intro e value member
    rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
    exact ⟨typedA,scalarA,denotesA⟩
  obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,actual,base,scope⟩ :=
    prepare s object receiver Proofs.UnionFindCandidateInstance.UnionFind_size [(expressionA,(a : Int))]
      ready rfl readable unique covered validAllocations limit contexts
  have same : buffer = data := Option.some.inj (actual.symm.trans current)
  subst buffer
  have fields := qs_two initial (receiverPrefix s) receiver.counter.address receiver.size.value (a : Int) qs
  rw [size] at fields
  obtain ⟨fuel,out,root,weight,final,post⟩ := Proofs.UfCompactSizeCall.size_call s prepared initial
    (arguments s object receiver [(expressionA,(a : Int))]) vc data.items rank forest length weights a ha
    (receiverPrefix s) ⟨receiver.counter.address,true⟩ (box data) tyEq ⟨writable,flag⟩ run compacted
    fields fw (by rw [base]; exact baseline) (Nat.le_of_eq sc) (prefix_length s) (prefix_take s) contexts covered
  exact ⟨prepared,initial,vc,fuel,out,root,weight,final,run,compacted,fw,post⟩

theorem unite_call (s : Context) (object : ObjectRef) (receiver : Receiver s object i32)
    (data : Buffer Int)
    (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (size : receiver.size.value = (data.items.length : Int))
    (rank : Nat → Nat) (validUF : Proofs.UfClassInvariant.Valid data.items receiver.counter.value rank)
    (a : Nat) (ha : a < data.items.length) (b : Nat) (hb : b < data.items.length)
    (expressionA : NExpr) (typedA : expressionA.resultType = i32) (scalarA : expressionA.scalarOnly = true)
    (denotesA : expressionA.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (expressionB : NExpr) (typedB : expressionB.resultType = i32) (scalarB : expressionB.scalarOnly = true)
    (denotesB : expressionB.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (b : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (validAllocations : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat) (out : Context) (r1 r2 : Nat) (middle two final : List Int),
      prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters
        (arguments s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc data.items (box data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite fuel s i32 (arguments s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = .finished (out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧
      Compressed data.items middle a r1 ∧ Compressed middle two b r2 ∧
      final = Proofs.UfUniteCall.uniteVec two r1 r2 ∧
      (∃ rank', Proofs.UfClassInvariant.Valid final (Proofs.UfFieldsUnite.countAfter receiver.counter.value r1 r2) rank') ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected data.items a b) ∧
      work out ≤ work prepared+91*rank a+91*rank b+343 ∧
      out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory s.scalars.memory receiver.counter.address receiver.counter.value r1 r2 ∧
      out.scalars.peak ≤ max (max s.scalars.peak (uniteScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max s.peak (uniteScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max s.scalars.peak (uniteScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
          (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer := by
  have ready : Ready s i32 [(expressionA,(a : Int)),(expressionB,(b : Int))] := by
    intro e value member
    rcases List.mem_cons.mp member with equal | member
    · rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
      exact ⟨typedA,scalarA,denotesA⟩
    · rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
      exact ⟨typedB,scalarB,denotesB⟩
  obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,actual,base,scope⟩ :=
    prepare s object receiver Proofs.UnionFindCandidateInstance.UnionFind_unite [(expressionA,(a : Int)),(expressionB,(b : Int))]
      ready rfl readable unique covered validAllocations limit contexts
  have same : buffer = data := Option.some.inj (actual.symm.trans current)
  subst buffer
  have fields := qs_three initial (receiverPrefix s) receiver.counter.address receiver.size.value (a : Int) (b : Int) qs
  rw [size] at fields
  obtain ⟨fuel,out,r1,r2,middle,two,final,post⟩ := Proofs.UfCompactUniteCall.unite_call s prepared initial
    (arguments s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) vc data.items rank receiver.counter.value validUF a b ha hb
    (receiverPrefix s) receiver.counter.address (prefix_cell s _ _ receiver.counter.found) (box data) tyEq ⟨writable,flag⟩ run compacted
    fields fw (by rw [base]; exact baseline) (Nat.le_of_eq sc) (prefix_length s) (prefix_take s) contexts covered
  exact ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,run,compacted,fw,post⟩

end Proofs.UfObjectMethods
