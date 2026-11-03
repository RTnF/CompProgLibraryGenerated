import Proofs.CppMoveObjectReceiver
import Proofs.UfReceiverLayout
import Proofs.UfCompactRootCall
import Proofs.UfCompactCounterCall

namespace Proofs.UfObjectCall
open Proofs.CppScalar Proofs.CppMoveContext Proofs.CppMoveObjectReceiver
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverLayout Proofs.CppMoveFrame
open Proofs.CppMoveCallBindings Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppMoveHeaders Proofs.CppVector Proofs.CppNestedVectorStore
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame Proofs.DoublingNested
open Proofs.UfReceiverLayout Proofs.UfRootCall Proofs.UfCompression Proofs.UfCompactRootBody
open Proofs.UfCompactCounterBody

def arguments (s : Context) (object : ObjectRef) (receiver : Receiver s object i32)
    (expressions : List (NExpr × Int)) : List Proofs.CppNestedCall.NArgument :=
  [.vectorReference object.vectorSlot,.scalarReference receiver.counter.slot,
    .value (.variable i32 receiver.size.slot)] ++ Proofs.CppMoveReceiverResolve.arguments expressions

theorem prepare (s : Context) (object : ObjectRef) (receiver : Receiver s object i32)
    (method : NProgram) (expressions : List (NExpr × Int))
    (ready : Ready s i32 expressions)
    (params : method.parameters = .vector i32 true :: .scalar i32 true true :: .scalar i32 false true ::
      Proofs.CppMoveReceiverResolve.parameters i32 expressions)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (buffer : Buffer Int),
      prepareArguments s i32 method.parameters (arguments s object receiver expressions) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      QS initial [] initial.scalars.baseMemory initial.scope
        (receiverPrefix s ++ cells i32 (receiver.size.value::values expressions))
        (⟨receiver.counter.address,true⟩ :: valueBindings (receiverPrefix s).length (expressions.length+1))
        (.vector 0 :: .scalar 0 :: valueSlots 1 (expressions.length+1)) ∧
      FW vc buffer.items (box buffer) 0 initial.frame ∧
      vc.ty = i32 ∧ vc.wV = true ∧ vc.flag = true ∧ vc.sc = initial.scope ∧
      currentBuffer s.objects.heap receiver.view.header receiver.header = some buffer ∧
      initial.scalars.baseMemory = s.scalars.baseMemory ∧ initial.scope = s.scope+1 := by
  obtain ⟨last,resolved⟩ := Receiver.resolve s object i32 receiver expressions ready
  have fullReady := ready_field s i32 receiver.size.slot ⟨receiver.size.address,receiver.size.writable⟩
    receiver.size.value (Field.cell s i32 receiver.size) expressions ready
  have valuesValid := ready_values_valid s i32 _ fullReady
  have parts := Proofs.CppMoveViews.resolve_parts s.objects receiver.viewSlot receiver.view receiver.header receiver.resolved
  have permission : true = true → receiver.header.writable = true := fun _ => parts.2.2 receiver.writable
  rw [← params] at resolved
  obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,current,base,scope⟩ :=
    prepare_qs_fw s last ⟨receiver.view.header,true⟩ receiver.header parts.2.1 permission readable
      unique covered valid limit receiver.counter.address receiver.counter.value receiver.counter.found
      receiver.counter.valid (receiver.size.value::values expressions) valuesValid method.parameters
      (arguments s object receiver expressions) resolved contexts
  exact ⟨prepared,initial,vc,buffer,run,compacted,by simpa [values] using qs,fw,
    tyEq,writable,flag,sc,current,base,scope⟩

-- Every setup condition is constructed from the source receiver and heap.
-- Preserve the existing complete work/peak postcondition of root_call.
theorem root_call (s : Context) (object : ObjectRef) (receiver : Receiver s object i32)
    (data : Buffer Int)
    (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (size : receiver.size.value = (data.items.length : Int))
    (rank : Nat → Nat) (forest : Forest data.items rank) (length : data.items.length < 2147483648)
    (a : Nat) (inside : a < data.items.length) (expression : NExpr)
    (typed : expression.resultType = i32) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (fuel : Nat)
      (out : Context) (root : Nat) (final : List Int),
      prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_root.parameters
        (arguments s object receiver [(expression,(a : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc data.items (box data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_root fuel s i32 (arguments s object receiver [(expression,(a : Int))]) = .finished (out,.scalar (root : Int)) ∧
      Compressed data.items final a root ∧ Forest final rank ∧
      work out ≤ work prepared+91*rank a+81 ∧
      out.scalars.memory = s.scalars.memory ∧
      out.scalars.peak ≤ max (max s.scalars.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max s.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max s.scalars.peak (scalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
          (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = final.map Value.integer := by
  have ready : Ready s i32 [(expression,(a : Int))] := by
    intro e value member
    rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
    exact ⟨typed,scalar,denotes⟩
  obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,actual,base,scope⟩ :=
    prepare s object receiver Proofs.UnionFindCandidateInstance.UnionFind_root [(expression,(a : Int))]
      ready rfl readable unique covered valid limit contexts
  have same : buffer = data := Option.some.inj (actual.symm.trans current)
  subst buffer
  have fields := qs_two initial (receiverPrefix s) receiver.counter.address receiver.size.value (a : Int) qs
  rw [size] at fields
  obtain ⟨fuel,out,root,final,post⟩ := Proofs.UfCompactRootCall.root_call s prepared initial
    (arguments s object receiver [(expression,(a : Int))]) vc data.items rank forest length a inside
    (receiverPrefix s) ⟨receiver.counter.address,true⟩ (box data) tyEq ⟨writable,flag⟩ run compacted
    fields fw (by rw [base]; exact baseline) (Nat.le_of_eq sc) (prefix_length s) (prefix_take s) contexts covered
  exact ⟨prepared,initial,vc,fuel,out,root,final,run,compacted,fw,post⟩

-- Getter termination uses the retained scalar fields, even after vector move.
theorem counter_call (s : Context) (object : ObjectRef) (receiver : Receiver s object i32)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (data : Buffer Int) (fuel : Nat) (out : Context),
      prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters
        (arguments s object receiver []) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      currentBuffer s.objects.heap receiver.view.header receiver.header = some data ∧
      FW vc data.items (box data) 0 initial.frame ∧
      callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel s i32 (arguments s object receiver []) = .finished (out,.scalar receiver.counter.value) ∧
      work out ≤ work prepared+3 ∧
      out.scalars.memory = s.scalars.memory ∧
      out.scalars.peak ≤ max (max s.scalars.peak (counterScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max s.peak (counterScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max s.scalars.peak (counterScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
          (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = data.items.map Value.integer := by
  obtain ⟨prepared,initial,vc,data,run,compacted,qs,fw,tyEq,writable,flag,sc,current,base,scope⟩ :=
    prepare s object receiver Proofs.UnionFindCandidateInstance.UnionFind_num_groups []
      (by intro e value member; simp at member) rfl readable unique covered valid limit contexts
  have fields := qs_one initial (receiverPrefix s) receiver.counter.address receiver.size.value qs
  obtain ⟨fuel,out,post⟩ := Proofs.UfCompactCounterCall.counter_call s prepared initial
    (arguments s object receiver []) vc data.items (receiverPrefix s) receiver.counter.address
    receiver.size.value receiver.counter.value (prefix_cell s _ _ receiver.counter.found) receiver.counter.valid
    (box data) tyEq run compacted fields fw (by rw [base]; exact baseline) (Nat.le_of_eq sc)
    (prefix_length s) (prefix_take s) contexts covered
  exact ⟨prepared,initial,vc,data,fuel,out,run,compacted,current,fw,post⟩

end Proofs.UfObjectCall
