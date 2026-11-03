import Proofs.Generated.UnionFindPublicCompat
import Proofs.UfReadValues
import Proofs.UfObjectMethods
import Proofs.UfClassCopyBridge
import Proofs.UfObjectConstructedState
import Proofs.UfHistoricalRank

-- Source-bound promotion fixture; the public sentinel header is unchanged.
namespace Proofs.UfPublicSource
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMoveContext
open Proofs.CppConstructorFinish Proofs.CppMoveReceiverResolve Proofs.DoublingNested
open Proofs.CppMoveCallBindings
theorem root_program : Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_root = Proofs.UnionFindCandidateInstance.UnionFind_root := rfl
theorem unite_program : Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_unite = Proofs.UnionFindCandidateInstance.UnionFind_unite := rfl
theorem same_program : Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_same_2 = Proofs.UnionFindCandidateInstance.UnionFind_same := rfl
theorem size_program : Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_size_1 = Proofs.UnionFindCandidateInstance.UnionFind_size := rfl
theorem num_groups_program : Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_num_groups_0 = Proofs.UnionFindCandidateInstance.UnionFind_num_groups := rfl
theorem sizeProgram_program : Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_size_1_2 = Proofs.UfReadPrograms.sizeProgram := rfl
theorem sameProgram_program : Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_same_2_2 = Proofs.UfReadPrograms.sameProgram := rfl
theorem counterProgram_program : Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_num_groups_0_2 = Proofs.UfReadPrograms.counterProgram := rfl
theorem construct0_program : Proofs.UnionFindPublicCompatInstance.Construction.UnionFind_construct0 = Proofs.UnionFindConstructionInstance.UnionFind_construct0 := rfl
theorem construct0_export (fuel : Nat) (s : NState) (args : List NArgument) :
    Proofs.UnionFindPublicCompatInstance.Construction.UnionFind_construct0_exportFuel fuel s args =
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel fuel s args
        (Proofs.UfConstructionExport.vectorField false) (.integer i32)
        (Proofs.UfConstructionExport.fields false) := rfl
theorem construct1_program : Proofs.UnionFindPublicCompatInstance.Construction.UnionFind_construct1 = Proofs.UnionFindConstructionInstance.UnionFind_construct1 := rfl
theorem construct1_export (fuel : Nat) (s : NState) (args : List NArgument) :
    Proofs.UnionFindPublicCompatInstance.Construction.UnionFind_construct1_exportFuel fuel s args =
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel fuel s args
        (Proofs.UfConstructionExport.vectorField true) (.integer i32)
        (Proofs.UfConstructionExport.fields true) := rfl
theorem copy_profile : Proofs.UnionFindPublicCompatInstance.Construction.profile = Proofs.UfClassCopyBridge.profile := rfl
theorem find_root_body (b0 b1 : Proofs.CppState.Binding) :
    Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_find_root.body = Proofs.UfReadCursor.body [b0,b1] := rfl
namespace Mutable
open Proofs.CppScalar Proofs.CppMoveContext Proofs.CppMoveObjectReceiver
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverLayout Proofs.CppMoveFrame
open Proofs.CppMoveCallBindings Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppMoveHeaders Proofs.CppVector Proofs.CppNestedVectorStore
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame Proofs.DoublingNested
open Proofs.UfReceiverLayout Proofs.UfRootCall Proofs.UfCompression Proofs.UfCompactRootBody
open Proofs.UfCompactCounterBody
open Proofs.CppScalar Proofs.CppMoveContext Proofs.CppMoveObjectReceiver
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverLayout Proofs.CppMoveFrame
open Proofs.CppMoveCallBindings Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppMoveHeaders Proofs.CppVector Proofs.CppNestedVectorStore
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame Proofs.DoublingNested
open Proofs.UfReceiverLayout Proofs.UfRootCall Proofs.UfCompression Proofs.UfCompactRootBody
open Proofs.UfCompactUniteBody Proofs.UfObjectCall
theorem root_call_equation (s : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver s object i32) (expressions : List (NExpr × Int))
    (arity : expressions.length = 1) (fuel : Nat) :
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_root_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments expressions) =
      callFuel Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_root fuel s i32
        (Proofs.UfObjectCall.arguments s object receiver expressions) := by
  apply Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_root_call_of_arguments
  simpa [Proofs.UfObjectCall.arguments] using
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_root_arguments_of_fields object (Proofs.CppMoveReceiverResolve.arguments expressions)
      receiver.counter.slot receiver.size.slot receiver.fields
      (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
theorem unite_call_equation (s : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver s object i32) (expressions : List (NExpr × Int))
    (arity : expressions.length = 2) (fuel : Nat) :
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_unite_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments expressions) =
      callFuel Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_unite fuel s i32
        (Proofs.UfObjectCall.arguments s object receiver expressions) := by
  apply Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_unite_call_of_arguments
  simpa [Proofs.UfObjectCall.arguments] using
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_unite_arguments_of_fields object (Proofs.CppMoveReceiverResolve.arguments expressions)
      receiver.counter.slot receiver.size.slot receiver.fields
      (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
theorem same_call_equation (s : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver s object i32) (expressions : List (NExpr × Int))
    (arity : expressions.length = 2) (fuel : Nat) :
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments expressions) =
      callFuel Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_same_2 fuel s i32
        (Proofs.UfObjectCall.arguments s object receiver expressions) := by
  apply Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_call_of_arguments
  simpa [Proofs.UfObjectCall.arguments] using
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_arguments_of_fields object (Proofs.CppMoveReceiverResolve.arguments expressions)
      receiver.counter.slot receiver.size.slot receiver.fields
      (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
theorem size_call_equation (s : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver s object i32) (expressions : List (NExpr × Int))
    (arity : expressions.length = 1) (fuel : Nat) :
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments expressions) =
      callFuel Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_size_1 fuel s i32
        (Proofs.UfObjectCall.arguments s object receiver expressions) := by
  apply Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_call_of_arguments
  simpa [Proofs.UfObjectCall.arguments] using
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_arguments_of_fields object (Proofs.CppMoveReceiverResolve.arguments expressions)
      receiver.counter.slot receiver.size.slot receiver.fields
      (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
theorem counter_call_equation (s : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveObjectReceiver.Receiver s object i32) (expressions : List (NExpr × Int))
    (arity : expressions.length = 0) (fuel : Nat) :
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments expressions) =
      callFuel Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_num_groups_0 fuel s i32
        (Proofs.UfObjectCall.arguments s object receiver expressions) := by
  apply Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_call_of_arguments
  simpa [Proofs.UfObjectCall.arguments] using
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_arguments_of_fields object (Proofs.CppMoveReceiverResolve.arguments expressions)
      receiver.counter.slot receiver.size.slot receiver.fields
      (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
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
      prepareArguments s i32 Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_root.parameters
        (arguments s object receiver [(expression,(a : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc data.items (box data) 0 initial.frame ∧
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_root_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments [(expression,(a : Int))]) = .finished (out,.scalar (root : Int)) ∧
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
  simpa only [root_call_equation s object receiver [(expression,(a : Int))] rfl, root_program] using
    (Proofs.UfObjectCall.root_call s object receiver data current size rank forest length a inside expression typed scalar denotes readable unique covered valid limit baseline contexts)
theorem counter_call (s : Context) (object : ObjectRef) (receiver : Receiver s object i32)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (data : Buffer Int) (fuel : Nat) (out : Context),
      prepareArguments s i32 Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_num_groups_0.parameters
        (arguments s object receiver []) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      currentBuffer s.objects.heap receiver.view.header receiver.header = some data ∧
      FW vc data.items (box data) 0 initial.frame ∧
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments []) = .finished (out,.scalar receiver.counter.value) ∧
      work out ≤ work prepared+3 ∧
      out.scalars.memory = s.scalars.memory ∧
      out.scalars.peak ≤ max (max s.scalars.peak (counterScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) ∧
      out.objects.heap.peak ≤ storageBudget initial vc.L0 ∧
      out.peak ≤ max (max s.peak (counterScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory+storageBudget initial vc.L0))
        (max (max s.scalars.peak (counterScalarBudget initial (receiverPrefix s).length initial.scalars.baseMemory))
          (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length)+storageBudget initial vc.L0) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup vc.R = some buffer ∧ buffer.items = data.items.map Value.integer := by
  simpa only [counter_call_equation s object receiver [] rfl, num_groups_program] using
    (Proofs.UfObjectCall.counter_call s object receiver readable unique covered valid limit baseline contexts)
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
      prepareArguments s i32 Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_same_2.parameters
        (arguments s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc data.items (box data) 0 initial.frame ∧
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments [(expressionA,(a : Int)),(expressionB,(b : Int))]) = .finished (out,.scalar (if r1=r2 then 1 else 0)) ∧
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
  simpa only [same_call_equation s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))] rfl, same_program] using
    (Proofs.UfObjectMethods.same_call s object receiver data current size rank forest length a ha b hb expressionA typedA scalarA denotesA expressionB typedB scalarB denotesB readable unique covered validAllocations limit baseline contexts)
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
      prepareArguments s i32 Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_size_1.parameters
        (arguments s object receiver [(expressionA,(a : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc data.items (box data) 0 initial.frame ∧
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments [(expressionA,(a : Int))]) = .finished (out,.scalar (-weight)) ∧
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
  simpa only [size_call_equation s object receiver [(expressionA,(a : Int))] rfl, size_program] using
    (Proofs.UfObjectMethods.size_call s object receiver data current size rank forest length weights a ha expressionA typedA scalarA denotesA readable unique covered validAllocations limit baseline contexts)
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
      prepareArguments s i32 Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_unite.parameters
        (arguments s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))]) = some prepared ∧
      compact (project prepared i32) = some initial ∧
      FW vc data.items (box data) 0 initial.frame ∧
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_unite_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments [(expressionA,(a : Int)),(expressionB,(b : Int))]) = .finished (out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧
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
  simpa only [unite_call_equation s object receiver [(expressionA,(a : Int)),(expressionB,(b : Int))] rfl, unite_program] using
    (Proofs.UfObjectMethods.unite_call s object receiver data current size rank validUF a ha b hb expressionA typedA scalarA denotesA expressionB typedB scalarB denotesB readable unique covered validAllocations limit baseline contexts)
end Mutable
namespace Readonly
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMoveContext Proofs.CppScalar
open Proofs.CppMoveCallLayout Proofs.CppMoveRestore Proofs.CppMoveFrame Proofs.CppMoveHeaders
open Proofs.CppMoveReadReceiver Proofs.CppConstructorFinish Proofs.CppMoveReceiverPermissions
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverLayout Proofs.CppMoveReceiverFrame
open Proofs.CppMoveCallBindings Proofs.CppVector Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppBufferHeaders Proofs.DoublingNested
open Proofs.CppNestedEval
open Proofs.UfReadPrograms Proofs.UfRootCall
theorem size_call_equation (s : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveReadReceiver.ReadReceiver s object i32) (expressions : List (NExpr × Int))
    (arity : expressions.length = 1) (fuel : Nat) :
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_2_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments expressions) =
      callFuel Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_size_1_2 fuel s i32
        (Proofs.CppMoveReceiverPermissions.readArguments s object receiver expressions) := by
  apply Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_2_call_of_arguments
  simpa [Proofs.CppMoveReceiverPermissions.readArguments] using
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_2_arguments_of_fields object (Proofs.CppMoveReceiverResolve.arguments expressions)
      receiver.counter.slot receiver.size.slot receiver.fields
      (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
theorem same_call_equation (s : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveReadReceiver.ReadReceiver s object i32) (expressions : List (NExpr × Int))
    (arity : expressions.length = 2) (fuel : Nat) :
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_2_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments expressions) =
      callFuel Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_same_2_2 fuel s i32
        (Proofs.CppMoveReceiverPermissions.readArguments s object receiver expressions) := by
  apply Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_2_call_of_arguments
  simpa [Proofs.CppMoveReceiverPermissions.readArguments] using
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_2_arguments_of_fields object (Proofs.CppMoveReceiverResolve.arguments expressions)
      receiver.counter.slot receiver.size.slot receiver.fields
      (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
theorem counter_call_equation (s : Context) (object : ObjectRef)
    (receiver : Proofs.CppMoveReadReceiver.ReadReceiver s object i32) (expressions : List (NExpr × Int))
    (arity : expressions.length = 0) (fuel : Nat) :
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_2_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments expressions) =
      callFuel Proofs.UnionFindPublicCompatInstance.Calls.Methods.UnionFind_num_groups_0_2 fuel s i32
        (Proofs.CppMoveReceiverPermissions.readArguments s object receiver expressions) := by
  apply Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_2_call_of_arguments
  simpa [Proofs.CppMoveReceiverPermissions.readArguments] using
    Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_2_arguments_of_fields object (Proofs.CppMoveReceiverResolve.arguments expressions)
      receiver.counter.slot receiver.size.slot receiver.fields
      (by simpa [Proofs.CppMoveReceiverResolve.arguments] using arity)
theorem size_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (rank : Nat → Nat) (forest : Forest data.items rank) (length : data.items.length < 2147483648)
    (weights : Proofs.UfFieldsSize.Weights data.items) (a : Nat) (inside : a < data.items.length)
    (expression : NExpr) (typed : expression.resultType = i32) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (fuel : Nat) (out : Context) (root : Nat) (weight : Int),
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_2_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments [(expression,(a : Int))]) = .finished (out,.scalar (-weight)) ∧
      Reach data.items a root ∧ root < data.items.length ∧ data.items[root]? = some weight ∧ weight < 0 ∧
      (∀ groups, Proofs.UfClassInvariant.Valid data.items groups rank →
        -weight = ((Proofs.UfClassInvariant.component data.items a).length : Int)) ∧
      work out ≤ work s+expression.nodes+16*rank a+49 ∧ Proofs.UfReadPrepareBudget.Resources s out expression.nodes ∧ Proofs.UfReadValues.Preserved s out object receiver := by
  simpa only [size_call_equation s object receiver [(expression,(a : Int))] rfl, sizeProgram_program] using
    (Proofs.UfReadValues.size_call s object receiver data current rank forest length weights a inside expression typed scalar denotes readable unique covered valid limit baseline contexts)
theorem same_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (rank : Nat → Nat) (forest : Forest data.items rank) (length : data.items.length < 2147483648)
    (a b : Nat) (ha : a < data.items.length) (hb : b < data.items.length)
    (ea eb : NExpr) (ready : Ready s i32 [(ea,(a : Int)),(eb,(b : Int))])
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (fuel : Nat) (out : Context) (root1 root2 : Nat),
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_2_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments [(ea,(a : Int)),(eb,(b : Int))]) =
        .finished (out,.scalar (if root1=root2 then 1 else 0)) ∧
      Reach data.items a root1 ∧ Reach data.items b root2 ∧
      (root1=root2 ↔ Proofs.UfFieldsSame.Connected data.items a b) ∧
      work out ≤ work s+ea.nodes+eb.nodes+16*rank a+16*rank b+84 ∧ Proofs.UfReadPrepareBudget.Resources s out (ea.nodes+eb.nodes) ∧ Proofs.UfReadValues.Preserved s out object receiver := by
  simpa only [same_call_equation s object receiver [(ea,(a : Int)),(eb,(b : Int))] rfl, sameProgram_program] using
    (Proofs.UfReadValues.same_call s object receiver data current rank forest length a b ha hb ea eb ready readable unique covered valid limit baseline contexts)
theorem counter_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (data : Buffer Int) (fuel : Nat) (out : Context),
      currentBuffer s.objects.heap receiver.view.header receiver.header = some data ∧
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_2_callFuel fuel s object (Proofs.CppMoveReceiverResolve.arguments []) = .finished (out,.scalar receiver.counter.value) ∧
      work out ≤ work s+10 ∧ Proofs.UfReadPrepareBudget.Resources s out 0 ∧ Proofs.UfReadValues.Preserved s out object receiver := by
  simpa only [counter_call_equation s object receiver [] rfl, counterProgram_program] using
    (Proofs.UfReadValues.counter_call s object receiver readable unique covered valid limit baseline contexts)
end Readonly
namespace Constructors
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.DoublingNested
open Proofs.UfObjectState Proofs.UfObjectConstructionExport Proofs.CppMoveFrame
open Proofs.CppMoveHeaders Proofs.CppMoveSpace Proofs.CppRootModel
open Proofs.UfObjectConstructionContext Proofs.CppMoveFrameScopes
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
      Proofs.UnionFindPublicCompatInstance.Construction.UnionFind_construct1_exportFuel 8 (project s i32) [.value en] =
          .finished (after,(Proofs.CppConstructorFinish.reference (project s i32) 2)) ∧
      initial.data.items = List.replicate n (-1) ∧ script.map Prod.snd = ops ∧
      Proofs.UfObjectTrace.run (exported s after n) (Proofs.CppConstructorFinish.reference (project s i32) 2) script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = initial.receiver.size.value ∧
      Proofs.UfObjectTrace.History (Proofs.CppConstructorFinish.reference (project s i32) 2) (exported s after n) initial ops out results next ∧
      Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out ≤ work s+en.nodes+n+30+718*ops.length*(Proofs.UfPotential.alpha n+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget (exported s after n) ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget (exported s after n) ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget (exported s after n) := by
  simpa only [construct1_export] using
    (Proofs.UfObjectConstructedState.construct_sized_resources s heap valid models lengths strict base unique covered live allocations en n small scalar type value ops ready)
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
      Proofs.UnionFindPublicCompatInstance.Construction.UnionFind_construct0_exportFuel 8 (project s i32) [] =
          .finished (after,(Proofs.CppConstructorFinish.reference (project s i32) 2)) ∧
      initial.data.items = List.replicate 0 (-1) ∧ script.map Prod.snd = ops ∧
      Proofs.UfObjectTrace.run (exported s after 0) (Proofs.CppConstructorFinish.reference (project s i32) 2) script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = initial.receiver.size.value ∧
      Proofs.UfObjectTrace.History (Proofs.CppConstructorFinish.reference (project s i32) 2) (exported s after 0) initial ops out results next ∧
      Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out ≤ work s+12+718*ops.length*(Proofs.UfPotential.alpha 0+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget (exported s after 0) ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget (exported s after 0) ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget (exported s after 0) := by
  simpa only [construct0_export] using
    (Proofs.UfObjectConstructedState.construct_default_resources s heap valid models lengths strict base unique covered live allocations ops ready)
end Constructors
end Proofs.UfPublicSource


namespace Proofs.UfPublicSource.Historical
open Proofs.UfRootCall Proofs.UfClassInvariant Proofs.UfHistoricalRank

-- The increasing historical rank supplies a bounded descending loop measure.
def descent (parents : List Int) (rho : Nat → Nat) (i : Nat) : Nat :=
  Nat.log2 parents.length - rho i

theorem descent_bound (parents : List Int) (rho : Nat → Nat) (i : Nat) :
    descent parents rho i ≤ Nat.log2 parents.length :=
  Nat.sub_le _ _

theorem descent_forest (parents : List Int) (groups : Int) (rank rho : Nat → Nat)
    (valid : Valid parents groups rank) (history : History parents rho) :
    Forest parents (descent parents rho) := by
  refine ⟨valid.forest.valid,valid.forest.inside,?_⟩
  intro i p found nonnegative
  have parentInside := valid.forest.inside i p found nonnegative
  have cast : (p.toNat : Int) = p := by omega
  have inside : p.toNat < parents.length := by omega
  have increasing := history.1 i p.toNat (by simpa only [cast] using found)
  have upper := historical_rank_bound valid history p.toNat inside
  simp only [descent]
  omega

end Proofs.UfPublicSource.Historical
namespace Proofs.UfPublicSource.Readonly
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMoveContext
open Proofs.CppConstructorFinish Proofs.CppMoveReadReceiver Proofs.DoublingNested
open Proofs.CppVector Proofs.CppMoveHeaders Proofs.CppMoveReceiverLayout Proofs.CppMoveFrame
open Proofs.CppMoveReceiverResolve Proofs.UfRootCall Proofs.CppMoveCallBindings

theorem size_log_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (rank rho : Nat → Nat) (math : Proofs.UfClassInvariant.Valid data.items receiver.counter.value rank)
    (history : Proofs.UfHistoricalRank.History data.items rho)
    (a : Nat) (inside : a < data.items.length)
    (expression : NExpr) (typed : expression.resultType = i32) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (fuel : Nat) (out : Context) (root : Nat) (weight : Int),
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_2_callFuel fuel s object
        [.value expression] = .finished (out,.scalar (-weight)) ∧
      Reach data.items a root ∧ root < data.items.length ∧ data.items[root]? = some weight ∧ weight < 0 ∧
      -weight = ((Proofs.UfClassInvariant.component data.items a).length : Int) ∧
      work out ≤ work s+expression.nodes+16*Nat.log2 data.items.length+49 ∧
      Proofs.UfReadPrepareBudget.Resources s out expression.nodes ∧
      Proofs.UfReadValues.Preserved s out object receiver := by
  have forest := Proofs.UfPublicSource.Historical.descent_forest data.items receiver.counter.value rank rho math history
  have descended : Proofs.UfClassInvariant.Valid data.items receiver.counter.value
      (Proofs.UfPublicSource.Historical.descent data.items rho) :=
    ⟨forest,math.length,math.sizes,math.count⟩
  obtain ⟨fuel,out,root,weight,call,reach,rootInside,found,negative,meaning,cost,resources,keep⟩ :=
    size_call s object receiver data current _ forest math.length math.weights a inside expression typed scalar denotes
      readable unique covered valid limit baseline contexts
  have upper := Proofs.UfPublicSource.Historical.descent_bound data.items rho a
  have bounded : work out ≤ work s+expression.nodes+16*Nat.log2 data.items.length+49 := by omega
  exact ⟨fuel,out,root,weight,call,reach,rootInside,found,negative,
    meaning receiver.counter.value descended,bounded,resources,keep⟩

theorem same_log_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (rank rho : Nat → Nat) (math : Proofs.UfClassInvariant.Valid data.items receiver.counter.value rank)
    (history : Proofs.UfHistoricalRank.History data.items rho)
    (a b : Nat) (ha : a < data.items.length) (hb : b < data.items.length)
    (ea eb : NExpr) (ready : Ready s i32 [(ea,(a : Int)),(eb,(b : Int))])
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (fuel : Nat) (out : Context) (root1 root2 : Nat),
      Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_2_callFuel fuel s object
        [.value ea,.value eb] = .finished (out,.scalar (if root1=root2 then 1 else 0)) ∧
      Reach data.items a root1 ∧ Reach data.items b root2 ∧
      (root1=root2 ↔ Proofs.UfFieldsSame.Connected data.items a b) ∧
      work out ≤ work s+ea.nodes+eb.nodes+32*Nat.log2 data.items.length+84 ∧
      Proofs.UfReadPrepareBudget.Resources s out (ea.nodes+eb.nodes) ∧
      Proofs.UfReadValues.Preserved s out object receiver := by
  have forest := Proofs.UfPublicSource.Historical.descent_forest data.items receiver.counter.value rank rho math history
  obtain ⟨fuel,out,r1,r2,call,reach1,reach2,connected,cost,resources,keep⟩ :=
    same_call s object receiver data current _ forest math.length a b ha hb ea eb ready
      readable unique covered valid limit baseline contexts
  have upperA := Proofs.UfPublicSource.Historical.descent_bound data.items rho a
  have upperB := Proofs.UfPublicSource.Historical.descent_bound data.items rho b
  have bounded : work out ≤ work s+ea.nodes+eb.nodes+32*Nat.log2 data.items.length+84 := by omega
  exact ⟨fuel,out,r1,r2,call,reach1,reach2,connected,bounded,resources,keep⟩

end Proofs.UfPublicSource.Readonly
