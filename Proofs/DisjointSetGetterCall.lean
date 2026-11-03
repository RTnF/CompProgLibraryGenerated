import Proofs.CppScalarGetterCall
import Proofs.CppMoveValueReceiver
import Proofs.DisjointSetGetter

namespace Proofs.DisjointSetGetterCall
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMoveContext Proofs.CppMoveHeaders
open Proofs.DoublingNested Proofs.CppScalarGetterCall

-- These are intermediate receiver/preparation obligations. No actual body,
-- finish, restoration or successful call is assumed.
theorem call_from_prepared (caller prepared : Context) (initial : NState)
    (object : Proofs.CppConstructorFinish.ObjectRef) (sizeSlot counterSlot : Nat) (count : Int)
    (fields : object.scalarSlots = [sizeSlot,counterSlot])
    (contexts : ∀ owner scope, (project caller i32).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (valid : (project caller i32).frame.state.wellFormed = true)
    (preparedRun : prepareArguments caller i32
      Proofs.Generated.DisjointSetMethods.Methods.DisjointSet_getNum.parameters
      [.vectorReference object.vectorSlot,.value (.variable i32 sizeSlot),.scalarReference counterSlot] = some prepared)
    (compacted : Proofs.CppMoveCallBindings.compact (project prepared i32) = some initial)
    (memoryPrefix : initial.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory)
    (counterValue : (.variable i32 2 : NExpr).denote (Proofs.CppNestedEval.envOf initial) = some count)
    (countValid : i32.valid count = true) :
    ∃ out, Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_callFuel 2 caller object [] =
      .finished (out,.scalar count) ∧ out.scalars.memory = caller.scalars.memory ∧
      (∀ owner, (project out i32).frame.state.storage.lookup owner = initial.frame.state.storage.lookup owner) ∧
      work out ≤ initial.work+3 := by
  obtain ⟨out,actual,memory,storage,cost⟩ := Proofs.CppScalarGetterCall.call_from_prepared
    Proofs.Generated.DisjointSetMethods.Methods.DisjointSet_getNum caller prepared initial i32 i32
    [.vectorReference object.vectorSlot,.value (.variable i32 sizeSlot),.scalarReference counterSlot]
    (.variable i32 2) (.primitive .skip) count rfl rfl rfl rfl contexts covered valid
    preparedRun compacted memoryPrefix counterValue countValid
  have mapped := Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_arguments_of_fields
    object [] sizeSlot counterSlot fields rfl
  have forwarded := Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_call_of_arguments
    2 caller object [] _ mapped
  refine ⟨out,?_,memory,storage,?_⟩
  · simpa only [List.append_nil] using forwarded.trans actual
  · simpa only [NExpr.nodes,Nat.reduceAdd,Nat.add_assoc] using cost

-- The original source receiver conditions now construct preparation as well.
-- The size field is a stored value; it need not equal the vector length.
theorem call_resources (caller : Context) (object : Proofs.CppConstructorFinish.ObjectRef)
    (sizeSlot counterSlot headerID : Nat) (header : Proofs.CppMoveHeaders.Header)
    (counterBinding sizeBinding : Proofs.CppState.Binding) (count size : Int)
    (fields : object.scalarSlots = [sizeSlot,counterSlot])
    (captured : captureBorrow caller object.vectorSlot true = some ⟨headerID,true⟩)
    (headerFound : caller.objects.heap.header headerID = some header)
    (headerWritable : header.writable = true)
    (counter : (project caller i32).scalarCell counterSlot i32 = some (counterBinding,⟨i32,count⟩))
    (counterWritable : counterBinding.writable = true)
    (sizeCell : (project caller i32).scalarCell sizeSlot i32 = some (sizeBinding,⟨i32,size⟩))
    (contexts : ∀ owner scope, (project caller i32).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (valid : (project caller i32).frame.state.wellFormed = true) :
    ∃ out, Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_callFuel 2 caller object [] =
      .finished (out,.scalar count) ∧ out.scalars.memory = caller.scalars.memory ∧
      (∀ owner, (project out i32).frame.state.storage.lookup owner = (project caller i32).frame.state.storage.lookup owner) ∧
      work out ≤ work caller+10 ∧
      out.scalars.peak ≤ Proofs.CppMoveValueReceiver.fieldScalarBudget caller ∧
      out.objects.heap.peak = Proofs.CppScalarGetterCall.heapBudget (project caller i32) ∧
      out.peak ≤ max caller.peak (Proofs.CppMoveValueReceiver.fieldScalarBudget caller+
        Proofs.CppScalarGetterCall.heapBudget (project caller i32)) := by
  obtain ⟨_,_,_,_,_,countValid⟩ := Proofs.ExtremaCall.scalarCell_facts counter
  obtain ⟨prepared,initial,preparedRun,compacted,memoryPrefix,counterValue,state,cost,scalarBefore,liveBefore,totalBefore⟩ :=
    Proofs.CppMoveValueReceiver.prepare_fields_compact caller i32 object.vectorSlot sizeSlot counterSlot
      ⟨headerID,true⟩ header counterBinding sizeBinding count size true captured headerFound
      (fun _ => headerWritable) counter sizeCell (fun _ => counterWritable)
  obtain ⟨out,actual,memory,storage,calledCost,resources⟩ := Proofs.CppScalarGetterCall.call_resources
    Proofs.Generated.DisjointSetMethods.Methods.DisjointSet_getNum caller prepared initial i32 i32
    [.vectorReference object.vectorSlot,.value (.variable i32 sizeSlot),.scalarReference counterSlot]
    (.variable i32 2) (.primitive .skip) count rfl rfl rfl rfl contexts covered valid
    preparedRun compacted memoryPrefix counterValue countValid
  have mapped := Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_arguments_of_fields
    object [] sizeSlot counterSlot fields rfl
  have forwarded := Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_call_of_arguments
    2 caller object [] _ mapped
  let budget := Proofs.CppMoveValueReceiver.fieldScalarBudget caller
  have oldBounds : caller.scalars.peak ≤ budget ∧ scalarLive caller ≤ budget := by
    simp only [budget,Proofs.CppMoveValueReceiver.fieldScalarBudget]
    omega
  have commonBound : Proofs.CppScalarGetterCall.scalarBudget caller initial 1 ≤ budget := by
    simp only [Proofs.CppScalarGetterCall.scalarBudget]
    omega
  have heapEq : Proofs.CppScalarGetterCall.heapBudget initial =
      Proofs.CppScalarGetterCall.heapBudget (project caller i32) := by
    unfold Proofs.CppScalarGetterCall.heapBudget
    rw [state]
  have heapLower : caller.objects.heap.peak ≤ Proofs.CppScalarGetterCall.heapBudget (project caller i32) := by
    change (project caller i32).frame.state.storage.peak ≤ _
    exact Nat.le_max_left _ _
  have totalBound : out.peak ≤ max caller.peak (budget+Proofs.CppScalarGetterCall.heapBudget (project caller i32)) := by
    have bound := resources.total
    change out.peak ≤ Proofs.CppScalarGetterCall.totalBudget caller initial 1 at bound
    simp only [Proofs.CppScalarGetterCall.totalBudget] at bound
    rw [heapEq] at bound
    omega
  refine ⟨out,?_,memory,?_,?_,?_,?_,totalBound⟩
  · simpa only [List.append_nil] using forwarded.trans actual
  · intro owner
    rw [storage owner,state]
  · simp only [NExpr.nodes] at calledCost
    omega
  · exact resources.scalar.trans commonBound
  · exact resources.heap.trans heapEq

theorem call (caller : Context) (object : Proofs.CppConstructorFinish.ObjectRef)
    (sizeSlot counterSlot headerID : Nat) (header : Proofs.CppMoveHeaders.Header)
    (counterBinding sizeBinding : Proofs.CppState.Binding) (count size : Int)
    (fields : object.scalarSlots = [sizeSlot,counterSlot])
    (captured : captureBorrow caller object.vectorSlot true = some ⟨headerID,true⟩)
    (headerFound : caller.objects.heap.header headerID = some header)
    (headerWritable : header.writable = true)
    (counter : (project caller i32).scalarCell counterSlot i32 = some (counterBinding,⟨i32,count⟩))
    (counterWritable : counterBinding.writable = true)
    (sizeCell : (project caller i32).scalarCell sizeSlot i32 = some (sizeBinding,⟨i32,size⟩))
    (contexts : ∀ owner scope, (project caller i32).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (valid : (project caller i32).frame.state.wellFormed = true) :
    ∃ out, Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_callFuel 2 caller object [] =
      .finished (out,.scalar count) ∧ out.scalars.memory = caller.scalars.memory ∧
      (∀ owner, (project out i32).frame.state.storage.lookup owner = (project caller i32).frame.state.storage.lookup owner) ∧
      work out ≤ work caller+10 := by
  obtain ⟨out,actual,memory,storage,cost,_scalar,_heap,_total⟩ := call_resources caller object
    sizeSlot counterSlot headerID header counterBinding sizeBinding count size fields captured headerFound
    headerWritable counter counterWritable sizeCell contexts covered valid
  exact ⟨out,actual,memory,storage,cost⟩

end Proofs.DisjointSetGetterCall
