import Proofs.CppMoveCallOuter
import Proofs.UfObjectUniformScalarPeak

namespace Proofs.UfObjectTotalPeak
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.CppMoveCallBindings
open Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectTraceWork Proofs.UfObjectState
open Proofs.CppMoveCallLayout Proofs.CppMoveSpace

abbrev scalarBudget := Proofs.UfObjectUniformScalarPeak.budget
abbrev heapBudget := Proofs.UfObjectHeapPeak.budget
def budget (s : Context) : Nat := max s.peak (scalarBudget s+heapBudget s)

theorem invoke_components (s out : Context) (object : ObjectRef) (state : State s object)
    (op : Operation) (fuel : Nat) (result : Ret) (actual : invoke fuel s object op = .finished (out,result)) :
    out.peak ≤ max s.peak (out.scalars.peak+out.objects.heap.peak) := by
  rw [invoke_state fuel s object state op] at actual
  have scalar : ∃ retType : Proofs.CppScalar.Ty, op.program.result = .scalar retType := by
    cases op <;> exact ⟨_,rfl⟩
  obtain ⟨retType,ret⟩ := scalar
  exact Proofs.CppMoveCallOuter.call_outer op.program fuel s out Proofs.DoublingNested.i32 retType _ result
    (Proofs.UfObjectTraceWork.arguments_pure s object state op) (by cases op <;> dsimp only [Operation.program] <;> decide +kernel) ret
    state.contexts state.covered actual

theorem invoke_bounds (s out : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (op : Operation) (ready : op.Valid state.data.items.length)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object op = .finished (out,result)) :
    out.peak ≤ budget s ∧ budget out ≤ budget s ∧ HeadersLive out.objects.heap := by
  have scalar := Proofs.UfObjectUniformScalarPeak.invoke_peak s out object state op ready fuel result actual
  have heap := Proofs.UfObjectHeapPeak.invoke_peak s out object state live op ready fuel result actual
  change out.scalars.peak ≤ scalarBudget s at scalar
  change out.objects.heap.peak ≤ heapBudget s at heap
  have effects := Proofs.UfObjectHeapPeak.invoke_heap_effects s out object state live op fuel result actual
  have component := invoke_components s out object state op fuel result actual
  have total : out.peak ≤ budget s := by
    unfold budget
    clear * - scalar heap component
    omega
  have ran := actual
  rw [invoke_state fuel s object state op] at ran
  have layout := call_layout op.program fuel s out Proofs.DoublingNested.i32 _ result ran
  have scalarNext := Proofs.UfObjectUniformScalarPeak.layout_budget s out layout scalar
  change scalarBudget out ≤ scalarBudget s at scalarNext
  have heapNext : heapBudget out ≤ heapBudget s := by
    unfold heapBudget Proofs.UfObjectHeapPeak.budget
    rw [effects.1,effects.2.1]
    unfold heapBudget Proofs.UfObjectHeapPeak.budget at heap
    clear * - heap
    omega
  refine ⟨total,?_,effects.2.2⟩
  unfold budget at total ⊢
  clear * - total scalarNext heapNext
  omega

theorem history_peak (object : ObjectRef) (s out : Context) (state : State s object) (next : State out object)
    (ops : List Operation) (results : List Ret) (history : History object s state ops out results next)
    (live : HeadersLive s.objects.heap) : out.peak ≤ budget s := by
  induction history with
  | nil source state => exact Nat.le_max_left _ _
  | @cons source middle final initial after last op tail result results ready fuel first rest ih =>
    have bounds := invoke_bounds source middle object initial live op ready fuel result first.actual
    exact (ih bounds.2.2).trans bounds.2.1

theorem actual_peak (s out : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (script : List (Nat × Operation)) (results : List Ret)
    (ready : ∀ op ∈ script.map Prod.snd, op.Valid state.data.items.length)
    (actual : run s object script = .finished (out,results)) : out.peak ≤ budget s := by
  obtain ⟨next,charge,history,charges,bound,count,size⟩ := actual_work s out object state script results ready actual
  exact history_peak object s out state next _ results history live

theorem execute_resources (s : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid state.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out object) (charge : Nat),
      script.map Prod.snd = ops ∧ run s object script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = state.receiver.size.value ∧
      History object s state ops out results next ∧ Charges object s state ops out results next charge ∧
      work out ≤ work s+charge ∧ out.scalars.peak ≤ scalarBudget s ∧ out.peak ≤ budget s ∧
      out.objects.heap.peak ≤ heapBudget s ∧ out.objects.heap.liveSpace = s.objects.heap.liveSpace ∧
      out.objects.heap.baseSpace = s.objects.heap.baseSpace ∧ HeadersLive out.objects.heap := by
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,work,scalar,heap⟩ :=
    Proofs.UfObjectUniformScalarPeak.execute_resources s object state live ops ready
  have total := history_peak object s out state next ops results history live
  exact ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,work,scalar,total,heap⟩

theorem baseline_budget (s : Context) (scalarBase : s.scalars.baseMemory = s.scalars.memory.length)
    (heapBase : s.objects.heap.baseSpace = s.objects.heap.liveSpace) :
    budget s = max s.peak
      (max s.scalars.peak (max (s.scalars.bindings.length+5) (s.slots.length+101)) + max s.objects.heap.peak 1) := by
  have scalarLive : Proofs.CppMoveContext.scalarLive s = s.scalars.bindings.length := by
    unfold Proofs.CppMoveContext.scalarLive
    rw [scalarBase]
    simp
  have scalarAmount : (Proofs.CppMoveReceiverLayout.receiverPrefix s).length+100-s.scalars.baseMemory = s.slots.length+101 := by
    unfold Proofs.CppMoveReceiverLayout.receiverPrefix
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]
    rw [scalarBase]
    omega
  have heapAmount : s.objects.heap.liveSpace+1-s.objects.heap.baseSpace = 1 := by rw [heapBase]; omega
  simp only [budget,scalarBudget,heapBudget,Proofs.UfObjectUniformScalarPeak.budget,Proofs.UfObjectHeapPeak.budget,
    scalarLive,scalarAmount,heapAmount]

theorem actual_additional (s out : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (scalarBase : s.scalars.baseMemory = s.scalars.memory.length)
    (heapBase : s.objects.heap.baseSpace = s.objects.heap.liveSpace)
    (scalarZero : s.scalars.peak = 0) (heapZero : s.objects.heap.peak = 0) (outerZero : s.peak = 0)
    (script : List (Nat × Operation)) (results : List Ret)
    (ready : ∀ op ∈ script.map Prod.snd, op.Valid state.data.items.length)
    (actual : run s object script = .finished (out,results)) :
    out.peak ≤ max (s.scalars.bindings.length+5) (s.slots.length+101) + 1 := by
  have bound := actual_peak s out object state live script results ready actual
  rw [baseline_budget s scalarBase heapBase,scalarZero,heapZero,outerZero] at bound
  simpa using bound

end Proofs.UfObjectTotalPeak
