import Proofs.CppMoveArgumentPeak
import Proofs.UfObjectMethodScalarPeak

namespace Proofs.UfObjectUniformScalarPeak
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram
open Proofs.CppMoveCallLayout Proofs.CppMoveCallBindings Proofs.CppMoveReceiverLayout
open Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectTraceWork Proofs.UfObjectState
open Proofs.CppMoveArgumentPeak

def budget (s : Context) : Nat := max s.scalars.peak
  (max (scalarLive s+5) ((receiverPrefix s).length+100-s.scalars.baseMemory))

theorem arity_bound (op : Operation) : arity op ≤ 2 := by cases op <;> simp [arity]

theorem invoke_peak (s out : Context) (object : ObjectRef) (state : State s object)
    (op : Operation) (ready : op.Valid state.data.items.length) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object op = .finished (out,result)) : out.scalars.peak ≤ budget s := by
  obtain ⟨prepared,prep,body⟩ := Proofs.UfObjectMethodScalarPeak.call_peak s out object state op ready fuel result actual
  have setup := prepare_peak s prepared Proofs.DoublingNested.i32 op.program.parameters
    (Proofs.UfObjectCall.arguments s object state.receiver op.expressions) (arguments_pure s object state op) prep
  rw [arguments_cost,parameters_length] at setup
  have small := arity_bound op
  have length : (receiverPrefix s).length = s.scalars.memory.length+s.slots.length+1 := by simp [receiverPrefix,Nat.add_assoc]
  have base := state.baseline
  change out.scalars.peak ≤ max (max s.scalars.peak
      (max prepared.scalars.peak ((receiverPrefix s).length+100-s.scalars.baseMemory))) (scalarLive s) at body
  unfold budget
  clear * - setup body small length base
  omega

theorem layout_constant (s out : Context) (layout : Layout s out) :
    max (scalarLive out+5) ((receiverPrefix out).length+100-out.scalars.baseMemory) =
    max (scalarLive s+5) ((receiverPrefix s).length+100-s.scalars.baseMemory) := by
  simp only [scalarLive,receiverPrefix,List.length_append,List.length_replicate,List.length_cons,List.length_nil,
    layout.memoryLength,layout.bindings,layout.baseline,layout.slots]

theorem layout_budget (s out : Context) (layout : Layout s out) (peak : out.scalars.peak ≤ budget s) :
    budget out ≤ budget s := by
  unfold budget
  rw [layout_constant s out layout]
  unfold budget at peak
  clear * - peak
  omega

theorem history_peak (object : ObjectRef) (s out : Context) (state : State s object) (next : State out object)
    (ops : List Operation) (results : List Ret) (history : History object s state ops out results next) :
    out.scalars.peak ≤ budget s := by
  induction history with
  | nil initial state => exact Nat.le_max_left _ _
  | @cons source middle final initial after last op tail result results ready fuel first rest ih =>
    have one := invoke_peak source middle object initial op ready fuel result first.actual
    have actual := first.actual
    rw [invoke_state fuel source object initial op] at actual
    have layout := call_layout op.program fuel source middle Proofs.DoublingNested.i32 _ result actual
    exact ih.trans (layout_budget source middle layout one)

theorem actual_peak (s out : Context) (object : ObjectRef) (state : State s object)
    (script : List (Nat × Operation)) (results : List Ret)
    (ready : ∀ op ∈ script.map Prod.snd, op.Valid state.data.items.length)
    (actual : run s object script = .finished (out,results)) : out.scalars.peak ≤ budget s := by
  obtain ⟨next,charge,history,charges,bound,count,size⟩ := actual_work s out object state script results ready actual
  exact history_peak object s out state next _ results history

-- Construct the actual run with its meanings, work, scalar, and heap bounds together.
theorem execute_resources (s : Context) (object : ObjectRef) (state : State s object)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap) (ops : List Operation)
    (ready : ∀ op ∈ ops, op.Valid state.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out object) (charge : Nat),
      script.map Prod.snd = ops ∧ run s object script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = state.receiver.size.value ∧
      History object s state ops out results next ∧ Charges object s state ops out results next charge ∧
      work out ≤ work s + charge ∧ out.scalars.peak ≤ budget s ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget s ∧
      out.objects.heap.liveSpace = s.objects.heap.liveSpace ∧ out.objects.heap.baseSpace = s.objects.heap.baseSpace ∧
      Proofs.CppMoveSpace.HeadersLive out.objects.heap := by
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound,heap⟩ :=
    Proofs.UfObjectHeapPeak.execute_peak_work s object state live ops ready
  have scalar := history_peak object s out state next ops results history
  exact ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound,scalar,heap⟩

end Proofs.UfObjectUniformScalarPeak
