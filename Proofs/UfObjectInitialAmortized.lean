import Proofs.UfObjectAmortized

namespace Proofs.UfObjectInitialAmortized
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram
open Proofs.UfObjectTrace Proofs.UfObjectState Proofs.UfForestPotential Proofs.UfPotential

theorem zero_vertex (n : Nat) (parents : List Int) (i : Nat) :
    vertexPotential n parents (fun _ => 0) i = 0 := by
  cases found : parents[i]? with
  | none => simp only [vertexPotential,found]
  | some value =>
    simp only [vertexPotential,found]
    split <;> simp only [Nat.mul_zero,nodePotential_zero]

theorem zero_forest (parents : List Int) : forestPotential parents (fun _ => 0) = 0 := by
  have same : vertexPotential parents.length parents (fun _ => 0) = fun _ => 0 :=
    funext (zero_vertex parents.length parents)
  unfold forestPotential
  rw [same]
  simp

theorem initialized_resources (s : Context) (object : ObjectRef) (state : State s object)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (n : Nat) (initial : state.data.items = List.replicate n (-1))
    (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid n) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out object) (nextRho : Nat → Nat),
      script.map Prod.snd = ops ∧ run s object script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = state.receiver.size.value ∧
      History object s state ops out results next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out ≤ work s+718*ops.length*(alpha n+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget s ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget s ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget s := by
  have mathHistory : Proofs.UfHistoricalRank.History state.data.items (fun _ => 0) := by
    rw [initial]
    exact Proofs.UfHistoricalRank.initial_history n
  have length : state.data.items.length = n := by rw [initial,List.length_replicate]
  have allReady : ∀ op ∈ ops, op.Valid state.data.items.length := by rw [length]; exact ready
  obtain ⟨script,out,results,next,nextRho,mapped,ran,count,size,history,mathNext,bound,scalar,heap,total⟩ :=
    Proofs.UfObjectAmortized.execute_resources s object state live (fun _ => 0) mathHistory ops allReady
  simp only [zero_forest,Nat.mul_zero,Nat.add_zero,length] at bound
  refine ⟨script,out,results,next,nextRho,mapped,ran,count,size,history,mathNext,?_,scalar,heap,total⟩
  exact (Nat.le_add_right _ _).trans bound

end Proofs.UfObjectInitialAmortized
