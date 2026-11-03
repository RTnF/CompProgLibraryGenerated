import Proofs.UfObjectSizeAmortized
import Proofs.UfObjectSameAmortized
import Proofs.UfObjectUniteAmortized

namespace Proofs.UfObjectAmortized
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram
open Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectTraceWork Proofs.UfObjectState
open Proofs.UfForestPotential Proofs.UfPotential Proofs.CppLoop

theorem actual_step_amortized (s out : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (op : Operation) (ready : op.Valid state.data.items.length) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object op = .finished (out,result)) :
    ∃ (next : State out object) (nextRho : Nat → Nat), Step s object state op fuel out result next ∧
      Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out+91*forestPotential next.data.items nextRho ≤
        work s+91*forestPotential state.data.items rho+718*(alpha state.data.items.length+1) := by
  cases op with
  | root a =>
    obtain ⟨next,first,hist,bound⟩ := Proofs.UfObjectRootAmortized.actual_root_amortized s out object state rho history a ready fuel result actual
    refine ⟨next,rho,first,hist,?_⟩
    exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide : 272 ≤ 718)) _)
  | size a =>
    obtain ⟨next,first,hist,bound⟩ := Proofs.UfObjectSizeAmortized.actual_size_amortized s out object state rho history a ready fuel result actual
    refine ⟨next,rho,first,hist,?_⟩
    exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide : 292 ≤ 718)) _)
  | same a b =>
    obtain ⟨next,first,hist,bound⟩ := Proofs.UfObjectSameAmortized.actual_same_amortized s out object state rho history a b ready.1 ready.2 fuel result actual
    refine ⟨next,rho,first,hist,?_⟩
    exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide : 556 ≤ 718)) _)
  | unite a b =>
    exact Proofs.UfObjectUniteAmortized.actual_unite_amortized s out object state rho history a b ready.1 ready.2 fuel result actual
  | groups =>
    obtain ⟨next,first⟩ := actual_step s out object state .groups ready fuel result actual
    have dataEq := first.meaning.2.1
    have cost := step_work s out object state next .groups fuel result first
    change work out ≤ work s+(7+2*0)+3 at cost
    refine ⟨next,rho,first,?_,?_⟩
    · rw [dataEq]; exact history
    · rw [dataEq]
      clear * - cost
      omega

theorem step_amortized (s : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (op : Operation) (ready : op.Valid state.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out object) (nextRho : Nat → Nat),
      Step s object state op fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out+91*forestPotential next.data.items nextRho ≤
        work s+91*forestPotential state.data.items rho+718*(alpha state.data.items.length+1) := by
  obtain ⟨fuel,out,result,next,first⟩ := step s object state op ready
  obtain ⟨after,nextRho,certificate,hist,bound⟩ := actual_step_amortized s out object state rho history op ready fuel result first.actual
  exact ⟨fuel,out,result,after,nextRho,certificate,hist,bound⟩

theorem execute_amortized (s : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (mathHistory : Proofs.UfHistoricalRank.History state.data.items rho)
    (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid state.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out object) (nextRho : Nat → Nat),
      script.map Prod.snd = ops ∧ run s object script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = state.receiver.size.value ∧
      History object s state ops out results next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out+91*forestPotential next.data.items nextRho ≤
        work s+91*forestPotential state.data.items rho+718*ops.length*(alpha state.data.items.length+1) := by
  induction ops generalizing s rho with
  | nil => exact ⟨[],s,[],state,rho,rfl,rfl,rfl,rfl,.nil s state,mathHistory,by simp⟩
  | cons op tail ih =>
    obtain ⟨fuel,middle,result,next,middleRho,first,mathMiddle,firstBound⟩ :=
      step_amortized s object state rho mathHistory op (ready op (by simp))
    have length := same_length s middle object state next first.size
    have restReady : ∀ entry ∈ tail, entry.Valid next.data.items.length := by
      intro entry member
      rw [length]
      exact ready entry (by simp [member])
    obtain ⟨script,out,results,final,nextRho,mapped,ran,count,sizeFinal,history,mathFinal,tailBound⟩ :=
      ih middle next middleRho mathMiddle restReady
    refine ⟨(fuel,op)::script,out,result::results,final,nextRho,by simp [mapped],
      by simp [run,first.actual,ran,bind,Outcome.bind,pure],by simp [count],sizeFinal.trans first.size,
      .cons (ready op (by simp)) fuel first history,mathFinal,?_⟩
    rw [length] at tailBound
    rw [List.length_cons,Nat.mul_add 718 tail.length 1,Nat.mul_one,Nat.add_mul]
    clear * - firstBound tailBound
    omega

theorem actual_amortized (s out : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (mathHistory : Proofs.UfHistoricalRank.History state.data.items rho)
    (script : List (Nat × Operation)) (results : List Ret)
    (ready : ∀ op ∈ script.map Prod.snd, op.Valid state.data.items.length)
    (actual : run s object script = .finished (out,results)) :
    ∃ (next : State out object) (nextRho : Nat → Nat),
      History object s state (script.map Prod.snd) out results next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out+91*forestPotential next.data.items nextRho ≤
        work s+91*forestPotential state.data.items rho+718*script.length*(alpha state.data.items.length+1) := by
  obtain ⟨chosen,last,values,next,nextRho,mapped,ran,count,size,history,mathNext,bound⟩ :=
    execute_amortized s object state rho mathHistory (script.map Prod.snd) ready
  have same := Prod.mk.inj (run_unique s object chosen script _ _ mapped ran actual)
  rw [← same.1,← same.2]
  exact ⟨next,nextRho,history,mathNext,by simpa using bound⟩

theorem execute_resources (s : Context) (object : ObjectRef) (state : State s object)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (rho : Nat → Nat) (mathHistory : Proofs.UfHistoricalRank.History state.data.items rho)
    (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid state.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out object) (nextRho : Nat → Nat),
      script.map Prod.snd = ops ∧ run s object script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = state.receiver.size.value ∧
      History object s state ops out results next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out+91*forestPotential next.data.items nextRho ≤
        work s+91*forestPotential state.data.items rho+718*ops.length*(alpha state.data.items.length+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget s ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget s ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget s := by
  obtain ⟨script,out,results,next,nextRho,mapped,ran,count,size,history,mathNext,bound⟩ :=
    execute_amortized s object state rho mathHistory ops ready
  have scalar := Proofs.UfObjectUniformScalarPeak.history_peak object s out state next ops results history
  have heap := Proofs.UfObjectHeapPeak.history_peak object s out state next ops results history live
  have total := Proofs.UfObjectTotalPeak.history_peak object s out state next ops results history live
  exact ⟨script,out,results,next,nextRho,mapped,ran,count,size,history,mathNext,bound,scalar,heap.1,total⟩

end Proofs.UfObjectAmortized
