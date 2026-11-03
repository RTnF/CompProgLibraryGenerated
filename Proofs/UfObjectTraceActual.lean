import Proofs.CppMoveCallUnique
import Proofs.UfObjectTraceWork

namespace Proofs.UfObjectTraceActual
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.CppLoop
open Proofs.UfObjectTrace Proofs.UfObjectState Proofs.UfObjectTraceWork
open Proofs.CppMoveCallLayout

theorem invoke_success_mono (s : Context) (object : ObjectRef) (op : Operation) (fuel extra : Nat)
    (result : Context × Ret) (actual : invoke fuel s object op = .finished result) :
    invoke (fuel+extra) s object op = .finished result := by
  cases args : expand object op with
  | none => simp [invoke,args,liftChecked,bind,Outcome.bind] at actual
  | some arguments =>
    simp only [invoke,args,liftChecked,bind,Outcome.bind] at actual ⊢
    exact Proofs.CppMoveCallUnique.call_success_mono op.program fuel extra s
      Proofs.DoublingNested.i32 arguments result actual

theorem invoke_unique (s : Context) (object : ObjectRef) (op : Operation) (first second : Nat)
    (a b : Context × Ret) (one : invoke first s object op = .finished a)
    (two : invoke second s object op = .finished b) : a = b := by
  cases args : expand object op with
  | none => simp [invoke,args,liftChecked,bind,Outcome.bind] at one
  | some arguments =>
    simp only [invoke,args,liftChecked,bind,Outcome.bind] at one two
    exact Proofs.CppMoveCallUnique.call_unique op.program first second s Proofs.DoublingNested.i32 arguments a b one two

-- Attach the full per-method meaning/cost certificate to the supplied fuel.
theorem actual_step (s out : Context) (object : ObjectRef) (state : State s object)
    (op : Operation) (ready : op.Valid state.data.items.length) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object op = .finished (out,result)) :
    ∃ next : State out object, Step s object state op fuel out result next := by
  obtain ⟨chosen,after,answer,next,first⟩ := step s object state op ready
  have same := Prod.mk.inj (invoke_unique s object op chosen fuel _ _ first.actual actual)
  have sameOut := same.1
  have sameResult := same.2
  subst out
  subst result
  exact ⟨next,actual,first.size,first.meaning,first.cost⟩

theorem run_unique (s : Context) (object : ObjectRef) (first second : List (Nat × Operation))
    (a b : Context × List Ret) (same : first.map Prod.snd = second.map Prod.snd)
    (one : run s object first = .finished a) (two : run s object second = .finished b) : a = b := by
  induction first generalizing s second a b with
  | nil =>
    cases second with
    | nil => exact Outcome.finished.inj (one.symm.trans two)
    | cons entry tail => simp at same
  | cons entry tail ih =>
    rcases entry with ⟨fuel,op⟩
    cases second with
    | nil => simp at same
    | cons entry rest =>
      rcases entry with ⟨otherFuel,otherOp⟩
      have equal := List.cons.inj same
      have head : op = otherOp := equal.1
      subst otherOp
      simp only [run,bind] at one two
      obtain ⟨pair,firstCall,one⟩ := outcome_bind_finished _ _ _ one
      rcases pair with ⟨middle,result⟩
      obtain ⟨pair,secondCall,two⟩ := outcome_bind_finished _ _ _ two
      rcases pair with ⟨otherMiddle,otherResult⟩
      have matchCall := Prod.mk.inj (invoke_unique s object op fuel otherFuel _ _ firstCall secondCall)
      rw [← matchCall.1,← matchCall.2] at two
      obtain ⟨lastPair,firstTail,one⟩ := outcome_bind_finished _ _ _ one
      rcases lastPair with ⟨last,results⟩
      obtain ⟨lastPair,secondTail,two⟩ := outcome_bind_finished _ _ _ two
      rcases lastPair with ⟨otherLast,otherResults⟩
      have matchTail := Prod.mk.inj (ih middle rest _ _ equal.2 firstTail secondTail)
      have oneResult := Outcome.finished.inj one
      have twoResult := Outcome.finished.inj two
      rw [← matchTail.1,← matchTail.2] at twoResult
      exact oneResult.symm.trans twoResult

theorem run_success_mono (s : Context) (object : ObjectRef) (script : List (Nat × Operation))
    (extra : Nat) (out : Context) (results : List Ret)
    (actual : run s object script = .finished (out,results)) :
    run s object (script.map (fun entry => (entry.1+extra,entry.2))) = .finished (out,results) := by
  induction script generalizing s out results with
  | nil => exact actual
  | cons entry tail ih =>
    rcases entry with ⟨fuel,op⟩
    simp only [run,bind] at actual
    obtain ⟨pair,first,rest⟩ := outcome_bind_finished _ _ _ actual
    rcases pair with ⟨middle,result⟩
    obtain ⟨pair,tailRun,last⟩ := outcome_bind_finished _ _ _ rest
    rcases pair with ⟨final,values⟩
    have equal := Outcome.finished.inj last
    rw [← (Prod.mk.inj equal).1,← (Prod.mk.inj equal).2]
    have firstMore := invoke_success_mono s object op fuel extra _ first
    have tailMore := ih middle final values tailRun
    simp only [List.map_cons,run,bind,Outcome.bind,firstMore,tailMore,pure]

theorem actual_work (s out : Context) (object : ObjectRef) (state : State s object)
    (script : List (Nat × Operation)) (results : List Ret)
    (ready : ∀ op ∈ script.map Prod.snd, op.Valid state.data.items.length)
    (actual : run s object script = .finished (out,results)) :
    ∃ (next : State out object) (charge : Nat),
      History object s state (script.map Prod.snd) out results next ∧
      Charges object s state (script.map Prod.snd) out results next charge ∧
      work out ≤ work s + charge ∧ results.length = script.length ∧
      next.receiver.size.value = state.receiver.size.value := by
  obtain ⟨chosen,last,values,next,charge,mapped,ran,count,size,history,charges,bound⟩ :=
    execute_work s object state (script.map Prod.snd) ready
  have same := Prod.mk.inj (run_unique s object chosen script _ _ mapped ran actual)
  rw [← same.1,← same.2]
  exact ⟨next,charge,history,charges,bound,by simpa using count,size⟩

end Proofs.UfObjectTraceActual
