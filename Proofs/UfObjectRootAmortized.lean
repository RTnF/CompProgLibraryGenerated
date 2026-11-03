import Proofs.CppCompactWork
import Proofs.UfObjectTotalPeak
import Proofs.UfPathAmortized

namespace Proofs.UfObjectRootAmortized
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram
open Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectTraceWork Proofs.UfObjectState
open Proofs.CppMoveCallBindings Proofs.CppMoveReceiverLayout Proofs.CppMoveFrame Proofs.UfReceiverLayout
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame Proofs.StraightLine Proofs.DoublingNested
open Proofs.CppCompactWork Proofs.CppCompactScalarPeak
open Proofs.UfPathAmortized Proofs.UfRootCall Proofs.UfClassInvariant Proofs.UfCompression

-- Reuse the same generated body, but choose the mathematical depth to count path work.
theorem root_trace_work (s out : Context) (object : ObjectRef) (state : State s object)
    (a root : Nat) (nodes : List Nat) (trace : Trace state.data.items a root nodes)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object (.root a) = .finished (out,result)) :
    work out ≤ work s+91*nodes.length+90 := by
  obtain ⟨prepared,initial,vc,buffer,prep,compacted,qs,frame,ty,writable,flag,sc,current,base,scope⟩ :=
    Proofs.UfObjectCall.prepare s object state.receiver Proofs.UnionFindCandidateInstance.UnionFind_root
      [(.literal i32 (a : Int),(a : Int))] (Proofs.UfObjectMethodScalarPeak.expressions_ready s object state (.root a) trace.inside)
      rfl state.readable state.unique state.covered state.allocations state.limit state.contexts
  have sameBuffer := Option.some.inj (current.symm.trans state.current)
  subst buffer
  have fields := qs_two initial (receiverPrefix s) state.receiver.counter.address state.receiver.size.value (a : Int) qs
  rw [state.size] at fields
  rw [invoke_state fuel s object state (.root a)] at actual
  obtain ⟨prepared2,initial2,step,after,prep2,compact2,body,breaking,finished,restored⟩ :=
    call_parts Proofs.UnionFindCandidateInstance.UnionFind_root fuel s out i32 _ result actual
  have samePrepared := Option.some.inj (prep.symm.trans prep2)
  subst prepared2
  have sameInitial := Option.some.inj (compacted.symm.trans compact2)
  subst initial2
  obtain ⟨res,r,executed,returned,compressed,newForest,recursive,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsRoot.body_correct (receiverPrefix s) ⟨state.receiver.counter.address,true⟩ state.data.items
      (depth state.math) (depth_forest state.math) state.math.length a trace.inside (depth state.math a+2) (by omega)
  have run : pexecW vc.ty (depth state.math a+2) Proofs.UnionFindCandidateInstance.UnionFind_root.body
      (Proofs.UfFieldsRoot.fields (receiverPrefix s) ⟨state.receiver.counter.address,true⟩ state.data.items.length a) state.data.items = some res := by
    rw [ty]
    exact executed
  have post := actual_post initial vc true (fun _ => ⟨writable,flag⟩) _ (by decide) (depth state.math a+2) _ state.data.items res run
    (box state.data) fields frame
    (by simp only [Proofs.UfFieldsRoot.fields,Proofs.VecShift.pad,Proofs.PrefixSumsCall.stI,List.length_append,List.length_cons,List.length_nil]; rw [base]; have b := state.baseline; omega)
    (Nat.le_of_eq sc) fuel step body
  have bodyWork := post_work initial vc _ res state.data.items (box state.data) frame step post
  have fresh := post_fresh initial vc _ res step (Nat.le_of_eq sc) post
  have finishWork := Proofs.CppMovePreparedCall.finish_work (project s i32) step.state after i32 step.returned result fresh finished
  have restoredWork : work out = after.work := by
    rw [← project_work out i32,Proofs.CppMoveRestore.restoreContext_project s out i32 after restored state.covered]
  have metadata := compact_metadata (project prepared i32) initial compacted
  have initialWork : initial.work = work prepared := by
    unfold NState.work work
    rw [metadata.2.2.1,metadata.1]
    rfl
  rw [initialWork] at bodyWork
  have setup := Proofs.CppMoveArgumentWork.prepare_work s prepared i32
    Proofs.UnionFindCandidateInstance.UnionFind_root.parameters _ (Proofs.UfObjectTraceWork.arguments_pure s object state (.root a)) prep
  have setupWork := setup.2
  change work prepared ≤ work s+4+1+4 at setupWork
  rw [depth_of_trace state.math trace] at cost writes
  rw [restoredWork,finishWork]
  clear * - bodyWork setupWork cost writes
  omega

theorem actual_root_amortized (s out : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (a : Nat) (inside : a < state.data.items.length) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object (.root a) = .finished (out,result)) :
    ∃ next : State out object, Step s object state (.root a) fuel out result next ∧
      Proofs.UfHistoricalRank.History next.data.items rho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
        work s+91*Proofs.UfForestPotential.forestPotential state.data.items rho+
          272*(Proofs.UfPotential.alpha state.data.items.length+1) := by
  obtain ⟨root,nodes,trace⟩ := trace_exists state.math a inside
  have cost := root_trace_work s out object state a root nodes trace fuel result actual
  obtain ⟨next,first⟩ := actual_step s out object state (.root a) inside fuel result actual
  obtain ⟨r,resultEq,compressed,countEq⟩ := first.meaning
  have same := root_unique compressed.reach trace.reaches compressed.root trace.root
  subst r
  have potential := trace.forest_budget state.math history compressed
  have after := Proofs.UfHistoricalRank.history_compressed history compressed
  refine ⟨next,first,after,?_⟩
  clear * - cost potential
  omega

theorem root_amortized_step (s : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (a : Nat) (inside : a < state.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out object),
      invoke fuel s object (.root a) = .finished (out,result) ∧
      Step s object state (.root a) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items rho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
        work s+91*Proofs.UfForestPotential.forestPotential state.data.items rho+
          272*(Proofs.UfPotential.alpha state.data.items.length+1) := by
  obtain ⟨fuel,out,result,next,first⟩ := step s object state (.root a) inside
  obtain ⟨after,certificate,historyAfter,bound⟩ := actual_root_amortized s out object state rho history a inside fuel result first.actual
  exact ⟨fuel,out,result,after,first.actual,certificate,historyAfter,bound⟩

theorem root_amortized_resources (s : Context) (object : ObjectRef) (state : State s object)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (a : Nat) (inside : a < state.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out object),
      invoke fuel s object (.root a) = .finished (out,result) ∧
      Step s object state (.root a) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items rho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
        work s+91*Proofs.UfForestPotential.forestPotential state.data.items rho+
          272*(Proofs.UfPotential.alpha state.data.items.length+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget s ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget s ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget s := by
  obtain ⟨fuel,out,result,next,ran,first,historyAfter,bound⟩ := root_amortized_step s object state rho history a inside
  have scalar := Proofs.UfObjectUniformScalarPeak.invoke_peak s out object state (.root a) inside fuel result ran
  have heap := Proofs.UfObjectHeapPeak.invoke_peak s out object state live (.root a) inside fuel result ran
  have total := Proofs.UfObjectTotalPeak.invoke_bounds s out object state live (.root a) inside fuel result ran
  exact ⟨fuel,out,result,next,ran,first,historyAfter,bound,scalar,heap,total.1⟩

end Proofs.UfObjectRootAmortized
