import Proofs.CppCompactWork
import Proofs.UfObjectTotalPeak
import Proofs.UfMethodAmortized

namespace Proofs.UfObjectSameAmortized
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram
open Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectTraceWork Proofs.UfObjectState
open Proofs.CppMoveCallBindings Proofs.CppMoveReceiverLayout Proofs.CppMoveFrame Proofs.UfReceiverLayout
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame Proofs.StraightLine Proofs.DoublingNested
open Proofs.CppCompactWork Proofs.CppCompactScalarPeak
open Proofs.UfPathAmortized Proofs.UfRootCall Proofs.UfClassInvariant Proofs.UfCompression

-- Reuse the same generated body, but choose the mathematical depth to count path work.
theorem same_trace_work (s out : Context) (object : ObjectRef) (state : State s object)
    (a b : Nat) (ha : a < state.data.items.length) (hb : b < state.data.items.length)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object (.same a b) = .finished (out,result)) :
    ∃ (r1 r2 : Nat) (middle final : List Int) (nodes1 nodes2 : List Nat),
      Compressed state.data.items middle a r1 ∧ Compressed middle final b r2 ∧
      Trace state.data.items a r1 nodes1 ∧ Trace middle b r2 nodes2 ∧
      work out ≤ work s+91*nodes1.length+91*nodes2.length+192 := by
  obtain ⟨prepared,initial,vc,buffer,prep,compacted,qs,frame,ty,writable,flag,sc,current,base,scope⟩ :=
    Proofs.UfObjectCall.prepare s object state.receiver Proofs.UnionFindCandidateInstance.UnionFind_same
      [(.literal i32 (a : Int),(a : Int)),(.literal i32 (b : Int),(b : Int))] (Proofs.UfObjectMethodScalarPeak.expressions_ready s object state (.same a b) ⟨ha,hb⟩)
      rfl state.readable state.unique state.covered state.allocations state.limit state.contexts
  have sameBuffer := Option.some.inj (current.symm.trans state.current)
  subst buffer
  have fields := qs_three initial (receiverPrefix s) state.receiver.counter.address state.receiver.size.value (a : Int) (b : Int) qs
  rw [state.size] at fields
  rw [invoke_state fuel s object state (.same a b)] at actual
  obtain ⟨prepared2,initial2,step,after,prep2,compact2,body,breaking,finished,restored⟩ :=
    call_parts Proofs.UnionFindCandidateInstance.UnionFind_same fuel s out i32 _ result actual
  have samePrepared := Option.some.inj (prep.symm.trans prep2)
  subst prepared2
  have sameInitial := Option.some.inj (compacted.symm.trans compact2)
  subst initial2
  obtain ⟨res,r1,r2,middle,nodes1,nodes2,executed,returned,c1,c2,newForest,reach1,reach2,oldRoot2,saved,cost,need,writes,t1,t2⟩ :=
    Proofs.UfMethodAmortized.same_body_paths (receiverPrefix s) ⟨state.receiver.counter.address,true⟩ state.data.items
      state.rank state.receiver.counter.value state.math state.math.length a b ha hb
      (max (state.rank a) (state.rank b)+2) (by omega) (by omega)
  have run : pexecW vc.ty (max (state.rank a) (state.rank b)+2) Proofs.UnionFindCandidateInstance.UnionFind_same.body
      (Proofs.UfFieldsSame.fields (receiverPrefix s) ⟨state.receiver.counter.address,true⟩ state.data.items.length a b) state.data.items = some res := by
    rw [ty]
    exact executed
  have post := actual_post initial vc true (fun _ => ⟨writable,flag⟩) _ (by decide) (max (state.rank a) (state.rank b)+2) _ state.data.items res run
    (box state.data) fields frame
    (by simp only [Proofs.UfFieldsSame.fields,List.length_append,List.length_cons,List.length_nil]; rw [base]; have b := state.baseline; omega)
    (Nat.le_of_eq sc) fuel step body
  have bodyWork := post_work initial vc _ res state.data.items (box state.data) frame step post
  have fresh := post_fresh initial vc _ res step (Nat.le_of_eq sc) post
  have finishWork := Proofs.CppMovePreparedCall.finish_work (project s i32) step.state after _ step.returned result fresh finished
  have restoredWork : work out = after.work := by
    rw [← project_work out i32,Proofs.CppMoveRestore.restoreContext_project s out i32 after restored state.covered]
  have metadata := compact_metadata (project prepared i32) initial compacted
  have initialWork : initial.work = work prepared := by
    unfold NState.work work
    rw [metadata.2.2.1,metadata.1]
    rfl
  rw [initialWork] at bodyWork
  have setup := Proofs.CppMoveArgumentWork.prepare_work s prepared i32
    Proofs.UnionFindCandidateInstance.UnionFind_same.parameters _ (Proofs.UfObjectTraceWork.arguments_pure s object state (.same a b)) prep
  have setupWork := setup.2
  change work prepared ≤ work s+5+1+5 at setupWork
  refine ⟨r1,r2,middle,res.vec,nodes1,nodes2,c1,c2,t1,t2,?_⟩
  rw [restoredWork,finishWork]
  clear * - bodyWork setupWork cost writes
  omega


theorem actual_same_amortized (s out : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (a b : Nat) (ha : a < state.data.items.length) (hb : b < state.data.items.length)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object (.same a b) = .finished (out,result)) :
    ∃ next : State out object, Step s object state (.same a b) fuel out result next ∧
      Proofs.UfHistoricalRank.History next.data.items rho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
        work s+91*Proofs.UfForestPotential.forestPotential state.data.items rho+
          556*(Proofs.UfPotential.alpha state.data.items.length+1) := by
  obtain ⟨r1,r2,middle,final,nodes1,nodes2,c1,c2,t1,t2,cost⟩ := same_trace_work s out object state a b ha hb fuel result actual
  obtain ⟨next,first⟩ := actual_step s out object state (.same a b) ⟨ha,hb⟩ fuel result actual
  obtain ⟨z1,z2,actualMiddle,resultEq,actualC1,actualC2,connected,countEq⟩ := first.meaning
  have sameMiddle := (Proofs.UfCompression.unique c1 actualC1).2
  subst actualMiddle
  have sameFinal := (Proofs.UfCompression.unique c2 actualC2).2
  have history1 := Proofs.UfHistoricalRank.history_compressed history c1
  have history2 := Proofs.UfHistoricalRank.history_compressed history1 c2
  have potential1 := t1.forest_budget state.math history c1
  have potential2 := t2.forest_budget (state.math.compressed c1) history1 c2
  rw [c1.length] at potential2
  refine ⟨next,first,?_,?_⟩
  · rw [← sameFinal]; exact history2
  · rw [← sameFinal]
    clear * - cost potential1 potential2
    omega

theorem same_amortized_step (s : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (a b : Nat) (ha : a < state.data.items.length) (hb : b < state.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out object),
      invoke fuel s object (.same a b) = .finished (out,result) ∧
      Step s object state (.same a b) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items rho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
        work s+91*Proofs.UfForestPotential.forestPotential state.data.items rho+
          556*(Proofs.UfPotential.alpha state.data.items.length+1) := by
  obtain ⟨fuel,out,result,next,first⟩ := step s object state (.same a b) ⟨ha,hb⟩
  obtain ⟨after,certificate,historyAfter,bound⟩ := actual_same_amortized s out object state rho history a b ha hb fuel result first.actual
  exact ⟨fuel,out,result,after,first.actual,certificate,historyAfter,bound⟩

theorem same_amortized_resources (s : Context) (object : ObjectRef) (state : State s object)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (a b : Nat) (ha : a < state.data.items.length) (hb : b < state.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out object),
      invoke fuel s object (.same a b) = .finished (out,result) ∧
      Step s object state (.same a b) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items rho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
        work s+91*Proofs.UfForestPotential.forestPotential state.data.items rho+
          556*(Proofs.UfPotential.alpha state.data.items.length+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget s ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget s ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget s := by
  obtain ⟨fuel,out,result,next,ran,first,historyAfter,bound⟩ := same_amortized_step s object state rho history a b ha hb
  have scalar := Proofs.UfObjectUniformScalarPeak.invoke_peak s out object state (.same a b) ⟨ha,hb⟩ fuel result ran
  have heap := Proofs.UfObjectHeapPeak.invoke_peak s out object state live (.same a b) ⟨ha,hb⟩ fuel result ran
  have total := Proofs.UfObjectTotalPeak.invoke_bounds s out object state live (.same a b) ⟨ha,hb⟩ fuel result ran
  exact ⟨fuel,out,result,next,ran,first,historyAfter,bound,scalar,heap,total.1⟩

end Proofs.UfObjectSameAmortized
