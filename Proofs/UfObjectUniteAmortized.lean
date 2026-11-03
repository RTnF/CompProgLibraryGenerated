import Proofs.CppCompactWork
import Proofs.UfObjectTotalPeak
import Proofs.UfMethodAmortized

namespace Proofs.UfObjectUniteAmortized
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram
open Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectTraceWork Proofs.UfObjectState
open Proofs.CppMoveCallBindings Proofs.CppMoveReceiverLayout Proofs.CppMoveFrame Proofs.UfReceiverLayout
open Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame Proofs.StraightLine Proofs.DoublingNested
open Proofs.CppCompactWork Proofs.CppCompactScalarPeak
open Proofs.UfPathAmortized Proofs.UfRootCall Proofs.UfClassInvariant Proofs.UfCompression

-- Reuse the same generated body, but choose the mathematical depth to count path work.
theorem unite_trace_work (s out : Context) (object : ObjectRef) (state : State s object)
    (a b : Nat) (ha : a < state.data.items.length) (hb : b < state.data.items.length)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object (.unite a b) = .finished (out,result)) :
    ∃ (r1 r2 : Nat) (middle two : List Int) (nodes1 nodes2 : List Nat),
      Compressed state.data.items middle a r1 ∧ Compressed middle two b r2 ∧
      Trace state.data.items a r1 nodes1 ∧ Trace middle b r2 nodes2 ∧
      work out ≤ work s+91*nodes1.length+91*nodes2.length+354 := by
  obtain ⟨prepared,initial,vc,buffer,prep,compacted,qs,frame,ty,writable,flag,sc,current,base,scope⟩ :=
    Proofs.UfObjectCall.prepare s object state.receiver Proofs.UnionFindCandidateInstance.UnionFind_unite
      [(.literal i32 (a : Int),(a : Int)),(.literal i32 (b : Int),(b : Int))] (Proofs.UfObjectMethodScalarPeak.expressions_ready s object state (.unite a b) ⟨ha,hb⟩)
      rfl state.readable state.unique state.covered state.allocations state.limit state.contexts
  have sameBuffer := Option.some.inj (current.symm.trans state.current)
  subst buffer
  have fields := qs_three initial (receiverPrefix s) state.receiver.counter.address state.receiver.size.value (a : Int) (b : Int) qs
  rw [state.size] at fields
  rw [invoke_state fuel s object state (.unite a b)] at actual
  obtain ⟨prepared2,initial2,step,after,prep2,compact2,body,breaking,finished,restored⟩ :=
    call_parts Proofs.UnionFindCandidateInstance.UnionFind_unite fuel s out i32 _ result actual
  have samePrepared := Option.some.inj (prep.symm.trans prep2)
  subst prepared2
  have sameInitial := Option.some.inj (compacted.symm.trans compact2)
  subst initial2
  obtain ⟨res,r1,r2,middle,two,nodes1,nodes2,executed,returned,c1,c2,finalEq,newValid,saved,cost,need,writes,t1,t2⟩ :=
    Proofs.UfMethodAmortized.unite_body_paths (receiverPrefix s) state.receiver.counter.address state.receiver.counter.value
      state.data.items state.rank state.math (prefix_cell s _ _ state.receiver.counter.found) a b ha hb
      (max (state.rank a) (state.rank b)+2) (by omega) (by omega)
  have run : pexecW vc.ty (max (state.rank a) (state.rank b)+2) Proofs.UnionFindCandidateInstance.UnionFind_unite.body
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
    Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters _ (Proofs.UfObjectTraceWork.arguments_pure s object state (.unite a b)) prep
  have setupWork := setup.2
  change work prepared ≤ work s+5+1+5 at setupWork
  refine ⟨r1,r2,middle,two,nodes1,nodes2,c1,c2,t1,t2,?_⟩
  rw [restoredWork,finishWork]
  clear * - bodyWork setupWork cost writes
  omega



theorem actual_unite_amortized (s out : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (a b : Nat) (ha : a < state.data.items.length) (hb : b < state.data.items.length)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object (.unite a b) = .finished (out,result)) :
    ∃ (next : State out object) (nextRho : Nat → Nat), Step s object state (.unite a b) fuel out result next ∧
      Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items nextRho ≤
        work s+91*Proofs.UfForestPotential.forestPotential state.data.items rho+
          718*(Proofs.UfPotential.alpha state.data.items.length+1) := by
  obtain ⟨r1,r2,middle,two,nodes1,nodes2,c1,c2,t1,t2,cost⟩ := unite_trace_work s out object state a b ha hb fuel result actual
  obtain ⟨next,first⟩ := actual_step s out object state (.unite a b) ⟨ha,hb⟩ fuel result actual
  obtain ⟨z1,z2,actualMiddle,actualTwo,resultEq,actualC1,actualC2,nextEq,connected,countEq⟩ := first.meaning
  obtain ⟨rootEq1,sameMiddle⟩ := Proofs.UfCompression.unique c1 actualC1
  subst z1
  subst actualMiddle
  obtain ⟨rootEq2,sameTwo⟩ := Proofs.UfCompression.unique c2 actualC2
  subst z2
  subst actualTwo
  have history1 := Proofs.UfHistoricalRank.history_compressed history c1
  have history2 := Proofs.UfHistoricalRank.history_compressed history1 c2
  have potential1 := t1.forest_budget state.math history c1
  have potential2 := t2.forest_budget (state.math.compressed c1) history1 c2
  rw [c1.length] at potential2
  obtain ⟨w1,f1,n1⟩ := c1.root
  have f1middle := (negative_entry c1 w1 n1).mpr f1
  have f1two := (negative_entry c2 w1 n1).mpr f1middle
  obtain ⟨w2,f2,n2⟩ := c2.root
  have f2two := (negative_entry c2 w2 n2).mpr f2
  obtain ⟨nextRho,nextHistory,potential⟩ := Proofs.UfForestPotential.unite_potential
    ((state.math.compressed c1).compressed c2) history2 r1 r2 ⟨w1,f1two,n1⟩ ⟨w2,f2two,n2⟩
  rw [c2.length,c1.length] at potential
  refine ⟨next,nextRho,first,?_,?_⟩
  · rw [nextEq]; exact nextHistory
  · rw [nextEq]
    clear * - cost potential1 potential2 potential
    omega

theorem unite_amortized_step (s : Context) (object : ObjectRef) (state : State s object)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (a b : Nat) (ha : a < state.data.items.length) (hb : b < state.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out object) (nextRho : Nat → Nat),
      invoke fuel s object (.unite a b) = .finished (out,result) ∧
      Step s object state (.unite a b) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items nextRho ≤
        work s+91*Proofs.UfForestPotential.forestPotential state.data.items rho+
          718*(Proofs.UfPotential.alpha state.data.items.length+1) := by
  obtain ⟨fuel,out,result,next,first⟩ := step s object state (.unite a b) ⟨ha,hb⟩
  obtain ⟨after,nextRho,certificate,historyAfter,bound⟩ := actual_unite_amortized s out object state rho history a b ha hb fuel result first.actual
  exact ⟨fuel,out,result,after,nextRho,first.actual,certificate,historyAfter,bound⟩

theorem unite_amortized_resources (s : Context) (object : ObjectRef) (state : State s object)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History state.data.items rho)
    (a b : Nat) (ha : a < state.data.items.length) (hb : b < state.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out object) (nextRho : Nat → Nat),
      invoke fuel s object (.unite a b) = .finished (out,result) ∧
      Step s object state (.unite a b) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items nextRho ≤
        work s+91*Proofs.UfForestPotential.forestPotential state.data.items rho+
          718*(Proofs.UfPotential.alpha state.data.items.length+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget s ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget s ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget s := by
  obtain ⟨fuel,out,result,next,nextRho,ran,first,historyAfter,bound⟩ := unite_amortized_step s object state rho history a b ha hb
  have scalar := Proofs.UfObjectUniformScalarPeak.invoke_peak s out object state (.unite a b) ⟨ha,hb⟩ fuel result ran
  have heap := Proofs.UfObjectHeapPeak.invoke_peak s out object state live (.unite a b) ⟨ha,hb⟩ fuel result ran
  have total := Proofs.UfObjectTotalPeak.invoke_bounds s out object state live (.unite a b) ⟨ha,hb⟩ fuel result ran
  exact ⟨fuel,out,result,next,nextRho,ran,first,historyAfter,bound,scalar,heap,total.1⟩

end Proofs.UfObjectUniteAmortized
