import Proofs.UfObjectConstructedState
import Proofs.CppCompactScalarPeak
import Proofs.CppScalarReturnFrame

namespace Proofs.UfObjectGetterFrame
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.DoublingNested
open Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectState
open Proofs.CppMoveCallBindings Proofs.CppMoveFrame Proofs.CppCompactScalarPeak

theorem storage_snapshot (s out : Context) (object : ObjectRef) (state : State s object)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object .groups = .finished (out,result)) :
    (project out i32).frame.state.forest = (project s i32).frame.state.forest ∧
      (project out i32).frame.state.storage.objects = (project s i32).frame.state.storage.objects := by
  rw [invoke_state fuel s object state .groups] at actual
  obtain ⟨prepared,initial,step,after,prep,compacted,body,breaking,finished,restored⟩ :=
    call_parts Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel s out i32 _ result actual
  have preparedEffects := Proofs.CppMovePreparedCall.prepareArguments_effects s prepared i32 _ _ prep
  have metadata := compact_metadata (project prepared i32) initial compacted
  have projected : (project prepared i32).frame.state = (project s i32).frame.state := by
    simp [project,materialize,preparedEffects.1]
  have initialFrame := metadata.1.trans projected
  have initialScope : initial.scope = s.scope+1 := metadata.2.2.2.1.trans preparedEffects.2
  have core := Proofs.CppScalarReturnFrame.sequence_core fuel initial (.variable i32 1) (.primitive .skip) step rfl body
  have stepFrame : step.state.frame.state = (project s i32).frame.state :=
    (congrArg (fun frame : Proofs.CppNestedVectorBindings.Frame => frame.state) core.1.1).trans initialFrame
  have fresh : ∀ owner, step.state.frame.state.forest.context owner ≠ some step.state.scope := by
    intro owner found
    rw [stepFrame] at found
    have bound := state.contexts owner step.state.scope found
    rw [core.1.2.2.1,initialScope] at bound
    omega
  have payload := Proofs.CppScalarReturnFrame.finish_payload (project s i32) step.state after i32 step.returned result fresh finished
  have projectedOut := Proofs.CppMoveRestore.restoreContext_project s out i32 after restored state.covered
  refine ⟨?_,?_⟩
  · rw [projectedOut,payload.1,stepFrame]
  · rw [projectedOut,payload.2,stepFrame]

theorem scalar_snapshot (s out : Context) (object : ObjectRef) (state : State s object)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object .groups = .finished (out,result)) :
    out.scalars.memory = s.scalars.memory := by
  obtain ⟨prepared,initial,vc,chosen,other,post,next,rank,count,size,items⟩ := counter_step s object state
  obtain ⟨prep,compacted,current,fw,called,cost,memory,rest⟩ := post
  have first : invoke chosen s object .groups = .finished (other,.scalar state.receiver.counter.value) := by
    rw [invoke_state chosen s object state .groups]
    exact called
  have same := (Prod.mk.inj (invoke_unique s object .groups chosen fuel _ _ first actual)).1
  simpa only [same] using memory

theorem other_state (s out : Context) (object otherObject : ObjectRef)
    (state : State s object) (other : State s otherObject) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object .groups = .finished (out,result)) :
    ∃ next : State out otherObject, next.rank = other.rank ∧
      next.receiver.counter.value = other.receiver.counter.value ∧ next.receiver.size.value = other.receiver.size.value ∧
      next.data.items = other.data.items := by
  have snapshot := storage_snapshot s out object state fuel result actual
  have memory := scalar_snapshot s out object state fuel result actual
  have headerFound := (Proofs.CppMoveViews.resolve_parts s.objects other.receiver.viewSlot other.receiver.view other.receiver.header other.receiver.resolved).2.1
  obtain ⟨before,current,entry,valid,limit,owner⟩ := Proofs.CppMoveReceiverFrame.current_entry s.objects.heap i32
    other.receiver.view.header other.receiver.header headerFound other.readable other.unique other.covered
  have same : before = other.data := Option.some.inj (current.symm.trans other.current)
  subst before
  have previous := (materialize_entry s.objects i32 other.data.owner (box other.data) _ entry).1
  have lookup : (project out i32).frame.state.storage.lookup other.data.owner = some (box other.data) := by
    unfold Proofs.CppVectorStore.Store.lookup
    rw [snapshot.2]
    exact previous
  rw [invoke_state fuel s object state .groups] at actual
  exact transition s out otherObject other Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel _ result actual
    other.receiver.counter.value other.receiver.counter.valid (by rw [memory]; exact other.receiver.counter.found)
    (by rw [memory]; exact other.receiver.size.found) other.data.items other.rank other.math rfl (box other.data) lookup rfl


theorem getter_pair_step (s : Context) (object otherObject : ObjectRef) (state : State s object) (other : State s otherObject) :
    ∃ (fuel : Nat) (out : Context) (next : State out object) (otherNext : State out otherObject),
      invoke fuel s object .groups = .finished (out,.scalar state.receiver.counter.value) ∧
      next.rank = state.rank ∧ next.receiver.counter.value = state.receiver.counter.value ∧
      next.receiver.size.value = state.receiver.size.value ∧ next.data.items = state.data.items ∧
      otherNext.rank = other.rank ∧ otherNext.receiver.counter.value = other.receiver.counter.value ∧
      otherNext.receiver.size.value = other.receiver.size.value ∧ otherNext.data.items = other.data.items ∧ work out ≤ work s+10 := by
  obtain ⟨fuel,out,result,witness,first⟩ := step s object state .groups trivial
  have resultEq : result = .scalar state.receiver.counter.value := first.meaning.1
  have actual := first.actual
  rw [resultEq] at actual
  obtain ⟨next,rank,count,size,items⟩ := other_state s out object object state state fuel _ actual
  obtain ⟨otherNext,rankOther,countOther,sizeOther,itemsOther⟩ := other_state s out object otherObject state other fuel _ actual
  have cost := Proofs.UfObjectTraceWork.step_work s out object state witness .groups fuel result first
  change work out ≤ work s+(7+2*0)+3 at cost
  refine ⟨fuel,out,next,otherNext,actual,rank,count,size,items,rankOther,countOther,sizeOther,itemsOther,?_⟩
  simpa only [Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using cost

end Proofs.UfObjectGetterFrame
