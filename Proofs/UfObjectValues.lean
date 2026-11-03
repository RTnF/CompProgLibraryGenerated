import Proofs.CppCompactValues
import Proofs.UfObjectTraceActual

namespace Proofs.UfObjectValues
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.DoublingNested
open Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectState
open Proofs.UfObjectStateMethods
open Proofs.CppMoveReceiverResolve Proofs.CppMoveCallBindings Proofs.CppMoveFrame

theorem literal_ready (s : Context) (object : ObjectRef) (state : State s object) (a : Nat)
    (inside : a < state.data.items.length) : Ready s i32 [(.literal i32 (a : Int),(a : Int))] := by
  intro expression value member
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  exact ⟨rfl,rfl,by simp [NExpr.denote,literal_valid s object state a inside]⟩

theorem operation_ready (s : Context) (object : ObjectRef) (state : State s object) (op : Operation)
    (valid : op.Valid state.data.items.length) : Ready s i32 op.expressions := by
  cases op with
  | root a | size a => exact literal_ready s object state a valid
  | same a b | unite a b =>
    intro expression value member
    rcases List.mem_cons.mp member with first | second
    · exact literal_ready s object state a valid.1 expression value (by simp only [List.mem_singleton]; exact first)
    · exact literal_ready s object state b valid.2 expression value second
  | groups => intro expression value member; cases member

theorem other_payload (s out : Context) (object : ObjectRef) (state : State s object)
    (op : Operation) (valid : op.Valid state.data.items.length) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object op = .finished (out,result)) :
    ∀ owner, owner ≠ state.data.owner →
      (project out i32).frame.state.storage.lookup owner = (project s i32).frame.state.storage.lookup owner := by
  obtain ⟨prepared,initial,vc,buffer,prep,compacted,qs,fw,ty,writable,flag,scope,current,base,initialScope⟩ :=
    Proofs.UfObjectCall.prepare s object state.receiver op.program op.expressions
      (operation_ready s object state op valid) (by cases op <;> rfl) state.readable state.unique state.covered
      state.allocations state.limit state.contexts
  have bufferEq := Option.some.inj (current.symm.trans state.current)
  subst buffer
  have target : Proofs.CppFixedWrite.Target initial vc.R := by
    refine ⟨0,⟨vc.R,.integer vc.ty,vc.wV,.root vc.vsc⟩,?_,?_,rfl⟩
    · simp only [NState.vectorSlot,qs.slots]
      rfl
    · rw [fw.bindings]
      rfl
  obtain ⟨retType,scalar⟩ : ∃ ty, op.program.result = .scalar ty := by cases op <;> exact ⟨_,rfl⟩
  have allowed : Proofs.CppFixedRun.Allowed op.program.body = true := by cases op <;> simp only [Operation.program] <;> decide +kernel
  rw [invoke_state fuel s object state op] at actual
  have kept := Proofs.CppCompactValues.call_other op.program fuel s out prepared initial i32 retType
    (Proofs.UfObjectCall.arguments s object state.receiver op.expressions) result vc.R scalar allowed prep compacted
    target state.contexts state.covered actual
  have ownerEq : state.data.owner = vc.R := fw.owner
  rw [← ownerEq] at kept
  exact kept

theorem scalar_frame_exists (s : Context) (object : ObjectRef) (state : State s object) (op : Operation)
    (ready : op.Valid state.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret), invoke fuel s object op = .finished (out,result) ∧
      ∀ address, address ≠ state.receiver.counter.address → out.scalars.memory[address]? = s.scalars.memory[address]? := by
  cases op with
  | root a =>
    change a < state.data.items.length at ready
    have av := literal_valid s object state a ready
    obtain ⟨prepared,initial,vc,fuel,out,r,final,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      root_step s object state a ready (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
    obtain ⟨prep,compacted,fw,actual,compressed,forest,cost,memory,rest⟩ := post

    refine ⟨fuel,out,.scalar (r : Int),?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · intro address different
      rw [memory]
  | same a b =>
    change a < state.data.items.length ∧ b < state.data.items.length at ready
    have av := literal_valid s object state a ready.1
    have bv := literal_valid s object state b ready.2
    obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,final,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      same_step s object state a ready.1 b ready.2 (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
        (.literal i32 (b : Int)) rfl rfl (by simp [NExpr.denote,bv])
    obtain ⟨prep,compacted,fw,actual,c1,c2,forest,connected,cost,memory,rest⟩ := post

    refine ⟨fuel,out,.scalar (if r1=r2 then 1 else 0),?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · intro address different
      rw [memory]
  | size a =>
    change a < state.data.items.length at ready
    have av := literal_valid s object state a ready
    obtain ⟨prepared,initial,vc,fuel,out,r,weight,final,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      size_step s object state a ready (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
    obtain ⟨prep,compacted,fw,actual,atRoot,negative,compressed,forest,weights,meaning,cost,memory,rest⟩ := post

    refine ⟨fuel,out,.scalar (-weight),?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · intro address different
      rw [memory]
  | unite a b =>
    change a < state.data.items.length ∧ b < state.data.items.length at ready
    have av := literal_valid s object state a ready.1
    have bv := literal_valid s object state b ready.2
    obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,post,next,countEq,sizeEq,itemsEq⟩ :=
      unite_step s object state a ready.1 b ready.2 (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
        (.literal i32 (b : Int)) rfl rfl (by simp [NExpr.denote,bv])
    obtain ⟨prep,compacted,fw,actual,c1,c2,finalEq,newValid,connected,cost,memory,rest⟩ := post

    refine ⟨fuel,out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int),?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · intro address different
      rw [memory]
      by_cases same : r1=r2
      · simp only [Proofs.UfFieldsUnite.updatedMemory,ite_eq_left same]
      · simp only [Proofs.UfFieldsUnite.updatedMemory,ite_eq_right same,List.getElem?_set_ne (Ne.symm different)]
  | groups =>
    obtain ⟨prepared,initial,vc,fuel,out,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      counter_step s object state
    obtain ⟨prep,compacted,current,fw,actual,cost,memory,rest⟩ := post

    refine ⟨fuel,out,.scalar state.receiver.counter.value,?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · intro address different
      rw [memory]

theorem scalar_other (s out : Context) (object : ObjectRef) (state : State s object)
    (op : Operation) (valid : op.Valid state.data.items.length) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object op = .finished (out,result)) :
    ∀ address, address ≠ state.receiver.counter.address → out.scalars.memory[address]? = s.scalars.memory[address]? := by
  obtain ⟨chosen,after,answer,first,memory⟩ := scalar_frame_exists s object state op valid
  have same := (Prod.mk.inj (invoke_unique s object op chosen fuel _ _ first actual)).1
  subst out
  exact memory

theorem other_state (s out : Context) (object otherObject : ObjectRef)
    (state : State s object) (other : State s otherObject) (op : Operation)
    (valid : op.Valid state.data.items.length)
    (different : other.data.owner ≠ state.data.owner)
    (counterApart : other.receiver.counter.address ≠ state.receiver.counter.address)
    (sizeApart : other.receiver.size.address ≠ state.receiver.counter.address)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object op = .finished (out,result)) :
    ∃ next : State out otherObject, next.rank = other.rank ∧
      next.receiver.counter.value = other.receiver.counter.value ∧ next.receiver.size.value = other.receiver.size.value ∧
      next.data.items = other.data.items := by
  have snapshot := other_payload s out object state op valid fuel result actual
  have memory := scalar_other s out object state op valid fuel result actual
  have headerFound := (Proofs.CppMoveViews.resolve_parts s.objects other.receiver.viewSlot other.receiver.view other.receiver.header other.receiver.resolved).2.1
  obtain ⟨before,current,entry,bufferValid,limit,owner⟩ := Proofs.CppMoveReceiverFrame.current_entry s.objects.heap i32
    other.receiver.view.header other.receiver.header headerFound other.readable other.unique other.covered
  have same : before = other.data := Option.some.inj (current.symm.trans other.current)
  subst before
  have previous := (materialize_entry s.objects i32 other.data.owner (box other.data) _ entry).1
  have lookup : (project out i32).frame.state.storage.lookup other.data.owner = some (box other.data) :=
    (snapshot other.data.owner different).trans previous
  rw [invoke_state fuel s object state op] at actual
  exact transition s out otherObject other op.program fuel _ result actual
    other.receiver.counter.value other.receiver.counter.valid
    (by rw [memory other.receiver.counter.address counterApart]; exact other.receiver.counter.found)
    (by rw [memory other.receiver.size.address sizeApart]; exact other.receiver.size.found)
    other.data.items other.rank other.math rfl (box other.data) lookup rfl

theorem pair_step (s : Context) (object otherObject : ObjectRef)
    (state : State s object) (other : State s otherObject) (op : Operation)
    (valid : op.Valid state.data.items.length)
    (different : other.data.owner ≠ state.data.owner)
    (counterApart : other.receiver.counter.address ≠ state.receiver.counter.address)
    (sizeApart : other.receiver.size.address ≠ state.receiver.counter.address) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out object) (otherNext : State out otherObject),
      Step s object state op fuel out result next ∧ otherNext.rank = other.rank ∧
      otherNext.receiver.counter.value = other.receiver.counter.value ∧ otherNext.receiver.size.value = other.receiver.size.value ∧
      otherNext.data.items = other.data.items := by
  obtain ⟨fuel,out,result,next,first⟩ := step s object state op valid
  obtain ⟨otherNext,rank,count,size,items⟩ := other_state s out object otherObject state other op valid
    different counterApart sizeApart fuel result first.actual
  exact ⟨fuel,out,result,next,otherNext,first,rank,count,size,items⟩

end Proofs.UfObjectValues
