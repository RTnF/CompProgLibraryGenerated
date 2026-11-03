import Proofs.CppNestedInvoke
import Proofs.UfReceiverTrace

namespace Proofs.UfCallerTrace
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedInvoke
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.CppLoop

theorem save_represents (s : NState) (layout : Layout) (ps : List Int)
    (count : Int) (rank : Nat → Nat) (ty : Ty) (value : Int)
    (represented : Represents s layout ps count rank) :
    Represents (saveResult s ty value) layout ps count rank := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have ok : Proofs.UfFindCall.VOKWF (saveResult s ty value) layout.vectorSlot
      layout.vectorBinding layout.owner layout.scope buf := by
    refine ⟨inv.ok.valid,save_result_vector_slot s ty value _ _ inv.ok.slot,
      inv.ok.binding,inv.ok.vtag,inv.ok.vfound,inv.ok.lengths,inv.ok.flag,inv.ok.strict,?_⟩
    change s.scalars.baseMemory ≤ (s.scalars.memory++[(⟨ty,value⟩ : Proofs.CppState.Cell)]).length
    have base := inv.ok.base
    simp only [List.length_append,List.length_singleton]
    omega
  exact ⟨buf,cb,nb,ok,inv.items,inv.bufferValid,inv.limit,inv.owner,inv.math,
    save_result_keeps s ty value _ _ cb _ inv.countCell,inv.writable,
    save_result_keeps s ty value _ _ nb _ inv.nCell,inv.different⟩

-- The result local extends the environment; subsequent methods still use the
-- original receiver's slots and see the preceding method's actual mutations.
theorem invoke_step (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank : Nat → Nat) (represented : Represents s layout ps count rank)
    (op : Operation) (allowed : op.allowed ps.length) :
    ∃ fuel out vec nextCount nextRank ty answer,
      op.program.result = .scalar ty ∧
      invokeScalarFuel op.program fuel s (arguments layout ++ op.extra) =
        .finished ⟨out,none,false⟩ ∧
      Represents out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      out.scalarCell s.slots.length ty =
        some (⟨s.scalars.memory.length,false⟩,⟨ty,answer⟩) ∧
      out.slots.length = s.slots.length+1 := by
  obtain ⟨fuel,next,vec,nextCount,nextRank,answer,ran,rep,length⟩ :=
    Proofs.UfReceiverTrace.step s layout ps count rank represented op allowed
  have kind : ∃ ty, op.program.result = .scalar ty := by
    cases op <;> exact ⟨_,rfl⟩
  obtain ⟨ty,kind⟩ := kind
  have post := invoke_result op.program fuel s next (arguments layout ++ op.extra) ty answer kind ran
  have slots := (call_scalar_facts op.program fuel s next (arguments layout ++ op.extra) ty answer kind ran).2.1
  refine ⟨fuel,saveResult next ty answer,vec,nextCount,nextRank,ty,answer,
    kind,post.1,save_represents next layout vec nextCount nextRank ty answer rep,length,post.2.1,?_⟩
  simp [saveResult,NState.declared,NState.charge,NState.observe,slots]

def runInvocations : List Nat → List Operation → NState → Layout → Outcome (NState × List Int)
  | [],[],s,_ => .finished (s,[])
  | fuel::fuels,op::ops,s,layout => do
      let .scalar ty := op.program.result | .fault
      let step ← invokeScalarFuel op.program fuel s (arguments layout ++ op.extra)
      if step.returned.isSome || step.breaking then .fault else do
        let (_,cell) ← liftChecked (step.state.scalarCell s.slots.length ty)
        let (out,answers) ← runInvocations fuels ops step.state layout
        pure (out,cell.value::answers)
  | _,_,_,_ => .fault

theorem invocations_preserve (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runInvocations fuels ops s layout = .finished (out,answers) ∧
      Represents out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.slots.length = s.slots.length+ops.length := by
  induction ops generalizing s ps count rank with
  | nil => exact ⟨[],s,ps,count,rank,[],rfl,represented,rfl,rfl,rfl,by simp⟩
  | cons op ops ih =>
    obtain ⟨fuel,middle,vec1,count1,rank1,ty,answer,kind,ran,rep,length1,cell,slots⟩ :=
      invoke_step s layout ps count rank represented op (allowed op (by simp))
    have tailAllowed : ∀ other ∈ ops, other.allowed vec1.length := by
      intro other member
      rw [length1]
      exact allowed other (by simp [member])
    obtain ⟨fuels,out,vec,count2,rank2,answers,tailRun,finalRep,length2,fl,al,sl⟩ :=
      ih middle vec1 count1 rank1 rep tailAllowed
    refine ⟨fuel::fuels,out,vec,count2,rank2,answer::answers,?_,finalRep,
      length2.trans length1,by simp [fl],by simp [al],?_⟩
    · simp [runInvocations,kind,ran,cell,tailRun,liftChecked,Bind.bind,Outcome.bind,Pure.pure]
    · simp only [List.length_cons] at *
      omega

end Proofs.UfCallerTrace
