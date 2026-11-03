import Proofs.UfScalarOther
import Proofs.UfReceiverMetadata

namespace Proofs.UfScalarTrace
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppCallFrame
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver
open Proofs.CppState (Cell Binding)
open Proofs.CppLoop (Outcome)
open Proofs.DoublingNested (i32)

theorem binding_same (s out : NState) (slot : Nat) (ty otherTy : Ty) (b next : Binding) (c other : Cell)
    (effects : CallEffects s out) (before : s.scalarCell slot ty = some (b,c))
    (after : out.scalarCell slot otherTy = some (next,other)) : next = b := by
  obtain ⟨i,loc,found,_⟩ := Proofs.ExtremaCall.scalarCell_facts before
  obtain ⟨j,nextLoc,nextFound,_⟩ := Proofs.ExtremaCall.scalarCell_facts after
  rw [effects.slots,loc] at nextLoc
  have same : i = j := Proofs.CppMixedInvoke.Location.scalar.inj (Option.some.inj nextLoc)
  subst j
  rw [effects.scalarBindings,found] at nextFound
  exact (Option.some.inj nextFound).symm

theorem calls_work_other (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat) (cb : Binding)
    (strong : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length)
    (counter : s.scalarCell layout.countSlot i32 = some (cb,⟨i32,count⟩)) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧ CallEffects s out ∧
      ∀ slot ty binding cell, s.scalarCell slot ty = some (binding,cell) → binding.address ≠ cb.address →
        out.scalarCell slot ty = some (binding,cell) := by
  induction ops generalizing s ps count rank with
  | nil =>
    refine ⟨[],s,ps,count,rank,[],rfl,strong,rfl,rfl,rfl,by simp,CallEffects.refl _,?_⟩
    intro slot ty binding cell found _
    exact found
  | cons op ops ih =>
    obtain ⟨buf,countBinding,nb,inv⟩ := strong.1
    have same : countBinding = cb := congrArg Prod.fst (Option.some.inj (inv.countCell.symm.trans counter))
    subst countBinding
    have headAllowed := allowed op (by simp)
    obtain ⟨fuel,middle,vec1,count1,rank1,answer,headRun,headStrong,len1,headWork⟩ :=
      Proofs.UfTraceWork.step_work s layout ps count rank strong op headAllowed
    have headEffects := Proofs.UfReceiverMetadata.call_effect fuel s middle layout op (.scalar answer) inv.ok.strict headRun
    have headCells := Proofs.UfScalarOther.scalar_other s middle layout ps count rank buf cb nb inv op
      headAllowed fuel (.scalar answer) headRun
    obtain ⟨middleBuf,middleCb,middleNb,middleInv⟩ := headStrong.1
    have cbEq := binding_same s middle layout.countSlot i32 i32 cb middleCb ⟨i32,count⟩ ⟨i32,count1⟩
      headEffects counter middleInv.countCell
    have middleCounter : middle.scalarCell layout.countSlot i32 = some (cb,⟨i32,count1⟩) := by
      rw [←cbEq]
      exact middleInv.countCell
    have tailAllowed : ∀ op ∈ ops, op.allowed vec1.length := by
      intro other member
      rw [len1]
      exact allowed other (by simp [member])
    obtain ⟨fuels,out,vec,nextCount,nextRank,answers,tailRun,post,len2,fl,al,tailWork,tailEffects,tailCells⟩ :=
      ih middle vec1 count1 rank1 headStrong tailAllowed middleCounter
    refine ⟨fuel::fuels,out,vec,nextCount,nextRank,answer::answers,?_,post,len2.trans len1,
      by simp [fl],by simp [al],?_,headEffects.trans tailEffects,?_⟩
    · simp [runCalls,headRun,tailRun,Bind.bind,Outcome.bind,pure]
    · rw [len1] at tailWork
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · intro slot ty binding cell found different
      exact tailCells slot ty binding cell (headCells slot ty binding cell found different) different

end Proofs.UfScalarTrace
