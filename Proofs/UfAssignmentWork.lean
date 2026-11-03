import Proofs.UfAssignmentView
import Proofs.UfMethodAmortized

namespace Proofs.UfAssignmentWork
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.UfReceiverState Proofs.UfFindCall Proofs.UfAssignment Proofs.CppClassAssign Proofs.UfAssignmentView
open Proofs.DoublingNested (i32)

theorem assign_work (s out : NState) (target source : Layout) (old buffer : Buffer Value)
    (ps : List Int) (count : Int) (rank : Nat → Nat) (binding : Binding)
    (cb nb : Proofs.CppState.Binding) (ref : ObjectRef)
    (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (view : SourceView s source ps count rank buffer binding cb nb)
    (ran : assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,ref)) :
    out.work ≤ s.work+old.items.length+ps.length+6 := by
  obtain ⟨_,a,b,frame,targetSlot,sourceSlot,vectorRun,_,_,_,_,_,_,work⟩ :=
    class_success s out (object target) (object source) ref Proofs.UfClassCopyBridge.profile ran
  have aEq : a = target.vectorBinding := Option.some.inj (targetSlot.symm.trans ok.slot)
  have bEq : b = source.vectorBinding := Option.some.inj (sourceSlot.symm.trans view.slot)
  subst a
  subst b
  obtain ⟨tb,sb,actualOld,actualSource,result,tr,sr,primitive,post,_⟩ :=
    data_success s target.vectorBinding source.vectorBinding frame vectorRun
  have te := Prod.mk.inj (Option.some.inj (tr.symm.trans (resolve_ok s target old ok)))
  have se := Prod.mk.inj (Option.some.inj (sr.symm.trans view.resolved))
  have oldEq := te.2
  have sourceEq := se.2
  subst actualOld
  subst actualSource
  have bound := (Proofs.CppVectorCopyAssign.copy_properties _ _ _ _ result primitive).2.2.1
  rw [view.items,List.length_map] at bound
  change result.work ≤ old.items.length+ps.length+1 at bound
  have storage : frame.state.storage.work = s.frame.state.storage.work+result.work := by rw [post]; rfl
  simp only [Proofs.UfClassCopyBridge.profile,List.length_cons,List.length_nil] at work
  rw [storage] at work
  have total : s.work = s.scalars.work+s.frame.state.storage.work := rfl
  omega


open Proofs.UfReceiverTrace Proofs.UfHistoricalRank Proofs.UfPotential Proofs.UfForestPotential

theorem assignment_then_calls (s assigned : NState) (target source : Layout) (old buffer : Buffer Value)
    (ps : List Int) (count : Int) (rank rho : Nat → Nat) (binding : Binding)
    (cb nb tb tn : Proofs.CppState.Binding) (tc nc : Proofs.CppState.Cell) (ref : ObjectRef)
    (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (limit : old.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (view : SourceView s source ps count rank buffer binding cb nb)
    (targetCount : s.scalarCell target.countSlot i32 = some (tb,tc))
    (targetN : s.scalarCell target.nSlot i32 = some (tn,nc)) (writable : tb.writable = true)
    (different : tb.address ≠ tn.address) (sourceDifferent : tb.address ≠ nb.address)
    (ran : assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (assigned,ref))
    (ops : List Operation) (history : History ps rho) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank nextRho answers,
      runCalls fuels ops assigned target = .finished (out,answers) ∧
      Represents out target vec nextCount nextRank ∧ History vec nextRho ∧ vec.length = ps.length ∧
      out.work+91*forestPotential vec nextRho ≤
        s.work+old.items.length+ps.length+6+91*forestPotential ps rho+769*ops.length*(alpha ps.length+1) ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  have represented := assign_represents s assigned target source old buffer ps count rank binding cb nb tb tn tc nc ref
    ok limit view targetCount targetN writable different sourceDifferent ran
  have copyCost := assign_work s assigned target source old buffer ps count rank binding cb nb ref ok view ran
  obtain ⟨fuels,out,vec,nextCount,nextRank,nextRho,answers,calls,post,hist,length,work,fl,al⟩ :=
    Proofs.UfMethodAmortized.amortized_calls ops assigned target ps count rank rho represented history allowed
  exact ⟨fuels,out,vec,nextCount,nextRank,nextRho,answers,calls,post,hist,length,by omega,fl,al⟩

end Proofs.UfAssignmentWork
