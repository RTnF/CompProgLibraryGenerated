import Proofs.CppCallPeak
import Proofs.UfUniformStoragePeak

namespace Proofs.UfUniformPeak
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop Proofs.CppPeakComponents
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver Proofs.CppCallFrame

def components (s : NState) : Nat := max s.scalars.peak (Proofs.UfUniformScalarPeak.budget s)+Proofs.CppStoragePeak.bound s

theorem call_grows (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : call fuel s layout op = .finished (out,ret)) : Grows s out := by
  exact Proofs.CppCallPeak.call_peak op.program fuel s out (arguments layout++op.extra) ret
    (Proofs.UfReceiverMetadata.scalar_type op) (Proofs.UfReceiverMetadata.scalar_result op)
    (Proofs.UfReceiverMetadata.body_allowed op) contexts actual

theorem actual_calls (fuels : List Nat) (ops : List Operation) (s : NState) (layout : Layout)
    (out : NState) (answers : List Int)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : runCalls fuels ops s layout = .finished (out,answers)) : Grows s out := by
  induction ops generalizing fuels s out answers with
  | nil =>
    cases fuels with
    | nil =>
      have eq := congrArg Prod.fst (Outcome.finished.inj actual)
      change s = out at eq
      subst out
      exact Grows.refl _
    | cons fuel fuels => simp [runCalls] at actual
  | cons op ops ih =>
    cases fuels with
    | nil => simp [runCalls] at actual
    | cons fuel fuels =>
      cases ran : call fuel s layout op with
      | fault => simp [runCalls,ran,bind,Outcome.bind] at actual
      | exhausted => simp [runCalls,ran,bind,Outcome.bind] at actual
      | finished pair =>
        obtain ⟨middle,ret⟩ := pair
        have metadata := Proofs.UfReceiverMetadata.call_effect fuel s middle layout op ret contexts ran
        have head := call_grows fuel s middle layout op ret contexts ran
        cases ret with
        | unit => simp [runCalls,ran,bind,Outcome.bind] at actual
        | vector owner element => simp [runCalls,ran,bind,Outcome.bind] at actual
        | scalar answer =>
          cases tailRun : runCalls fuels ops middle layout with
          | fault => simp [runCalls,ran,tailRun,bind,Outcome.bind] at actual
          | exhausted => simp [runCalls,ran,tailRun,bind,Outcome.bind] at actual
          | finished pair =>
            obtain ⟨final,rest⟩ := pair
            simp only [runCalls,ran,tailRun,bind,Outcome.bind,pure] at actual
            have eq := congrArg Prod.fst (Outcome.finished.inj actual)
            change final = out at eq
            subst out
            exact head.trans (ih fuels middle final rest (metadata.contexts contexts) tailRun)


theorem calls_peak (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧ CallEffects s out ∧
      out.scalars.peak ≤ max s.scalars.peak (Proofs.UfUniformScalarPeak.budget s) ∧
      out.frame.state.storage.peak ≤ Proofs.CppStoragePeak.bound s ∧
      out.peak ≤ max s.peak (components s) := by
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,metadata,scalarPeak,storagePeak⟩ :=
    Proofs.UfUniformStoragePeak.calls_components ops s layout ps count rank represented allowed
  obtain ⟨buf,cb,nb,inv⟩ := represented.1
  have growth := actual_calls fuels ops s layout out answers inv.ok.strict ran
  exact ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,metadata,
    scalarPeak,storagePeak,growth.bound _ _ scalarPeak storagePeak⟩

theorem actual_calls_peak (fuels : List Nat) (ops : List Operation) (s : NState) (layout : Layout)
    (out : NState) (answers : List Int) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length)
    (actual : runCalls fuels ops s layout = .finished (out,answers)) : out.peak ≤ max s.peak (components s) := by
  have scalarPeak := Proofs.UfUniformScalarPeak.actual_calls_peak fuels ops s layout out answers ps count rank represented allowed actual
  obtain ⟨buf,cb,nb,inv⟩ := represented.1
  have storagePeak := Proofs.UfUniformStoragePeak.actual_calls fuels ops s layout out answers inv.ok.strict actual
  have growth := actual_calls fuels ops s layout out answers inv.ok.strict actual
  exact growth.bound _ _ scalarPeak storagePeak

end Proofs.UfUniformPeak
