import Proofs.CppCallStoragePeak
import Proofs.UfUniformScalarPeak

namespace Proofs.UfUniformStoragePeak
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver Proofs.CppCallFrame
open Proofs.CppStoragePeak (bound)

theorem bound_after (s t : NState) (effects : CallEffects s t)
    (peak : t.frame.state.storage.peak ≤ bound s) : bound t ≤ bound s := by
  unfold bound
  rw [effects.headers.live,effects.headers.base]
  exact Nat.max_le.mpr ⟨peak,Nat.le_max_right _ _⟩

theorem call_peak (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : call fuel s layout op = .finished (out,ret)) : out.frame.state.storage.peak ≤ bound s := by
  exact Proofs.CppCallStoragePeak.call_peak op.program fuel s out (arguments layout++op.extra) ret
    (Proofs.UfReceiverMetadata.scalar_type op) (Proofs.UfReceiverMetadata.scalar_result op)
    (Proofs.UfReceiverMetadata.body_allowed op) contexts actual

theorem actual_calls (fuels : List Nat) (ops : List Operation) (s : NState) (layout : Layout)
    (out : NState) (answers : List Int)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : runCalls fuels ops s layout = .finished (out,answers)) : out.frame.state.storage.peak ≤ bound s := by
  induction ops generalizing fuels s out answers with
  | nil =>
    cases fuels with
    | nil =>
      have eq := congrArg Prod.fst (Outcome.finished.inj actual)
      change s = out at eq
      subst out
      exact Nat.le_max_left _ _
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
        have head := call_peak fuel s middle layout op ret contexts ran
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
            exact Nat.le_trans (ih fuels middle final rest (metadata.contexts contexts) tailRun) (bound_after s middle metadata head)


theorem calls_components (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧ CallEffects s out ∧
      out.scalars.peak ≤ max s.scalars.peak (Proofs.UfUniformScalarPeak.budget s) ∧
      out.frame.state.storage.peak ≤ bound s := by
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,scalarPeak⟩ :=
    Proofs.UfUniformScalarPeak.calls_peak ops s layout ps count rank represented allowed
  obtain ⟨buf,cb,nb,inv⟩ := represented.1
  have metadata := Proofs.UfReceiverMetadata.actual_calls fuels ops s layout out answers inv.ok.strict ran
  exact ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,metadata,scalarPeak,
    actual_calls fuels ops s layout out answers inv.ok.strict ran⟩

end Proofs.UfUniformStoragePeak
