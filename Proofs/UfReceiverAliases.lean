import Proofs.CppHeaderAliases
import Proofs.UfReceiverReferences

namespace Proofs.UfReceiverAliases
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppBufferHeaders Proofs.CppCallFrame
open Proofs.CppHeaderAliases Proofs.CppReferenceHeaders Proofs.UfReceiverReferences
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver Proofs.CppLoop

-- Integer contents may change; grants, header identity and resolver metadata
-- retain both their successful and rejected results.
def Preserves (s t : NState) : Prop :=
  (∀ binding, t.frame.headerOwner binding = s.frame.headerOwner binding) ∧
  (∀ slot element, (t.frame.resolve slot element).map (fun pair => (pair.1,signature pair.2)) =
    (s.frame.resolve slot element).map (fun pair => (pair.1,signature pair.2))) ∧
  (∀ reference, (t.frame.read reference).isSome = (s.frame.read reference).isSome)

theorem of_effects (s t : NState) (effects : CallEffects s t)
    (before : s.frame.state.wellFormed = true) (after : t.frame.state.wellFormed = true) : Preserves s t :=
  ⟨fun binding => header_owner s t binding effects before after,
    fun slot element => resolve_signature s t slot element effects before after,
    fun reference => read_isSome s t reference effects before after⟩

theorem call_preserves (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
    (ps vec : List Int) (count nextCount : Int) (rank nextRank : Nat → Nat)
    (before : Represents s layout ps count rank) (after : Represents out layout vec nextCount nextRank)
    (actual : call fuel s layout op = .finished (out,ret)) : Preserves s out := by
  obtain ⟨buf,cb,nb,inv⟩ := before
  exact of_effects s out (Proofs.UfReceiverMetadata.call_effect fuel s out layout op ret inv.ok.strict actual)
    inv.ok.valid (represents_valid out layout vec nextCount nextRank after)

theorem actual_calls_preserve (fuels : List Nat) (ops : List Operation) (s out : NState) (layout : Layout)
    (answers : List Int)
    (before : s.frame.state.wellFormed = true) (after : out.frame.state.wellFormed = true)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : runCalls fuels ops s layout = .finished (out,answers)) : Preserves s out :=
  of_effects s out (Proofs.UfReceiverMetadata.actual_calls fuels ops s layout out answers contexts actual) before after

theorem calls_work_aliases (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧ CallEffects s out ∧ Preserves s out := by
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,effects⟩ :=
    Proofs.UfReceiverMetadata.calls_work_effects ops s layout ps count rank represented allowed
  exact ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,effects,
    of_effects s out effects (represents_valid s layout ps count rank represented.1)
      (represents_valid out layout vec nextCount nextRank strong.1)⟩

end Proofs.UfReceiverAliases
