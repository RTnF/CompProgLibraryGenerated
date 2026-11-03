import Proofs.CppReferenceHeaders
import Proofs.UfReceiverMetadata

namespace Proofs.UfReceiverReferences
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppCallFrame Proofs.CppReferenceHeaders
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver Proofs.CppLoop

theorem represents_valid (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) : s.frame.state.wellFormed = true := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  exact inv.ok.valid

theorem call_reads (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
    (ps vec : List Int) (count nextCount : Int) (rank nextRank : Nat → Nat)
    (before : Represents s layout ps count rank) (after : Represents out layout vec nextCount nextRank)
    (actual : call fuel s layout op = .finished (out,ret)) :
    ∀ reference, (out.frame.read reference).isSome = (s.frame.read reference).isSome := by
  obtain ⟨buf,cb,nb,inv⟩ := before
  have effects := Proofs.UfReceiverMetadata.call_effect fuel s out layout op ret inv.ok.strict actual
  intro reference
  exact read_isSome s out reference effects inv.ok.valid
    (represents_valid out layout vec nextCount nextRank after)

theorem actual_calls_reads (fuels : List Nat) (ops : List Operation) (s out : NState) (layout : Layout)
    (answers : List Int)
    (before : s.frame.state.wellFormed = true) (after : out.frame.state.wellFormed = true)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : runCalls fuels ops s layout = .finished (out,answers)) :
    ∀ reference, (out.frame.read reference).isSome = (s.frame.read reference).isSome := by
  have effects := Proofs.UfReceiverMetadata.actual_calls fuels ops s layout out answers contexts actual
  intro reference
  exact read_isSome s out reference effects before after

theorem calls_work_reads (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧ CallEffects s out ∧
      ∀ reference, (out.frame.read reference).isSome = (s.frame.read reference).isSome := by
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,effects⟩ :=
    Proofs.UfReceiverMetadata.calls_work_effects ops s layout ps count rank represented allowed
  refine ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,effects,?_⟩
  intro reference
  exact read_isSome s out reference effects
    (represents_valid s layout ps count rank represented.1)
    (represents_valid out layout vec nextCount nextRank strong.1)

end Proofs.UfReceiverReferences
