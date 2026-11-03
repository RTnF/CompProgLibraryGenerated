import Proofs.CppPrepareTarget
import Proofs.CppFixedCall
import Proofs.UfReceiverMetadata

namespace Proofs.UfReceiverValues
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver Proofs.CppCallFrame
open Proofs.DoublingNested (i32)

def Selected (s : NState) (layout : Layout) : Prop :=
  ∃ binding : Proofs.CppNestedVectorBindings.Binding,
    s.vectorSlot layout.vectorSlot = some layout.vectorBinding ∧
    s.frame.bindings[layout.vectorBinding]? = some binding ∧ binding.owner = layout.owner

theorem Selected.after {s t : NState} {layout : Layout} (selected : Selected s layout)
    (effects : CallEffects s t) : Selected t layout := by
  obtain ⟨binding,slot,found,owner⟩ := selected
  refine ⟨binding,?_,?_,owner⟩
  · simpa only [NState.vectorSlot,effects.slots] using slot
  · rw [effects.vectorBindings]; exact found

theorem represents_selected (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) : Selected s layout := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  exact ⟨_,inv.ok.slot,inv.ok.binding,rfl⟩

theorem body_allowed (op : Operation) : Proofs.CppFixedRun.Allowed op.program.body = true := by
  cases op <;> simp only [Operation.program] <;> decide +kernel

theorem prepared_target (s init : NState) (layout : Layout) (op : Operation)
    (selected : Selected s layout)
    (actual : prepare s op.program.parameters (arguments layout++op.extra) = some init) :
    Proofs.CppFixedWrite.Target init layout.owner := by
  obtain ⟨binding,slot,found,owner⟩ := selected
  rw [← owner]
  cases op <;>
    exact Proofs.CppPrepareTarget.prepare_target s init i32 true _ _ layout.vectorSlot layout.vectorBinding binding slot found actual

theorem call_values (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
    (selected : Selected s layout)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : call fuel s layout op = .finished (out,ret)) :
    ∀ owner, owner ≠ layout.owner → out.frame.state.storage.lookup owner = s.frame.state.storage.lookup owner := by
  exact Proofs.CppFixedCall.call_values op.program fuel s out (arguments layout++op.extra) ret
    (Proofs.UfReceiverMetadata.scalar_type op) layout.owner (Proofs.UfReceiverMetadata.scalar_result op)
    (body_allowed op) (fun init prep => prepared_target s init layout op selected prep) contexts actual

theorem actual_calls (fuels : List Nat) (ops : List Operation) (s : NState) (layout : Layout)
    (out : NState) (answers : List Int) (selected : Selected s layout)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : runCalls fuels ops s layout = .finished (out,answers)) :
    ∀ owner, owner ≠ layout.owner → out.frame.state.storage.lookup owner = s.frame.state.storage.lookup owner := by
  induction ops generalizing fuels s out answers with
  | nil =>
    cases fuels with
    | nil =>
      have eq := congrArg Prod.fst (Outcome.finished.inj actual)
      change s = out at eq
      subst out
      exact fun _ _ => rfl
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
        have head := call_values fuel s middle layout op ret selected contexts ran
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
            have tail := ih fuels middle final rest (selected.after metadata) (metadata.contexts contexts) tailRun
            exact fun owner different => (tail owner different).trans (head owner different)

theorem calls_work_values (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧ CallEffects s out ∧
      ∀ owner, owner ≠ layout.owner → out.frame.state.storage.lookup owner = s.frame.state.storage.lookup owner := by
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,effects⟩ :=
    Proofs.UfReceiverMetadata.calls_work_effects ops s layout ps count rank represented allowed
  have selected := represents_selected s layout ps count rank represented.1
  obtain ⟨buf,cb,nb,inv⟩ := represented.1
  exact ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,effects,
    actual_calls fuels ops s layout out answers selected inv.ok.strict ran⟩


theorem actual_calls_reads (fuels : List Nat) (ops : List Operation) (s : NState) (layout : Layout)
    (out : NState) (answers : List Int) (selected : Selected s layout)
    (oldValid : s.frame.state.wellFormed = true) (newValid : out.frame.state.wellFormed = true)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : runCalls fuels ops s layout = .finished (out,answers)) :
    ∀ reference : Proofs.CppNestedVectorBindings.Reference, reference.address.owner ≠ layout.owner →
      out.frame.read reference = s.frame.read reference := by
  have effects := Proofs.UfReceiverMetadata.actual_calls fuels ops s layout out answers contexts actual
  have lookups := actual_calls fuels ops s layout out answers selected contexts actual
  exact Proofs.CppFixedCall.read_other s out layout.owner effects oldValid newValid lookups

theorem calls_work_reads (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧ CallEffects s out ∧
      (∀ owner, owner ≠ layout.owner → out.frame.state.storage.lookup owner = s.frame.state.storage.lookup owner) ∧
      ∀ reference : Proofs.CppNestedVectorBindings.Reference, reference.address.owner ≠ layout.owner →
        out.frame.read reference = s.frame.read reference := by
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,effects,lookups⟩ :=
    calls_work_values ops s layout ps count rank represented allowed
  obtain ⟨oldBuffer,oldCount,oldN,oldInv⟩ := represented.1
  obtain ⟨newBuffer,newCount,newN,newInv⟩ := strong.1
  exact ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,effects,lookups,
    Proofs.CppFixedCall.read_other s out layout.owner effects oldInv.ok.valid newInv.ok.valid lookups⟩

end Proofs.UfReceiverValues
