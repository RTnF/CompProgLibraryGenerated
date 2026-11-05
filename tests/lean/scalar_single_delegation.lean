namespace DelegationAudit
open Proofs.CppNestedProgram Proofs.CppNestedCall

def caller : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def observed (program : NProgram) : Bool :=
  match program.callFuel 20 caller [] with
  | .finished (state,.scalar value) => decide (value = 7 ∧ state.scalars.memory = [] ∧ state.slots = [] ∧
      state.scalars.work ≤ 40 ∧ state.peak ≤ 12)
  | _ => false

theorem factory : observed DelegationCandidate.ScalarIdentity_e = true := by decide +kernel

theorem delegated : observed DelegationCandidate.ScalarIdentity_new1 = true := by decide +kernel
end DelegationAudit
