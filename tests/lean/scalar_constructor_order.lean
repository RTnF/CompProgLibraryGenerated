namespace ConstructorOrderAudit
open Proofs.CppNestedProgram Proofs.CppNestedCall
def caller : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def observed (program : NProgram) (expected : Int) : Bool :=
  match program.callFuel 100 caller [] with
  | .finished (state,.scalar value) => decide (value = expected ∧ state.scalars.memory = [] ∧
      state.slots = [] ∧ state.scalars.work ≤ 100 ∧ state.peak ≤ 32)
  | _ => false

theorem parameter_write : observed Order_parameter_write.Holder_new1 1 = true := by decide +kernel
theorem field_write : observed Order_field_write.Holder_new1 2 = true := by decide +kernel
theorem both_writes : observed Order_both_writes.Holder_new1 3 = true := by decide +kernel
theorem body_constructor : observed Order_body_constructor.Holder_new1 1 = true := by decide +kernel
theorem initializer_call : observed Order_initializer_call.Holder_new1 2 = true := by decide +kernel
end ConstructorOrderAudit
