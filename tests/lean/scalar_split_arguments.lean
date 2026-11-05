namespace SplitArgumentAudit
open Proofs.CppNestedProgram Proofs.CppNestedCall
def caller : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def observed (program : NProgram) (expected : Int) : Bool :=
  match program.callFuel 100 caller [.value (.literal ⟨64,true,false⟩ 1)] with
  | .finished (state,.scalar value) => decide (value = expected ∧ state.scalars.memory = [] ∧
      state.slots = [] ∧ state.scalars.work ≤ 100 ∧ state.peak ≤ 32)
  | _ => false
def zeroDivision (program : NProgram) : Bool :=
  match program.callFuel 100 caller [.value (.literal ⟨64,true,false⟩ 0)] with
  | .fault => true
  | _ => false

theorem left_ok : observed UnusedSplitArgument.Parcel_e_left 11 = true := by decide +kernel
theorem right_ok : observed UnusedSplitArgument.Parcel_e_right 17 = true := by decide +kernel
theorem left_zero_division : zeroDivision UnusedSplitArgument.Parcel_e_left = true := by decide +kernel
theorem right_zero_division : zeroDivision UnusedSplitArgument.Parcel_e_right = true := by decide +kernel
end SplitArgumentAudit
