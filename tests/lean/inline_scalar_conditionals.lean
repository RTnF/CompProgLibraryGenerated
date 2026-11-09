namespace ConditionalCallAudit
open Proofs.CppNestedProgram Proofs.CppNestedCall

def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def observed (program : NProgram) (args : List NArgument) (expected : Int) : Bool :=
  match program.callFuel 100 empty args with
  | .finished (state,.scalar value) => decide (value = expected ∧ state.scalars.memory = [] ∧
      state.slots = [] ∧ state.scalars.work ≤ 300 ∧ state.peak ≤ 100)
  | _ => false

def boolean (v : Int) : NArgument := .value (.literal ⟨1,false,true⟩ v)
def integer (v : Int) : NArgument := .value (.literal ⟨64,true,false⟩ v)
theorem nested_tt : observed InlineConditionals.nested [boolean 1,boolean 1] 122 = true := by decide +kernel
theorem nested_tf : observed InlineConditionals.nested [boolean 1,boolean 0] 122 = true := by decide +kernel
theorem nested_ft : observed InlineConditionals.nested [boolean 0,boolean 1] 233 = true := by decide +kernel
theorem nested_ff : observed InlineConditionals.nested [boolean 0,boolean 0] 244 = true := by decide +kernel
theorem condition_true : observed InlineConditionals.condition_only [boolean 1] 107 = true := by decide +kernel
theorem condition_false : observed InlineConditionals.condition_only [boolean 0] 108 = true := by decide +kernel
theorem skip_zero_division : observed InlineConditionals.selected_division [boolean 0,integer 0] 17 = true := by decide +kernel
theorem take_division : observed InlineConditionals.selected_division [boolean 1,integer 2] 3 = true := by decide +kernel
theorem selected_zero_division_fails :
    (match InlineConditionals.selected_division.callFuel 100 empty [boolean 1,integer 0] with
     | .fault => true
     | _ => false) = true := by decide +kernel
theorem unused_division_value_still_evaluates :
    observed InlineConditionals.discarded_division [integer 2] 17 = true := by decide +kernel
theorem unused_division_cannot_hide_zero_division :
    InlineConditionals.discarded_division.callFuel 100 empty [integer 0] = .fault := by decide +kernel
theorem unused_increment_value_still_evaluates :
    observed InlineConditionals.discarded_overflow [integer 0] 19 = true := by decide +kernel
theorem unused_increment_cannot_hide_signed_overflow :
    InlineConditionals.discarded_overflow.callFuel 100 empty [integer 9223372036854775807] = .fault := by decide +kernel
end ConditionalCallAudit
