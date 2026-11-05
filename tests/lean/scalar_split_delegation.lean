namespace CaseChecks
open Proofs.CppNestedProgram Proofs.CppNestedCall
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 def observed (program : NProgram) (args : List NArgument) (expected : Int) : Bool :=
   match program.callFuel 20 empty args with
   | .finished (state,.scalar value) => decide (value = expected ∧ state.scalars.memory = [] ∧
       state.slots = [] ∧ state.frame = empty.frame ∧ state.scope = 0 ∧
       state.scalars.work ≤ 40 ∧ state.peak ≤ 20)
   | _ => false
theorem check_0 : observed Case_literal.Parcel_new1_left [] 11 = true := by decide +kernel
theorem check_1 : observed Case_literal.Parcel_new1_right [] 17 = true := by decide +kernel
theorem check_2 : observed Case_changed.Parcel_new1_left [] 13 = true := by decide +kernel
theorem check_3 : observed Case_changed.Parcel_new1_right [] 19 = true := by decide +kernel
theorem check_4 : observed Case_renamed.Bundle_new1_first [] 11 = true := by decide +kernel
theorem check_5 : observed Case_renamed.Bundle_new1_second [] 17 = true := by decide +kernel
theorem check_6 : observed Case_namespace.Parcel_new1_left [] 11 = true := by decide +kernel
theorem check_7 : observed Case_namespace.Parcel_new1_right [] 17 = true := by decide +kernel
theorem check_8 : observed Case_triple.Parcel_new1_left [] 11 = true := by decide +kernel
theorem check_9 : observed Case_triple.Parcel_new1_right [] 17 = true := by decide +kernel
theorem check_10 : observed Case_triple.Parcel_new1_tail [] 23 = true := by decide +kernel
theorem check_11 : observed Case_mixed.Parcel_new1_left [] 11 = true := by decide +kernel
theorem check_12 : observed Case_mixed.Parcel_new1_right [] 17 = true := by decide +kernel
theorem check_13 : observed Case_literal.Parcel_new0_left [.value (.literal ⟨64,true,false⟩ 3),.value (.literal ⟨64,true,false⟩ 8)] 3 = true := by decide +kernel
theorem check_14 : observed Case_literal.Parcel_new0_right [.value (.literal ⟨64,true,false⟩ 3),.value (.literal ⟨64,true,false⟩ 8)] 8 = true := by decide +kernel
end CaseChecks
