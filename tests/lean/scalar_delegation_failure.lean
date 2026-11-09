namespace DelegationFailureAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open FailurePairObject
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
theorem direct_valid_fields :
    (match Pair_construct0_exportViewFuel 40 empty [.value (.literal s64 11),.value (.literal i32 1)] false with
     | .finished (state,_) => state.scalars.memory.map (·.value) == [11,7]
     | _ => false) = true := by decide +kernel

theorem default_does_not_skip_failing_second_field :
    Pair_construct1_exportViewFuel 40 empty [] false = .fault := by decide +kernel

theorem unexported_default_also_rejects_failed_field :
    Pair_construct1.callFuel 40 empty [] = .fault := by decide +kernel

theorem direct_invalid_field_fails :
    Pair_construct0_exportViewFuel 40 empty [.value (.literal s64 11),.value (.literal i32 0)] false = .fault := by decide +kernel
end DelegationFailureAudit
