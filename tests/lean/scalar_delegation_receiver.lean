namespace DelegationReceiverAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open ReceiverPairObject
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def observed (outcome : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int) (slots : List Nat) : Bool :=
  match outcome with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = slots ∧ state.scalars.work ≤ 400 ∧ state.peak ≤ 150)
  | _ => false

theorem direct_nested_calls_share_the_actual_fields : observed
    (Pair_construct0_exportViewFuel 100 empty [.value (.literal s64 3),.value (.literal i32 4)] false)
    [14,6] [0,1] = true := by decide +kernel

theorem factory_calls_mutate_the_temporary_before_outer_fields : observed
    (Pair_construct1_exportViewFuel 100 empty [] false) [114,1006] [0,1] = true := by decide +kernel

theorem const_destination_retains_permissions :
    (match Pair_construct1_exportViewFuel 100 empty [] true with
     | .finished (state,_) => state.scalars.bindings.map (·.writable) == [false,false]
     | _ => false) = true := by decide +kernel

def caller : NState := ⟨⟨[⟨s64,55⟩],[⟨0,true⟩],0,0,1⟩,empty.frame,[.scalar 0],0,0⟩
theorem temporary_calls_preserve_existing_caller_storage : observed
    (Pair_construct1_exportViewFuel 100 caller [] false) [55,114,1006] [1,2] = true := by decide +kernel

theorem unit_call_retires_temporary_receiver_fields :
    (match Pair_construct1.callFuel 100 caller [] with
     | .finished (state,.unit) => decide (state.scalars.memory = caller.scalars.memory ∧ state.slots = caller.slots)
     | _ => false) = true := by decide +kernel

theorem discarded_return_still_faults_in_temporary_receiver :
    Pair_construct2_exportViewFuel 100 empty [.value (.literal ⟨1,false,true⟩ 1)] false = .fault := by decide +kernel

theorem discarded_return_still_faults_in_direct_constructor :
    Pair_construct0_exportViewFuel 100 empty [.value (.literal s64 3),.value (.literal i32 (-2))] false = .fault := by decide +kernel

theorem failed_temporary_cannot_be_exported_as_a_unit_call :
    Pair_construct2.callFuel 100 caller [.value (.literal ⟨1,false,true⟩ 0)] = .fault := by decide +kernel
end DelegationReceiverAudit
