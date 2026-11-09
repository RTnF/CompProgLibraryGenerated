namespace DelegationBodyAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open DelegatedPairObject
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def observed (outcome : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int) (slots : List Nat) : Bool :=
  match outcome with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = slots ∧ state.scalars.work ≤ 400 ∧ state.peak ≤ 100)
  | _ => false

theorem direct_body_uses_prebody_parameter_values : observed
    (Pair_construct0_exportViewFuel 60 empty [.value (.literal s64 3),.value (.literal i32 4)] false)
    [13,5] [0,1] = true := by decide +kernel

theorem factory_body_precedes_move_and_outer_body : observed
    (Pair_construct1_exportViewFuel 60 empty [] false) [113,1005] [0,1] = true := by decide +kernel

theorem chained_delegation_preserves_factory_and_both_bodies : observed
    (Pair_construct2_exportViewFuel 60 empty [.value (.literal ⟨1,false,true⟩ 1)] false)
    [113,11005] [0,1] = true := by decide +kernel

def caller : NState := ⟨⟨[⟨s64,55⟩],[⟨0,true⟩],0,0,1⟩,empty.frame,[.scalar 0],0,0⟩
theorem chained_delegation_keeps_existing_caller_prefix : observed
    (Pair_construct2_exportViewFuel 60 caller [.value (.literal ⟨1,false,true⟩ 0)] false)
    [55,113,11005] [1,2] = true := by decide +kernel

theorem chained_call_retires_all_temporaries :
    (match Pair_construct2.callFuel 60 empty [.value (.literal ⟨1,false,true⟩ 1)] with
     | .finished (state,.unit) => decide (state.scalars.memory = [] ∧ state.slots = [] ∧
         state.scalars.work ≤ 400 ∧ state.peak ≤ 100)
     | _ => false) = true := by decide +kernel
end DelegationBodyAudit
