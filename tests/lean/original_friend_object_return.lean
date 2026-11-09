namespace FriendObjectReturnAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open OriginalFriendSumObject
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller (x n y m : Int) : NState :=
  ⟨⟨[⟨s64,x⟩,⟨i32,n⟩,⟨s64,y⟩,⟨i32,m⟩],[⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩],0,0,4⟩,
    empty.frame,[.scalar 0,.scalar 1,.scalar 2,.scalar 3],0,4⟩
def a : ObjectRef := ⟨[],[0,1]⟩
def b : ObjectRef := ⟨[],[2,3]⟩
def observed (outcome : Proofs.CppLoop.Outcome (NState × ObjectRef))
    (values : List Int) (permissions : List Bool) : Bool :=
  match outcome with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = [4,5] ∧
      state.scalars.bindings.map (·.writable) = permissions ∧ state.scalars.work ≤ 200 ∧ state.peak ≤ 100)
  | _ => false

theorem complete_friend_result_and_both_inputs_are_preserved : observed
    (RangeSum_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [a,b] false)
    [7,-4,2,1,9,-3] [false,false,false,false,true,true] = true := by decide +kernel

theorem aliased_const_reference_arguments_remain_valid : observed
    (RangeSum_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [a,a] false)
    [7,-4,2,1,14,-8] [false,false,false,false,true,true] = true := by decide +kernel

theorem const_result_preserves_all_field_permissions : observed
    (RangeSum_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [a,b] true)
    [7,-4,2,1,9,-3] [false,false,false,false,false,false] = true := by decide +kernel

theorem overflow_of_first_result_field_rejects_export :
    RangeSum_factory_op_exportObjectsFuel 100 (caller 9223372036854775807 0 2 1) [a,b] false = .fault := by decide +kernel

theorem overflow_of_second_result_field_rejects_export :
    RangeSum_factory_op_exportObjectsFuel 100 (caller 7 2147483647 2 1) [a,b] false = .fault := by decide +kernel

theorem incomplete_record_is_rejected :
    RangeSum_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [⟨[],[0]⟩,b] false = .fault := by decide +kernel

theorem wrong_field_types_are_rejected :
    RangeSum_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [⟨[],[1,0]⟩,b] false = .fault := by decide +kernel

theorem future_destination_slots_cannot_be_used_as_inputs :
    RangeSum_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [a,⟨[],[4,5]⟩] false = .fault := by decide +kernel

theorem unexpected_vector_fields_are_rejected :
    RangeSum_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [⟨[0],[0,1]⟩,b] false = .fault := by decide +kernel

theorem extra_objects_are_rejected :
    RangeSum_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [a,b,a] false = .fault := by decide +kernel

theorem expired_object_fields_are_rejected :
    RangeSum_factory_op_exportObjectsFuel 100 empty [a,b] false = .fault := by decide +kernel
end FriendObjectReturnAudit
