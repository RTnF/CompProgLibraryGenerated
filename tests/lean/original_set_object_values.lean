namespace OriginalSetObjectAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open OriginalSetObject
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev bl : Ty := ⟨1,false,true⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller (x f y g : Int) : NState :=
  ⟨⟨[⟨s64,x⟩,⟨bl,f⟩,⟨s64,y⟩,⟨bl,g⟩],[⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩],0,0,4⟩,
    empty.frame,[.scalar 0,.scalar 1,.scalar 2,.scalar 3],0,4⟩
def observed (o : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int)
    (slots : List Nat) (flags : List Bool) : Bool :=
  match o with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = slots ∧
      state.scalars.bindings.map (·.writable) = flags ∧ state.scalars.work ≤ 300 ∧ state.peak ≤ 150)
  | _ => false

theorem snapshots_copy_both_fields : MemberFactory.objectArguments (caller 7 1 22 1)
    [(true,[(s64,true),(bl,true)]),(true,[(s64,true),(bl,true)])] [⟨[],[0,1]⟩,⟨[],[2,3]⟩] =
    some [.value (.literal s64 7),.value (.literal bl 1),.value (.literal s64 22),.value (.literal bl 1)] := rfl

theorem both_flags_and_values_are_selected_together :
    ([-7,22].all fun x => [0,1].all fun f => [-7,22].all fun y => [0,1].all fun g => observed
      (RangeSet_factory_compose_exportObjectsFuel 100 (caller x f y g) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false)
      [x,f,y,g,if f=1 then y else x,if f=1 then g else f] [4,5]
      [false,false,false,false,true,true]) = true := by decide +kernel

theorem copy_handles_extreme_values_without_arithmetic : observed
    (RangeSet_factory_compose_exportObjectsFuel 100
      (caller 9223372036854775807 1 (-9223372036854775808) 1) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false)
    [9223372036854775807,1,-9223372036854775808,1,-9223372036854775808,1] [4,5]
    [false,false,false,false,true,true] = true := by decide +kernel

theorem alias_inputs_remain_readonly : observed
    (RangeSet_factory_compose_exportObjectsFuel 100 (caller 7 1 22 0) [⟨[],[0,1]⟩,⟨[],[0,1]⟩] false)
    [7,1,22,0,7,1] [4,5] [false,false,false,false,true,true] = true := by decide +kernel

theorem const_destination_keeps_selected_flag : observed
    (RangeSet_factory_compose_exportObjectsFuel 100 (caller 7 1 22 1) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] true)
    [7,1,22,1,22,1] [4,5] [false,false,false,false,false,false] = true := by decide +kernel

theorem id_preserves_both_default_fields : observed
    (RangeSet_factory_id_exportViewFuel 100 empty [] false) [0,1] [0,1] [true,true] = true := by decide +kernel

theorem future_field_rejected_before_parameter_allocation :
    RangeSet_factory_compose_exportObjectsFuel 100 (caller 7 1 22 0) [⟨[],[0,4]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem wrong_field_type_is_rejected :
    RangeSet_factory_compose_exportObjectsFuel 100 (caller 7 1 22 0) [⟨[],[1,0]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem incomplete_object_is_rejected :
    RangeSet_factory_compose_exportObjectsFuel 100 (caller 7 1 22 0) [⟨[],[0]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem invalid_bool_value_is_rejected :
    RangeSet_factory_compose_exportObjectsFuel 100 (caller 7 2 22 0) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel
end OriginalSetObjectAudit
