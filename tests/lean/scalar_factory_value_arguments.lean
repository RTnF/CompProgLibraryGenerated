namespace FactoryValueArgumentsAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open ValuePairObject
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller (x n y m : Int) : NState :=
  ⟨⟨[⟨s64,x⟩,⟨i32,n⟩,⟨s64,y⟩,⟨i32,m⟩],[⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩],0,0,4⟩,
    empty.frame,[.scalar 0,.scalar 1,.scalar 2,.scalar 3],0,4⟩
def observed (o : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int) (flags : List Bool) : Bool :=
  match o with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = [4,5] ∧
      state.scalars.bindings.map (·.writable) = flags ∧ state.scalars.work ≤ 100 ∧ state.peak ≤ 100)
  | _ => false

theorem values_are_snapshotted_before_prepare :
    MemberFactory.objectArguments (caller 7 (-4) 2 1)
      [(true,[(s64,true),(i32,true)]),(false,[(s64,false),(i32,false)])]
      [⟨[],[0,1]⟩,⟨[],[2,3]⟩] = some
      [.value (.literal s64 7),.value (.literal i32 (-4)),.scalarReference 2,.scalarReference 3] := rfl

theorem mixed_value_and_reference_return_complete_object : observed
    (Pair_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false)
    [7,-4,2,1,9,-3] [false,false,false,false,true,true] = true := by decide +kernel

theorem alias_inputs_keep_original_values : observed
    (Pair_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [⟨[],[0,1]⟩,⟨[],[0,1]⟩] false)
    [7,-4,2,1,14,-8] [false,false,false,false,true,true] = true := by decide +kernel

theorem const_destination_restricts_only_new_fields : observed
    (Pair_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] true)
    [7,-4,2,1,9,-3] [false,false,false,false,false,false] = true := by decide +kernel

theorem future_value_field_rejected_before_allocation :
    Pair_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [⟨[],[0,4]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem wrong_value_type_is_rejected :
    Pair_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [⟨[],[1,0]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem extra_vector_field_is_rejected :
    Pair_factory_op_exportObjectsFuel 100 (caller 7 (-4) 2 1) [⟨[0],[0,1]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem value_body_overflow_is_fault :
    Pair_factory_op_exportObjectsFuel 100 (caller 9223372036854775807 0 2 1)
      [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel
end FactoryValueArgumentsAudit
