namespace OriginalValueAddAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open OriginalValueAdd
abbrev s64 : Ty := ⟨64,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller (x y : Int) : NState :=
  ⟨⟨[⟨s64,x⟩,⟨s64,y⟩],[⟨0,false⟩,⟨1,false⟩],0,0,2⟩,empty.frame,[.scalar 0,.scalar 1],0,2⟩
def observed (o : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int)
    (slots : List Nat) (flags : List Bool) : Bool :=
  match o with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = slots ∧
      state.scalars.bindings.map (·.writable) = flags ∧ state.scalars.work ≤ 100 ∧ state.peak ≤ 100)
  | _ => false

theorem both_parameters_are_value_snapshots : MemberFactory.objectArguments (caller 7 2)
    [(true,[(s64,true)]),(true,[(s64,true)])] [⟨[],[0]⟩,⟨[],[1]⟩] =
    some [.value (.literal s64 7),.value (.literal s64 2)] := rfl

theorem compose_returns_whole_record : observed
    (RangeAdd_factory_compose_exportObjectsFuel 100 (caller 7 2) [⟨[],[0]⟩,⟨[],[1]⟩] false)
    [7,2,9] [2] [false,false,true] = true := by decide +kernel

theorem aliases_are_copied_independently : observed
    (RangeAdd_factory_compose_exportObjectsFuel 100 (caller 7 2) [⟨[],[0]⟩,⟨[],[0]⟩] false)
    [7,2,14] [2] [false,false,true] = true := by decide +kernel

theorem const_result_keeps_inputs_readonly : observed
    (RangeAdd_factory_compose_exportObjectsFuel 100 (caller 7 2) [⟨[],[0]⟩,⟨[],[1]⟩] true)
    [7,2,9] [2] [false,false,false] = true := by decide +kernel

theorem id_returns_whole_record : observed
    (RangeAdd_factory_id_exportViewFuel 100 empty [] false) [0] [0] [true] = true := by decide +kernel

theorem future_source_is_rejected_before_allocation :
    RangeAdd_factory_compose_exportObjectsFuel 100 (caller 7 2) [⟨[],[0]⟩,⟨[],[2]⟩] false = .fault := by decide +kernel

theorem addition_overflow_is_fault :
    RangeAdd_factory_compose_exportObjectsFuel 100 (caller 9223372036854775807 2)
      [⟨[],[0]⟩,⟨[],[1]⟩] false = .fault := by decide +kernel

theorem missing_value_field_is_rejected :
    RangeAdd_factory_compose_exportObjectsFuel 100 (caller 7 2) [⟨[],[]⟩,⟨[],[1]⟩] false = .fault := by decide +kernel
end OriginalValueAddAudit
