namespace RecordCopyReturnAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open CopyChoiceObject
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev bl : Ty := ⟨1,false,true⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller : NState :=
  ⟨⟨[⟨s64,22⟩,⟨bl,1⟩],[⟨0,false⟩,⟨1,false⟩],0,0,2⟩,empty.frame,[.scalar 0,.scalar 1],0,2⟩
def observed (o : Proofs.CppLoop.Outcome (NState × ObjectRef)) (flags : List Bool) : Bool :=
  match o with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = [22,1,22,1] ∧
      object.vectorSlots = [] ∧ object.scalarSlots = [2,3] ∧
      state.scalars.bindings.map (·.writable) = flags)
  | _ => false

theorem const_reference_copies_both_fields : observed
    (Choice_factory_copy_exportObjectsFuel 100 caller [⟨[],[0,1]⟩] false)
    [false,false,true,true] = true := by decide +kernel

theorem value_parameter_move_copies_both_fields : observed
    (Choice_factory_moved_exportObjectsFuel 100 caller [⟨[],[0,1]⟩] false)
    [false,false,true,true] = true := by decide +kernel

theorem const_result_retains_noop_value : observed
    (Choice_factory_copy_exportObjectsFuel 100 caller [⟨[],[0,1]⟩] true)
    [false,false,false,false] = true := by decide +kernel

theorem future_move_source_is_rejected :
    Choice_factory_moved_exportObjectsFuel 100 caller [⟨[],[0,2]⟩] false = .fault := by decide +kernel
end RecordCopyReturnAudit
