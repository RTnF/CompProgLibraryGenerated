namespace ConstRecordMemberAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open ConstBoxResult
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller : NState :=
  ⟨⟨[⟨s64,3⟩,⟨i32,1⟩,⟨s64,7⟩,⟨i32,4⟩],[⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩],0,0,4⟩,
    empty.frame,[.scalar 0,.scalar 1,.scalar 2,.scalar 3],0,4⟩
def observed (o : Proofs.CppLoop.Outcome (NState × ObjectRef)) (flags : List Bool) : Bool :=
  match o with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = [3,1,7,4,12,4] ∧
      object.vectorSlots = [] ∧ object.scalarSlots = [4,5] ∧ state.scalars.bindings.map (·.writable) = flags)
  | _ => false

theorem const_noexcept_receiver_accepts_readonly_fields : observed
    (Box_factory_receiver0_apply_exportObjectsFuel 100 caller [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false)
    [false,false,false,false,true,true] = true := by decide +kernel

theorem const_result_keeps_receiver_and_argument_unchanged : observed
    (Box_factory_receiver0_apply_exportObjectsFuel 100 caller [⟨[],[0,1]⟩,⟨[],[2,3]⟩] true)
    [false,false,false,false,false,false] = true := by decide +kernel

theorem const_member_rejects_future_argument_slot :
    Box_factory_receiver0_apply_exportObjectsFuel 100 caller [⟨[],[0,1]⟩,⟨[],[2,4]⟩] false = .fault := by decide +kernel
end ConstRecordMemberAudit
