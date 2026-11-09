namespace MemberPrefixUpdateAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open PrefixBoxResult
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller (v : Int) : NState :=
  ⟨⟨[⟨s64,v⟩,⟨i32,1⟩,⟨s64,7⟩,⟨i32,4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,false⟩,⟨3,false⟩],0,0,4⟩,
    empty.frame,[.scalar 0,.scalar 1,.scalar 2,.scalar 3],0,4⟩
def observed (o : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int)
    (slots : List Nat) (flags : List Bool) : Bool :=
  match o with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = slots ∧ state.scalars.bindings.map (·.writable) = flags)
  | _ => false

theorem receiver_updates_before_return_and_argument_copy_stays_private : observed
    (Box_factory_receiver0_apply_exportObjectsFuel 100 (caller 3) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false)
    [4,1,7,4,23,4] [4,5] [true,true,false,false,true,true] = true := by decide +kernel

theorem alias_uses_argument_snapshot_before_receiver_update : observed
    (Box_factory_receiver0_apply_exportObjectsFuel 100 (caller 3) [⟨[],[0,1]⟩,⟨[],[0,1]⟩] false)
    [4,1,7,4,7,1] [4,5] [true,true,false,false,true,true] = true := by decide +kernel

theorem const_result_preserves_updated_receiver_and_old_argument : observed
    (Box_factory_receiver0_apply_exportObjectsFuel 100 (caller 3) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] true)
    [4,1,7,4,23,4] [4,5] [true,true,false,false,false,false] = true := by decide +kernel

theorem prefix_overflow_is_fault :
    Box_factory_receiver0_apply_exportObjectsFuel 100 (caller 9223372036854775807)
      [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem future_argument_rejected_before_receiver_update :
    Box_factory_receiver0_apply_exportObjectsFuel 100 (caller 3) [⟨[],[0,1]⟩,⟨[],[2,4]⟩] false = .fault := by decide +kernel
end MemberPrefixUpdateAudit
