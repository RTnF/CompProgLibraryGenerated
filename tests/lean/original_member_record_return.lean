namespace OriginalMemberReturnAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open OriginalMemberResult SelectedMember
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev bl : Ty := ⟨1,false,true⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller (v f x n : Int) : NState :=
  ⟨⟨[⟨s64,v⟩,⟨bl,f⟩,⟨s64,x⟩,⟨i32,n⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,false⟩,⟨3,false⟩],0,0,4⟩,
    empty.frame,[.scalar 0,.scalar 1,.scalar 2,.scalar 3],0,4⟩
def readonlyCaller : NState :=
  {caller 3 0 7 4 with scalars := {(caller 3 0 7 4).scalars with bindings := [⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩]}}
def observed (o : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int) (flags : List Bool) : Bool :=
  match o with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = [4,5] ∧
      state.scalars.bindings.map (·.writable) = flags ∧ state.scalars.work ≤ 200 ∧ state.peak ≤ 150)
  | _ => false

theorem original_apply_returns_both_fields : observed
    (applyExport 100 (caller 3 0 7 4) [⟨[],receiverSlots⟩,⟨[],[2,3]⟩] false)
    [3,0,7,4,expected 3 0 7 4,4] [true,true,false,false,true,true] = true := by decide +kernel

theorem copied_argument_retains_negative_size : observed
    (applyExport 100 (caller 3 0 7 (-4)) [⟨[],receiverSlots⟩,⟨[],[2,3]⟩] false)
    [3,0,7,-4,expected 3 0 7 (-4),-4] [true,true,false,false,true,true] = true := by decide +kernel

theorem noop_preserves_source_value_when_declared : observed
    (applyExport 100 (caller 3 1 7 4) [⟨[],receiverSlots⟩,⟨[],[2,3]⟩] false)
    [3,1,7,4,expected 3 1 7 4,4] [true,true,false,false,true,true] = true := by decide +kernel

theorem const_destination_restricts_only_result : observed
    (applyExport 100 (caller 3 0 7 4) [⟨[],receiverSlots⟩,⟨[],[2,3]⟩] true)
    [3,0,7,4,expected 3 0 7 4,4] [true,true,false,false,false,false] = true := by decide +kernel

theorem readonly_receiver_is_rejected :
    applyExport 100 readonlyCaller [⟨[],receiverSlots⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem future_argument_field_is_rejected_before_copy :
    applyExport 100 (caller 3 0 7 4) [⟨[],receiverSlots⟩,⟨[],[2,4]⟩] false = .fault := by decide +kernel

theorem multiplication_overflow_is_fault :
    applyExport 100 (caller 9223372036854775807 0 7 2) [⟨[],receiverSlots⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem zero_size_does_not_overflow : observed
    (applyExport 100 (caller 9223372036854775807 0 7 0) [⟨[],receiverSlots⟩,⟨[],[2,3]⟩] false)
    [9223372036854775807,0,7,0,expected 9223372036854775807 0 7 0,0]
    [true,true,false,false,true,true] = true := by decide +kernel

theorem unused_receiver_noop_avoids_multiplication :
    (if isSet then observed
      (applyExport 100 (caller 9223372036854775807 1 7 2) [⟨[],receiverSlots⟩,⟨[],[2,3]⟩] false)
      [9223372036854775807,1,7,2,7,2] [true,true,false,false,true,true]
    else decide (applyExport 100 (caller 9223372036854775807 1 7 2)
      [⟨[],receiverSlots⟩,⟨[],[2,3]⟩] false = .fault)) = true := by decide +kernel
end OriginalMemberReturnAudit
