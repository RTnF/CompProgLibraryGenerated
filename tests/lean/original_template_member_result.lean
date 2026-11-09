namespace TemplateMemberResultAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open SelectedTemplateMember
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev bl : Ty := ⟨1,false,true⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller (v f x : Int) : NState :=
  ⟨⟨[⟨s64,v⟩,⟨bl,f⟩,⟨s64,x⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,false⟩],0,0,3⟩,
    empty.frame,[.scalar 0,.scalar 1,.scalar 2],0,3⟩
def observed (o : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int) (flags : List Bool) : Bool :=
  match o with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = [3] ∧
      state.scalars.bindings.map (·.writable) = flags ∧ state.scalars.work ≤ 300 ∧ state.peak ≤ 200)
  | _ => false

theorem original_template_member_returns_record : observed
    (applyExport 100 (caller 3 0 7) [⟨[],receiverSlots⟩,⟨[],[2]⟩] false)
    [3,0,7,expected 3 0 7] [true,true,false,true] = true := by decide +kernel

theorem negative_values_preserve_generic_record_result : observed
    (applyExport 100 (caller (-3) 0 (-7)) [⟨[],receiverSlots⟩,⟨[],[2]⟩] false)
    [-3,0,-7,expected (-3) 0 (-7)] [true,true,false,true] = true := by decide +kernel

theorem noop_result_is_copied_without_value_reconstruction : observed
    (applyExport 100 (caller 3 1 7) [⟨[],receiverSlots⟩,⟨[],[2]⟩] false)
    [3,1,7,expected 3 1 7] [true,true,false,true] = true := by decide +kernel

theorem const_destination_restricts_new_field : observed
    (applyExport 100 (caller 3 0 7) [⟨[],receiverSlots⟩,⟨[],[2]⟩] true)
    [3,0,7,expected 3 0 7] [true,true,false,false] = true := by decide +kernel

theorem future_argument_is_rejected :
    applyExport 100 (caller 3 0 7) [⟨[],receiverSlots⟩,⟨[],[3]⟩] false = .fault := by decide +kernel

theorem readonly_receiver_is_rejected :
    let old := caller 3 0 7
    let readonly := {old with scalars := {old.scalars with bindings := [⟨0,false⟩,⟨1,false⟩,⟨2,false⟩]}}
    applyExport 100 readonly [⟨[],receiverSlots⟩,⟨[],[2]⟩] false = .fault := by decide +kernel

theorem addition_overflow_or_direct_assignment :
    (if isSet then observed
      (applyExport 100 (caller 9223372036854775807 0 1) [⟨[],receiverSlots⟩,⟨[],[2]⟩] false)
      [9223372036854775807,0,1,9223372036854775807] [true,true,false,true]
    else decide (applyExport 100 (caller 9223372036854775807 0 1)
      [⟨[],receiverSlots⟩,⟨[],[2]⟩] false = .fault)) = true := by decide +kernel

theorem identity_preserves_input : observed
    (applyExport 100 (caller 0 1 7) [⟨[],receiverSlots⟩,⟨[],[2]⟩] false)
    [0,1,7,7] [true,true,false,true] = true := by decide +kernel
end TemplateMemberResultAudit
