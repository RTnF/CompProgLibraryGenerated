namespace MemberConstructorChoiceAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open SelectedConstructorChoice
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
abbrev bl : Ty := ⟨1,false,true⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller (v f : Int) : NState :=
  ⟨⟨[⟨s64,v⟩,⟨bl,f⟩,⟨s64,107⟩,⟨i32,5⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,false⟩,⟨3,false⟩],0,0,4⟩,
    empty.frame,[.scalar 0,.scalar 1,.scalar 2,.scalar 3],0,4⟩
def observed (o : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int) (flags : List Bool) : Bool :=
  match o with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = [4,5] ∧
      state.scalars.bindings.map (·.writable) = flags ∧ state.scalars.work ≤ 300 ∧ state.peak ≤ 200)
  | _ => false

theorem chosen_constructor_initializes_every_field : observed
    (applyExport 100 (caller 3 0) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false)
    [3,0,107,5,103,5] [true,true,false,false,true,true] = true := by decide +kernel

theorem unchosen_constructor_is_not_executed : observed
    (applyExport 100 (caller 9223372036854775807 1) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false)
    [9223372036854775807,1,107,5,107,5] [true,true,false,false,true,true] = true := by decide +kernel

theorem copied_record_is_not_reconstructed : observed
    (applyExport 100 (caller 3 1) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false)
    [3,1,107,5,107,5] [true,true,false,false,true,true] = true := by decide +kernel

theorem chosen_constructor_overflow_is_fault :
    applyExport 100 (caller 9223372036854775807 0) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] false = .fault := by decide +kernel

theorem const_result_preserves_source_permissions : observed
    (applyExport 100 (caller 3 0) [⟨[],[0,1]⟩,⟨[],[2,3]⟩] true)
    [3,0,107,5,103,5] [true,true,false,false,false,false] = true := by decide +kernel
end MemberConstructorChoiceAudit
