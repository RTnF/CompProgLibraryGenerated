namespace DelegatingObjectAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open OriginalRangeSumObject
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def built (targetConst : Bool) : Option (NState × ObjectRef) :=
  match RangeSum_construct1_exportViewFuel 40 empty [] targetConst with
  | .finished pair => some pair
  | _ => none

theorem destination_fields_follow_complete_factory_storage :
    OriginalRangeSumObject.Stages.RangeSum_construct1.scalarFields = [⟨4,s64⟩,⟨5,i32⟩] := rfl

theorem default_program_materializes_once_and_moves_all_fields :
    RangeSum_construct1 = ⟨[],.unit,
      .sequence (.primitive (.declare s64 true (.cast s64 (.literal i32 0))))
        (.sequence (.primitive (.declare i32 true (.literal i32 0)))
          (.sequence (.primitive (.declare s64 true (.variable s64 0)))
            (.sequence (.primitive (.declare i32 true (.variable i32 1)))
              (.sequence (.scope (.primitive .skip))
                (.sequence (.primitive (.declare s64 true (.variable s64 2)))
                  (.sequence (.primitive (.declare i32 true (.variable i32 3))) (.primitive .skip)))))))⟩ := rfl

theorem default_exports_only_destination_fields :
    (built false).map (fun p => (p.1.scalars.memory.map (·.value),p.1.scalars.memory.map (·.type),p.2.scalarSlots)) =
      some ([0,0],[s64,i32],[0,1]) := by decide +kernel

theorem const_destination_keeps_declared_types_and_permissions :
    (built true).map (fun p => p.1.scalars.bindings.map (·.writable)) = some [false,false] := by decide +kernel

theorem direct_constructor_keeps_negative_size :
    (match RangeSum_construct0_exportViewFuel 40 empty [.value (.literal s64 7),.value (.literal i32 (-4))] false with
     | .finished (state,object) => decide (state.scalars.memory.map (·.value) = [7,-4] ∧ object.scalarSlots = [0,1])
     | _ => false) = true := by decide +kernel

theorem unexported_call_retires_all_temporary_fields :
    (match RangeSum_construct1.callFuel 40 empty [] with
     | .finished (state,.unit) => decide (state.scalars.memory = [] ∧ state.slots = [] ∧
         state.scalars.work ≤ 300 ∧ state.peak ≤ 100)
     | _ => false) = true := by decide +kernel

def modifiedCopy : Option NState := do
  let (state,object) ← built true
  let (next,target) ← match copyFuel 30 state object false with
    | .finished pair => some pair
    | _ => none
  let a ← (NStmt.assign target.scalarSlots[0]! s64 (.literal s64 23)).run next
  let b ← (NStmt.assign target.scalarSlots[1]! i32 (.literal i32 (-4))).run a.state
  pure b.state

theorem copy_from_const_is_independent_for_both_fields :
    modifiedCopy.map (fun state => (state.scalars.memory.map (·.value),state.scalars.bindings.map (·.writable))) =
      some ([0,0,23,-4],[false,false,true,true]) := by decide +kernel
end DelegatingObjectAudit
