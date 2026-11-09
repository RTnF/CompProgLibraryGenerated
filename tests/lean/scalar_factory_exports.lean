namespace FactoryExportAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open FactoryPairObject
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def observed (outcome : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int) (slots : List Nat) : Bool :=
  match outcome with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = slots ∧ state.scalars.work ≤ 400 ∧ state.peak ≤ 150)
  | _ => false

theorem complete_factory_result_exports_all_fields : observed
    (Pair_factory_make_exportViewFuel 100 empty [] false) [14,6] [0,1] = true := by decide +kernel

theorem factory_parameters_flow_through_the_complete_object : observed
    (Pair_factory_from_exportViewFuel 100 empty [.value (.literal s64 7),.value (.literal i32 8)] false)
    [26,10] [0,1] = true := by decide +kernel

theorem negative_fields_are_not_restricted : observed
    (Pair_factory_from_exportViewFuel 100 empty [.value (.literal s64 3),.value (.literal i32 (-4))] false)
    [6,-2] [0,1] = true := by decide +kernel

theorem const_factory_target_keeps_field_permissions :
    (match Pair_factory_make_exportViewFuel 100 empty [] true with
     | .finished (state,_) => state.scalars.bindings.map (·.writable) == [false,false]
     | _ => false) = true := by decide +kernel

def caller : NState := ⟨⟨[⟨s64,55⟩],[⟨0,true⟩],0,0,1⟩,empty.frame,[.scalar 0],0,0⟩
theorem factory_export_preserves_caller_prefix : observed
    (Pair_factory_make_exportViewFuel 100 caller [] false) [55,14,6] [1,2] = true := by decide +kernel

theorem failed_returned_object_is_not_exported :
    Pair_factory_bad_exportViewFuel 100 empty [] false = .fault := by decide +kernel

theorem failing_parameterized_factory_is_not_exported :
    Pair_factory_from_exportViewFuel 100 empty [.value (.literal s64 3),.value (.literal i32 (-2))] false = .fault := by decide +kernel

def copyResult : Option NState := do
  let (state,object) ← match Pair_factory_make_exportViewFuel 100 empty [] true with
    | .finished pair => some pair
    | _ => none
  let (next,target) ← match copyFuel 40 state object false with
    | .finished pair => some pair
    | _ => none
  let a ← (NStmt.assign target.scalarSlots[0]! s64 (.literal s64 23)).run next
  let b ← (NStmt.assign target.scalarSlots[1]! i32 (.literal i32 (-4))).run a.state
  pure b.state

theorem copy_from_const_factory_result_preserves_original :
    copyResult.map (fun state => state.scalars.memory.map (·.value)) = some [14,6,23,-4] := by decide +kernel

def expired : Option NState := do
  let (state,_) ← match Pair_factory_make_exportViewFuel 100 {empty with scope:=1} [] false with
    | .finished pair => some pair
    | _ => none
  empty.leave state none

theorem factory_fields_expire_at_the_enclosing_scope :
    expired.map (fun state => state.scalarCell 0 s64) = some none := by decide +kernel
theorem unused_constructor_argument_is_still_evaluated :
    Pair_factory_unused_exportViewFuel 100 empty [] false = .fault := by decide +kernel
end FactoryExportAudit
