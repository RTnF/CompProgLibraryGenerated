namespace TemplateObjectAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open OriginalRangeSetObject

def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
abbrev s64 : Ty := ⟨64,true,false⟩
abbrev bl : Ty := ⟨1,false,true⟩
def built (targetConst : Bool) : Option (NState × ObjectRef) :=
  match RangeSet_construct0_exportViewFuel 20 empty [.value (.literal s64 7)] targetConst with
  | .finished pair => some pair
  | _ => none

def copied (sourceConst targetConst : Bool) : Option (NState × ObjectRef) := do
  let (state,object) ← built sourceConst
  match copyFuel 20 state object targetConst with
  | .finished pair => some pair
  | _ => none

def mutated (sourceConst : Bool) : Option NState := do
  let (state,object) ← copied sourceConst false
  let first ← (NStmt.assign object.scalarSlots[0]! s64 (.literal s64 11)).run state
  let second ← (NStmt.assign object.scalarSlots[1]! bl (.literal bl 1)).run first.state
  pure second.state

def scopedCopy (sourceConst : Bool) : Option NStep := do
  let (state,object) ← built sourceConst
  let fields ← copyFields object false
  match runFuel 30 (.scope (.sequence (MemberCopy.command fields)
    (.sequence (.primitive (.assign 2 s64 (.literal s64 11)))
      (.sequence (.primitive (.assign 3 bl (.literal bl 1)))
        (.primitive (.ret (.variable s64 2))))))) state with
  | .finished step => some step
  | _ => none

theorem constructed_fields :
    (built false).map (fun p => (p.1.scalars.memory.map (·.value),p.2.vectorSlots,p.2.scalarSlots)) =
      some ([7,0],[],[0,1]) := by decide +kernel

theorem default_fields :
    (match RangeSet_construct1_exportViewFuel 20 empty [] false with
     | .finished (state,object) => decide (state.scalars.memory.map (·.value) = [0,1] ∧
         object.vectorSlots = [] ∧ object.scalarSlots = [0,1])
     | _ => false) = true := by decide +kernel

theorem copies_from_const_have_writable_fields :
    (copied true false).map (fun p => (p.1.scalars.bindings.map (·.writable),p.2.scalarSlots)) =
      some ([false,false,true,true],[2,3]) := by decide +kernel

theorem const_copy_has_readonly_fields :
    (copied false true).map (fun p => p.1.scalars.bindings.map (·.writable)) =
      some [true,true,false,false] := by decide +kernel

theorem const_copy_rejects_assignment :
    (copied false true).map (fun p => ((NStmt.assign 2 s64 (.literal s64 11)).run p.1).isNone) =
      some true := by decide +kernel

theorem mutable_copies_preserve_both_original_fields :
    [false,true].all (fun sourceConst =>
      (mutated sourceConst).map (fun state => decide (state.scalars.memory.map (·.value) = [7,0,11,1] ∧
        state.scalars.work ≤ 300 ∧ state.peak ≤ 100)) == some true) = true := by decide +kernel

theorem scope_restores_original_and_retires_copy_slots :
    [false,true].all (fun sourceConst =>
      (scopedCopy sourceConst).map (fun step => decide (step.returned = some (.scalar 11) ∧
        step.state.scalars.memory.map (·.value) = [7,0] ∧ step.state.slots = [.scalar 0,.scalar 1] ∧
        step.state.scalarCell 2 s64 = none ∧ step.state.scalarCell 3 bl = none ∧
        step.state.scalars.work ≤ 300 ∧ step.state.peak ≤ 100)) == some true) = true := by decide +kernel

theorem incomplete_object_reference_rejected :
    copyFields ⟨[],[0]⟩ false = none := by decide +kernel

theorem unexpected_vector_reference_rejected :
    copyFields ⟨[0],[0,1]⟩ false = none := by decide +kernel
end TemplateObjectAudit
