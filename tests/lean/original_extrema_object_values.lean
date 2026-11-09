namespace ExtremaObjectAudit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorMultiFinish
open Proofs.GroupCall
open OriginalExtremaObject SelectedExtrema
abbrev s64 : Ty := ⟨64,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def caller (x y : Int) : NState :=
  ⟨⟨[⟨s64,x⟩,⟨s64,y⟩],[⟨0,false⟩,⟨1,false⟩],0,0,2⟩,empty.frame,[.scalar 0,.scalar 1],0,2⟩
def observed (outcome : Proofs.CppLoop.Outcome (NState × ObjectRef)) (values : List Int)
    (slots : List Nat) (permissions : List Bool) : Bool :=
  match outcome with
  | .finished (state,object) => decide (state.scalars.memory.map (·.value) = values ∧
      object.vectorSlots = [] ∧ object.scalarSlots = slots ∧ state.scalars.bindings.map (·.writable) = permissions ∧
      state.scalars.work ≤ 300 ∧ state.peak ≤ 100)
  | _ => false

def samples : List Int := [-9223372036854775808,-1,0,9223372036854775807]
theorem default_is_the_declared_identity : observed
    (defaultExport 100 empty [] false) [neutral] [0] [true] = true := by decide +kernel

theorem factory_is_the_declared_identity : observed
    (identityExport 100 empty [] true) [neutral] [0] [false] = true := by decide +kernel

theorem extreme_pairs_return_complete_objects :
    (samples.all fun x => samples.all fun y => observed
      (combineExport 100 (caller x y) [⟨[],[0]⟩,⟨[],[1]⟩] false)
      [x,y,expected x y] [2] [false,false,true]) = true := by decide +kernel

theorem aliased_arguments_preserve_input_and_result :
    (samples.all fun x => observed
      (combineExport 100 (caller x 0) [⟨[],[0]⟩,⟨[],[0]⟩] false)
      [x,0,x] [2] [false,false,true]) = true := by decide +kernel

theorem const_result_keeps_original_permissions : observed
    (combineExport 100 (caller 7 (-3)) [⟨[],[0]⟩,⟨[],[1]⟩] true)
    [7,-3,expected 7 (-3)] [2] [false,false,false] = true := by decide +kernel

theorem incomplete_object_is_rejected :
    combineExport 100 (caller 7 (-3)) [⟨[],[]⟩,⟨[],[1]⟩] false = .fault := by decide +kernel

theorem future_destination_slot_cannot_be_an_input :
    combineExport 100 (caller 7 (-3)) [⟨[],[0]⟩,⟨[],[2]⟩] false = .fault := by decide +kernel

theorem expired_inputs_are_rejected :
    combineExport 100 empty [⟨[],[0]⟩,⟨[],[1]⟩] false = .fault := by decide +kernel

theorem source_body_shape : program.body = ExtremaObjectGeneral.selectionBody leftIndex rightIndex := rfl

theorem source_raw_exec (P : List Proofs.CppState.Cell) (a b : Nat) (x y : Int)
    (hx : s64.valid x = true) (hy : s64.valid y = true)
    (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, Proofs.StraightLine.pexec 1 program.body ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = none ∧ r.cost ≤ 40 ∧ r.need ≤ P.length+16 ∧
      r.ps = Proofs.GroupCall.ws P [⟨a,false⟩,⟨b,false⟩] (List.replicate 4 ⟨s64,expected x y⟩) := by
  obtain ⟨r,ran,ret,cost,need,mem⟩ := ExtremaObjectGeneral.selection_exec leftIndex rightIndex
    (by decide) P a b x y hx hy ha hb
  refine ⟨r,?_,ret,cost,need,?_⟩
  · rw [source_body_shape]; exact ran
  · rw [expected_value] at mem
    exact mem
end ExtremaObjectAudit
