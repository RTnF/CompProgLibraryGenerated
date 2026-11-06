namespace ScalarChoiceAudit
open Proofs.CppNestedProgram Proofs.CppNestedCall
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def observed (program : NProgram) (ty : Proofs.CppScalar.Ty) (a b expected : Int) : Bool :=
  match program.callFuel 100 empty [.value (.literal ty a),.value (.literal ty b)] with
  | .finished (state,.scalar value) => decide (value = expected ∧ state.scalars.memory = [] ∧
      state.slots = [] ∧ state.scalars.work ≤ 200 ∧ state.peak ≤ 40)
  | _ => false
def signed : List Int := [-9223372036854775808,-1,0,9223372036854775807]
def unsigned : List Int := [0,1,18446744073709551615]
theorem signed_max : signed.all (fun a => signed.all (fun b =>
    observed ScalarChoices.largest ⟨64,true,false⟩ a b (if a < b then b else a))) = true := by decide +kernel
theorem signed_min : signed.all (fun a => signed.all (fun b =>
    observed ScalarChoices.smallest ⟨64,true,false⟩ a b (if b < a then b else a))) = true := by decide +kernel
theorem unsigned_max : unsigned.all (fun a => unsigned.all (fun b =>
    observed ScalarChoices.largest_u ⟨64,false,false⟩ a b (if a < b then b else a))) = true := by decide +kernel
theorem unsigned_min : unsigned.all (fun a => unsigned.all (fun b =>
    observed ScalarChoices.smallest_u ⟨64,false,false⟩ a b (if b < a then b else a))) = true := by decide +kernel
def signed32 : List Int := [-2147483648,-1,0,2147483647]
def unsigned32 : List Int := [0,1,4294967295]
theorem signed32_max : signed32.all (fun a => signed32.all (fun b =>
    observed ScalarChoices.largest_i ⟨32,true,false⟩ a b (if a < b then b else a))) = true := by decide +kernel
theorem unsigned32_min : unsigned32.all (fun a => unsigned32.all (fun b =>
    observed ScalarChoices.smallest_ui ⟨32,false,false⟩ a b (if b < a then b else a))) = true := by decide +kernel
def aliasCaller : NState :=
  ⟨⟨[⟨⟨64,true,false⟩,4⟩],[⟨0,true⟩],0,0,1⟩,empty.frame,[.scalar 0],0,0⟩
theorem snapshot_alias :
    (match ScalarChoices.snapshot.callFuel 100 aliasCaller [.scalarReference 0,.scalarReference 0] with
     | .finished (state,.scalar value) => decide (value = 4 ∧
         state.scalars.memory = [⟨⟨64,true,false⟩,17⟩] ∧ state.slots = [.scalar 0])
     | _ => false) = true := by decide +kernel
end ScalarChoiceAudit
