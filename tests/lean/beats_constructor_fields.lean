namespace BeatsConstructorFieldsExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorStore
open Proofs.CppConstructorMultiFinish Proofs.BeatsConstructorFields Proofs.BeatsInlineExec
open BeatsAllocationExamples

def prepared (a : List Int) := (prepare (caller a) [.vector Proofs.IntSim.s64 false]
  [.vectorReference 0]).getD (caller a)
def exported (a : List Int) : Option (NState × ObjectRef) := do
  let step ← match runFuel 256 (stage 0 15) (prepared a) with
    | .finished result => some result
    | _ => none
  finish (caller a) step.state vectorFields scalarFields

def result (a : List Int) : NState := (exported a).getD (caller a,⟨[],[]⟩) |>.1
#guard (exported [7]).isSome
#guard (exported [4,5,6]).isSome
#guard ((exported [4,5,6]).map (fun r => r.2.vectorSlots)) == some (List.range' 1 15)
#guard ((exported [4,5,6]).map (fun r => r.2.scalarSlots)) == some [16,17]
#guard (result [4,5,6]).scope == 0
#guard (result [4,5,6]).scalarCell 16 Proofs.IntSim.s64 ==
  some (⟨0,true⟩,⟨Proofs.IntSim.s64,4000000000000000000⟩)
#guard (result [4,5,6]).scalarCell 17 Proofs.DoublingNested.i32 == some (⟨1,true⟩,⟨Proofs.DoublingNested.i32,3⟩)
#guard (result [4,5,6]).frame.state.storage.lookup 0 == (caller [4,5,6]).frame.state.storage.lookup 0
#guard (List.range 15).all (fun i => (result [4,5,6]).frame.state.forest.context (i+1) == some 0)
#guard (result [4,5,6]).frame.state.wellFormed
#guard (result [4,5,6]).frame.bindings.length == 16
#guard (result [4,5,6]).slots.length == 18
#guard (result [4,5,6]).scalars.memory.length == 2
#guard (result [4,5,6]).frame.elementRef 1 Proofs.IntSim.s64 0 |>.isSome

example (caller initial out : NState) (V vsc : Nat → Nat) (m : Bool) (vv : Nat → List Int)
    (P : List Proofs.CppState.Cell) (n : Nat) (layout : FinalLayout initial out V vsc m vv P n)
    (range : 4*n < 2147483648) (scope : out.scope = caller.scope+1)
    (fieldsScope : ∀ i, i < 15 → vsc i = out.scope)
    (fits : caller.scalars.memory.length ≤ P.length)
    (types : (P.take caller.scalars.memory.length).map Proofs.CppState.Cell.type = caller.scalars.memory.map Proofs.CppState.Cell.type) :=
  finish_from_layout caller initial out V vsc m vv P n layout range scope fieldsScope fits types

-- The complete stage derives its own final layout and all field captures.
example := @Proofs.BeatsConstructorFields.stage_export
end BeatsConstructorFieldsExamples
