namespace BeatsConstructReceiverExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorStore
open Proofs.CppRootModel Proofs.BeatsConstructReceiver Proofs.BeatsConstructCall
open Proofs.BeatsConstructorFields Proofs.CppConstructorMultiFinish Proofs.IntSim
open BeatsConstructCallExamples

-- Resolve the vector slot returned by the object, then read and write through
-- the real field grant. Other fields and the caller's old buffers stay intact.
def useField : Option Bool := do
  let (out,_) ← match closed aliasCaller with | .finished result => some result | _ => none
  let index ← out.vectorSlot aliasCaller.slots.length
  let ref ← out.frame.elementRef index s64 0
  let before ← out.frame.read ref
  let modified ← out.frame.write ref 12
  let after ← modified.read ref
  some (before == 6 && after == 12 &&
    modified.state.storage.lookup 4 == out.frame.state.storage.lookup 4 &&
    modified.state.storage.lookup 2 == out.frame.state.storage.lookup 2 &&
    out.scalarCell 3 Proofs.DoublingNested.i32 == some (⟨0,false⟩,⟨Proofs.DoublingNested.i32,9⟩))
#guard useField == some true

def inputStillReadonly : Option Bool := do
  let (out,_) ← match closed maxConstCaller with | .finished result => some result | _ => none
  let index ← out.vectorSlot 2
  let ref ← out.frame.elementRef index s64 0
  let value ← out.frame.read ref
  some (value == 4 && (out.frame.write ref 99).isNone)
#guard inputStillReadonly == some true

example (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb owner scope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : Proofs.BeatsModel.InRange a) :
    ∃ fuel result, program.constructMembersFuel fuel caller [.vectorReference slot] vectorFields scalarFields =
      .finished (result,reference caller 15 2) ∧
      result.scalars.memory = caller.scalars.memory ++ [⟨s64,4000000000000000000⟩,⟨Proofs.DoublingNested.i32,n⟩] ∧
      (∀ oldSlot, oldSlot < caller.slots.length → ∀ ty binding cell,
        caller.scalarCell oldSlot ty = some (binding,cell) → result.scalarCell oldSlot ty = some (binding,cell)) ∧
      ∀ i, i < 15 → ∃ buffer,
        result.vectorSlot (caller.slots.length+i) = some (caller.frame.bindings.length+i) ∧
        result.frame.resolve (caller.frame.bindings.length+i) (.integer (Proofs.BeatsRep.cty i)) =
          some (memberBinding caller (fun j => caller.frame.state.storage.objects.length+j) i,buffer) := by
  obtain ⟨fuel,result,bf,heap,ran,rep,input,layout,fields⟩ :=
    construct_fields caller slot vb owner scope wb maximum buf a ok items limit n positive range length values
  refine ⟨fuel,result,ran,layout.memory,?_,?_⟩
  · intro oldSlot bound ty binding cell found
    exact old_scalar_kept layout oldSlot bound ty binding cell found
  · intro i bound
    obtain ⟨buffer,slot,resolved,_⟩ := fields i bound
    exact ⟨buffer,slot,resolved⟩


-- Runtime checks include all owners, every field type, metadata contract and
-- standard vector limit after the actual prepare/stage/export sequence.
def contracts : Option Bool := do
  let (out,_) ← match closed aliasCaller with | .finished result => some result | _ => none
  let buffersOk := (List.range 15).all fun i =>
    match out.frame.state.storage.lookup (3+i) with
    | none => false
    | some buffer => decide (buffer.Valid (accepts (.integer (Proofs.BeatsRep.cty i)))) &&
      buffer.limit == Proofs.CppVectorBindings.sizeLimit (Proofs.BeatsRep.cty i) &&
      buffer.owner == 3+i && buffer.items.length < 18446744073709551616
  let scopesOk := (List.range out.frame.state.forest.objects.length).all fun owner =>
    match out.frame.state.forest.context owner with
    | none => true
    | some c => c ≤ out.scope
  some (buffersOk && scopesOk && out.scalars.baseMemory ≤ out.scalars.memory.length)
#guard contracts == some true

example (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb owner scope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : Proofs.BeatsModel.InRange a) :
    ∃ fuel result bf heap, program.constructMembersFuel fuel caller [.vectorReference slot] vectorFields scalarFields =
      .finished (result,reference caller 15 2) ∧
      Proofs.BeatsRep.BRepS n (8*n+8) 256 a bf (Proofs.BeatsModel.buildBT a 0 n) heap ∧
      Proofs.BeatsRep.BVecs result (fun i => caller.slots.length+i) (fun i => caller.frame.bindings.length+i)
        (fun i => caller.frame.state.storage.objects.length+i) (fun _ => caller.scope)
        (fieldBuffer result (fun i => caller.frame.state.storage.objects.length+i)) (Proofs.BeatsExec.VVB bf) := by
  obtain ⟨fuel,result,bf,heap,ran,rep,_,_,vectors⟩ :=
    construct_ready caller slot vb owner scope wb maximum buf a ok items limit n positive range length values
  exact ⟨fuel,result,bf,heap,ran,rep,vectors⟩

end BeatsConstructReceiverExamples
