namespace BeatsConstructCallExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppConstructorMultiFinish Proofs.BeatsConstructorFields
open Proofs.BeatsConstructCall Proofs.IntSim
open BeatsInputPrepareExamples (caller constCaller)

def aliasCaller : NState := {caller with
  scalars := {caller.scalars with bindings := [⟨0,true⟩,⟨0,false⟩]},
  slots := caller.slots ++ [.scalar 1]}
def maxConstCaller : NState := {constCaller with
  frame := {constCaller.frame with rootWritable := [true,true,false]}}

def closed (source : NState) := program.constructMembersFuel 256 source [.vectorReference 2] vectorFields scalarFields

def retained (source : NState) : Bool := match closed source with
  | .finished (out,object) =>
    object == reference source 15 2 &&
    out.scope == source.scope &&
    out.slots.take source.slots.length == source.slots &&
    out.frame.bindings.take source.frame.bindings.length == source.frame.bindings &&
    out.scalars.bindings.take source.scalars.bindings.length == source.scalars.bindings &&
    out.scalars.memory.take source.scalars.memory.length == source.scalars.memory &&
    out.scalars.memory.map (·.value) == [9,4000000000000000000,3] &&
    out.scalars.baseMemory == source.scalars.baseMemory &&
    out.frame.state.storage.baseSpace == source.frame.state.storage.baseSpace &&
    out.frame.rootWritable.take 3 == source.frame.rootWritable &&
    out.frame.state.wellFormed &&
    out.frame.bindings.length == source.frame.bindings.length+15 &&
    out.slots.length == source.slots.length+17 &&
    (List.range 3).all (fun i => out.frame.state.storage.lookup i == source.frame.state.storage.lookup i) &&
    (List.range 15).all (fun i =>
      out.frame.state.forest.context (3+i) == some 2 &&
      out.vectorSlot (source.slots.length+i) == some (source.frame.bindings.length+i) &&
      (out.frame.resolve (source.frame.bindings.length+i) (.integer (Proofs.BeatsRep.cty i))).isSome) &&
    ((out.frame.state.storage.lookup 3).bind (fun b => b.items[0]?)) == some (.integer 6) &&
    ((out.frame.state.storage.lookup 6).bind (fun b => b.items[0]?)) == some (.integer 4) &&
    out.scalarCell (source.slots.length+15) s64 == some (⟨1,true⟩,⟨s64,4000000000000000000⟩) &&
    out.scalarCell (source.slots.length+16) Proofs.DoublingNested.i32 ==
      some (⟨2,true⟩,⟨Proofs.DoublingNested.i32,3⟩)
  | _ => false

#guard retained caller
#guard retained constCaller
#guard retained maxConstCaller
#guard retained aliasCaller
#guard program.constructMembersFuel 0 caller [.vectorReference 2] vectorFields scalarFields == .exhausted
#guard program.constructMembersFuel 256 caller [.vectorReference 0] vectorFields scalarFields == .fault

-- The caller's scalar alias and all vector grants remain usable after export.
#guard (match closed aliasCaller with
  | .finished (out,_) => out.scalarCell 3 Proofs.DoublingNested.i32 == some (⟨0,false⟩,⟨Proofs.DoublingNested.i32,9⟩)
  | _ => false)

example := @Proofs.BeatsConstructCall.construct

-- This original-size input requires node capacity above INT_MAX. This is a
-- symbolic application, with no enormous buffer allocated or enumerated.
example (source : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG source s64 slot vb owner scope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64)
    (length : a.length = 268435456) (values : Proofs.BeatsModel.InRange a) :
    ∃ fuel result, program.constructMembersFuel fuel source [.vectorReference slot] vectorFields scalarFields =
      .finished (result,reference source 15 2) := by
  obtain ⟨fuel,result,_,_,ran,_⟩ := Proofs.BeatsConstructCall.construct source slot vb owner scope wb maximum
    buf a ok items limit 268435456 (by decide) (by decide) length values
  exact ⟨fuel,result,ran⟩
end BeatsConstructCallExamples
