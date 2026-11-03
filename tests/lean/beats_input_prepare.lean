import Proofs.Generated.BeatsConstructionStage

namespace BeatsInputPrepareExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppVectorOwnership
open Proofs.BeatsInputPrepare Proofs.IntSim

example : parameters = Proofs.BeatsConstructionStage.SegmentTreeBeats_construct0.parameters := rfl

-- The selected root is neither owner zero nor binding zero, and the caller
-- has unrelated scalar/vector slots and aliases in its binding table.
def rootBinding (owner : Nat) (wr : Bool) : Binding := ⟨owner,.integer s64,wr,.root 0⟩
def caller : NState :=
  {scalars := ⟨[⟨⟨32,true,false⟩,9⟩],[⟨0,true⟩],7,0,4⟩,
   frame := ⟨⟨⟨List.replicate 3 (some ⟨.integer s64,none,some 0,[]⟩)⟩,
     ⟨(List.range 3).map (fun i => some ⟨i,[.integer 4,.integer 5,.integer 6],3,Proofs.CppVectorBindings.sizeLimit s64,0⟩),0,0,0⟩⟩,
     [true,true,true],[rootBinding 0 false,rootBinding 1 true,rootBinding 0 false,rootBinding 2 true]⟩,
   slots := [.scalar 0,.vector 1,.vector 3],scope := 2,peak := 6}
def constCaller : NState :=
  {caller with frame := {caller.frame with bindings :=
    [rootBinding 0 false,rootBinding 1 true,rootBinding 0 false,rootBinding 2 false]}}
def result := prepare caller parameters [.vectorReference 2]
def constResult := prepare constCaller parameters [.vectorReference 2]
def callee := prepared caller 2 0

#guard caller.frame.state.wellFormed
#guard caller.scalars.baseMemory ≤ caller.scalars.memory.length
#guard result == some callee
#guard constResult == result
#guard callee.frame.state == caller.frame.state
#guard callee.frame.rootWritable == [true,true,true]
#guard callee.frame.bindings == [rootBinding 2 false]
#guard callee.slots == [.vector 0]
#guard callee.scalars.bindings == []
#guard callee.scalars.memory.length == 6
#guard callee.scalars.memory.take caller.scalars.memory.length == caller.scalars.memory
#guard callee.scalars.work == 10
#guard callee.scope == 3
#guard (logical caller 2 0 true [4,5,6]).nextOwner == 3
#guard (logical caller 2 0 true [4,5,6]).params == [⟨0,2,.integer s64,0,false,true⟩]
#guard (callee.frame.state.storage.lookup 2).map (·.items) == some [.integer 4,.integer 5,.integer 6]

example (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller s64 slot vb owner scope wb maximum buf)
    (items : buf.items = a.map Value.integer)
    (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : Proofs.BeatsModel.InRange a) :
    ∃ init fuel step bf h,
      prepare caller parameters [.vectorReference slot] = some init ∧
      runFuel fuel (Proofs.BeatsInlineExec.stage 0 15) init = .finished step ∧
      Proofs.BeatsRep.BRepS n (8*n+8) 256 a bf (Proofs.BeatsModel.buildBT a 0 n) h ∧
      ∃ input, step.state.frame.state.storage.lookup owner = some input ∧ input.items = a.map Value.integer := by
  obtain ⟨init,fuel,step,bf,h,prepared,ran,_,_,rep,_,input⟩ :=
    prepare_stage caller slot vb owner scope wb maximum buf a ok items limit n positive range length values
  exact ⟨init,fuel,step,bf,h,prepared,ran,rep,input⟩

end BeatsInputPrepareExamples
