namespace BeatsInlineFrameExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppMixedInvoke Proofs.MultiVec
open Proofs.BeatsInlineFrame Proofs.BeatsAllocation Proofs.BeatsAllocationArgs
open BeatsAllocationExamples BeatsAllocationLayoutExamples

def normalized := normalize (allocated [4,5,6])
#guard normalized.slots == slN 16 0
#guard normalized.frame.bindings.map (·.owner) == List.range' 1 15 ++ [0]
#guard normalized.frame.state == (allocated [4,5,6]).frame.state
#guard normalized.scope == (allocated [4,5,6]).scope
#guard normalized.scalars == (allocated [4,5,6]).scalars
#guard normalized.work == (allocated [4,5,6]).work

example (a : List Int) : Entry (logical a) ⟨0,0,.integer Proofs.IntSim.s64,0,false,false⟩ :=
  ⟨rfl,rfl,rfl,rfl⟩

example (st : Proofs.DynamicOwnedState.State) (p : Proofs.MultiVecDynamic.Parameter) (a : List Int)
    (h : Input st p a) (entry : Entry st p) (n : Nat) (s : NState)
    (real : Proofs.DynamicOwnedState.Realizes (states st n 15) s) :
    s.slots = (List.range 16).map Location.vector ∧
      Proofs.QuotientFrame.QS (normalize s) [] s.scalars.baseMemory s.scope st.core.locals.memory [] (slN 16 0) :=
  ⟨allocated_slots h entry n s real,normalized_qs h entry n s real⟩

end BeatsInlineFrameExamples
