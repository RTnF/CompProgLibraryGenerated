namespace BeatsWideCallExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.BeatsAllocationArgs Proofs.BeatsPrepare
open Proofs.BeatsWideCall
open BeatsAllocationExamples BeatsAllocationLayoutExamples

example : program.parameters = Proofs.BeatsInstance.SegmentTreeBeats_new0.parameters := rfl
example : program.body = Proofs.BeatsRep.WideCtorCmd 16 := rfl

example (fuel : Nat) (s : NState) (slots : 16 ≤ s.slots.length) (bindings : 16 ≤ s.frame.bindings.length) :
    Proofs.BeatsBindingCycle.outcomeView (Proofs.BeatsSlotCycle.outcomeView
      (runFuel fuel (Proofs.CppSlotRename.command Proofs.BeatsSlotCycle.cycle program.body) s)) =
      runFuel fuel program.body (Proofs.BeatsBindingCycle.view (Proofs.BeatsSlotCycle.permute s)) :=
  inline_body_view fuel s slots bindings

def preparedResult := prepare (allocated [4,5,6]) program.parameters (vargs (slot (logical [4,5,6])) 0 16)
def prepared : NState := preparedResult.getD (allocated [4,5,6])
#guard preparedResult.isSome
-- Prepare builds a new binding table in declaration order while retaining
-- every original allocation and its permission flags.
#guard (allocated [4,5,6]).frame.bindings.map (·.owner) == List.range 16
#guard prepared.frame.bindings.map (·.owner) == List.range' 1 15 ++ [0]
#guard prepared.slots == (List.range 16).map Proofs.CppMixedInvoke.Location.vector
#guard prepared.frame.state == (allocated [4,5,6]).frame.state
#guard prepared.frame.rootWritable == (allocated [4,5,6]).frame.rootWritable
#guard prepared.scope == (allocated [4,5,6]).scope+1
#guard (prepared.frame.bindings[15]?).map (·.writable) == some false

-- No successful run, post-allocation invariant or mathematical tree is
-- assumed. Both actual allocation and the normalized call must terminate.
example (st : Proofs.DynamicOwnedState.State) (p : Proofs.MultiVecDynamic.Parameter)
    (a : List Int) (h : Proofs.BeatsAllocation.Input st p a) (n : Nat)
    (positive : 1 ≤ n) (length : a.length = n) (range : 4*n < 2147483648)
    (values : Proofs.BeatsModel.InRange a) (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64) :
    ∃ allocatedState fuel res bf heap,
      runFuel 16 (Proofs.BeatsAllocation.fillPrefix 0 15) s = .finished ⟨allocatedState,none,false⟩ ∧
      program.callFuel fuel allocatedState (vargs (slot st) 0 16) = .finished (res,Ret.unit) ∧
      Proofs.BeatsRep.BRepS n (8*n+8) 256 a bf (Proofs.BeatsModel.buildBT a 0 n) heap ∧
      res.frame.bindings = allocatedState.frame.bindings ∧ res.slots = allocatedState.slots := by
  obtain ⟨allocatedState,_,fuel,res,bf,heap,ran,_,called,rep,_,bindings,slots,_⟩ :=
    allocated_call h n positive length range values s real strict base buf stored readonly limit
  exact ⟨allocatedState,fuel,res,bf,heap,ran,called,rep,bindings,slots⟩

end BeatsWideCallExamples
