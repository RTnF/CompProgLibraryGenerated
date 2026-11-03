namespace BeatsInlineExecExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorStore
open Proofs.BeatsAllocation Proofs.BeatsInlineFrame Proofs.BeatsInlineExec

-- The entire source-matched stage must run; no successful allocation or
-- constructor execution is a premise. The owner-keyed output is checked too.
example (st : Proofs.DynamicOwnedState.State) (p : Proofs.MultiVecDynamic.Parameter) (a : List Int)
    (h : Input st p a) (entry : Entry st p) (n : Nat) (positive : 1 ≤ n)
    (range : 4*n < 2147483648) (length : a.length = n) (values : Proofs.BeatsModel.InRange a)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Proofs.CppVector.Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64) :
    ∃ fuel step bf heap, runFuel fuel (stage 0 15) s = .finished step ∧
      Proofs.BeatsRep.BRepS n (8*n+8) 256 a bf (Proofs.BeatsModel.buildBT a 0 n) heap ∧
      step.state.frame.state.storage.work ≤ s.frame.state.storage.work+12*(8*n+8)+783+(4*n*18+10) ∧
      ∀ i, i < 16 → ∃ finalBuffer,
        step.state.frame.state.storage.lookup (Proofs.BeatsAllocationArgs.owner st p i) = some finalBuffer ∧
        finalBuffer.items = (Proofs.BeatsExec.VVA a bf i).map Value.integer := by
  obtain ⟨_,fuel,step,bf,heap,_,ran,_,_,rep,_,_,work,_,_,_,vectors⟩ :=
    stage_exec h entry n positive range length values s real strict base buf stored readonly limit
  rw [Proofs.BeatsAllocationLayout.storageWork_fifteen] at work
  exact ⟨fuel,step,bf,heap,ran,rep,by simpa only [Nat.add_assoc] using work,vectors⟩

-- This original-size boundary exceeds INT_MAX for node capacity. Only
-- symbolic inputs are used, so this theorem allocates no enormous test data.
example (st : Proofs.DynamicOwnedState.State) (p : Proofs.MultiVecDynamic.Parameter) (a : List Int)
    (h : Input st p a) (entry : Entry st p) (length : a.length = 268435456) (values : Proofs.BeatsModel.InRange a)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Proofs.CppVector.Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64) :
    ∃ fuel step, runFuel fuel (stage 0 15) s = .finished step := by
  obtain ⟨_,fuel,step,_,_,_,ran,_⟩ := stage_exec h entry 268435456 (by decide) (by decide)
    length values s real strict base buf stored readonly limit
  exact ⟨fuel,step,ran⟩

end BeatsInlineExecExamples
