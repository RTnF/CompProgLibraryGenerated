namespace BeatsAllocationResourcesExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorStore Proofs.CppNestedEval
open Proofs.BeatsAllocation Proofs.BeatsAllocationResources

def shifted : NState :=
  let s := BeatsAllocationExamples.caller [4,5,6]
  {s with
    scalars := ⟨[⟨⟨32,true,false⟩,7⟩,⟨⟨32,true,false⟩,9⟩],[⟨0,true⟩],7,1,3⟩,
    frame := {s.frame with state := {s.frame.state with storage := {s.frame.state.storage with baseSpace := 2}}},
    slots := [.vector 0,.scalar 0],peak := 6}

def completed (s : NState) : NState := match runFuel 16 (fillPrefix 0 15) s with
  | .finished step => step.state
  | _ => s
def samples : List (NState × Nat) :=
  [(BeatsAllocationExamples.caller [],0),(BeatsAllocationExamples.caller [4,5,6],3),(shifted,3)]

#guard scalarCost 0 15 == 319
#guard shifted.frame.state.wellFormed
#guard samples.all (fun (s,n) => match runFuel 16 (fillPrefix 0 15) s with
  | .finished step =>
    decide (step.state.scalars.work ≤ s.scalars.work+319) &&
    decide (liveS step.state = liveS s) &&
    decide (step.state.scalars.peak ≤ prefixScalar s) &&
    decide (step.state.frame.state.liveSpace = s.frame.state.liveSpace+allocationSize n) &&
    decide (step.state.frame.state.storage.work = s.frame.state.storage.work+allocationSize n) &&
    decide (step.state.frame.state.storage.peak ≤ prefixStorage s n) &&
    decide (step.state.peak ≤ prefixPeak s n)
  | _ => false)
#guard (completed shifted).scalars.baseMemory == 1
#guard (completed shifted).frame.state.storage.baseSpace == 2
#guard (completed shifted).frame.state.liveSpace == 1171

-- Closed time bounds apply to the whole stage from its initial state,
-- without a premise about a successful allocation or post-allocation peak.
example (st : Proofs.DynamicOwnedState.State) (p : Proofs.MultiVecDynamic.Parameter) (a : List Int)
    (h : Input st p a) (entry : Proofs.BeatsInlineFrame.Entry st p) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : Proofs.BeatsModel.InRange a)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Proofs.CppVector.Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64) :
    ∃ fuel step, runFuel fuel (Proofs.BeatsInlineExec.stage 0 15) s = .finished step ∧
      step.state.work ≤ s.work+181824*n+1308 ∧
      step.state.peak ≤ stageScalar s st.core.locals.memory n+stageStorage s n := by
  obtain ⟨fuel,step,_,_,ran,_,_,_,scalar,storage,_,_,peak,_⟩ :=
    stage_resources h entry n positive range length values s real strict base buf stored readonly limit
  exact ⟨fuel,step,ran,total_work s step.state n scalar storage,peak⟩

example (caller : NState) (slot vb owner scope : Nat) (wb maximum : Bool)
    (buf : Proofs.CppVector.Buffer Value) (a : List Int)
    (ok : Proofs.MatMulPrepare.VOKG caller Proofs.IntSim.s64 slot vb owner scope wb maximum buf)
    (items : buf.items = a.map Value.integer) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64)
    (n : Nat) (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : Proofs.BeatsModel.InRange a) :
    ∃ callee fuel step,
      Proofs.CppNestedCall.prepare caller Proofs.BeatsInputPrepare.parameters [.vectorReference slot] = some callee ∧
      runFuel fuel (Proofs.BeatsInlineExec.stage 0 15) callee = .finished step ∧
      step.state.work ≤ caller.work+181824*n+1311 := by
  obtain ⟨callee,fuel,step,_,_,prepared,ran,_,_,_,work,_⟩ :=
    prepare_resources caller slot vb owner scope wb maximum buf a ok items limit n positive range length values
  exact ⟨callee,fuel,step,prepared,ran,work⟩

end BeatsAllocationResourcesExamples
