namespace BeatsAllocationArgsExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.MultiVecDynamic
open Proofs.BeatsAllocation Proofs.BeatsAllocationArgs

-- Initial caller assumptions suffice; no post-allocation ownership or
-- readonly/limit assumption is added to the resulting state.
example (st : Proofs.DynamicOwnedState.State) (p : Parameter) (a : List Int)
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64) :
    ∃ out, runFuel 16 (fillPrefix 0 15) s = .finished ⟨out,none,false⟩ ∧
      Proofs.BeatsRep.CVecs out (slot st) (binding st p) (owner st p) (scope st p) p.maximum
        (buffer st n buf) (Proofs.BeatsExec.VVA a (initial n)) := by
  obtain ⟨out,ran,_,_,args⟩ := prefix_cvecs h n length small s real strict base buf stored readonly limit
  exact ⟨out,ran,args⟩

open BeatsAllocationLayoutExamples
#guard (List.range 16).map (slot (logical [4,5,6])) == List.range' 1 15 ++ [0]
#guard (List.range 16).map (binding (logical [4,5,6]) ⟨0,0,.integer Proofs.IntSim.s64,0,false,true⟩) ==
  List.range' 1 15 ++ [0]

-- Slots, binding indices, owner ids and scopes need not coincide. Tombstones,
-- unregistered roots and unrelated caller slots may precede the fields.
def offsetState : Proofs.DynamicOwnedState.State :=
  ⟨⟨⟨[],[],[.vector 1,.vector 2,.vector 3]⟩,(logical []).core.contents⟩,[],7,4,3⟩
def inputParameter : Parameter := ⟨1,2,.integer Proofs.IntSim.s64,1,false,true⟩
#guard (List.range 16).map (slot offsetState) == List.range' 3 15 ++ [0]
#guard (List.range 16).map (binding offsetState inputParameter) == List.range' 4 15 ++ [1]
#guard (List.range 16).map (owner offsetState inputParameter) == List.range' 7 15 ++ [2]
#guard (List.range 16).map (scope offsetState inputParameter) == List.replicate 15 3 ++ [1]
#guard (List.range 15).all (fun i =>
  Proofs.BeatsExec.VVB (initial 3) i == List.replicate (fieldCount 3 i) (fieldValue i))
def inputBuffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value :=
  ⟨0,[.integer 4,.integer 5,.integer 6],3,Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64,0⟩
#guard (List.range 16).all (fun i =>
  (buffer (logical [4,5,6]) 3 inputBuffer i).items ==
    (Proofs.BeatsExec.VVA [4,5,6] (initial 3) i).map Proofs.CppNestedVectorStore.Value.integer)

-- Freshness remains valid when the node arrays exceed INT_MAX. This is a
-- symbolic theorem application; no large allocation is evaluated.
example : Proofs.BeatsSeparate.BFreshS 2147483656 256 (initial 268435456) := initial_fresh 268435456

end BeatsAllocationArgsExamples
