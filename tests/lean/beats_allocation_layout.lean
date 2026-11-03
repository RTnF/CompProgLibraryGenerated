namespace BeatsAllocationLayoutExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorStore
open Proofs.MultiVecDynamic Proofs.BeatsAllocation Proofs.BeatsAllocationLayout
open BeatsAllocationExamples

def logical (a : List Int) : Proofs.DynamicOwnedState.State :=
  ⟨⟨⟨[],[],[.vector 0]⟩,fun i => if i=0 then some (.flat Proofs.IntSim.s64 0 a) else none⟩,
    [⟨0,0,.integer Proofs.IntSim.s64,0,false,false⟩],1,1,0⟩

#guard (allocated [4,5,6]).frame.state.storage.objects ==
  (caller [4,5,6]).frame.state.storage.objects++bufferList (logical [4,5,6]) 3 0 15
#guard (allocated [4,5,6]).frame.state.storage.work == 12*(8*3+8)+783
#guard (allocated []).frame.state.storage.work == 12*8+783
#guard (List.range 15).all (fun j =>
  (allocated [4,5,6]).frame.state.storage.lookup (1+j) == some (fieldBuffer (logical [4,5,6]) 3 j))

-- Old allocation metadata must survive; it must not be replaced by the new
-- buffers' capacity, max-size limit or epoch.
def altered : NState :=
  let s := caller [4,5,6]
  {s with frame := {s.frame with state := {s.frame.state with storage :=
    {s.frame.state.storage with objects := [some ⟨0,[.integer 4,.integer 5,.integer 6],5,7,9⟩]}}}}
def alteredResult := runFuel 16 (fillPrefix 0 15) altered
def alteredFinal : NState := match alteredResult with | .finished r => r.state | _ => altered
#guard altered.frame.state.wellFormed
#guard (match alteredResult with | .finished _ => true | _ => false)
#guard alteredFinal.frame.state.storage.lookup 0 == altered.frame.state.storage.lookup 0
#guard alteredFinal.frame.state.storage.objects == altered.frame.state.storage.objects++bufferList (logical [4,5,6]) 3 0 15
#guard alteredFinal.frame.state.storage.work == 1167

example (st : Proofs.DynamicOwnedState.State) (p : Parameter) (a : List Int)
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s) :
    ∃ out, runFuel 16 (fillPrefix 0 15) s = .finished ⟨out,none,false⟩ ∧
      out.frame.state.storage.work = s.frame.state.storage.work+12*(8*n+8)+783 ∧
      ((∀ owner scope, out.frame.state.forest.context owner = some scope → scope ≤ out.scope) →
       out.scalars.baseMemory ≤ out.scalars.memory.length →
       ∀ j, j < 15 → Proofs.MatMulPrepare.VOKG out (fieldTy j)
         (st.core.locals.slots.length+j) (st.nextBinding+j) (st.nextOwner+j) st.scope true true
         (fieldBuffer st n j)) := by
  obtain ⟨out,ran,after,objects,work⟩ := prefix_layout h n length small 15 0 s real
  refine ⟨out,ran,?_,?_⟩
  · simpa only [storageWork_fifteen,Nat.add_assoc] using work
  · intro strict base j bound
    have buffers := fun j bound => buffer_at st n s out real.owner objects j bound
    exact (field_argument st n out after buffers strict base j bound).1

-- No post-allocation scope or scalar-memory condition is assumed here.
example (st : Proofs.DynamicOwnedState.State) (p : Parameter) (a : List Int)
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Proofs.CppVector.Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf) :
    ∃ out, runFuel 16 (fillPrefix 0 15) s = .finished ⟨out,none,false⟩ ∧
      (∀ j, j < 15 → Proofs.MatMulPrepare.VOKG out (fieldTy j) (st.core.locals.slots.length+j)
        (st.nextBinding+j) (st.nextOwner+j) st.scope true true (fieldBuffer st n j)) ∧
      Proofs.MatMulPrepare.VOKG out Proofs.IntSim.s64 0 p.slot p.owner p.scope p.writable p.maximum buf := by
  obtain ⟨out,ran,_,_,_,fields,input⟩ := prefix_arguments h n length small s real strict base buf stored
  exact ⟨out,ran,fields,input⟩

-- Existing descendants inherit their old root's context; the newly appended
-- root gets the current context, and owners past the end remain absent.
def nestedForest : Proofs.CppVectorOwnership.Forest :=
  ⟨[some ⟨.vector (.integer Proofs.IntSim.s64),none,some 2,[1]⟩,
    some ⟨.integer Proofs.IntSim.s64,some 0,none,[]⟩]⟩
#guard nestedForest.wellFormed
#guard (List.range 5).map (nestedForest.declareRoot Proofs.IntSim.s64 3).context ==
  [some 2,some 2,some 3,none,none]

end BeatsAllocationLayoutExamples
