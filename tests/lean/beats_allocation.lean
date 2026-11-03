namespace BeatsAllocationExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppMixedInvoke
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
open Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.BeatsAllocation
open Proofs.IntSim (s64)

def caller (a : List Int) : NState :=
  { scalars := ⟨[],[],0,0,0⟩,
    frame := ⟨⟨⟨[some ⟨.integer s64,none,some 0,[]⟩]⟩,
      ⟨[some ⟨0,a.map Value.integer,a.length,Proofs.CppVectorBindings.sizeLimit s64,0⟩],0,0,0⟩⟩,
      [false],[⟨0,.integer s64,false,.root 0⟩]⟩,
    slots := [.vector 0],scope := 0,peak := 0 }

def outcome (a : List Int) := runFuel 16 (fillPrefix 0 15) (caller a)
def allocated (a : List Int) : NState := match outcome a with
  | .finished r => r.state
  | _ => caller a

#guard (caller [4,5,6]).frame.state.wellFormed
#guard (match outcome [] with | .finished r => r.returned.isNone && !r.breaking | _ => false)
#guard (match outcome [4,5,6] with | .finished r => r.returned.isNone && !r.breaking | _ => false)
#guard (allocated []).slots.length == 16
#guard (allocated [4,5,6]).slots.length == 16
#guard (allocated [4,5,6]).frame.bindings.length == 16
#guard (allocated [4,5,6]).frame.state.storage.objects.length == 16
#guard (allocated [4,5,6]).scalars.memory == []
#guard (allocated [4,5,6]).scalars.bindings == []
#guard (allocated [4,5,6]).frame.rootWritable[0]? == some false
#guard ((allocated [4,5,6]).frame.state.storage.lookup 0).map (·.items) == some [.integer 4,.integer 5,.integer 6]
#guard ((allocated []).frame.state.storage.lookup 0).map (·.items) == some []
#guard (allocated [4,5,6]).frame.state.wellFormed
#guard (List.range 15).all (fun j =>
  ((allocated [4,5,6]).frame.state.storage.lookup (1+j)).map (fun b =>
    b.items == List.replicate (fieldCount 3 j) (.integer (fieldValue j))) == some true)
#guard (List.range 15).all (fun j =>
  (allocated [4,5,6]).frame.bindings[1+j]? == some ⟨1+j,.integer (fieldTy j),true,.root 0⟩ &&
  (allocated [4,5,6]).slots[1+j]? == some (.vector (1+j)) &&
  (allocated [4,5,6]).frame.rootWritable[1+j]? == some true)
#guard (runFuel 15 (fillPrefix 0 15) (caller [4,5,6])) == .exhausted

-- The proof starts from a represented caller, not a successful allocation.
example (st : Proofs.DynamicOwnedState.State) (p : Parameter) (a : List Int)
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (slots : st.core.locals.slots.length = 1) :
    ∃ r : NStep, runFuel 16 (fillPrefix 0 15) s = .finished r ∧ r.state.slots.length = 16 := by
  obtain ⟨r,ran,after,returned,breaking,size,owners,bindings⟩ := prefix_actual h n length small s real
  exact ⟨r,ran,by omega⟩

example (st : Proofs.DynamicOwnedState.State) (n : Nat) (s : NState)
    (real : Proofs.DynamicOwnedState.Realizes (states st n 15) s) (j : Nat) (bound : j < 15) :
    Proofs.CppRootModel.Flat s.frame.state (st.nextOwner+j) (fieldTy j) st.scope
      (List.replicate (fieldCount n j) (fieldValue j)) := (actual_field st n 15 s real j bound).1

end BeatsAllocationExamples
