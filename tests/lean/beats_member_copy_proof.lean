namespace GeneratedBeatsCopyProof
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.BeatsRep
open Proofs.IntSim Proofs.DoublingNested
abbrev Copy := BeatsMemberBundle.Construction.MemberCopy.Field

def fields (sl : Nat → Nat) (base : Nat) (targetConst : Bool) : List Copy :=
  (List.range 15).map (fun i => .vector (sl i) (bty i) (!targetConst)) ++
    [.scalar (base+15) s64 (!targetConst),.scalar (base+16) i32 (!targetConst)]

theorem assembled (sl : Nat → Nat) (base : Nat) (targetConst : Bool) :
    BeatsMemberBundle.Construction.copyFields (sourceReceiver sl base) targetConst =
      some (fields sl base targetConst) := by
  cases targetConst <;> rfl

theorem target_reference (state : NState) (sl : Nat → Nat) (base : Nat) (targetConst : Bool) :
    BeatsMemberBundle.Construction.MemberCopy.reference state (fields sl base targetConst) =
      Proofs.CppConstructorMultiFinish.reference state 15 2 := rfl

-- The source may be readonly. Its permissions do not determine permissions
-- of the fresh copy; only typed readable owned fields are required here.
theorem copy_from_owned_fields (state : NState) (sl vb V vsc : Nat → Nat)
    (buffers : Nat → Buffer Value) (writable maximum : Nat → Bool) (base : Nat)
    (vectors : ∀ i, i < 15 → Proofs.MatMulPrepare.VOKG state (bty i)
      (sl i) (vb i) (V i) (vsc i) (writable i) (maximum i) (buffers i))
    (inf : ∃ binding cell, state.scalarCell (base+15) s64 = some (binding,cell))
    (size : ∃ binding cell, state.scalarCell (base+16) i32 = some (binding,cell))
    (targetConst : Bool) :
    ∃ after, BeatsMemberBundle.Construction.copyFuel 18 state (sourceReceiver sl base) targetConst =
        .finished (after,Proofs.CppConstructorMultiFinish.reference state 15 2) ∧
      BeatsMemberBundle.Construction.MemberCopy.Good after ∧
      BeatsMemberBundle.Construction.MemberCopy.Keeps state after ∧
      after.slots.length = state.slots.length + 17 ∧ after.scope = state.scope ∧
      BeatsMemberBundle.Construction.MemberCopy.ObjectCopies state after (fields sl base targetConst)
        (Proofs.CppConstructorMultiFinish.reference state 15 2) ∧
      BeatsMemberBundle.Construction.MemberCopy.Placements after state.scope state.slots.length
        state.frame.state.storage.objects.length state.scalars.memory.length (fields sl base targetConst) ∧
      after.frame.state.storage.objects.length = state.frame.state.storage.objects.length + 15 ∧
      after.scalars.memory.length = state.scalars.memory.length + 2 ∧
      after.work = state.work + BeatsMemberBundle.Construction.MemberCopy.copyWork state (fields sl base targetConst) ∧
      BeatsMemberBundle.Construction.MemberCopy.SpaceBounds state after
        (BeatsMemberBundle.Construction.MemberCopy.copyWork state (fields sl base targetConst)) := by
  have vectorSource (i : Nat) (bound : i < 15) :
      BeatsMemberBundle.Construction.MemberCopy.Source state (.vector (sl i) (bty i) (!targetConst)) := by
    have ok := vectors i bound
    obtain ⟨resolved,_,_⟩ := Proofs.CppNestedRows.resolve_vroot state.frame (vb i) (V i) (vsc i)
      (bty i) (writable i) (maximum i) (buffers i) ok.binding ok.valid ok.vtag ok.vfound
      ok.lengths ok.flag ok.perm
    refine ⟨vb i,_,buffers i,vsc i,ok.slot,resolved,rfl,?_⟩
    unfold bty
    split <;> decide
  have sources : BeatsMemberBundle.Construction.MemberCopy.Sources state (fields sl base targetConst) := by
    intro field member
    simp only [fields,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ⟨i,inside,rfl⟩ | rfl | rfl
    · exact vectorSource i (List.mem_range.mp inside)
    · exact inf
    · exact size
  have good : BeatsMemberBundle.Construction.MemberCopy.Good state :=
    ⟨(vectors 0 (by decide)).valid,(vectors 0 (by decide)).lengths⟩
  obtain ⟨after,ran,goodAfter,kept,slots,scope,values,placed,vectors,scalars,work,space⟩ := BeatsMemberBundle.Construction.copy_space_of_fields state
    (sourceReceiver sl base) targetConst (fields sl base targetConst)
    (assembled sl base targetConst) good sources
  rw [target_reference] at ran values
  have vectorCount : ((fields sl base targetConst).filter BeatsMemberBundle.Construction.MemberCopy.vectorField).length = 15 := rfl
  have scalarCount : ((fields sl base targetConst).filter BeatsMemberBundle.Construction.MemberCopy.scalarField).length = 2 := rfl
  rw [vectorCount] at vectors
  rw [scalarCount] at scalars
  exact ⟨after,ran,goodAfter,kept,by simpa [fields] using slots,scope,values,placed,vectors,scalars,work,space⟩
end GeneratedBeatsCopyProof
