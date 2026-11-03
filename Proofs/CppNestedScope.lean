import Proofs.CppNestedStmt

namespace Proofs.CppNestedScope
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt

-- Retiring a scope that owns no object only updates the peak observation.
theorem retired_fresh (s : State) (scope : Nat) (fresh : ∀ owner, s.forest.context owner ≠ some scope) :
    s.retired scope = {s with storage := {s.storage with
      peak := max s.storage.peak (s.liveSpace-s.storage.baseSpace)}} := by
  unfold State.retired
  have forest : s.forest.retired scope = s.forest := by
    unfold Forest.retired
    congr 1
    apply List.mapIdx_eq_iff.mpr
    intro i
    cases found : s.forest.objects[i]? with
    | none => rfl
    | some tag => simp [fresh i]
  have objects : s.storage.objects.mapIdx (fun owner buffer =>
      if s.forest.context owner = some scope then none else buffer) = s.storage.objects := by
    apply List.mapIdx_eq_iff.mpr
    intro i
    cases found : s.storage.objects[i]? with
    | none => rfl
    | some buffer => simp [fresh i]
  have work : s.destroyWork scope = 0 := by
    unfold State.destroyWork
    have zero : ∀ owner, (if s.forest.context owner = some scope then
        (match s.forest.lookup owner, s.storage.lookup owner with
          | some tag, some buffer => match tag.element with
            | .integer _ => 1
            | .vector _ => buffer.items.length+1
          | _, _ => 0) else 0) = 0 := by
      intro owner
      simp [fresh owner]
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x member
    obtain ⟨owner,_,rfl⟩ := List.mem_map.mp member
    exact zero owner
  simp [forest,objects,work]

-- The frame of a scope exit that retires nothing: only the peak observation changes.
def noopRetired (f : Frame) : Frame :=
  {f with state := {f.state with storage := {f.state.storage with
    peak := max f.state.storage.peak (f.state.liveSpace-f.state.storage.baseSpace)}}}

theorem retireScope_fresh (f : Frame) (scope : Nat) (valid : f.state.wellFormed = true)
    (fresh : ∀ owner, f.state.forest.context owner ≠ some scope) :
    f.retireScope scope = some (noopRetired f) := by
  have retired := retired_fresh f.state scope fresh
  have next := CppNestedVectorStore.retired_wellFormed f.state scope valid
  rw [retired] at next
  unfold Frame.retireScope State.retireScope
  rw [if_pos valid]
  simp only [retired,next,if_true]
  rfl

-- The state after leaving a lexical scope that returned no vector and owned no object.
def _root_.Proofs.CppNestedProgram.NState.left (outer inner : NState) : NState :=
  let scalars : CppState.State := {outer.scalars with
    memory := inner.scalars.memory.take outer.scalars.memory.length,
    work := inner.scalars.work+1,peak := max outer.scalars.peak inner.scalars.peak}
  let frame : Frame := {noopRetired inner.frame with
    bindings := inner.frame.bindings.take outer.frame.bindings.length}
  (⟨scalars.observe 0,frame,outer.slots,outer.scope,max outer.peak inner.peak⟩ : NState).observe

theorem leave_scalar (outer inner : NState) (returned : Option Ret)
    (notVector : ∀ owner element, returned ≠ some (.vector owner element))
    (fits : outer.scalars.memory.length ≤ inner.scalars.memory.length)
    (types : (inner.scalars.memory.take outer.scalars.memory.length).map CppState.Cell.type =
      outer.scalars.memory.map CppState.Cell.type)
    (valid : inner.frame.state.wellFormed = true)
    (fresh : ∀ owner, inner.frame.state.forest.context owner ≠ some (outer.scope+1)) :
    outer.leave inner returned = some (outer.left inner) := by
  have run := retireScope_fresh inner.frame (outer.scope+1) valid fresh
  cases returned with
  | none => simp [NState.leave,fits,types,run]; rfl
  | some value =>
    cases value with
    | scalar v => simp [NState.leave,fits,types,run]; rfl
    | unit => simp [NState.leave,fits,types,run]; rfl
    | vector owner element => exact absurd rfl (notVector owner element)

section leftFields
variable (outer inner : NState)
@[simp] theorem left_slots : (outer.left inner).slots = outer.slots := rfl
@[simp] theorem left_scope : (outer.left inner).scope = outer.scope := rfl
@[simp] theorem left_memory :
    (outer.left inner).scalars.memory = inner.scalars.memory.take outer.scalars.memory.length := rfl
@[simp] theorem left_bindings : (outer.left inner).scalars.bindings = outer.scalars.bindings := rfl
@[simp] theorem left_baseMemory : (outer.left inner).scalars.baseMemory = outer.scalars.baseMemory := rfl
@[simp] theorem left_work : (outer.left inner).scalars.work = inner.scalars.work+1 := rfl
theorem left_scalar_peak : (outer.left inner).scalars.peak = max (max outer.scalars.peak inner.scalars.peak)
    ((inner.scalars.memory.take outer.scalars.memory.length).length-outer.scalars.baseMemory+
      outer.scalars.bindings.length+0) := rfl
@[simp] theorem left_state : (outer.left inner).frame.state = (noopRetired inner.frame).state := rfl
@[simp] theorem left_rootWritable : (outer.left inner).frame.rootWritable = inner.frame.rootWritable := rfl
@[simp] theorem left_frameBindings :
    (outer.left inner).frame.bindings = inner.frame.bindings.take outer.frame.bindings.length := rfl
theorem left_peak : (outer.left inner).peak = max (max outer.peak inner.peak)
    ((outer.left inner).scalars.peak+(noopRetired inner.frame).state.storage.peak) := rfl
end leftFields

end Proofs.CppNestedScope
