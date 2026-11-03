import Proofs.DynamicFinishSelect

namespace Proofs.DynamicOwnedFinish
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.DynamicOwnedState Proofs.DynamicExpr
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicRetire
open Proofs.DynamicFinishFamily

-- Caller metadata replaces callee metadata. No inclusion or length ordering
-- between their parameter registries or vector binding lists is assumed.
def finish (outer inner : State) (kind : ResultKind) (returned : Option Ret) : Option (State × Ret) := do
  let left ← DynamicControl.leave outer.core inner.core
  let (selected,value) ← DynamicFinishSelect.contents inner outer.scope kind returned
  let final := retireContents selected inner.scope
  if compatible outer.params final then
    some (⟨{left with contents := final},outer.params,inner.nextOwner,outer.nextBinding,outer.scope⟩,value)
  else none

def restored (caller callee : NState) (retired : Proofs.CppNestedVectorBindings.Frame) : NState :=
  let scalars : Proofs.CppState.State := {caller.scalars with
    memory := callee.scalars.memory.take caller.scalars.memory.length,
    work := callee.scalars.work+1,peak := max caller.scalars.peak callee.scalars.peak}
  let frame := {retired with bindings := caller.frame.bindings}
  (⟨scalars.observe 0,frame,caller.slots,caller.scope,max caller.peak callee.peak⟩ : NState).observe

theorem finish_eq (s t : NState) (kind : ResultKind) (returned : Option Ret)
    (frame : Proofs.CppNestedVectorBindings.Frame) (value : Ret)
    (fits : s.scalars.memory.length ≤ t.scalars.memory.length)
    (types : (t.scalars.memory.take s.scalars.memory.length).map Proofs.CppState.Cell.type = s.scalars.memory.map Proofs.CppState.Cell.type)
    (selected : DynamicFinishSelect.frame t s.scope kind returned = some (frame,value))
    (valid : frame.state.wellFormed = true) :
    CppNestedCall.finish s t kind returned = some (restored s t (retiredFrame frame t.scope),value) := by
  have retire := frame_runs frame t.scope valid
  cases kind with
  | unit =>
    cases returned with
    | none =>
      have pairs := Prod.mk.inj (Option.some.inj selected)
      obtain ⟨rfl,rfl⟩ := pairs
      simp [CppNestedCall.finish,fits,types,retire,restored]
    | some value => cases value <;> simp [DynamicFinishSelect.frame] at selected
  | scalar ty =>
    cases returned with
    | none => simp [DynamicFinishSelect.frame] at selected
    | some ret =>
      cases ret with
      | unit | vector _ _ => simp [DynamicFinishSelect.frame] at selected
      | scalar x =>
        by_cases good : ty.valid x = true
        · have pairs := Prod.mk.inj (Option.some.inj (by simpa [DynamicFinishSelect.frame,good] using selected))
          obtain ⟨rfl,rfl⟩ := pairs
          simp [CppNestedCall.finish,fits,types,good,retire,restored]
        · simp [DynamicFinishSelect.frame,good] at selected
  | vector element =>
    cases returned with
    | none => simp [DynamicFinishSelect.frame] at selected
    | some ret =>
      cases ret with
      | unit | scalar _ => simp [DynamicFinishSelect.frame] at selected
      | vector root returnedElement =>
        by_cases typed : returnedElement = element
        · subst returnedElement
          cases moved : t.frame.transferRoot root element t.scope s.scope with
          | none => simp [DynamicFinishSelect.frame,moved] at selected
          | some next =>
            have pairs := Prod.mk.inj (Option.some.inj (by simpa [DynamicFinishSelect.frame,moved] using selected))
            obtain ⟨rfl,rfl⟩ := pairs
            simp [CppNestedCall.finish,fits,types,moved,retire,restored]
        · simp [DynamicFinishSelect.frame,typed] at selected

theorem sound (outer inner final : State) (s t : NState)
    (before : Realizes outer s) (after : Realizes inner t) (kind : ResultKind) (returned : Option Ret) (value : Ret)
    (pureRun : finish outer inner kind returned = some (final,value))
    (flags : ∃ extra, t.frame.rootWritable = s.frame.rootWritable ++ extra) :
    ∃ (frame : Proofs.CppNestedVectorBindings.Frame) (out : NState),
      DynamicFinishSelect.frame t s.scope kind returned = some (frame,value) ∧
      CppNestedCall.finish s t kind returned = some (out,value) ∧ Realizes final out ∧
      out.work = t.work+frame.state.destroyWork t.scope+1 := by
  obtain ⟨left,leftRun,selectRest⟩ := DynamicResultValid.bind_some _ _ _ pureRun
  obtain ⟨pair,selectedPure,finishRest⟩ := DynamicResultValid.bind_some _ _ _ selectRest
  obtain ⟨logical,ret⟩ := pair
  dsimp only at finishRest
  split at finishRest
  · rename_i checked
    have pairs := Prod.mk.inj (Option.some.inj finishRest)
    obtain ⟨rfl,rfl⟩ := pairs
    obtain ⟨fits,types,fields⟩ := DynamicScopeAuto.leave_fields outer.core inner.core left leftRun
    have sm := congrArg Locals.memory before.data.locals
    have tm := congrArg Locals.memory after.data.locals
    change s.scalars.memory = outer.core.locals.memory at sm
    change t.scalars.memory = inner.core.locals.memory at tm
    have fits' : s.scalars.memory.length ≤ t.scalars.memory.length := by rw [sm,tm]; exact fits
    have types' : (t.scalars.memory.take s.scalars.memory.length).map Proofs.CppState.Cell.type = s.scalars.memory.map Proofs.CppState.Cell.type := by rw [sm,tm]; exact types
    obtain ⟨frame,heap,m,selected,family,erased,rights,count,work⟩ := DynamicFinishSelect.sound inner t after outer.scope kind returned logical ret selectedPure
    rw [← before.scopedState] at selected
    have retired := DynamicRetire.Family.retired family t.scope (kept := []) (fun p h => by cases h) (fun p h => by cases h)
    have erasedRetired : eraseHeap (retireHeap heap t.scope) = retireContents logical inner.scope := by rw [erase_retire,erased,after.scopedState]
    have compatibleRetired : compatible outer.params (eraseHeap (retireHeap heap t.scope)) = true := by rw [erasedRetired]; exact checked
    obtain ⟨old,m0,oldFamily,oldErase⟩ := before.data.heap
    have rebound := DynamicFinishFamily.rebound oldFamily retired compatibleRetired (by
      change ∃ extra, frame.rootWritable = s.frame.rootWritable ++ extra
      rw [rights]; exact flags)
    let out := restored s t (retiredFrame frame t.scope)
    have data : DynamicRealizes.Realizes outer.params left.locals (retireContents logical inner.scope) out := by
      refine ⟨?_,retireHeap heap t.scope,resources (retiredFrame frame t.scope),rebound,erasedRetired⟩
      rw [fields]
      have sb := congrArg Locals.bindings before.data.locals
      have ss := congrArg Locals.slots before.data.locals
      change s.scalars.bindings = outer.core.locals.bindings at sb
      change s.slots = outer.core.locals.slots at ss
      change (⟨t.scalars.memory.take s.scalars.memory.length,s.scalars.bindings,s.slots⟩ : Locals) = _
      rw [sm,tm,sb,ss]
    refine ⟨frame,out,selected,finish_eq s t kind returned frame ret fits' types' selected family.valid,
      ⟨data,?_,before.binding,before.scopedState⟩,?_⟩
    · change (frame.state.retired t.scope).storage.objects.length = inner.nextOwner
      rw [(Proofs.CppNestedVectorStore.retired_lengths frame.state t.scope).2,count,after.owner]
    · change t.scalars.work+1+(frame.state.storage.work+frame.state.destroyWork t.scope) = t.work+frame.state.destroyWork t.scope+1
      rw [work]
      unfold NState.work
      omega
  · contradiction

end Proofs.DynamicOwnedFinish
