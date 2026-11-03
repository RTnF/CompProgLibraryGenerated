import Proofs.DynamicRetire

namespace Proofs.DynamicOwnedScope
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicRetire

-- Scalar cleanup followed by removal of roots owned by this scope.
def leave (outer inner : DynamicStmt.State) (scope : Nat) : Option DynamicStmt.State := do
  let final ← DynamicControl.leave outer inner
  some {final with contents := retireContents inner.contents scope}

def left (outer inner : NState) : NState :=
  let scalars : Proofs.CppState.State := {outer.scalars with
    memory := inner.scalars.memory.take outer.scalars.memory.length,
    work := inner.scalars.work+1,peak := max outer.scalars.peak inner.scalars.peak}
  let frame := {retiredFrame inner.frame (outer.scope+1) with bindings := inner.frame.bindings.take outer.frame.bindings.length}
  (⟨scalars.observe 0,frame,outer.slots,outer.scope,max outer.peak inner.peak⟩ : NState).observe

theorem left_peak (outer inner : NState)
    (fits : outer.scalars.memory.length ≤ inner.scalars.memory.length) :
    (left outer inner).peak = max (max outer.peak inner.peak)
      (max (max outer.scalars.peak inner.scalars.peak) (Proofs.CppNestedEval.liveS outer)+
        max inner.frame.state.storage.peak (inner.frame.state.liveSpace-inner.frame.state.storage.baseSpace)) := by
  have length : (inner.scalars.memory.take outer.scalars.memory.length).length = outer.scalars.memory.length := by
    simp [List.length_take,Nat.min_eq_left fits]
  change max (max outer.peak inner.peak)
    (max (max outer.scalars.peak inner.scalars.peak)
      ((inner.scalars.memory.take outer.scalars.memory.length).length-outer.scalars.baseMemory+outer.scalars.bindings.length+0)+_) = _
  rw [length]
  rfl

theorem leave_scalar (outer inner : NState) (returned : Option Int)
    (fits : outer.scalars.memory.length ≤ inner.scalars.memory.length)
    (types : (inner.scalars.memory.take outer.scalars.memory.length).map Proofs.CppState.Cell.type = outer.scalars.memory.map Proofs.CppState.Cell.type)
    (valid : inner.frame.state.wellFormed = true) :
    outer.leave inner (returned.map Ret.scalar) = some (left outer inner) := by
  have run := frame_runs inner.frame (outer.scope+1) valid
  cases returned <;> simp [NState.leave,fits,types,run,left] <;> rfl

theorem sound (params innerParams : List Parameter) (outer inner final : DynamicStmt.State) (s t : NState)
    (before : Realizes params outer.locals outer.contents s)
    (after : Realizes innerParams inner.locals inner.contents t)
    (subset : ∀ p ∈ params, p ∈ innerParams)
    (kept : ∀ p ∈ params, p.scope ≠ s.scope+1)
    (returned : Option Int) (pure : leave outer inner (s.scope+1) = some final) :
    s.leave t (returned.map Ret.scalar) = some (left s t) ∧ Realizes params final.locals final.contents (left s t) ∧
      (left s t).work = t.work+t.frame.state.destroyWork (s.scope+1)+1 := by
  obtain ⟨cleaned,leftRun,same⟩ := DynamicResultValid.bind_some _ _ _ pure
  have equal := Option.some.inj same
  subst final
  obtain ⟨fits,types,fields⟩ := DynamicScopeAuto.leave_fields outer inner cleaned leftRun
  have sm := congrArg Locals.memory before.locals
  have tm := congrArg Locals.memory after.locals
  change s.scalars.memory = outer.locals.memory at sm
  change t.scalars.memory = inner.locals.memory at tm
  have fits' : s.scalars.memory.length ≤ t.scalars.memory.length := by rw [sm,tm]; exact fits
  have types' : (t.scalars.memory.take s.scalars.memory.length).map Proofs.CppState.Cell.type = s.scalars.memory.map Proofs.CppState.Cell.type := by rw [sm,tm]; exact types
  obtain ⟨old,m0,oldFamily,_⟩ := before.heap
  obtain ⟨heap,m,family,erased⟩ := after.heap
  have retired := Family.retired family (s.scope+1) subset kept
  have bindings : ∀ p ∈ params, p.slot < s.frame.bindings.length := by
    intro p member
    exact (List.getElem?_eq_some_iff.mp (oldFamily.bindings p member)).1
  have finalFamily := retired.rebind (t.frame.bindings.take s.frame.bindings.length) (by
    intro p member
    rw [List.getElem?_take_of_lt (bindings p member)]
    exact family.bindings p (subset p member))
  refine ⟨leave_scalar s t returned fits' types' family.valid,?_,?_⟩
  · subst cleaned
    refine ⟨?_,retireHeap heap (s.scope+1),resources (retiredFrame t.frame (s.scope+1)),finalFamily,?_⟩
    · have sb := congrArg Locals.bindings before.locals
      have ss := congrArg Locals.slots before.locals
      change s.scalars.bindings = outer.locals.bindings at sb
      change s.slots = outer.locals.slots at ss
      change (⟨t.scalars.memory.take s.scalars.memory.length,s.scalars.bindings,s.slots⟩ : Locals) = _
      rw [sm,tm,sb,ss]
    · rw [erase_retire,erased]
  · change t.scalars.work+1+(t.frame.state.storage.work+t.frame.state.destroyWork (s.scope+1)) =
      t.scalars.work+t.frame.state.storage.work+t.frame.state.destroyWork (s.scope+1)+1
    omega

end Proofs.DynamicOwnedScope
