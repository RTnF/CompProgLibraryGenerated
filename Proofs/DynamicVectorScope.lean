import Proofs.DynamicTransfer

namespace Proofs.DynamicVectorScope
open Proofs.CppNestedProgram Proofs.DynamicExpr Proofs.DynamicOwnedState
open Proofs.CppVectorOwnership Proofs.CppRootModel Proofs.CppRowsFrame Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicTransfer

-- The returned root remains in contents, but its stale inner-scope bindings
-- must not remain in the restored parameter registry.
def leave (outer inner : State) (root : Nat) (element : Element) : Option State := do
  let view ← inner.core.contents root
  if view.scope = outer.scope+1 ∧ view.element = element ∧
      outer.nextBinding ≤ inner.nextBinding ∧
      outer.params.all (fun p => decide (p ∈ inner.params)) = true ∧
      outer.params.all (fun p => decide (p.owner ≠ root)) = true ∧
      outer.params.all (fun p => decide (p.scope ≠ outer.scope+1)) = true then do
    let core ← DynamicOwnedScope.leave outer.core
      {inner.core with contents := moveContents inner.core.contents root outer.scope} (outer.scope+1)
    some ⟨core,outer.params,inner.nextOwner,outer.nextBinding,outer.scope⟩
  else none

theorem leave_eq (s t : NState) (root : Nat) (element : Element) (frame : Proofs.CppNestedVectorBindings.Frame)
    (moved : t.frame.transferRoot root element (s.scope+1) s.scope = some frame) :
    s.leave t (some (.vector root element)) = s.leave {t with frame := frame} none := by
  simp only [NState.leave]
  split
  · simp only [moved,Bind.bind,Option.bind]
  · rfl

theorem sound (outer inner final : State) (s t : NState)
    (before : Realizes outer s) (after : Realizes inner t) (root : Nat) (element : Element)
    (pureRun : leave outer inner root element = some final) :
    ∃ (frame : Proofs.CppNestedVectorBindings.Frame) (out : NState),
      t.frame.transferRoot root element (s.scope+1) s.scope = some frame ∧
      s.leave t (some (.vector root element)) = some out ∧ Realizes final out ∧
      out.work = t.work+frame.state.destroyWork (s.scope+1)+1 := by
  obtain ⟨view,lookup,rest⟩ := DynamicResultValid.bind_some _ _ _ pureRun
  split at rest
  · rename_i good
    obtain ⟨core,pureLeave,same⟩ := DynamicResultValid.bind_some _ _ _ rest
    have equal := Option.some.inj same
    subst final
    have subset : ∀ p ∈ outer.params, p ∈ inner.params := by
      intro p member
      exact of_decide_eq_true (List.all_eq_true.mp good.2.2.2.1 p member)
    have different : ∀ p ∈ outer.params, p.owner ≠ root := by
      intro p member
      exact of_decide_eq_true (List.all_eq_true.mp good.2.2.2.2.1 p member)
    have kept : ∀ p ∈ outer.params, p.scope ≠ s.scope+1 := by
      intro p member
      rw [before.scopedState]
      exact of_decide_eq_true (List.all_eq_true.mp good.2.2.2.2.2 p member)
    obtain ⟨heap,m,family,he⟩ := after.data.heap
    obtain ⟨v,hv,erased⟩ := DynamicTransfer.lift heap root view (by rw [he]; exact lookup)
    have scope : v.scope = s.scope+1 := by
      have sameScope : (erase v).scope = v.scope := by cases v <;> rfl
      rw [← sameScope,erased,before.scopedState]; exact good.1
    have typed : v.element = element := by
      have sameElement : (erase v).element = v.element := by cases v <;> rfl
      rw [← sameElement,erased]; exact good.2.1
    let frame := movedFrame t.frame root s.scope v
    let moved := {t with frame := frame}
    have movedFamily := DynamicTransfer.Family.moved family root s.scope v hv subset different
    have movedReal : DynamicRealizes.Realizes outer.params inner.core.locals
        (moveContents inner.core.contents root outer.scope) moved := by
      refine ⟨after.data.locals,moveHeap heap root s.scope,resources frame,movedFamily,?_⟩
      rw [erase_move,he,before.scopedState]
    have run : t.frame.transferRoot root element (s.scope+1) s.scope = some frame := by
      rw [← scope,← typed]
      exact frame_runs t.frame root s.scope v (family.models root v hv)
    have actualPure : DynamicOwnedScope.leave outer.core
        {inner.core with contents := moveContents inner.core.contents root outer.scope} (s.scope+1) = some core := by
      rw [before.scopedState]; exact pureLeave
    obtain ⟨done,real,work⟩ := DynamicOwnedScope.sound outer.params outer.params outer.core
      {inner.core with contents := moveContents inner.core.contents root outer.scope} core s moved before.data movedReal
      (fun _ h => h) kept none actualPure
    have actual : s.leave t (some (.vector root element)) = some (DynamicOwnedScope.left s moved) := by
      rw [leave_eq s t root element frame run]; exact done
    refine ⟨frame,DynamicOwnedScope.left s moved,run,actual,⟨real,?_,?_,before.scopedState⟩,work⟩
    · change (frame.state.retired (s.scope+1)).storage.objects.length = inner.nextOwner
      rw [(Proofs.CppNestedVectorStore.retired_lengths frame.state (s.scope+1)).2]
      exact after.owner
    · change (t.frame.bindings.take s.frame.bindings.length).length = outer.nextBinding
      rw [List.length_take,before.binding,after.binding,Nat.min_eq_left good.2.2.1]
  · contradiction

end Proofs.DynamicVectorScope
