import Proofs.DynamicFinishFamily

namespace Proofs.DynamicFinishSelect
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppRootModel Proofs.CppRowsFrame Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicTransfer

-- Check the declared result kind, then transfer a returned root before any
-- callee-owned object is retired. Scalar and unit returns transfer nothing.
def contents (st : DynamicOwnedState.State) (scope : Nat) (kind : ResultKind) (returned : Option Ret) : Option (ContentsHeap × Ret) :=
  match kind,returned with
  | .scalar ty,some (.scalar x) => if ty.valid x then some (st.core.contents,.scalar x) else none
  | .unit,none => some (st.core.contents,.unit)
  | .vector element,some (.vector root returnedElement) =>
      if returnedElement = element then do
        let view ← st.core.contents root
        if view.scope = st.scope ∧ view.element = element then
          some (moveContents st.core.contents root scope,.vector root element)
        else none
      else none
  | _,_ => none

def frame (s : NState) (scope : Nat) (kind : ResultKind) (returned : Option Ret) :
    Option (Frame × Ret) := match kind,returned with
  | .scalar ty,some (.scalar x) => if ty.valid x then some (s.frame,.scalar x) else none
  | .unit,none => some (s.frame,.unit)
  | .vector element,some (.vector root returnedElement) =>
      if returnedElement = element then do
        let moved ← s.frame.transferRoot root element s.scope scope
        some (moved,.vector root element)
      else none
  | _,_ => none

theorem sound (st : DynamicOwnedState.State) (s : NState) (real : DynamicOwnedState.Realizes st s)
    (scope : Nat) (kind : ResultKind) (returned : Option Ret) (final : ContentsHeap) (value : Ret)
    (pureRun : contents st scope kind returned = some (final,value)) :
    ∃ (next : Frame) (heap : Heap) (m : Resources), frame s scope kind returned = some (next,value) ∧
      Family [] heap next m ∧ eraseHeap heap = final ∧ next.rootWritable = s.frame.rootWritable ∧
      next.state.storage.objects.length = s.frame.state.storage.objects.length ∧
      next.state.storage.work = s.frame.state.storage.work := by
  obtain ⟨h,m,family,erased⟩ := real.data.heap
  have empty := DynamicFinishFamily.Family.restrict family [] (fun p member => by cases member)
  cases kind with
  | unit =>
    cases returned with
    | none =>
      have pairs := Prod.mk.inj (Option.some.inj pureRun)
      obtain ⟨rfl,rfl⟩ := pairs
      exact ⟨s.frame,h,m,rfl,empty,erased,rfl,rfl,rfl⟩
    | some value => cases value <;> simp [contents] at pureRun
  | scalar ty =>
    cases returned with
    | none => simp [contents] at pureRun
    | some ret =>
      cases ret with
      | unit | vector _ _ => simp [contents] at pureRun
      | scalar x =>
        by_cases accepted : ty.valid x = true
        · have pairs := Prod.mk.inj (Option.some.inj (by simpa [contents,accepted] using pureRun))
          obtain ⟨rfl,rfl⟩ := pairs
          exact ⟨s.frame,h,m,by simp [frame,accepted],empty,erased,rfl,rfl,rfl⟩
        · simp [contents,accepted] at pureRun
  | vector element =>
    cases returned with
    | none => simp [contents] at pureRun
    | some ret =>
      cases ret with
      | unit | scalar _ => simp [contents] at pureRun
      | vector root returnedElement =>
        by_cases typed : returnedElement = element
        · subst returnedElement
          cases lookup : st.core.contents root with
          | none => simp [contents,lookup] at pureRun
          | some view =>
            simp only [contents,ite_true,lookup,Bind.bind,Option.bind] at pureRun
            split at pureRun
            · rename_i good
              have pairs := Prod.mk.inj (Option.some.inj pureRun)
              obtain ⟨rfl,rfl⟩ := pairs
              obtain ⟨v,hv,eraseEq⟩ := DynamicTransfer.lift h root view (by rw [erased]; exact lookup)
              have viewScope : v.scope = s.scope := by
                have same : (erase v).scope = v.scope := by cases v <;> rfl
                rw [← same,eraseEq,real.scopedState]; exact good.1
              have viewElement : v.element = element := by
                have same : (erase v).element = v.element := by cases v <;> rfl
                rw [← same,eraseEq]; exact good.2
              have moved := frame_runs s.frame root scope v (family.models root v hv)
              rw [viewScope,viewElement] at moved
              refine ⟨movedFrame s.frame root scope v,moveHeap h root scope,resources (movedFrame s.frame root scope v),?_,?_,?_,rfl,rfl,rfl⟩
              · simp [frame,moved]
              · exact DynamicTransfer.Family.moved family root scope v hv (fun p member => by cases member) (fun p member => by cases member)
              · rw [erase_move,erased]
            · contradiction
        · simp [contents,typed] at pureRun

end Proofs.DynamicFinishSelect
