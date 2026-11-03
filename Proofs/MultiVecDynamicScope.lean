import Proofs.MultiVecDynamicHoare
import Proofs.DoublingNested

namespace Proofs.MultiVecDynamicScope
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppNestedProgram Proofs.CppNestedScope Proofs.CppNestedHoare
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.MultiVecDynamicHoare
open Proofs.DoublingNested

theorem Models.same_objects {s t : State} (same : SameObjects s t) (root : Nat) (v : View)
    (model : Models s root v) : Models t root v := by
  cases v with
  | flat ty sc vs =>
    refine ⟨?_,?_,?_⟩
    · rw [same.wellFormed]; exact model.valid
    · rw [same.1]; exact model.tag
    · obtain ⟨b,hb,hi⟩ := model.buffer
      exact ⟨b,by rw [same.lookup]; exact hb,hi⟩
  | rows ty sc ids epoch vs =>
    refine ⟨⟨?_,?_,?_⟩,model.length,?_⟩
    · rw [same.wellFormed]; exact model.rows.valid
    · rw [same.1]; exact model.rows.rootTag
    · obtain ⟨b,hb,he,hi⟩ := model.rows.buffer
      exact ⟨b,by rw [same.lookup]; exact hb,he,hi⟩
    · intro k owner lookup
      obtain ⟨b,hb,hi⟩ := model.contents k owner lookup
      exact ⟨b,by rw [same.lookup]; exact hb,hi⟩

def observed (m : Resources) : Resources := {m with peak := max m.peak (m.live-m.base)}

theorem Family.noopRetired {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) : Family params h (noopRetired f) (observed m) := by
  have same := noopRetired_same f
  refine ⟨?_,?_,family.lengths,family.bindings,family.flags,family.permissions,family.views,?_⟩
  · rw [same.wellFormed]; exact family.valid
  · intro root v lookup
    exact Models.same_objects same root v (family.models root v lookup)
  · refine ⟨?_,family.measured.work,?_,family.measured.count,family.measured.base⟩
    · rw [same.liveSpace]; exact family.measured.live
    · simp [Proofs.CppNestedScope.noopRetired,observed,family.measured.peak,family.measured.live,family.measured.base]

theorem Family.left {params : List Parameter} {h : Heap} {m : Resources} (outer inner : NState)
    (family : Family params h inner.frame m)
    (bounds : ∀ p ∈ params, p.slot < outer.frame.bindings.length) :
    Family params h (outer.left inner).frame (observed m) := by
  have retired := Family.noopRetired family
  exact retired.rebind _ (by
    intro p hp
    rw [List.getElem?_take_of_lt (bounds p hp)]
    exact family.bindings p hp)

theorem Runs.scope_scalar {params : List Parameter} {body : Command} {s : NState} {Q : Post}
    (run : Runs params body {s with scope := s.scope+1} fun h m inner =>
      (∀ owner element, inner.returned ≠ some (.vector owner element)) ∧
      s.scalars.memory.length ≤ inner.state.scalars.memory.length ∧
      (inner.state.scalars.memory.take s.scalars.memory.length).map Proofs.CppState.Cell.type =
        s.scalars.memory.map Proofs.CppState.Cell.type ∧
      (∀ owner, inner.state.frame.state.forest.context owner ≠ some (s.scope+1)) ∧
      (∀ p ∈ params, p.slot < s.frame.bindings.length) ∧
      Q h (observed m) {inner with state := s.left inner.state}) :
    Runs params (.scope body) s Q := by
  apply RunsTo.scope
  apply RunsTo.mono run
  intro inner ⟨h,m,family,notVector,fits,types,fresh,bounds,post⟩
  exact ⟨s.left inner.state,leave_scalar s inner.state inner.returned notVector fits types family.valid fresh,
    h,observed m,Family.left s inner.state family bounds,post⟩

end Proofs.MultiVecDynamicScope
