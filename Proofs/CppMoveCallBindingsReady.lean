import Proofs.CppMoveCallBindings

namespace Proofs.CppMoveCallBindingsReady
open Proofs.CppMoveCallBindings Proofs.CppNestedProgram Proofs.CppNestedVectorBindings

theorem gather_ready (bindings : List Binding) (indices : List Nat)
    (bounds : ∀ index, index ∈ indices → index < bindings.length) :
    ∃ out, indices.mapM (fun index => bindings[index]?) = some out := by
  induction indices with
  | nil => exact ⟨[],rfl⟩
  | cons head tail ih =>
    have inside := bounds head (by simp)
    cases found : bindings[head]? with
    | none =>
      have outside := List.getElem?_eq_none_iff.mp found
      omega
    | some binding =>
      obtain ⟨rest,run⟩ := ih (fun index member => bounds index (by simp [member]))
      exact ⟨binding::rest,by simp [List.mapM_cons,found,run]⟩

theorem compact_ready (s : NState)
    (bounds : ∀ index, index ∈ vectorIndices s.slots → index < s.frame.bindings.length) :
    ∃ out, compact s = some out := by
  obtain ⟨bindings,run⟩ := gather_ready s.frame.bindings (vectorIndices s.slots) bounds
  exact ⟨{s with frame := {s.frame with bindings := bindings},slots := compactSlots 0 s.slots},
    by simp [compact,run]⟩

end Proofs.CppMoveCallBindingsReady
