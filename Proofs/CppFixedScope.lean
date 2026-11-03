import Proofs.CppFixedWrite
import Proofs.CppNoResizeRun

namespace Proofs.CppFixedScope
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppNoResizeStmt Proofs.CppBufferHeaders Proofs.DynamicResultValid

theorem retire_values (f g : Frame) (scope : Nat)
    (fresh : ∀ owner, f.state.forest.context owner ≠ some scope)
    (actual : f.retireScope scope = some g) : g.bindings = f.bindings ∧ ∀ other, g.state.storage.lookup other = f.state.storage.lookup other := by
  unfold Frame.retireScope at actual
  obtain ⟨state,retired,rest⟩ := bind_some _ _ _ actual
  unfold State.retireScope at retired
  split at retired
  · dsimp only at retired
    split at retired
    · have eq := Option.some.inj retired
      subst state
      have eq := Option.some.inj rest
      subst g
      refine ⟨rfl,?_⟩
      intro other
      rw [Proofs.CppNestedScope.retired_fresh f.state scope fresh]
      rfl
    · simp at retired
  · simp at retired

theorem leave_values (outer inner out : NState) (returned : Option Ret)
    (headers : SameHeaders outer.frame.state inner.frame.state)
    (bindings : inner.frame.bindings = outer.frame.bindings)
    (value : ScalarResult returned)
    (contexts : ∀ owner scope, outer.frame.state.forest.context owner = some scope → scope ≤ outer.scope)
    (actual : outer.leave inner returned = some out) :
    out.frame.bindings = outer.frame.bindings ∧ out.slots = outer.slots ∧
      ∀ other, out.frame.state.storage.lookup other = inner.frame.state.storage.lookup other := by
  have fresh : ∀ owner, inner.frame.state.forest.context owner ≠ some (outer.scope+1) := by
    intro owner found
    rw [headers.forest] at found
    have bound := contexts owner (outer.scope+1) found
    omega
  cases returned with
  | none =>
    unfold NState.leave at actual
    split at actual
    · dsimp only at actual
      obtain ⟨moved,movedEq,rest⟩ := bind_some _ _ _ actual
      have eq := Option.some.inj movedEq
      subst moved
      obtain ⟨retired,ran,rest⟩ := bind_some _ _ _ rest
      obtain ⟨retiredBindings,lookups⟩ := retire_values inner.frame retired (outer.scope+1) fresh ran
      have eq := Option.some.inj rest
      subst out
      refine ⟨?_,rfl,lookups⟩
      change retired.bindings.take outer.frame.bindings.length = outer.frame.bindings
      rw [retiredBindings,bindings,List.take_length]
    · simp at actual
  | some result =>
    cases result with
    | scalar v =>
      unfold NState.leave at actual
      split at actual
      · dsimp only at actual
        obtain ⟨moved,movedEq,rest⟩ := bind_some _ _ _ actual
        have eq := Option.some.inj movedEq
        subst moved
        obtain ⟨retired,ran,rest⟩ := bind_some _ _ _ rest
        obtain ⟨retiredBindings,lookups⟩ := retire_values inner.frame retired (outer.scope+1) fresh ran
        have eq := Option.some.inj rest
        subst out
        refine ⟨?_,rfl,lookups⟩
        change retired.bindings.take outer.frame.bindings.length = outer.frame.bindings
        rw [retiredBindings,bindings,List.take_length]
      · simp at actual
    | unit => simp [ScalarResult] at value
    | vector owner element => simp [ScalarResult] at value

end Proofs.CppFixedScope
