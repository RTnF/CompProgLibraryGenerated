import Proofs.CppNoResizeStmt
import Proofs.CppNestedScope

namespace Proofs.CppNoResizeScope
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppNoResizeStmt Proofs.CppBufferHeaders Proofs.DynamicResultValid

def Allowed : Command → Bool
  | .primitive stmt => Proofs.CppNoResizeStmt.Allowed stmt
  | .sequence a b | .branch _ a b => Allowed a && Allowed b
  | .scope body | .whileLoop _ body => Allowed body
  | .breakLoop => true
  | _ => false

theorem retired_headers (s : State) (scope : Nat)
    (fresh : ∀ owner, s.forest.context owner ≠ some scope) : SameHeaders s (s.retired scope) := by
  rw [Proofs.CppNestedScope.retired_fresh s scope fresh]
  exact ⟨rfl,rfl,rfl,fun _ => rfl⟩

theorem retire_frame (f g : Frame) (scope : Nat)
    (fresh : ∀ owner, f.state.forest.context owner ≠ some scope)
    (actual : f.retireScope scope = some g) : SameHeaders f.state g.state ∧ g.rootWritable = f.rootWritable := by
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
      exact ⟨retired_headers f.state scope fresh,rfl⟩
    · simp at retired
  · simp at retired

theorem leave_effect (outer inner out : NState) (returned : Option Ret)
    (headers : SameHeaders outer.frame.state inner.frame.state)
    (flags : inner.frame.rootWritable = outer.frame.rootWritable)
    (value : ScalarResult returned)
    (contexts : ∀ owner scope, outer.frame.state.forest.context owner = some scope → scope ≤ outer.scope)
    (actual : outer.leave inner returned = some out) :
    SameHeaders outer.frame.state out.frame.state ∧ out.frame.rootWritable = outer.frame.rootWritable ∧ out.scope = outer.scope := by
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
      obtain ⟨post,rw⟩ := retire_frame inner.frame retired (outer.scope+1) fresh ran
      have eq := Option.some.inj rest
      subst out
      exact ⟨headers.trans post,rw.trans flags,rfl⟩
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
        obtain ⟨post,rw⟩ := retire_frame inner.frame retired (outer.scope+1) fresh ran
        have eq := Option.some.inj rest
        subst out
        exact ⟨headers.trans post,rw.trans flags,rfl⟩
      · simp at actual
    | unit => simp [ScalarResult] at value
    | vector owner element => simp [ScalarResult] at value

end Proofs.CppNoResizeScope
