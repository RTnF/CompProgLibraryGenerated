import Proofs.DynamicOwnedConstruct

namespace Proofs.DynamicOwnedCleanup
open Proofs.CppNestedProgram Proofs.DynamicExpr Proofs.DynamicOwnedState

def enter (st : State) : State := {st with scope := st.scope+1}

theorem enter_real (st : State) (s : NState) (real : Realizes st s) :
    Realizes (enter st) {s with scope := s.scope+1} :=
  ⟨⟨real.data.locals,real.data.heap⟩,real.owner,real.binding,by change s.scope+1 = st.scope+1; rw [real.scopedState]⟩

-- Restore the outer reference table, retain the allocation cursor, and
-- remove owned roots from the logical heap. Tombstone IDs remain consumed.
def leave (outer inner : State) : Option State :=
  if outer.nextBinding ≤ inner.nextBinding ∧
      outer.params.all (fun p => decide (p ∈ inner.params)) = true ∧
      outer.params.all (fun p => decide (p.scope ≠ outer.scope+1)) = true then do
    let core ← DynamicOwnedScope.leave outer.core inner.core (outer.scope+1)
    some ⟨core,outer.params,inner.nextOwner,outer.nextBinding,outer.scope⟩
  else none

theorem sound (outer inner final : State) (s t : NState)
    (before : Realizes outer s) (after : Realizes inner t) (returned : Option Int)
    (pure : leave outer inner = some final) :
    s.leave t (returned.map Ret.scalar) = some (DynamicOwnedScope.left s t) ∧
      Realizes final (DynamicOwnedScope.left s t) ∧
      (DynamicOwnedScope.left s t).work = t.work+t.frame.state.destroyWork (outer.scope+1)+1 := by
  unfold leave at pure
  split at pure
  · rename_i good
    obtain ⟨core,leftRun,same⟩ := DynamicResultValid.bind_some _ _ _ pure
    have equal := Option.some.inj same
    subst final
    have subset : ∀ p ∈ outer.params, p ∈ inner.params := by
      intro p member
      exact of_decide_eq_true (List.all_eq_true.mp good.2.1 p member)
    have kept : ∀ p ∈ outer.params, p.scope ≠ s.scope+1 := by
      intro p member
      rw [before.scopedState]
      exact of_decide_eq_true (List.all_eq_true.mp good.2.2 p member)
    have actualCore : DynamicOwnedScope.leave outer.core inner.core (s.scope+1) = some core := by
      rw [before.scopedState]; exact leftRun
    obtain ⟨ran,real,work⟩ := DynamicOwnedScope.sound outer.params inner.params outer.core inner.core core s t before.data after.data subset kept returned actualCore
    refine ⟨ran,⟨real,?_,?_,before.scopedState⟩,?_⟩
    · change (t.frame.state.retired (s.scope+1)).storage.objects.length = inner.nextOwner
      rw [(Proofs.CppNestedVectorStore.retired_lengths t.frame.state (s.scope+1)).2,after.owner]
    · change (t.frame.bindings.take s.frame.bindings.length).length = outer.nextBinding
      rw [List.length_take,before.binding,after.binding,Nat.min_eq_left good.1]
    · rw [before.scopedState] at work; exact work
  · contradiction

end Proofs.DynamicOwnedCleanup
