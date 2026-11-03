import Proofs.CppStmtPeak
import Proofs.CppNoResizeScope

namespace Proofs.CppPeakScope
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppNoResizeStmt Proofs.CppBufferHeaders Proofs.DynamicResultValid Proofs.CppPeakComponents

theorem restore {s t u : NState} (growth : Grows s t)
    (scalar : t.scalars.peak ≤ u.scalars.peak) (storage : t.frame.state.storage.peak ≤ u.frame.state.storage.peak)
    (peak : u.peak ≤ max (max s.peak t.peak) (u.scalars.peak+u.frame.state.storage.peak)) : Grows s u := by
  refine ⟨Nat.le_trans growth.scalar scalar,Nat.le_trans growth.storage storage,?_⟩
  have inner := Nat.le_trans growth.outer (max_mono s.peak (Nat.add_le_add scalar storage))
  exact Nat.le_trans peak (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.le_max_left _ _,inner⟩,Nat.le_max_right _ _⟩)

theorem leave_grows (outer inner out : NState) (returned : Option Ret)
    (headers : SameHeaders outer.frame.state inner.frame.state)
    (growth : Grows outer inner)
    (value : ScalarResult returned)
    (contexts : ∀ owner scope, outer.frame.state.forest.context owner = some scope → scope ≤ outer.scope)
    (actual : outer.leave inner returned = some out) :
    Grows outer out := by
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
      have retiredPeak := Proofs.CppWritePeak.retire_peak inner.frame retired (outer.scope+1) fresh ran
      have eq := Option.some.inj rest
      subst out
      apply restore growth ?_ ?_ (Nat.le_refl _)
      · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
      · change inner.frame.state.storage.peak ≤ retired.state.storage.peak
        rw [retiredPeak]
        exact Nat.le_max_left _ _
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
        have retiredPeak := Proofs.CppWritePeak.retire_peak inner.frame retired (outer.scope+1) fresh ran
        have eq := Option.some.inj rest
        subst out
        apply restore growth ?_ ?_ (Nat.le_refl _)
        · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
        · change inner.frame.state.storage.peak ≤ retired.state.storage.peak
          rw [retiredPeak]
          exact Nat.le_max_left _ _
      · simp at actual
    | unit => simp [ScalarResult] at value
    | vector owner element => simp [ScalarResult] at value

end Proofs.CppPeakScope
