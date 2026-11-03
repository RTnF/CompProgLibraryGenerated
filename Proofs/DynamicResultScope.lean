import Proofs.DynamicVectorReturn

namespace Proofs.DynamicResultScope
open Proofs.CppNestedProgram Proofs.DynamicOwnedState

-- Scalar/unit returns leave ownership unchanged; vector returns transfer the
-- returned root before retiring the rest of the exiting scope.
def leave (outer inner : State) (returned : Option Ret) : Option State := match returned with
  | some (.vector root element) => DynamicVectorScope.leave outer inner root element
  | _ => DynamicOwnedCleanup.leave outer inner

theorem sound (outer inner final : State) (s t : NState)
    (before : Realizes outer s) (after : Realizes inner t) (returned : Option Ret)
    (pureRun : leave outer inner returned = some final) :
    ∃ out, s.leave t returned = some out ∧ Realizes final out := by
  cases returned with
  | none =>
    obtain ⟨ran,real,_⟩ := DynamicOwnedCleanup.sound outer inner final s t before after none pureRun
    exact ⟨_,ran,real⟩
  | some value =>
    cases value with
    | scalar x =>
      obtain ⟨ran,real,_⟩ := DynamicOwnedCleanup.sound outer inner final s t before after (some x) pureRun
      exact ⟨_,ran,real⟩
    | unit =>
      obtain ⟨ran,real,_⟩ := DynamicOwnedCleanup.sound outer inner final s t before after none pureRun
      exact ⟨_,by simpa [NState.leave] using ran,real⟩
    | vector root element =>
      obtain ⟨frame,out,_,ran,real,_⟩ := DynamicVectorScope.sound outer inner final s t before after root element pureRun
      exact ⟨out,ran,real⟩

end Proofs.DynamicResultScope
